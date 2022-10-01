/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if(!callGraph.contains(csMethod)){
            callGraph.addReachableMethod(csMethod);
            csMethod.getMethod().getIR().getStmts().forEach(stmt -> stmt.accept(new StmtProcessor(csMethod)));
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            Pointer ptr = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context ctx = contextSelector.selectHeapContext(csMethod, obj);
            PointsToSet pts = PointsToSetFactory.make(csManager.getCSObj(ctx, obj));
            workList.addEntry(ptr, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(Invoke callSite) {
            if(callSite.isStatic()){
                JMethod callee = resolveCallee(null, callSite);
                CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
                Context calleeContext = contextSelector.selectContext(csCallSite, callee);
                processSingleCall(csCallSite, csManager.getCSMethod(calleeContext, callee));
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()){
                addPFGEdge(
                        csManager.getStaticField(stmt.getFieldRef().resolve()),
                        csManager.getCSVar(context, stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if(!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            PointsToSet pts = source.getPointsToSet();
            if(!pts.isEmpty()){
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(pointer, pts);
            if(pointer instanceof CSVar ptr){
                Var var = ptr.getVar();
                Context ctx = ptr.getContext();
                delta.forEach(obj -> {
                    // StoreField
                    var.getStoreFields().forEach(stmt -> {
                        addPFGEdge(
                                csManager.getCSVar(ctx, stmt.getRValue()),
                                csManager.getInstanceField(obj, stmt.getFieldAccess().getFieldRef().resolve())
                        );
                    });
                    // LoadField
                    var.getLoadFields().forEach(stmt -> {
                        addPFGEdge(
                                csManager.getInstanceField(obj, stmt.getFieldAccess().getFieldRef().resolve()),
                                csManager.getCSVar(ctx, stmt.getLValue())
                        );
                    });
                    // StoreArray
                    var.getStoreArrays().forEach(stmt -> {
                        addPFGEdge(
                                csManager.getCSVar(ctx, stmt.getRValue()),
                                csManager.getArrayIndex(obj)
                        );
                    });
                    // LoadArray
                    var.getLoadArrays().forEach(stmt -> {
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(ctx, stmt.getLValue())
                        );
                    });
                    // ProcessCall
                    processCall(ptr, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = PointsToSetFactory.make();
        pointsToSet.objects()
                .filter(ptr -> !pointer.getPointsToSet().contains(ptr))
                .forEach(delta::addObject);
        if(!delta.isEmpty()){
            delta.forEach(obj -> pointer.getPointsToSet().addObject(obj));
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, delta));
        }
        return delta;
    }

    private void processSingleCall(CSCallSite csCallSite, CSMethod callee){
        Invoke callSite = csCallSite.getCallSite();
        Context callerContext = csCallSite.getContext();
        Context calleeContext = callee.getContext();
        if(!callGraph.getCalleesOf(csCallSite).contains(callee)){
            CallKind kind = null;
            if(callSite.isInterface()) kind = CallKind.INTERFACE;
            else if(callSite.isSpecial()) kind = CallKind.SPECIAL;
            else if(callSite.isStatic()) kind = CallKind.STATIC;
            else if(callSite.isVirtual()) kind = CallKind.VIRTUAL;
            if(kind != null) {
                callGraph.addEdge(new Edge<>(kind, csCallSite, callee));
                addReachable(callee);
                List<Var> args = callee.getMethod().getIR().getParams();
                assert args.size() == callSite.getRValue().getArgs().size();
                for(int i = 0;i < args.size();i ++){
                    addPFGEdge(
                            csManager.getCSVar(callerContext, callSite.getRValue().getArg(i)),
                            csManager.getCSVar(calleeContext, args.get(i))
                    );
                }
                if(callSite.getLValue() != null){
                    callee.getMethod().getIR().getReturnVars().forEach(ret -> {
                        addPFGEdge(
                                csManager.getCSVar(calleeContext, ret),
                                csManager.getCSVar(callerContext, callSite.getLValue())
                        );
                    });
                }
            }
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        recv.getVar().getInvokes().forEach(callSite -> {
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), callSite);
            JMethod callee = resolveCallee(recvObj, callSite);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
            workList.addEntry(
                    csManager.getCSVar(calleeContext, callee.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );
            processSingleCall(csCallSite, csCallee);
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
