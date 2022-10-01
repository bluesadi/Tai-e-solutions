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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;
import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    // Call (source)
    public Obj handleTaintSource(Invoke callSite, JMethod callee){
        Type type = callee.getReturnType();
        Source source = new Source(callee, type);
        if(config.getSources().contains(source)){
            return manager.makeTaint(callSite, type);
        }
        return null;
    }

    public Set<Pair<Var, Obj>> handleTaintTransfer(CSCallSite csCallSite, JMethod callee, CSVar base){
        Invoke callSite = csCallSite.getCallSite();
        Var lVar = callSite.getLValue();
        PointerAnalysisResult ptaResult = solver.getResult();
        Set<Pair<Var, Obj>> result = new HashSet<>();
        TaintTransfer transfer;
        if(base != null) {
            // Call (base-to-result)
            Type resultType = callee.getReturnType();
            transfer = new TaintTransfer(callee, TaintTransfer.BASE, TaintTransfer.RESULT, resultType);
            if(config.getTransfers().contains(transfer) && lVar != null){
                Set<CSObj> basePts = ptaResult.getPointsToSet(base);
                basePts.forEach(csObj -> {
                    if(manager.isTaint(csObj.getObject())){
                        result.add(new Pair<>(lVar,
                                manager.makeTaint(manager.getSourceCall(csObj.getObject()), resultType)));
                    }
                });
            }
            // Call (arg-to-base)
            Type baseType = base.getType();
            List<Var> args = callSite.getInvokeExp().getArgs();
            for (int i = 0; i < args.size(); i++) {
                Var arg = args.get(i);
                Set<CSObj> argPts = ptaResult.getPointsToSet(csManager.getCSVar(csCallSite.getContext(), arg));
                transfer = new TaintTransfer(callee, i, TaintTransfer.BASE, baseType);
                if (config.getTransfers().contains(transfer)) {
                    argPts.forEach(csObj -> {
                        if(manager.isTaint(csObj.getObject())){
                            result.add(new Pair<>(base.getVar(),
                                    manager.makeTaint(manager.getSourceCall(csObj.getObject()), baseType)));
                        }
                    });
                }
            }
        }
        // Call (arg-to-result)
        List<Var> args = callSite.getInvokeExp().getArgs();
        Type resultType = callee.getReturnType();
        for (int i = 0; i < args.size(); i++) {
            Var arg = args.get(i);
            Set<CSObj> argPts = ptaResult.getPointsToSet(csManager.getCSVar(csCallSite.getContext(), arg));
            transfer = new TaintTransfer(callee, i, TaintTransfer.RESULT, resultType);
            if (config.getTransfers().contains(transfer)) {
                argPts.forEach(csObj -> {
                    if(manager.isTaint(csObj.getObject())){
                        result.add(new Pair<>(lVar,
                                manager.makeTaint(manager.getSourceCall(csObj.getObject()), resultType)));
                    }
                });
            }
        }
        return result;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        CallGraph<CSCallSite, CSMethod> callGraph = result.getCSCallGraph();
        callGraph.reachableMethods().forEach(csMethod -> {
            callGraph.getCallersOf(csMethod).forEach(csCallSite -> {
                Invoke callSite = csCallSite.getCallSite();
                JMethod callee = csMethod.getMethod();
                List<Var> args = callSite.getInvokeExp().getArgs();
                for(int i = 0;i < args.size();i ++){
                    Var arg = args.get(i);
                    Sink sink = new Sink(callee, i);
                    if(config.getSinks().contains(sink)){
                        int index = i;
                        result.getPointsToSet(arg).forEach(obj -> {
                            if(manager.isTaint(obj)){
                                taintFlows.add(new TaintFlow(manager.getSourceCall(obj), callSite, index));
                            }
                        });
                    }
                }
            });
        });
        return taintFlows;
    }
}
