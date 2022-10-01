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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public static final Map<Obj, Set<Var>> aliasMap = new HashMap<>();
    public static final Map<Pair<?, ?>, Value> valMap = new HashMap<>();
    public static final Map<Pair<JClass, FieldRef>, Set<LoadField>> staticLoadFields = new HashMap<>();
    public static PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
//        for(CSVar var : pta.getCSVars()){
//            for(CSObj obj : pta.getPointsToSet(var)){
//                Set<Var> s = aliasMap.getOrDefault(obj.getObject(), new HashSet<>());
//                s.add(var.getVar());
//                aliasMap.put(obj.getObject(), s);
//            }
//        }
        for(Var var : pta.getVars()){
            for(Obj obj : pta.getPointsToSet(var)){
                Set<Var> s = aliasMap.getOrDefault(obj, new HashSet<>());
                s.add(var);
                aliasMap.put(obj, s);
            }
        }
        icfg.getNodes().forEach(stmt -> {
            if(stmt instanceof LoadField s && s.getFieldAccess() instanceof StaticFieldAccess access){
                Pair<JClass, FieldRef> accessPair = new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef());
                Set<LoadField> set = staticLoadFields.getOrDefault(accessPair, new HashSet<>());
                set.add(s);
                staticLoadFields.put(accessPair, set);
            }
        });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        AtomicBoolean changed = new AtomicBoolean(false);
        in.forEach(((var, value) -> {
            if(out.update(var, value)){
                changed.set(true);
            }
        }));
        return changed.get() ;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        Invoke callSite = (Invoke) edge.getSource();
        Var lVar = callSite.getLValue();
        CPFact result = out.copy();
        if(lVar != null){
            result.remove(lVar);
        }
        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        Invoke callSite = (Invoke) edge.getSource();
        CPFact result = new CPFact();
        List<Var> args = edge.getCallee().getIR().getParams();
        assert args.size() == callSite.getRValue().getArgs().size();
        for(int i = 0;i < args.size();i ++){
            result.update(args.get(i), callSiteOut.get(callSite.getRValue().getArg(i)));
        }
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact result = new CPFact();
        Invoke callSite = (Invoke) edge.getCallSite();
        Var lVar = callSite.getLValue();
        if(lVar != null){
            edge.getReturnVars().forEach(var -> {
                result.update(lVar, cp.meetValue(result.get(lVar), returnOut.get(var)));
            });
        }
        return result;
    }
}
