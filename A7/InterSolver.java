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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.collection.Pair;
import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.*;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        for(Node node : icfg){
            result.setOutFact(node, analysis.newInitialFact());
        }
        icfg.entryMethods().forEach(method -> {
            Node entry = icfg.getEntryOf(method);
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        });
    }

    private Value meetValue(Value v1, Value v2) {
        if(v1.isConstant() && v2.isConstant()){
            if(v1.equals(v2)){
                return Value.makeConstant(v1.getConstant());
            }else{
                return Value.getNAC();
            }
        }else if(v1.isNAC() || v2.isNAC()){
            return Value.getNAC();
        }else if(v1.isConstant() && v2.isUndef()){
            return Value.makeConstant(v1.getConstant());
        }else if(v2.isConstant() && v1.isUndef()){
            return Value.makeConstant(v2.getConstant());
        }
        return Value.getUndef();
    }

    @SuppressWarnings("unchecked")
    private void handleStoreField(Stmt stmt, CPFact in){
        if(stmt instanceof StoreField s){
            if(!ConstantPropagation.canHoldInt(s.getRValue())) return;
            if(s.getFieldAccess() instanceof InstanceFieldAccess access) {
                Var base = access.getBase();
                pta.getPointsToSet(base).forEach(obj -> {
                    Pair<Obj, FieldRef> accessPair = new Pair<>(obj, s.getFieldRef());
                    Value newVal = ConstantPropagation.evaluate(s.getRValue(), in);
                    Value oldVal = valMap.getOrDefault(accessPair, Value.getUndef());
                    newVal = meetValue(oldVal, newVal);
                    valMap.put(accessPair, newVal);
                    if(!oldVal.equals(newVal)){
                        Set<Var> alias = aliasMap.get(obj);
                        alias.forEach(var -> {
                            var.getLoadFields().stream()
                                    .filter(loadStmt -> loadStmt.getFieldAccess().getFieldRef().equals(s.getFieldRef()))
                                    .forEach(loadStmt -> workList.offer((Node) loadStmt));
                        });
                    }
                });
            }else if(s.getFieldAccess() instanceof StaticFieldAccess access){
                JClass clz = access.getFieldRef().getDeclaringClass();
                Pair<JClass, FieldRef> accessPair = new Pair<>(clz, s.getFieldRef());
                Value oldVal = valMap.getOrDefault(accessPair, Value.getUndef());
                Value newVal = ConstantPropagation.evaluate(s.getRValue(), in);
                newVal = meetValue(oldVal, newVal);
                valMap.put(accessPair, newVal);
                if (!oldVal.equals(newVal)) {
                    staticLoadFields.getOrDefault(accessPair, new HashSet<>()).forEach(loadStmt -> {
                        workList.offer((Node) loadStmt);
                    });
                }
            }
        }
    }

    @SuppressWarnings("unchecked")
    private void handleStoreArray(Stmt stmt, CPFact in){
        if(stmt instanceof StoreArray s){
            if(!ConstantPropagation.canHoldInt(s.getRValue())) return;
            ArrayAccess access = s.getArrayAccess();
            Value index = ConstantPropagation.evaluate(access.getIndex(), in);
            if(index.isUndef()) return; // Ignore UNDEF
            Var base = access.getBase();
            pta.getPointsToSet(base).forEach(obj -> {
                Pair<Obj, Value> accessPair = new Pair<>(obj, index);
                Value newVal = ConstantPropagation.evaluate(s.getRValue(), in);
                Value oldVal = valMap.getOrDefault(accessPair, Value.getUndef());
                newVal = meetValue(oldVal, newVal);
                valMap.put(accessPair, newVal);
                if(!oldVal.equals(newVal)){
                    Set<Var> alias = aliasMap.get(obj);
                    alias.forEach(var -> {
                        var.getLoadArrays().forEach(loadStmt -> workList.offer((Node) loadStmt));
                    });
                }
            });
        }
    }

    @SuppressWarnings("unchecked")
    private void doSolve() {
        workList = new LinkedList<>(icfg.getNodes());
        while(!workList.isEmpty()){
            Node node = workList.poll();
            CPFact in = new CPFact();
            CPFact out = (CPFact) result.getOutFact(node);
            for(ICFGEdge<Node> edge : icfg.getInEdgesOf(node)){
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(edge.getSource())), (Fact) in);
            }
            handleStoreField((Stmt) node, in);
            handleStoreArray((Stmt) node, in);
            if(analysis.transferNode(node, (Fact) in, (Fact) out)){
                icfg.getSuccsOf(node).forEach(workList::offer);
            }
            result.setInFact(node, (Fact) in);
            result.setOutFact(node, (Fact) out);
        }
    }

}
