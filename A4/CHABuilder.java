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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import pascal.taie.language.type.ClassType;
import polyglot.ast.Call;

import java.util.*;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()){
            JMethod method = workList.poll();
            if(callGraph.contains(method)){
                continue;
            }
            callGraph.addReachableMethod(method);
            method.getIR().getStmts().stream().
                    filter(stmt -> stmt instanceof Invoke).forEach(stmt -> {
                Invoke callSite = (Invoke) stmt;
                CallKind kind = null;
                if(callSite.isInterface()) kind = CallKind.INTERFACE;
                else if(callSite.isSpecial()) kind = CallKind.SPECIAL;
                else if(callSite.isStatic()) kind = CallKind.STATIC;
                else if(callSite.isVirtual()) kind = CallKind.VIRTUAL;
                if(kind != null){
                    for(JMethod newMethod : resolve(callSite)){
                        callGraph.addEdge(new Edge<>(kind, callSite, newMethod));
                        workList.add(newMethod);
                    }
                }
            });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        MethodRef methodRef = callSite.getMethodRef();
        Set<JMethod> result = new HashSet<>();
        if(callSite.isInterface() || callSite.isVirtual()){
            JClass rootCls = methodRef.getDeclaringClass();
            Queue<JClass> queue = new LinkedList<>();
            queue.add(rootCls);
            while(!queue.isEmpty()){
                JClass cls = queue.poll();
                JMethod dispatchedMethod = dispatch(cls, methodRef.getSubsignature());
                if(dispatchedMethod != null){
                    result.add(dispatchedMethod);
                }
                if(cls.isInterface()){
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(cls));
                    queue.addAll(hierarchy.getDirectImplementorsOf(cls));
                }else{
                    queue.addAll(hierarchy.getDirectSubclassesOf(cls));
                }
            }
        }else if(callSite.isSpecial()){
            JMethod method = dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature());
            if(method != null) {
                result.add(method);
            }
        }else if(callSite.isStatic()){
            result.add(methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature()));
        }
        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if(method != null && !method.isAbstract()){
            return method;
        }else if(jclass.getSuperClass() == null){
            return null;
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
