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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.concurrent.atomic.AtomicBoolean;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        cfg.getIR().getParams().forEach(var -> {
            if(canHoldInt(var)) {
                fact.update(var, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach(((var, value) -> {
            target.update(var, meetValue(value, target.get(var)));
        }));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
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

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        AtomicBoolean changed = new AtomicBoolean(false);
        in.forEach(((var, value) -> {
            if(out.update(var, value)){
                changed.set(true);
            }
        }));
        if(stmt instanceof DefinitionStmt<?, ?> s){
            if(s.getLValue() instanceof Var var && canHoldInt(var)) {
                CPFact inCopy = in.copy();
                Value removedVal = inCopy.get(var);
                inCopy.remove(var);
                Value newVal = evaluate(s.getRValue(), in);
                out.update(var, newVal);
                return !removedVal.equals(newVal) || changed.get();
            }
        }
        return changed.get();
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if(exp instanceof IntLiteral e){
            return Value.makeConstant(e.getValue());
        }else if(exp instanceof Var var){
            if(in.get(var).isConstant()){
                return Value.makeConstant(in.get(var).getConstant());
            }
            return in.get(var);
        }else if(exp instanceof BinaryExp b){
            Value v1 = evaluate(b.getOperand1(), in);
            Value v2 = evaluate(b.getOperand2(), in);
            if(v2.isConstant() && v2.getConstant() == 0
                    && b.getOperator() instanceof ArithmeticExp.Op op){
                if(op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM){
                    return Value.getUndef();
                }
            }
            if(v1.isConstant() && v2.isConstant()){
                int c1 = v1.getConstant(), c2 = v2.getConstant();
                if(b.getOperator() instanceof ArithmeticExp.Op op){
                    switch (op){
                        case ADD -> {
                            return Value.makeConstant(c1 + c2);
                        }
                        case SUB -> {
                            return Value.makeConstant(c1 - c2);
                        }
                        case MUL -> {
                            return Value.makeConstant(c1 * c2);
                        }
                        case DIV -> {
                            return Value.makeConstant(c1 / c2);
                        }
                        case REM -> {
                            return Value.makeConstant(c1 % c2);
                        }
                    }
                }else if(b.getOperator() instanceof ShiftExp.Op op){
                    switch (op){
                        case SHL -> {
                            return Value.makeConstant(c1 << c2);
                        }
                        case SHR -> {
                            return Value.makeConstant(c1 >> c2);
                        }
                        case USHR -> {
                            return Value.makeConstant(c1 >>> c2);
                        }
                    }
                }else if(b.getOperator() instanceof BitwiseExp.Op op){
                    switch (op){
                        case OR -> {
                            return Value.makeConstant(c1 | c2);
                        }
                        case AND -> {
                            return Value.makeConstant(c1 & c2);
                        }
                        case XOR -> {
                            return Value.makeConstant(c1 ^ c2);
                        }
                    }
                }else if(b.getOperator() instanceof ConditionExp.Op op){
                    switch (op){
                        case EQ -> {
                            return Value.makeConstant(c1 == c2 ? 1 : 0);
                        }
                        case NE -> {
                            return Value.makeConstant(c1 != c2 ? 1 : 0);
                        }
                        case LT -> {
                            return Value.makeConstant(c1 < c2 ? 1 : 0);
                        }
                        case GT -> {
                            return Value.makeConstant(c1 > c2 ? 1 : 0);
                        }
                        case LE -> {
                            return Value.makeConstant(c1 <= c2 ? 1 : 0);
                        }
                        case GE -> {
                            return Value.makeConstant(c1 >= c2 ? 1 : 0);
                        }
                    }
                }
            }else if(v1.isNAC() || v2.isNAC()){
                return Value.getNAC();
            }
            return Value.getUndef();
        }
        return Value.getNAC();
    }
}
