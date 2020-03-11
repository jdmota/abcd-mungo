// Generated from org\checkerframework\checker\mungo\typestate\parser\Typestate.g4 by ANTLR 4.8

package org.checkerframework.checker.mungo.typestate.parser;
import org.checkerframework.checker.mungo.typestate.ast.*;
import static org.checkerframework.checker.mungo.typestate.ast.Position.tokenToPos;
import static org.checkerframework.checker.mungo.typestate.Utils.map;

import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link TypestateParser}.
 */
public interface TypestateListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link TypestateParser#typestate_declaration}.
	 * @param ctx the parse tree
	 */
	void enterTypestate_declaration(TypestateParser.Typestate_declarationContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypestateParser#typestate_declaration}.
	 * @param ctx the parse tree
	 */
	void exitTypestate_declaration(TypestateParser.Typestate_declarationContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypestateParser#typestate_body}.
	 * @param ctx the parse tree
	 */
	void enterTypestate_body(TypestateParser.Typestate_bodyContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypestateParser#typestate_body}.
	 * @param ctx the parse tree
	 */
	void exitTypestate_body(TypestateParser.Typestate_bodyContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypestateParser#state_declaration}.
	 * @param ctx the parse tree
	 */
	void enterState_declaration(TypestateParser.State_declarationContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypestateParser#state_declaration}.
	 * @param ctx the parse tree
	 */
	void exitState_declaration(TypestateParser.State_declarationContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypestateParser#state}.
	 * @param ctx the parse tree
	 */
	void enterState(TypestateParser.StateContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypestateParser#state}.
	 * @param ctx the parse tree
	 */
	void exitState(TypestateParser.StateContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypestateParser#method}.
	 * @param ctx the parse tree
	 */
	void enterMethod(TypestateParser.MethodContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypestateParser#method}.
	 * @param ctx the parse tree
	 */
	void exitMethod(TypestateParser.MethodContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypestateParser#decision_state}.
	 * @param ctx the parse tree
	 */
	void enterDecision_state(TypestateParser.Decision_stateContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypestateParser#decision_state}.
	 * @param ctx the parse tree
	 */
	void exitDecision_state(TypestateParser.Decision_stateContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypestateParser#decision}.
	 * @param ctx the parse tree
	 */
	void enterDecision(TypestateParser.DecisionContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypestateParser#decision}.
	 * @param ctx the parse tree
	 */
	void exitDecision(TypestateParser.DecisionContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypestateParser#id}.
	 * @param ctx the parse tree
	 */
	void enterId(TypestateParser.IdContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypestateParser#id}.
	 * @param ctx the parse tree
	 */
	void exitId(TypestateParser.IdContext ctx);
}