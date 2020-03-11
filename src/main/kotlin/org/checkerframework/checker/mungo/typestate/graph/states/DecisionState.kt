package org.checkerframework.checker.mungo.typestate.graph.states

import org.checkerframework.checker.mungo.typestate.ast.TDecisionNode
import org.checkerframework.checker.mungo.typestate.ast.TDecisionStateNode

class DecisionState(node: TDecisionStateNode?) : AbstractState<TDecisionStateNode, TDecisionNode>(node) {
  override fun toString(): String {
    return "DecisionState{node=$node}"
  }
}
