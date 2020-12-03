package org.checkerframework.checker.jtc.typestate.graph

import org.checkerframework.checker.jtc.typestate.*

private var uuid = 1L

sealed class AbstractState<N : TNode>(var node: N?)

open class State private constructor(val name: String, node: TStateNode?) : AbstractState<TStateNode>(node) {

  val id = uuid++

  protected constructor(name: String) : this(name, null)

  constructor(node: TStateNode) : this(node.name ?: "unknown:${node.pos.lineCol}", node)

  val isDroppable = node != null && node.isDroppable

  val transitions: MutableMap<TMethodNode, AbstractState<*>> = LinkedHashMap()

  open fun addTransition(transition: TMethodNode, destination: AbstractState<*>) {
    transitions[transition] = destination
  }

  fun isEnd() = transitions.isEmpty()

  fun canEndHere() = isDroppable || isEnd()

  override fun toString(): String {
    return if (isDroppable) "State{name=$name, droppable}" else "State{name=$name}"
  }
}

class DecisionState(node: TDecisionStateNode) : AbstractState<TDecisionStateNode>(node) {

  val transitions: MutableMap<TDecisionNode, State> = LinkedHashMap()

  fun addTransition(transition: TDecisionNode, destination: State) {
    transitions[transition] = destination
  }

  override fun toString(): String {
    return "DecisionState{node=$node}"
  }
}

class EndState : State("end") {
  override fun addTransition(transition: TMethodNode, destination: AbstractState<*>) {
    throw AssertionError("end state should have no transitions")
  }
}
