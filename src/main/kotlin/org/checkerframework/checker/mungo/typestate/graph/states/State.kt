package org.checkerframework.checker.mungo.typestate.graph.states

import org.checkerframework.checker.mungo.typestate.ast.TMethodNode
import org.checkerframework.checker.mungo.typestate.ast.TStateNode

open class State : AbstractState<TStateNode> {
  var name: String

  protected constructor(name: String) : super(null) {
    this.name = name
  }

  // TODO include source location in the name of unknown states

  constructor(node: TStateNode) : super(node) {
    name = node.name ?: "unknown"
  }

  val transitions: MutableMap<TMethodNode, AbstractState<*>> = HashMap()

  open fun addTransition(transition: TMethodNode, destination: AbstractState<*>) {
    transitions[transition] = destination
  }

  override fun toString(): String {
    return "State{name=$name}"
  }
}
