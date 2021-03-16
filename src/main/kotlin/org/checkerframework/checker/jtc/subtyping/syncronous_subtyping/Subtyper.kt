package org.checkerframework.checker.jtc.subtyping.syncronous_subtyping

import org.checkerframework.checker.jtc.typestate.graph.*

class Subtyper {

  val errors = mutableListOf<String>()

  fun subtyping(g1: Graph, g2: Graph, currentStates: Pair<AbstractState<*>, AbstractState<*>>, marked: Set<Pair<AbstractState<*>, AbstractState<*>>> = emptySet()) {
    if (currentStates in marked) return
    val first = currentStates.first
    val second = currentStates.second
    when {
      first is EndState && second is EndState -> {
      }
      first is State && second is State && first !is EndState && second !is EndState -> {
        val t1 = first.normalizedTransitions
        val t2 = second.normalizedTransitions
        if (!t1.keys.containsAll(t2.keys)) { // Input contravariance
          val common = t2.keys.intersect(t1.keys)
          common.forEach {
            subtyping(g1, g2, t1[it]!! to t2[it]!!, marked + currentStates)
          }
          errors.add(inputErrorMsg(g1, g2, currentStates, t2.minus(common).map { it.key.name }))
        } else {
          t2.keys.forEach {
            subtyping(g1, g2, t1[it]!! to t2[it]!!, marked + currentStates)
          }
        }
      }
      first is DecisionState && second is DecisionState -> {
        val t1 = first.normalizedTransitions
        val t2 = second.normalizedTransitions
        if (!t2.keys.containsAll(t1.keys)) { // Output contravariance
          val common = t1.keys.intersect(t2.keys)
          common.forEach {
            subtyping(g1, g2, t1[it]!! to t2[it]!!, marked + currentStates)
          }
          errors.add(outputErrorMsg(g1, g2, currentStates, t1.minus(common).map { it.key.label }))
        } else {
          t1.keys.forEach {
            subtyping(g1, g2, t1[it]!! to t2[it]!!, marked + currentStates)
          }
        }
      }
      else -> "Discordant states error: state $first in ${g1.userPath} is ${type(first)} while state $second in ${g2.userPath} is ${type(second)}\n"
    }
  }

  private fun type(state: AbstractState<*>): String {
    return when (state) {
      is EndState -> "END"
      is State -> "INPUT"
      is DecisionState -> "OUTPUT"
    }
  }

  private fun inputErrorMsg(fn1: Graph, fn2: Graph, currStates: Pair<AbstractState<*>, AbstractState<*>>, diff: List<String>): String {
    val first = currStates.first.format()
    val second = currStates.second.format()
    return "Input contravariance error: $diff transition(s) in state $second of ${fn2.userPath} are not included in state $first of ${fn1.userPath}\n"
  }

  private fun outputErrorMsg(fn1: Graph, fn2: Graph, currStates: Pair<AbstractState<*>, AbstractState<*>>, diff: List<String>): String {
    val first = currStates.first.format()
    val second = currStates.second.format()
    return "Output covariance error: $diff transition(s) in state $first of ${fn1.userPath} are not included in state $second of ${fn2.userPath}\n"
  }
}
