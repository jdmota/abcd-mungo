package jatyc.core

import jatyc.subtyping.syncronous_subtyping.ProtocolSyncSubtyping

object Subtyping {

  fun isSubtype(a: JTCType, b: JTCType): Boolean {
    return when (a) {
      is JTCUnknownType -> b is JTCUnknownType
      is JTCSharedType -> when (b) {
        is JTCUnknownType -> true
        is JTCSharedType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { isSubtype(a, it) }
        is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
        else -> false
      }
      is JTCLinearType -> when (b) {
        is JTCUnknownType -> true
        is JTCLinearType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { isSubtype(a, it) }
        is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
        else -> false
        //is JTCNoProtocolType -> javaType.isSubtype(other.javaType) && !other.exact
      }
      is JTCStateType -> when (b) {
        is JTCUnknownType -> true
        is JTCSharedType -> a.javaType.isSubtype(b.javaType) && a.state.canDropHere() // NEW
        is JTCLinearType -> a.javaType.isSubtype(b.javaType)
        is JTCStateType -> a.javaType.isSubtype(b.javaType) && ProtocolSyncSubtyping.isSubtype(a.state, b.state)
        is JTCUnionType -> b.types.any { isSubtype(a, it) }
        is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
        else -> false
        //is JTCNoProtocolType -> javaType.isSubtype(other.javaType) && !other.exact
      }
      is JTCPrimitiveType -> when (b) {
        is JTCUnknownType -> true
        is JTCPrimitiveType -> a.javaType.isSubtype(b.javaType)
        is JTCUnionType -> b.types.any { isSubtype(a, it) }
        is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
        else -> false
      }
      is JTCNullType -> when (b) {
        is JTCUnknownType -> true
        is JTCNullType -> true
        is JTCUnionType -> b.types.any { isSubtype(a, it) }
        is JTCIntersectionType -> b.types.all { isSubtype(a, it) }
        else -> false
      }
      is JTCBottomType -> true
      is JTCUnionType -> when (b) {
        is JTCUnknownType -> true
        is JTCUnionType -> a.types.all { itA -> isSubtype(itA, b) } || b.types.any { itB -> isSubtype(a, itB) }
        is JTCIntersectionType -> a.types.all { itA -> isSubtype(itA, b) } || b.types.all { itB -> isSubtype(a, itB) }
        else -> a.types.all { itA -> isSubtype(itA, b) }
      }
      is JTCIntersectionType -> when (b) {
        is JTCUnknownType -> true
        is JTCUnionType -> a.types.any { itA -> isSubtype(itA, b) } || b.types.any { itB -> isSubtype(a, itB) }
        is JTCIntersectionType -> a.types.any { itA -> isSubtype(itA, b) } || b.types.all { itB -> isSubtype(a, itB) }
        else -> a.types.any { itA -> isSubtype(itA, b) }
      }
    }
  }

  fun refineIntersection(a: JTCType, b: JTCType): JTCType? {
    if (areExclusive(a, b)) {
      return JTCBottomType.SINGLETON
    }
    if (a is JTCStateType && b is JTCLinearType) {
      return attemptDowncast(a, b)
    }
    if (a is JTCLinearType && b is JTCStateType) {
      return attemptDowncast(b, a)
    }
    if (a is JTCSharedType && b is JTCLinearType) {
      return attemptRefineToDroppable(a, b)
    }
    if (b is JTCSharedType && a is JTCLinearType) {
      return attemptRefineToDroppable(b, a)
    }
    return null
  }

  private fun areExclusive(a: JTCType, b: JTCType): Boolean {
    return when (a) {
      is JTCLinearType -> b is JTCPrimitiveType || b is JTCNullType
      is JTCStateType -> b is JTCPrimitiveType || b is JTCNullType || (b is JTCSharedType && !a.state.canDropHere())
      is JTCSharedType -> b is JTCPrimitiveType || b is JTCNullType || (b is JTCStateType && !b.state.canDropHere())
      is JTCPrimitiveType -> b is JTCNullType || b is JTCSharedType || b is JTCLinearType || b is JTCStateType
      is JTCNullType -> b is JTCPrimitiveType || b is JTCSharedType || b is JTCLinearType || b is JTCStateType
      else -> false
    }
  }

  private fun attemptDowncast(from: JTCStateType, to: JTCLinearType): JTCType? {
    // If downcasting...
    if (to.javaType.isSubtype(from.javaType)) {
      return JTCType.createIntersection(
        to.graph.getAllConcreteStates()
          .filter { ProtocolSyncSubtyping.isSubtype(it, from.state) }
          .map { JTCStateType(to.javaType, to.graph, it) }
      )
    }
    return null
  }

  private fun attemptRefineToDroppable(a: JTCSharedType, b: JTCLinearType): JTCType {
    if (a.javaType.isSubtype(b.javaType)) {
      val graph = a.javaType.getGraph() ?: return JTCBottomType.SINGLETON
      return JTCType.createUnion(
        graph.getAllConcreteStates().filter { it.canDropHere() }.map { JTCStateType(a.javaType, graph, it) }
      )
    }
    if (b.javaType.isSubtype(a.javaType)) {
      return JTCType.createUnion(
        b.graph.getAllConcreteStates().filter { it.canDropHere() }.map { JTCStateType(b.javaType, b.graph, it) }
      )
    }
    return JTCBottomType.SINGLETON
  }

}
