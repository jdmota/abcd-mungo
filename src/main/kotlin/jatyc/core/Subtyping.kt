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

  fun upcast(t: JTCType, j: JavaType): JTCType? {
    return when (t) {
      is JTCUnionType -> JTCUnionType(t.types.map { upcast(it,j)!! }.toSet())
      is JTCIntersectionType -> JTCIntersectionType(t.types.map { upcast(it,j)!! }.toSet())
      is JTCStateType -> j.getGraph()?.getAllConcreteStates()?.map { JTCStateType(j, j.getGraph()!!,it) }?.filter { isSubtype(t, it) }?.let { JTCIntersectionType(it.toSet()) }
      is JTCBottomType -> JTCBottomType.SINGLETON
      else -> null //should it be the top type ?
    }
  }

  fun downcast(t: JTCType, j: JavaType): JTCType? {
    return when (t) {
      is JTCUnionType -> JTCUnionType(t.types.map { downcast(it,j)!! }.toSet())
      is JTCIntersectionType -> JTCIntersectionType(t.types.map { downcast(it,j)!! }.toSet())
      is JTCStateType -> j.getGraph()?.getAllConcreteStates()?.map { JTCStateType(j, j.getGraph()!!,it) }?.filter { isSubtype(t, it) }?.let { JTCUnionType(it.toSet()) }
      is JTCBottomType -> JTCBottomType.SINGLETON
      else -> null //should it be the top type ?
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
      is JTCSharedType -> when (b) {
        is JTCPrimitiveType,
        is JTCNullType -> true
        is JTCSharedType -> areNotRelated(a.javaType, b.javaType)
        is JTCLinearType -> areNotRelated(a.javaType, b.javaType)
        is JTCStateType -> !b.state.canDropHere() || areNotRelated(a.javaType, b.javaType)
        else -> false
      }
      is JTCLinearType -> when (b) {
        is JTCPrimitiveType,
        is JTCNullType -> true
        is JTCSharedType -> areNotRelated(a.javaType, b.javaType)
        is JTCLinearType -> areNotRelated(a.javaType, b.javaType)
        is JTCStateType -> areNotRelated(a.javaType, b.javaType)
        else -> false
      }
      is JTCStateType -> when (b) {
        is JTCPrimitiveType,
        is JTCNullType -> true
        is JTCSharedType -> !a.state.canDropHere() || areNotRelated(a.javaType, b.javaType)
        is JTCLinearType -> areNotRelated(a.javaType, b.javaType)
        is JTCStateType -> areNotRelated(a.javaType, b.javaType)
        else -> false
      }
      is JTCPrimitiveType -> b is JTCNullType || b is JTCSharedType || b is JTCLinearType || b is JTCStateType
      is JTCNullType -> b is JTCPrimitiveType || b is JTCSharedType || b is JTCLinearType || b is JTCStateType
      else -> false
    }
  }

  private fun attemptDowncast(from: JTCStateType, to: JTCLinearType): JTCType? {
    // If downcasting...
    if (to.javaType.isSubtype(from.javaType)) {
      return JTCType.createUnion(
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

  private fun areNotRelated(a: JavaType, b: JavaType): Boolean {
    // Two types are not related if they are not subtypes of one another
    // And if one of them is final
    // This means that the intersection of both must be empty
    return !a.isSubtype(b) && !b.isSubtype(a) && (a.isFinal() || b.isFinal())
  }

}
