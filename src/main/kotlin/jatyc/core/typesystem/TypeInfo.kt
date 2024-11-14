package jatyc.core.typesystem

import jatyc.core.*
import jatyc.core.cfg.MethodCall
import jatyc.utils.JTCUtils

sealed class TypeInfo {
  abstract val javaType: JavaType
  abstract val jtcType: JTCType

  fun debugIsPrimitive(): Boolean {
    return jtcType is JTCPrimitiveType
  }

  fun checkJavaTypeInvariant(javaType: JavaType) {
    if (this.javaType !== javaType) {
      JTCUtils.printStack()
      error("TypeInfo.javaType: expected ${this.javaType} got $javaType")
    }
  }

  abstract fun isSubtype(other: TypeInfo): Boolean

  abstract fun isSubtype(other: JTCType): Boolean

  fun isUnknown(): Boolean {
    return JTCUnknownType.SINGLETON.isSubtype(jtcType)
  }

  fun isBottom(): Boolean {
    return jtcType.isSubtype(JTCBottomType.SINGLETON)
  }

  fun isNull(): Boolean {
    return jtcType.isSubtype(JTCNullType.SINGLETON)
  }

  fun isNullable(): Boolean {
    return JTCNullType.SINGLETON.isSubtype(jtcType)
  }

  fun isInDroppableStateNotEnd(): Boolean {
    return TypecheckUtils.isInDroppableStateNotEnd(jtcType)
  }

  fun canDrop(): Boolean {
    return TypecheckUtils.canDrop(jtcType)
  }

  fun requiresLinear(ref: Reference): Boolean {
    return TypecheckUtils.requiresLinear(ref, jtcType)
  }

  fun check(utils: TypecheckUtils, call: MethodCall): Boolean {
    return utils.check(jtcType, call)
  }

  abstract fun toShared(): TypeInfo
  abstract fun toUnknown(): TypeInfo
  abstract fun toBottom(): TypeInfo
  abstract fun intersect(other: JTCType): TypeInfo
  abstract fun cast(target: JavaType): TypeInfo
  abstract fun ensures(ensures: JTCType): TypeInfo
  abstract fun refine(utils: TypecheckUtils, call: MethodCall, predicate: (String) -> Boolean): TypeInfo
  abstract fun refineToNonNull(): TypeInfo
  abstract fun refineToNull(): TypeInfo

  fun format(): String {
    return jtcType.format()
  }

  abstract override fun toString(): String

  companion object {
    var useTypestateTrees = false

    fun setUseTypestateTreesFlag(flag: Boolean) {
      useTypestateTrees = flag
    }

    fun createUnion(javaType: JavaType, list: List<TypeInfo>): TypeInfo {
      list.forEach { it.checkJavaTypeInvariant(javaType) }
      return if (useTypestateTrees) {
        if (list.isEmpty()) {
          TypestateTreeInfo(javaType, JTCBottomType.SINGLETON)
        } else {
          list.singleOrNull() ?: TypestateTreeInfo(list.map { (it as TypestateTreeInfo).tree }.reduce { acc, it -> TypestateTreeManager.mergeTT(acc, it)})
        }
      } else {
        BasicTypeInfo(javaType, JTCType.createUnion(list.map { it.jtcType }))
      }
    }

    fun make(javaType: JavaType, jtcType: JTCType): TypeInfo {
      return if (useTypestateTrees) TypestateTreeInfo(javaType, jtcType) else BasicTypeInfo(javaType, jtcType)
    }

    fun make(prim: JTCPrimitiveType): TypeInfo {
      return make(prim.javaType, prim)
    }

    fun make(type: JTCSharedType): TypeInfo {
      return make(type.javaType, type)
    }
  }
}

class BasicTypeInfo internal constructor(override val javaType: JavaType, override val jtcType: JTCType) : TypeInfo() {
  override fun isSubtype(other: TypeInfo): Boolean {
    return jtcType.isSubtype(other.jtcType)
  }

  override fun isSubtype(other: JTCType): Boolean {
    return jtcType.isSubtype(other)
  }

  override fun toShared(): TypeInfo {
    return BasicTypeInfo(javaType, jtcType.toShared())
  }

  override fun toUnknown(): TypeInfo {
    return BasicTypeInfo(javaType, JTCUnknownType.SINGLETON)
  }

  override fun toBottom(): TypeInfo {
    return BasicTypeInfo(javaType, JTCBottomType.SINGLETON)
  }

  override fun intersect(other: JTCType): TypeInfo {
    return BasicTypeInfo(javaType, jtcType.intersect(other))
  }

  override fun cast(target: JavaType): TypeInfo {
    return BasicTypeInfo(target, Subtyping.cast(jtcType, target, false))
  }

  override fun ensures(ensures: JTCType): TypeInfo {
    return BasicTypeInfo(javaType, TypecheckUtils.invariant(jtcType).intersect(ensures))
  }

  override fun refine(utils: TypecheckUtils, call: MethodCall, predicate: (String) -> Boolean): TypeInfo {
    return BasicTypeInfo(javaType, utils.refine(jtcType, call, predicate))
  }

  override fun refineToNonNull(): TypeInfo {
    return BasicTypeInfo(javaType, TypecheckUtils.refineToNonNull(jtcType))
  }

  override fun refineToNull(): TypeInfo {
    return BasicTypeInfo(javaType, TypecheckUtils.refineToNull(jtcType))
  }

  override fun toString(): String {
    return "BasicTypeInfo{$javaType, $jtcType}"
  }
}

class TypestateTreeInfo internal constructor(val tree: TypestateTree) : TypeInfo() {
  internal constructor(javaType: JavaType, jtcType: JTCType) : this(TypestateTreeManager.make(javaType, jtcType))
  internal constructor(tree: TypestateTree, fn: (JTCType) -> JTCType) : this(TypestateTreeManager.visit(tree, fn))

  override val javaType get() = tree.jc
  override val jtcType get() = tree.ts

  override fun isSubtype(other: TypeInfo): Boolean {
    if (other is TypestateTreeInfo) {
      return TypestateTreeManager.isSubtype(tree, other.tree)
    }
    error("INTERNAL ERROR")
  }

  override fun isSubtype(other: JTCType): Boolean {
    // Even if this TS has children nodes, it is fine to just check the root types
    // because the children nodes (which provide more precise information)
    // are on the left of the subtyping check
    return jtcType.isSubtype(other)
  }

  override fun toShared(): TypeInfo {
    return TypestateTreeInfo(tree) { it.toShared() }
  }

  override fun toUnknown(): TypeInfo {
    return TypestateTreeInfo(javaType, JTCUnknownType.SINGLETON)
  }

  override fun toBottom(): TypeInfo {
    return TypestateTreeInfo(javaType, JTCBottomType.SINGLETON)
  }

  override fun intersect(other: JTCType): TypeInfo {
    // When doing actual casts, intersecting does nothing
    return this
  }

  override fun cast(target: JavaType): TypeInfo {
    if (javaType == target) {
      return this
    }
    return TypestateTreeInfo(when {
      // Upcast
      javaType.isSubtype(target) -> TypestateTreeManager.upcastTT(tree, target) ?: TypestateTreeManager.make(target, Subtyping.cast(jtcType, target, true))
      // Downcast
      target.isSubtype(javaType) -> TypestateTreeManager.downcastTT(tree, target) ?: TypestateTreeManager.make(target, Subtyping.cast(jtcType, target, true))
      // Impossible cast
      else -> TypestateTreeManager.make(target, JTCUnknownType.SINGLETON)
    })
  }

  override fun ensures(ensures: JTCType): TypeInfo {
    return TypestateTreeInfo(javaType, TypecheckUtils.invariant(jtcType).intersect(ensures))
  }

  override fun refine(utils: TypecheckUtils, call: MethodCall, predicate: (String) -> Boolean): TypeInfo {
    return TypestateTreeInfo(TypestateTreeManager.evolveTT(utils, tree, call, predicate))
  }

  override fun refineToNonNull(): TypeInfo {
    return TypestateTreeInfo(tree) { TypecheckUtils.refineToNonNull(it) }
  }

  override fun refineToNull(): TypeInfo {
    return TypestateTreeInfo(tree) { TypecheckUtils.refineToNull(it) }
  }

  override fun toString(): String {
    return "TypestateTreeInfo{$tree}"
  }
}
