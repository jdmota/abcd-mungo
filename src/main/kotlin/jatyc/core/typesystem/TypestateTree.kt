package jatyc.core.typesystem

import jatyc.core.*
import jatyc.core.cfg.MethodCall

class TypestateTree constructor(val jc: JavaType, val ts: JTCType, val children: List<TypestateTree>) {
  fun clss(): Set<JavaType> = children.map { it.jc }.toSet()

  fun toSimpleString(): String {
    return "($jc:$ts:[${children.size}])"
  }

  override fun toString(): String {
    return "($jc:$ts:[${children.map { it.toSimpleString() }}])"
  }
}

object TypestateTreeUtilities {
  fun find(j: JavaType, tts: List<TypestateTree>): TypestateTree? = tts.find { it.jc == j }

  // To build the path from "a" to "b" we start on "b" and go up in the hierarchy and build the path in reverse
  private fun path(a: JavaType, b: JavaType): List<JavaType>? {
    return if (a == b) {
      emptyList()
    } else {
      val supB = b.getSingleSuperType() ?: return null
      path(a, supB)?.plus(b)
    }
  }

  private fun closestByPath(path: List<JavaType>, tt: TypestateTree): TypestateTree {
    return if (path.isEmpty()) {
      tt
    } else {
      val child = find(path.first(), tt.children)
      if (child == null) {
        tt
      } else {
        closestByPath(path.drop(1), child)
      }
    }
  }

  fun closest(j: JavaType, tt: TypestateTree): TypestateTree? {
    return path(tt.jc, j)?.let { closestByPath(it, tt) }
  }
}

object TypestateTreeManager {
  fun upcastTT(tt: TypestateTree, j: JavaType): TypestateTree? {
    return if (tt.jc == j) tt
    else {
      val sup = tt.jc.getSingleSuperType() ?: return null
      upcastTT(TypestateTree(sup, Subtyping.cast(tt.ts, sup, true), listOf(tt)), j)
    }
  }

  fun downcastTT(tt: TypestateTree, j: JavaType): TypestateTree? {
    val closest = TypestateTreeUtilities.closest(j, tt) ?: return null
    return if (j == closest.jc) closest
    else TypestateTree(j, Subtyping.cast(closest.ts, j, true), listOf())
  }

  fun mergeTT(tt1: TypestateTree, tt2: TypestateTree): TypestateTree {
    val classes = tt1.clss() union tt2.clss()
    val newChildren = classes.map { merge(tt1.children, tt2.children, it, tt1.ts, tt2.ts) }
    return TypestateTree(tt1.jc, JTCType.createUnion(setOf(tt1.ts, tt2.ts)), newChildren)
  }

  private fun merge(c1: List<TypestateTree>, c2: List<TypestateTree>, j: JavaType, t1: JTCType, t2: JTCType): TypestateTree {
    val inC1 = TypestateTreeUtilities.find(j, c1)
    val inC2 = TypestateTreeUtilities.find(j, c2)
    return if (inC1 != null && inC2 != null) mergeTT(inC1, inC2)
    else if (inC1 != null) mergeTT(inC1, TypestateTree(j, Subtyping.cast(t2, j, true), listOf()))
    else if (inC2 != null) mergeTT(TypestateTree(j, Subtyping.cast(t1, j, true), listOf()), inC2)
    else error("non well-formed typestate tree")
  }

  fun evolveTT(utils: TypecheckUtils, tt: TypestateTree, call: MethodCall, outputs: (String) -> Boolean): TypestateTree {
    return TypestateTree(tt.jc, utils.refine(tt.ts, call, outputs), tt.children.map { evolveTT(utils, it, call, outputs) })
  }

  fun visit(tt: TypestateTree, fn : (JTCType) -> JTCType): TypestateTree {
    return TypestateTree(tt.jc, fn(tt.ts), tt.children.map { visit(it, fn) })
  }

  fun make(jc: JavaType, ts: JTCType): TypestateTree {
    return TypestateTree(jc, ts, emptyList())
  }

  fun isSubtype(a: TypestateTree, b: TypestateTree): Boolean {
    if (a.jc == b.jc) {
      if (a.ts.isSubtype(b.ts)) {
        return b.children.all { bC ->
          val aC = TypestateTreeUtilities.find(bC.jc, a.children)
          isSubtype(aC ?: make(bC.jc, Subtyping.cast(a.ts, bC.jc, true)), bC)
        }
      }
      return false
    }
    if (a.jc.isSubtype(b.jc)) {
      return isSubtype(a, downcastTT(b, a.jc) ?: make(a.jc, Subtyping.cast(b.ts, a.jc, true)))
    }
    return false
  }
}
