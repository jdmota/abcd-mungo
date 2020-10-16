package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.ClassTree
import com.sun.source.tree.CompilationUnitTree
import com.sun.source.tree.Tree
import com.sun.source.tree.VariableTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.abstract_analysis.*
import org.checkerframework.checker.mungo.analysis.FieldAccess
import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.typecheck.MungoBottomType
import org.checkerframework.checker.mungo.typecheck.MungoType
import org.checkerframework.checker.mungo.typecheck.MungoUnionType
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.framework.type.AnnotatedTypeMirror
import javax.lang.model.type.TypeMirror

/*class AccessLocation(val ref: Reference, val isZero: Boolean) {
  override fun equals(other: Any?): Boolean {
    if (other !is AccessLocation) return false
    return other.ref == ref && other.isZero == isZero
  }

  override fun hashCode(): Int {
    var result = ref.hashCode()
    result = 31 * result + isZero.hashCode()
    return result
  }

  override fun toString(): String {
    return if (isZero) "$ref.0" else "$ref"
  }
}*/

private val storeUtils = StoreUtils()
private val storeInfoUtils = StoreInfoUtils()
private val analyzerResultsUtils = AnalyzerResultsUtils()

class AnalyzerResult(
  private val thenStore: Store,
  private val elseStore: Store
) : AbstractAnalyzerResult<Store, MutableStore>() {

  private val regularStore = storeUtils.merge(thenStore, elseStore)

  constructor(thenStore: MutableStore, elseStore: MutableStore) : this(thenStore.toImmutable(), elseStore.toImmutable())
  constructor(result: MutableAnalyzerResult) : this(result.getThen().toImmutable(), result.getElse().toImmutable())

  override fun getThen(): Store = thenStore
  override fun getElse(): Store = elseStore
  override fun getRegular(): Store = regularStore
  override fun isRegular(): Boolean = thenStore === elseStore

  override fun getExceptionalStore(cause: Any): Store? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{store=$thenStore}"
    }
    return "Result{\nthen=$thenStore,\nelse=$elseStore\n}"
  }
}

class MutableAnalyzerResult(
  private var thenStore: MutableStore,
  private var elseStore: MutableStore
) : AbstractMutableAnalyzerResult<Store, MutableStore, AnalyzerResult>() {
  override fun merge(result: AnalyzerResult) {
    thenStore.merge(result.getThen())
    if (!isRegular() || !result.isRegular()) {
      elseStore.merge(result.getElse())
    }
  }

  override fun mergeThenAndElse() {
    thenStore.merge(elseStore)
    elseStore = thenStore
  }

  override fun getThen(): MutableStore = thenStore
  override fun getElse(): MutableStore = elseStore
  override fun isRegular(): Boolean = thenStore === elseStore

  override fun getExceptionalStore(cause: Any): MutableStore? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{store=$thenStore}"
    }
    return "Result{\nthen=$thenStore,\nelse=$elseStore\n}"
  }
}

class MutableAnalyzerResultWithValue(
  private var value: StoreInfo,
  private var thenStore: MutableStore,
  private var elseStore: MutableStore
) : AbstractMutableAnalyzerResultWithValue<StoreInfo, Store, MutableStore, AnalyzerResult>() {
  override fun merge(result: AnalyzerResult) {
    thenStore.merge(result.getThen())
    if (!isRegular() || !result.isRegular()) {
      elseStore.merge(result.getElse())
    }
  }

  override fun mergeThenAndElse() {
    thenStore.merge(elseStore)
    elseStore = thenStore
  }

  override fun getThen(): MutableStore = thenStore
  override fun getElse(): MutableStore = elseStore
  override fun isRegular(): Boolean = thenStore === elseStore

  override fun getExceptionalStore(cause: Any): MutableStore? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{value=$value, store=$thenStore}"
    }
    return "Result{value=$value,\nthen=$thenStore,\nelse=$elseStore\n}"
  }

  override fun getValue() = value
  override fun setValue(v: StoreInfo) {
    value = v
  }
}

class SymbolicFraction {
  fun intersect(other: SymbolicFraction): SymbolicFraction {
    return TODO()
  }

  fun leastUpperBound(other: SymbolicFraction): SymbolicFraction {
    return TODO()
  }
}

class SymbolicType {
  fun intersect(other: SymbolicType): SymbolicType {
    return TODO()
  }

  fun leastUpperBound(other: SymbolicType): SymbolicType {
    return TODO()
  }
}

class StoreInfo(
  val analyzer: AbstractAnalyzerBase,
  val fraction: SymbolicFraction,
  val mungoType: SymbolicType,
  val type: AnnotatedTypeMirror,
  // val packed: Boolean = false,
  // val packingFraction: SymbolicFraction,
) : AbstractStoreInfo() {

  constructor(prevInfo: StoreInfo, newFraction: SymbolicFraction, newType: SymbolicType) : this(prevInfo.analyzer, newFraction, newType, prevInfo.type)

  val underlyingType: TypeMirror = type.underlyingType

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is StoreInfo) return false
    if (fraction != other.fraction) return false
    if (mungoType != other.mungoType) return false
    return analyzer.utils.isSameType(underlyingType, other.underlyingType)
    // TODO infinite loop? return EQUALITY_COMPARER.visit(type, other.type, analyzer)
  }

  override fun hashCode(): Int {
    var result = fraction.hashCode()
    result = 31 * result + mungoType.hashCode()
    return result
  }

  override fun toString(): String {
    return "StoreInfo{$fraction, $mungoType, $type}"
  }
}

class Store(
  private val map: Map<Reference, StoreInfo> = emptyMap(),
  private val equalities: EqualityTracker = EqualityTracker()
) : AbstractStore<Store, MutableStore>() {

  operator fun contains(ref: Reference) = map.contains(ref)
  operator fun get(ref: Reference): StoreInfo? = map[ref]
  operator fun iterator(): Iterator<Map.Entry<Reference, StoreInfo>> = map.iterator()

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is Store && map == other.map && equalities == other.equalities
  }

  override fun hashCode(): Int {
    return map.hashCode()
  }

  override fun toString(): String {
    val accessesStr = map.map { (l, i) -> "acc($l,${i.fraction})" }.joinToString(" && ")
    val typeofsStr = map.map { (l, i) -> "typeof($l,${i.type})" }.joinToString(" && ")
    return "$accessesStr && $typeofsStr"
  }

  override fun toMutable(): MutableStore {
    return MutableStore(map.toMutableMap(), equalities.toMutable())
  }

  override fun toImmutable(): Store {
    return this
  }
}

class MutableStore(
  private val map: MutableMap<Reference, StoreInfo> = mutableMapOf(),
  private val equalities: MutableEqualityTracker = MutableEqualityTracker()
) : AbstractMutableStore<Store, MutableStore>() {

  operator fun contains(ref: Reference) = map.contains(ref)
  operator fun get(ref: Reference): StoreInfo? = map[ref]
  operator fun iterator(): Iterator<Map.Entry<Reference, StoreInfo>> = map.iterator()

  operator fun set(ref: Reference, info: StoreInfo) {
    map[ref] = info
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is MutableStore && map == other.map // TODO && equalities == other.equalities
  }

  override fun hashCode(): Int {
    return map.hashCode()
  }

  override fun toString(): String {
    val accessesStr = map.map { (l, i) -> "acc($l,${i.fraction})" }.joinToString(" && ")
    val typeofsStr = map.map { (l, i) -> "typeof($l,${i.type})" }.joinToString(" && ")
    return "$accessesStr && $typeofsStr"
  }

  override fun toMutable(): MutableStore {
    return MutableStore(map.toMutableMap(), equalities.toMutable())
  }

  override fun toImmutable(): Store {
    return Store(map.toMap(), equalities.toImmutable())
  }

  fun merge(ref: Reference, info: StoreInfo) {
    map.compute(ref) { _, curr -> if (curr == null) info else storeInfoUtils.merge(curr, info) }
  }

  override fun merge(other: Store) {
    for ((ref, info) in other) {
      merge(ref, info)
    }
  }

  override fun mergeFields(other: Store) {
    for ((ref, info) in other) {
      if (ref.isThisField()) {
        merge(ref, info)
      }
    }
  }

  override fun merge(other: MutableStore) {
    for ((ref, info) in other) {
      merge(ref, info)
    }
  }

  override fun mergeFields(other: MutableStore) {
    for ((ref, info) in other) {
      if (ref.isThisField()) {
        merge(ref, info)
      }
    }
  }

  fun intersect(ref: Reference, info: StoreInfo) {
    map.compute(ref) { _, curr -> if (curr == null) info else storeInfoUtils.intersect(curr, info) }
  }

  fun remove(ref: Reference): StoreInfo? {
    return map.remove(ref)
  }

  override fun toBottom(): MutableStore {
    for ((key, value) in map) {
      val newInfo = StoreInfo(value, SymbolicFraction(), SymbolicType())
      map[key] = newInfo
      // TODO newInfo.fraction == 1
      // TODO newInfo.mungoType <: Bottom
    }
    return this
  }

  override fun invalidate(analyzer: AbstractAnalyzerBase): MutableStore {
    for ((key, value) in map) {
      map[key] = StoreInfo(value, SymbolicFraction(), SymbolicType())
    }
    return this
  }

  override fun invalidateFields(analyzer: AbstractAnalyzerBase): MutableStore {
    for ((key, value) in map) {
      if (key.isThisField()) {
        map[key] = StoreInfo(value, SymbolicFraction(), SymbolicType())
      }
    }
    return this
  }

  override fun invalidatePublicFields(analyzer: AbstractAnalyzerBase): MutableStore {
    for ((key, value) in map) {
      if (key.isThisField() && key is FieldAccess && key.isNonPrivate) {
        map[key] = StoreInfo(value, SymbolicFraction(), SymbolicType())
      }
    }
    return this
  }
}

class StoreUtils : AbstractStoreUtils<Store, MutableStore>() {

  private val empty = Store(emptyMap())

  override fun emptyStore(): Store {
    return empty
  }

  override fun mutableEmptyStore(): MutableStore {
    return MutableStore()
  }

  override fun merge(a: Store, b: Store): Store {
    if (a === b) return a
    val newStore = a.toMutable()
    newStore.merge(b)
    return newStore.toImmutable()
  }

  override fun mutableMergeFields(a: Store, b: Store): MutableStore {
    val newStore = MutableStore()
    for ((key, info) in a) {
      if (key.isThisField()) {
        newStore[key] = info
      }
    }
    for ((key, info) in b) {
      if (key.isThisField()) {
        newStore.merge(key, info)
      }
    }
    return newStore
  }
}

class StoreInfoUtils : AbstractStoreInfoUtils<StoreInfo>() {
  override fun merge(a: StoreInfo, b: StoreInfo): StoreInfo {
    val analyzer = a.analyzer
    // TODO val type = analyzer.utils.leastUpperBound(a.underlyingType, b.underlyingType)
    val mostSpecific = analyzer.utils.mostSpecific(a.underlyingType, b.underlyingType)
    return StoreInfo(
      analyzer,
      a.fraction.leastUpperBound(b.fraction),
      a.mungoType.leastUpperBound(b.mungoType),
      if (mostSpecific === a.underlyingType) b.type else a.type
      // TODO this breaks the tests: analyzer.utils.createType(type, a.type.isDeclaration)
    )
  }

  override fun intersect(a: StoreInfo, b: StoreInfo): StoreInfo {
    val analyzer = a.analyzer
    val mostSpecific = analyzer.utils.mostSpecific(a.underlyingType, b.underlyingType)
    return StoreInfo(
      analyzer,
      a.fraction.intersect(b.fraction),
      a.mungoType.intersect(b.mungoType),
      if (mostSpecific === a.underlyingType) a.type else b.type
    )
  }
}

class AnalyzerResultsUtils : AbstractAnalyzerResultUtils<StoreInfo, Store, MutableStore, AnalyzerResult, MutableAnalyzerResult, MutableAnalyzerResultWithValue>() {
  override fun createAnalyzerResult(thenStore: Store, elseStore: Store): AnalyzerResult {
    return AnalyzerResult(thenStore, elseStore)
  }

  override fun createAnalyzerResult(thenStore: MutableStore, elseStore: MutableStore): AnalyzerResult {
    return AnalyzerResult(thenStore, elseStore)
  }

  override fun createAnalyzerResult(result: MutableAnalyzerResult): AnalyzerResult {
    return createAnalyzerResult(result.getThen(), result.getElse())
  }

  override fun createAnalyzerResult(): AnalyzerResult {
    return createAnalyzerResult(storeUtils.emptyStore(), storeUtils.emptyStore())
  }

  override fun createMutableAnalyzerResult(thenStore: MutableStore, elseStore: MutableStore): MutableAnalyzerResult {
    return MutableAnalyzerResult(thenStore, elseStore)
  }

  override fun createMutableAnalyzerResult(): MutableAnalyzerResult {
    return createMutableAnalyzerResult(storeUtils.mutableEmptyStore(), storeUtils.mutableEmptyStore())
  }

  override fun createMutableAnalyzerResultWithValue(value: StoreInfo, result: AnalyzerResult): MutableAnalyzerResultWithValue {
    return MutableAnalyzerResultWithValue(value, result.getThen().toMutable(), result.getElse().toMutable())
  }
}

class Inferrer(checker: MungoChecker) : AbstractAnalyzer<
  AnalyzerResult,
  MutableAnalyzerResult,
  MutableAnalyzerResultWithValue,
  StoreInfo,
  Store,
  MutableStore,
  StoreUtils,
  StoreInfoUtils,
  AnalyzerResultsUtils
  >(checker, storeUtils, storeInfoUtils, analyzerResultsUtils) {
  override fun setRoot(root: CompilationUnitTree) {
    super.setRoot(root)
  }

  override fun getInitialInfo(node: Node): StoreInfo {
    TODO("Not yet implemented")
  }

  override fun handleUninitializedField(store: MutableStore, field: VariableTree, ct: ClassTree) {
    TODO("Not yet implemented")
  }

  override fun initialStore(capturedStore: Store, cfg: ControlFlowGraph): Store {
    TODO("Not yet implemented")
  }

  override fun visit(node: Node, mutableResult: MutableAnalyzerResultWithValue) {
    TODO("Not yet implemented")
  }
}
