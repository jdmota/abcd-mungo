package org.checkerframework.checker.mungo.analysis

import com.sun.source.tree.*
import org.checkerframework.checker.mungo.qualifiers.MungoBottom
import org.checkerframework.checker.mungo.qualifiers.MungoInternalInfo
import org.checkerframework.checker.mungo.qualifiers.MungoUnknown
import org.checkerframework.common.basetype.BaseTypeChecker
import org.checkerframework.framework.source.SourceChecker
import org.checkerframework.framework.stub.StubTypes
import org.checkerframework.framework.type.*
import org.checkerframework.framework.util.AnnotatedTypes
import org.checkerframework.framework.util.DefaultAnnotationFormatter
import org.checkerframework.framework.util.GraphQualifierHierarchy
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy
import org.checkerframework.javacutil.AnnotationBuilder
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element
import javax.lang.model.type.TypeMirror

private class FakeBasicTypeChecker(myChecker: SourceChecker) : BaseTypeChecker() {
  init {
    processingEnvironment = myChecker.processingEnvironment
  }
}

private class FakeAnnotatedTypeFactory(myChecker: SourceChecker) : AnnotatedTypeFactory(FakeBasicTypeChecker(myChecker)) {

  private val typesFromStubFilesField = StubTypes::class.java.getDeclaredField("typesFromStubFiles")
  private val typesFromStubFiles = mutableMapOf<Element, AnnotatedTypeMirror>()

  private val topAnnotation = AnnotationBuilder(checker.processingEnvironment, MungoUnknown::class.java).build()
  private val bottomAnnotation = AnnotationBuilder(checker.processingEnvironment, MungoBottom::class.java).build()

  init {
    typesFromStubFilesField.isAccessible = true
    qualHierarchy = createQualifierHierarchy()
    typeHierarchy = createTypeHierarchy()
    typeVarSubstitutor = createTypeVariableSubstitutor()
    typeArgumentInference = createTypeArgumentInference()
    qualifierUpperBounds = createQualifierUpperBounds()
    parseStubFiles()
  }

  private class AnnotationFormatter : DefaultAnnotationFormatter() {
    override fun formatAnnotationString(annos: MutableCollection<out AnnotationMirror>?, printInvisible: Boolean): String {
      return ""
    }

    override fun formatAnnotationMirror(am: AnnotationMirror, sb: StringBuilder) {

    }
  }

  override fun createAnnotatedTypeFormatter(): AnnotatedTypeFormatter {
    val printVerboseGenerics = checker.hasOption("printVerboseGenerics")
    val defaultPrintInvisibleAnnos = printVerboseGenerics || checker.hasOption("printAllQualifiers")
    return DefaultAnnotatedTypeFormatter(
      AnnotationFormatter(),
      printVerboseGenerics, // -AprintVerboseGenerics implies -AprintAllQualifiers
      defaultPrintInvisibleAnnos
    )
  }

  override fun createSupportedTypeQualifiers(): Set<Class<out Annotation>> {
    return setOf(MungoBottom::class.java, MungoInternalInfo::class.java, MungoUnknown::class.java)
  }

  override fun createQualifierHierarchy(factory: MultiGraphQualifierHierarchy.MultiGraphFactory): QualifierHierarchy {
    return FakeQualifierHierarchy(factory, bottomAnnotation)
  }

  private inner class FakeQualifierHierarchy(f: MultiGraphFactory, bottom: AnnotationMirror) : GraphQualifierHierarchy(f, bottom) {
    override fun findTops(supertypes: MutableMap<AnnotationMirror, MutableSet<AnnotationMirror>>?): MutableSet<AnnotationMirror> {
      return mutableSetOf(topAnnotation)
    }

    override fun findBottoms(supertypes: MutableMap<AnnotationMirror, MutableSet<AnnotationMirror>>?): MutableSet<AnnotationMirror> {
      return mutableSetOf(bottomAnnotation)
    }

    override fun getTopAnnotation(start: AnnotationMirror?): AnnotationMirror = topAnnotation

    override fun getBottomAnnotation(start: AnnotationMirror?): AnnotationMirror = bottomAnnotation

    override fun isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean {
      return true
    }
  }

  override fun parseStubFiles() {
    super.parseStubFiles()

    val types = typesFromStubFilesField.get(stubTypes) as MutableMap<*, *>
    for ((element, annotatedType) in types) {
      typesFromStubFiles[element as Element] = annotatedType as AnnotatedTypeMirror
    }
  }

  // So that we get the original AnnotatedTypeMirror, with all the annotations
  // See "isSupportedQualifier" for context
  fun getTypeFromStub(elt: Element) = typesFromStubFiles[elt]

  // Allow all annotations to be added to AnnotatedTypeMirror's
  override fun isSupportedQualifier(a: AnnotationMirror?) = a != null
  override fun isSupportedQualifier(className: String?) = className != null
  override fun isSupportedQualifier(clazz: Class<out Annotation>?) = clazz != null

  override fun shouldWarnIfStubRedundantWithBytecode(): Boolean {
    return true
  }

  private var analyzer: Analyzer? = null

  fun setAnalyzer(analyzer: Analyzer) {
    this.analyzer = analyzer
  }

  override fun getAnnotatedType(tree: Tree): AnnotatedTypeMirror {
    val type = super.getAnnotatedType(tree)
    val info = analyzer?.getInferredInfoOptional(tree)
    if (info != null) {
      if (info.type is AnnotatedTypeMirror.AnnotatedDeclaredType) {
        return info.type
      }
    }
    return type
  }

}

class TypeFactory(private val checker: SourceChecker) {

  private val fake = FakeAnnotatedTypeFactory(checker)

  fun setRoot(root: CompilationUnitTree) {
    fake.setRoot(root)
  }

  fun setAnalyzer(analyzer: Analyzer) {
    fake.setAnalyzer(analyzer)
  }

  fun getTypeFromStub(elt: Element) = fake.getTypeFromStub(elt)

  fun getAnnotatedType(tree: Tree) = fake.getAnnotatedType(tree)
  fun getIteratedType(iterableType: AnnotatedTypeMirror): AnnotatedTypeMirror = AnnotatedTypes.getIteratedType(checker.processingEnvironment, fake, iterableType)
  fun getFunctionTypeFromTree(node: LambdaExpressionTree): AnnotatedTypeMirror.AnnotatedExecutableType = fake.getFunctionTypeFromTree(node)
  fun getMethodReturnType(method: MethodTree, returnTree: ReturnTree): AnnotatedTypeMirror = fake.getMethodReturnType(method, returnTree)

  fun createType(type: TypeMirror, isDeclaration: Boolean = false): AnnotatedTypeMirror = AnnotatedTypeMirror.createType(type, fake, isDeclaration)
  fun createNullType(): AnnotatedTypeMirror.AnnotatedNullType = fake.getAnnotatedNullType(emptySet())

  fun methodFromUse(method: MethodInvocationTree): AnnotatedTypeFactory.ParameterizedExecutableType = fake.methodFromUse(method)
  fun constructorFromUse(node: NewClassTree): AnnotatedTypeFactory.ParameterizedExecutableType = fake.constructorFromUse(node)

  fun expandVarArgs(invokedMethod: AnnotatedTypeMirror.AnnotatedExecutableType, node: MethodInvocationTree): List<AnnotatedTypeMirror> = AnnotatedTypes.expandVarArgs(fake, invokedMethod, node.arguments)
  fun expandVarArgs(invokedMethod: AnnotatedTypeMirror.AnnotatedExecutableType, node: NewClassTree): List<AnnotatedTypeMirror> = AnnotatedTypes.expandVarArgs(fake, invokedMethod, node.arguments)

}
