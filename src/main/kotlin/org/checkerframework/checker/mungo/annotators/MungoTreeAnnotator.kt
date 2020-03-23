package org.checkerframework.checker.mungo.annotators

import com.sun.source.tree.NewClassTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.qualifiers.MungoInfo
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.type.treeannotator.TreeAnnotator
import java.nio.file.Paths

class MungoTreeAnnotator(private val checker: MungoChecker, atypeFactory: MungoAnnotatedTypeFactory) : TreeAnnotator(atypeFactory) {
  override fun visitNewClass(node: NewClassTree, annotatedTypeMirror: AnnotatedTypeMirror): Void? {
    val tree = node.classBody
    if (tree != null && !annotatedTypeMirror.hasAnnotation(MungoInfo::class.java)) {
      // Here we handle anonymous classes because doing this in MungoDefaultQualifierForUseTypeAnnotator is not enough
      val graph = checker.utils.visitClassTree(Paths.get(atypeFactory.visitorState.path.compilationUnit.sourceFile.toUri()), tree)
      if (graph != null) {
        val anno = MungoUtils.buildAnnotation(checker.processingEnvironment, graph.file)
        annotatedTypeMirror.replaceAnnotation(anno)
      }
    }
    return null
  }
}