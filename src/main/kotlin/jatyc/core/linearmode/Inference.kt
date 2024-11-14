package jatyc.core.linearmode

import com.sun.source.tree.CompilationUnitTree
import com.sun.source.tree.Tree
import com.sun.tools.javac.code.Type
import jatyc.core.*
import jatyc.core.cfg.*
import jatyc.core.typesystem.TypeInfo
import jatyc.utils.JTCUtils

class Inference(
  private val utils: JTCUtils,
  private val inference: LinearModeInference,
  private val classAnalysis: LinearModeClassAnalysis
) {
  private val hierarchy get() = utils.hierarchy
  private val typeIntroducer get() = utils.typeIntroducer
  private val typecheckUtils get() = utils.typecheckUtils

  private val allLabels: (String) -> Boolean = { true }
  private val ifTrue: (String) -> Boolean = { it == "true" }
  private val ifFalse: (String) -> Boolean = { it == "false" }

  fun getRoot(node: AdaptedThing): CompilationUnitTree {
    return node.cfRoot ?: error("no root? $node ${node::class.java}")
  }

  fun getTree(node: AdaptedThing): Tree {
    return node.cfTree ?: error("no tree? $node ${node::class.java}")
  }

  private fun assign(node: CodeExpr, targetType: JTCType, pre: Store, post: Store, leftRef: Reference, rightRef: Reference, thisParam: Boolean) {
    val nodeRef = Reference.make(node)
    val targetJavaType = leftRef.javaType

    if (node is Assign) {
      val previousType = pre[leftRef].type
      if (!previousType.canDrop()) {
        inference.addError(node, "The previous value of [${leftRef.format()}] did not complete its protocol (found: ${previousType.format()})")
      }
    }

    // Correct conditional information to account for the assignment
    for ((ref, info) in pre) {
      post[ref] = info.invalidateCondition(leftRef).assignCondition(rightRef, listOf(leftRef, nodeRef))
    }

    val typeToAssign: TypeInfo
    val typeInExpr: TypeInfo
    val newTargetType: TypeInfo
    val succeeded: Boolean

    if (thisParam) {
      val move = TypecheckUtils.requiresLinear(leftRef, targetType)
      typeToAssign = if (move) pre[rightRef].type else pre[rightRef].toShared()
      typeInExpr = if (move) pre[rightRef].toShared() else pre[rightRef].type
      newTargetType = typeToAssign.cast(targetJavaType)
      succeeded = true // Checking that the method can be called in this state is performed later
    } else {
      typeToAssign = pre[rightRef].type
      typeInExpr = pre[rightRef].toShared()
      val typeToAssignCasted = typeToAssign.cast(targetJavaType)
      val castFailed = !typeToAssign.isUnknown() && typeToAssignCasted.isUnknown()

      succeeded = typeToAssignCasted.isSubtype(targetType)
      newTargetType = if (castFailed || !succeeded) {
        // Avoid error propagation
        typeToAssignCasted.toBottom()
      } else typeToAssignCasted

      if (succeeded && typeToAssign.isInDroppableStateNotEnd() && !TypecheckUtils.requiresLinear(leftRef, targetType)) {
        // We want to report a warning if we have an object in a droppable state, with more actions that can be made
        // But that is being passed to a shared parameter
        inference.addWarning(node, "Object [${rightRef.format()}] with type ${typeToAssign.format()} will be dropped")
      }
    }

    post[leftRef] = newTargetType
    post[rightRef] = typeInExpr
    post[nodeRef] = pre[rightRef].toShared()

    when {
      targetType is JTCBottomType -> inference.addError(node, "Cannot assign because [${leftRef.format()}] is not accessible here")
      succeeded -> {
      }
      else -> inference.addError(node, when (node) {
        is Assign -> "Cannot assign: cannot cast from ${typeToAssign.format()} to ${targetType.format()}"
        is ParamAssign -> {
          val method = node.call.methodExpr
          if (thisParam) {
            "Cannot call [${method.name}] on ${typeToAssign.format()}"
          } else {
            "Incompatible parameter: cannot cast from ${typeToAssign.format()} to ${targetType.format()}"
          }
        }
        is Return -> "Incompatible return value: cannot cast from ${typeToAssign.format()} to ${targetType.format()}"
        else -> "INTERNAL ERROR"
      })
    }
  }

  private fun castParamAfterCall(node: CodeExpr, info: StoreInfo, javaType: JavaType): StoreInfo {
    val newInfo = info.cast(javaType)
    if (newInfo.type.isUnknown()) {
      val currentType = info.type
      if (!currentType.isUnknown()) {
        inference.addError(node, "Cannot perform upcast on [${node}] from ${currentType.format()} to class [$javaType] after call")
        return StoreInfo.bottom(javaType)
      }
    }
    return newInfo
  }

  fun analyzeCode(func: FuncDeclaration, pre: Store, node: CodeExpr, post: Store) {
    inference.resetErrorsAndWarnings(node)
    val clazz = func.clazz
    val thisRef = Reference.makeThis(func)

    fun preserveConditional() {
      for ((ref, info) in pre) {
        post[ref] = info
      }
    }

    fun invalidateConditional() {
      for ((ref, info) in pre) {
        post[ref] = info.toRegular()
      }
    }

    when (node) {
      is VarDeclaration -> {
        preserveConditional()
        val ref = Reference.make(node.id)
        val inLoop = ref in post

        if (inLoop) {
          val type = post[ref].type
          if (!type.canDrop()) {
            inference.addError(node, "The previous value of [${ref.format()}] did not complete its protocol (found: ${type.format()})")
          }
        }

        post[ref] = TypeInfo.make(node.javaType, JTCNullType.SINGLETON)
      }

      is NewObj -> {
        preserveConditional()
        post[Reference.make(node)] = TypeInfo.make(node.javaType, node.type)
      }

      is Assign -> {
        preserveConditional()
        val leftRef = Reference.makeFromLHS(node)
        val rightRef = Reference.make(node.right)
        // Allow field assignments only if:
        // - the receiver object is "this" and we have linear access to it
        // - the target Java type has no protocol
        val targetType = when {
          thisRef != null && leftRef.isFieldOf(thisRef) && (func.isConstructor || pre[thisRef].type.requiresLinear(thisRef)) ->
            clazz!!.allFields(classAnalysis.classes).find { leftRef.isFieldOf(thisRef, it.id) }!!.type

          leftRef.isField() && leftRef.javaType.hasProtocol() ->
            JTCBottomType.SINGLETON

          else ->
            node.type
        }
        assign(node, targetType, pre, post, leftRef, rightRef, false)
      }

      is ParamAssign -> {
        preserveConditional()
        val leftRef = Reference.makeFromLHS(node)
        val rightRef = Reference.make(node.expr)
        val param = node.call.methodExpr.parameters[node.idx]
        assign(node, param.requires, pre, post, leftRef, rightRef, param.isThis)
      }

      is Return -> {
        preserveConditional()
        if (node.expr == null) {
          post[Reference.returnRef(node.javaType)] = TypeInfo.make(node.javaType, JTCNullType.SINGLETON)
          post[Reference.make(node)] = TypeInfo.make(node.javaType, JTCNullType.SINGLETON)
        } else {
          val leftRef = Reference.returnRef(node.javaType)
          val rightRef = Reference.make(node.expr)
          assign(node, node.type, pre, post, leftRef, rightRef, false)
        }
      }

      is MethodCall -> {
        invalidateConditional()
        // Note for later: a call is non-virtual if static or init or super call or private call
        val nodeRef = Reference.make(node)
        val methodExpr = node.methodExpr
        val arguments = node.parameters
        val argsIt = arguments.iterator()
        val parameters = methodExpr.parameters
        val paramsIt = parameters.iterator()
        val isSelfCall = thisRef != null && parameters.isNotEmpty() && parameters.first().isThis && Reference.make(arguments.first().expr) == thisRef

        if (
          isSelfCall &&
          !func.isConstructor && !methodExpr.isConstructor &&
          !methodExpr.isAnytime && methodExpr.isPublic
        ) {
          // We are calling our own public method!
          inference.addError(node, "Cannot call own public method [${methodExpr.name}]")
          post[nodeRef] = TypeInfo.make(methodExpr.returnJavaType, JTCBottomType.SINGLETON)
          post.toBottom()
          return
        }
        // We might need to invalidate some information...
        if (!methodExpr.isPure && isSelfCall) {
          checkNotNull(clazz)
          checkNotNull(thisRef)
          // If this is a self call we need to invalidate the information about the fields
          // Remember that we do not allow field accesses unless we are in a method of the object
          // so the only way to modify fields is to perform a self call
          val modified = if (node.isSuperCall) {
            // If it is a super call, we can resolve it and get more precise information
            clazz.superMethods(classAnalysis.classes).filter {
              it.name == node.methodExpr.name
            }.flatMap { superF ->
              val fields = superF.potentiallyModifiedFields()
              fields?.mapNotNull {
                clazz.resolveField(classAnalysis.classes, it.id, it.uuid)
              } ?: clazz.allFields(classAnalysis.classes)
            }
          } else {
            clazz.allFields(classAnalysis.classes)
          }
          for (field in modified) {
            post[Reference.make(thisRef, field)] = TypeInfo.make(field.javaType, field.type)
          }
        }
        // Invariant: arguments.size == parameters.size
        while (argsIt.hasNext()) {
          val arg = argsIt.next()
          val param = paramsIt.next()
          val argRef = Reference.makeFromLHS(arg)
          val exprRef = Reference.make(getInnerExpr(arg.expr))
          // First we refine the type of the parameter variable
          if (param.isThis) {
            if (methodExpr.name == "<init>") {
              post[argRef] = pre[argRef].type.ensures(param.ensures)
            } else {
              val returnType = methodExpr.returnType
              val returnsBool = returnType.isSubtype(hierarchy.BOOLEAN)
              val returnsEnum = returnType.isSubtype(hierarchy.ENUM)
              val currentType = pre[argRef].type

              when {
                returnsBool -> {
                  post[argRef] = StoreInfo.conditional(
                    nodeRef,
                    currentType.refine(typecheckUtils, node, ifTrue),
                    currentType.refine(typecheckUtils, node, ifFalse)
                  )
                }

                returnsEnum -> {
                  if (returnType is JTCSharedType) {
                    val (qualifiedName, labels) = returnType.javaType.getEnumLabels()
                    val cases = mutableMapOf<CasePatterns, TypeInfo>()
                    for (label in labels) {
                      cases[CasePatterns.labelled(nodeRef, "$qualifiedName.$label", true)] = currentType.refine(typecheckUtils, node) { it == label }
                    }
                    post[argRef] = StoreInfo.cases(argRef.javaType, cases.toList())
                  } else {
                    post[argRef] = currentType.refine(typecheckUtils, node, allLabels)
                  }
                }

                else -> {
                  post[argRef] = currentType.refine(typecheckUtils, node, allLabels)
                }
              }

              if (!currentType.check(typecheckUtils, node)) {
                inference.addError(node, "Cannot call [${node.methodExpr.name}] on ${currentType.format()}")
              }
            }
            // Whatever is in the "parameter variable", restore it to the "parameter expression"
            // only if the method requested linear type
            // If the method did not request linear type, it means the linear permission is still in the expression
            if (TypecheckUtils.requiresLinear(argRef, param.requires)) {
              val argInfo = post[argRef]
              post[argRef] = argInfo.toShared()
              post[exprRef] = castParamAfterCall(arg.expr, argInfo, exprRef.javaType) // Preserve conditional info!
            }
          } else {
            post[argRef] = pre[argRef].type.ensures(param.ensures)
            // Whatever is in the "parameter variable", restore it to the "parameter expression"
            val argInfo = post[argRef]
            post[argRef] = argInfo.toShared()
            post[exprRef] = castParamAfterCall(arg.expr, argInfo, exprRef.javaType) // Preserve conditional info!
          }
        }
        // The type of the method call is the type of the return value
        post[nodeRef] = TypeInfo.make(methodExpr.returnJavaType, methodExpr.returnType)
        // This means that the method interrupts execution
        if (methodExpr.returnType is JTCBottomType) {
          analyzeExit(methodExpr, post)
          post.toBottom()
        }
      }

      is Id -> {
        preserveConditional()
        val ref = Reference.make(node)
        val currentType = pre.getOrNull(ref)?.type
        if (currentType == null) {
          // Ignore internal names generated by the Checker Framework
          if (!node.name.contains("#num")) {
            showType(func, node, TypeInfo.make(ref.javaType, JTCUnknownType.SINGLETON))

            inference.addError(node, "Cannot access [${node.name}]")
            post[Reference.make(node)] = TypeInfo.make(node.javaType, JTCBottomType.SINGLETON)
          }
        } else {
          showType(func, node, currentType)
        }
      }

      is Select -> {
        preserveConditional()
        val ref = Reference.make(node)
        val obj = node.expr
        val objRef = Reference.make(node.expr)
        val objType = pre[objRef].type
        var currentType: TypeInfo? = null

        if (objType.isNull()) {
          currentType = TypeInfo.make(ref.javaType, JTCBottomType.SINGLETON)
        } else if (node.id == "length" && objRef.javaType.isJavaArray()) {
          currentType = TypeInfo.make(hierarchy.INTEGER)
        } else {
          // Handle enums or stuff like java.lang.System.out
          if (obj is SymbolResolveExpr) {
            currentType = typeIntroducer.getEnumFieldType(obj.javaType.original, node.id)
              ?: typeIntroducer.getJDKStaticFieldType(obj.javaType.original, node.id)
          }
          // Or default to what we currently know
          currentType = currentType ?: pre.getOrNull(ref)?.type
        }

        when {
          currentType == null -> {
            showType(func, node, TypeInfo.make(ref.javaType, JTCUnknownType.SINGLETON))

            inference.addError(node, "Cannot access [${node.format("")}]")
            post[ref] = TypeInfo.make(ref.javaType, JTCBottomType.SINGLETON)
          }

          obj !is SymbolResolveExpr && objType.isNullable() -> {
            showType(func, node, currentType)

            inference.addError(node, "Cannot access field [${node.id}] of null")
            post[objRef] = objType.refineToNonNull()
            post[ref] = currentType
          }

          else -> {
            showType(func, node, currentType)

            post[ref] = currentType
          }
        }
      }

      is Literal -> {
        preserveConditional()
        val nodeRef = Reference.make(node)
        post[nodeRef] = TypeInfo.make(nodeRef.javaType, when (node) {
          is BooleanLiteral -> hierarchy.BOOLEAN
          is CharLiteral -> hierarchy.CHAR
          is DoubleLiteral -> hierarchy.DOUBLE
          is FloatLiteral -> hierarchy.FLOAT
          is IntegerLiteral -> hierarchy.INTEGER
          is LongLiteral -> hierarchy.LONG
          is ShortLiteral -> hierarchy.SHORT
          is NullLiteral -> JTCNullType.SINGLETON
          is StringLiteral -> hierarchy.STRING
        })
      }

      is CastExpr -> {
        preserveConditional()
        val nodeRef = Reference.make(node)

        if (node.type is JTCPrimitiveType) {
          // Casts to primitive values are conversions
          post[nodeRef] = TypeInfo.make(node.type)
        } else {
          val currentType = pre[Reference.make(node.expr)].type
          post[Reference.make(node.expr)] = currentType.toShared()

          if (TypeInfo.useTypestateTrees) {
            val newType = currentType.cast(node.javaType)
            post[nodeRef] = newType

            if (!currentType.isUnknown() && newType.isUnknown()) {
              inference.addError(node, "Cannot perform cast from ${currentType.format()} to ${node.type.format()}")
              post[nodeRef] = newType.toBottom() // Avoid error propagation
            }
          } else {
            val newType = currentType.intersect(node.type).cast(node.javaType)
            post[nodeRef] = newType

            if (currentType.isBottom() || !newType.isBottom()) {
              if (!currentType.isSubtype(node.type)) {
                inference.addWarning(node, "Unsafe cast")
              }
            } else {
              // The cast is impossible
              inference.addError(node, "Cannot perform cast from ${currentType.format()} to ${node.type.format()}")
            }
          }
        }
      }

      is CaseExpr -> {
        preserveConditional()
        val value = (node.switchOp as Assign).left
        val labels = node.caseOps.mapNotNull { getLabel(it) }
        val valueRef = Reference.make(value)
        val nodeRef = Reference.make(node)
        // If all the cases have corresponding labels, we can refine
        if (labels.size == node.caseOps.size) {
          for ((ref, info) in pre) {
            post[ref] = StoreInfo.conditional(
              nodeRef,
              labels.fold(StoreInfo.bottom(info.javaType)) { acc, it -> acc.or(info.withLabel(valueRef, it)) },
              labels.fold(info) { acc, it -> acc.withoutLabel(valueRef, it) }
            )
          }
        }
      }

      is NullCheck -> {
        preserveConditional()
        val exprRef = Reference.make(node.expr)
        val currentType = pre[exprRef].type
        val notNull = currentType.refineToNonNull()
        post[exprRef] = notNull

        if (currentType.isNullable()) {
          inference.addError(node, "${node.message} (found: ${currentType.format()})")
        }
      }

      is BinaryExpr -> {
        preserveConditional()
        when (node.operator) {
          BinaryOP.And -> {
            val nodeRef = Reference.make(node)
            // Short-circuit
            val leftRef = Reference.make(node.left)
            val rightRef = Reference.make(node.right)
            for ((ref, info) in pre) {
              post[ref] = StoreInfo.conditional(
                nodeRef,
                info.withLabel(leftRef, "true").withLabel(rightRef, "true"),
                info.withLabel(leftRef, "false").removeCondition(rightRef).or(info.withLabel(rightRef, "false"))
              )
            }
            // This is expression evaluates to a boolean
            post[nodeRef] = TypeInfo.make(hierarchy.BOOLEAN)
          }
          BinaryOP.Or -> {
            val nodeRef = Reference.make(node)
            // Short-circuit
            val leftRef = Reference.make(node.left)
            val rightRef = Reference.make(node.right)
            for ((ref, info) in pre) {
              post[ref] = StoreInfo.conditional(
                nodeRef,
                info.withLabel(leftRef, "true").removeCondition(rightRef).or(info.withLabel(rightRef, "true")),
                info.withLabel(leftRef, "false").withLabel(rightRef, "false")
              )
            }
            // This is expression evaluates to a boolean
            post[nodeRef] = TypeInfo.make(hierarchy.BOOLEAN)
          }
          BinaryOP.Equal -> {
            val nodeRef = Reference.make(node)
            val (left, right) = literalOnTheRight(node)
            val leftRef = Reference.make(left)
            val currentType = pre[leftRef].type
            if (right is NullLiteral) {
              post[leftRef] = StoreInfo.conditional(
                nodeRef,
                currentType.refineToNull(),
                currentType.refineToNonNull()
              )
            } else {
              val label = getLabel(right)
              if (label != null) {
                for ((ref, info) in pre) {
                  post[ref] = StoreInfo.conditional(nodeRef, info.withLabel(leftRef, label), info.withoutLabel(leftRef, label))
                }
              }
            }
            post[nodeRef] = TypeInfo.make(hierarchy.BOOLEAN)
          }
          BinaryOP.NotEqual -> {
            val nodeRef = Reference.make(node)
            val (left, right) = literalOnTheRight(node)
            val leftRef = Reference.make(left)
            val currentType = pre[leftRef].type
            if (right is NullLiteral) {
              post[leftRef] = StoreInfo.conditional(
                nodeRef,
                currentType.refineToNonNull(),
                currentType.refineToNull()
              )
            } else {
              val label = getLabel(right)
              if (label != null) {
                for ((ref, info) in pre) {
                  post[ref] = StoreInfo.conditional(nodeRef, info.withoutLabel(leftRef, label), info.withLabel(leftRef, label))
                }
              }
            }
            post[nodeRef] = TypeInfo.make(hierarchy.BOOLEAN)
          }
          BinaryOP.Is -> {
            val nodeRef = Reference.make(node)
            val leftRef = Reference.make(node.left)
            val currentType = pre[leftRef].type
            val rightExpr = node.right as SymbolResolveExpr
            post[leftRef] = StoreInfo.conditional(
              nodeRef,
              currentType.refineToNonNull().intersect(rightExpr.type),
              currentType
            )
            post[nodeRef] = TypeInfo.make(hierarchy.BOOLEAN)
          }
          BinaryOP.Add,
          BinaryOP.Sub,
          BinaryOP.Mult,
          BinaryOP.FloatDivision,
          BinaryOP.FloatRemainder,
          BinaryOP.IntDivision,
          BinaryOP.IntRemainder,
          BinaryOP.BitwiseAnd,
          BinaryOP.BitwiseOr,
          BinaryOP.BitwiseXor,
          BinaryOP.LeftShift,
          BinaryOP.SignedRightShift,
          BinaryOP.UnsignedRightShift -> post[Reference.make(node)] = TypeInfo.make(hierarchy.getPrimitive(node.cfType as Type.JCPrimitiveType))
          BinaryOP.GreaterThan,
          BinaryOP.GreaterThanOrEqual,
          BinaryOP.LessThan,
          BinaryOP.LessThanOrEqual -> post[Reference.make(node)] = TypeInfo.make(hierarchy.BOOLEAN)
          BinaryOP.StringConcat -> post[Reference.make(node)] = TypeInfo.make(hierarchy.STRING)
        }
      }

      is UnaryExpr -> {
        preserveConditional()
        when (node.operator) {
          UnaryOP.Minus,
          UnaryOP.Plus,
          UnaryOP.BitwiseComplement,
          UnaryOP.Widening,
          UnaryOP.Narrowing -> post[Reference.make(node)] = TypeInfo.make(hierarchy.getPrimitive(node.cfType as Type.JCPrimitiveType))
          UnaryOP.Not -> {
            val nodeRef = Reference.make(node)
            val exprRef = Reference.make(node.expr)
            // Reverse stores
            for ((ref, info) in pre) {
              post[ref] = info.not(original = exprRef, negation = nodeRef)
            }
            post[nodeRef] = TypeInfo.make(hierarchy.BOOLEAN)
          }
          UnaryOP.ToString -> post[Reference.make(node)] = TypeInfo.make(hierarchy.STRING)
        }
      }

      is NewArrayWithDimensions -> {
        preserveConditional()
        for ((idx, init) in node.dimensions.withIndex()) {
          val valueType = pre[Reference.make(init)].toShared()
          if (!valueType.isSubtype(hierarchy.INTEGER)) {
            inference.addError(node, "Dimension in index $idx with type ${valueType.format()} is not a subtype of ${hierarchy.INTEGER}")
            break
          }
        }
        post[Reference.make(node)] = TypeInfo.make(node.javaType, node.type)
      }

      is NewArrayWithValues -> {
        preserveConditional()
        for ((idx, init) in node.initializers.withIndex()) {
          val valueType = pre[Reference.make(init)].toShared()
          if (!valueType.isSubtype(node.componentType)) {
            inference.addError(node, "Array value in index $idx with type ${valueType.format()} is not a subtype of ${node.componentType.format()}")
            break
          }
        }
        post[Reference.make(node)] = TypeInfo.make(node.javaType, node.type)
      }

      is SynchronizedExprEnd -> {
        preserveConditional()
        // TODO
      }

      is SynchronizedExprStart -> {
        preserveConditional()
        // TODO
      }

      is TernaryExpr -> {
        preserveConditional()
        post[Reference.make(node)] = pre[Reference.make(node.thenExpr)].or(pre[Reference.make(node.elseExpr)])
      }

      is ThrowExpr -> {
        preserveConditional()
        post.toBottom()
      }

      is SymbolResolveExpr -> {
        preserveConditional()
        // Skip
      }

      is NoOPExpr -> {
        preserveConditional()
        // Skip
      }

      is FuncDeclaration -> {
        preserveConditional()
        // We start with an empty store, so we do not use variables in outer scopes
        classAnalysis.analyzeMethod(null, node, Store())
      }

      is ClassDecl -> {
        preserveConditional()
        classAnalysis.analyze(node)
      }

      is ClassDeclAndCompanion -> {
        preserveConditional()
        classAnalysis.analyze(node.nonStatic)
        classAnalysis.analyze(node.static)
      }

      is FuncInterface -> {
        preserveConditional()
        // This case should come after FuncDeclaration since FuncDeclaration is a subtype of FuncInterface
        // Skip
      }
    }
  }

  fun analyzeEnd(func: FuncDeclaration, store: Store) {
    val thisRef = Reference.makeThis(func)
    val params = func.parameters.associateBy { Reference.make(it.id) }

    for ((ref, info) in store) {
      val type = info.type
      if (ref.isFieldOf(thisRef) || params.containsKey(ref) || ref == Reference.returnRef(ref.javaType)) {
        // We check completion of objects in fields later
        // and we check @Ensure annotations are respected as well
        continue
      }
      if (!type.canDrop()) {
        if (ref is CodeExprReference && ref.code is MethodCall) {
          inference.addError(ref.code, "Returned value did not complete its protocol (found: ${type.format()})")
        } else {
          inference.addError(func, "[${ref.format()}] did not complete its protocol (found: ${type.format()})")
        }
      }
    }

    for ((ref, param) in params) {
      val actual = store.getOrNull(ref)?.type ?: continue // If param is not in store, it means there is some while (true) loop in the code
      if (!actual.isSubtype(param.ensures)) {
        if (param.isThis || param.hasEnsures) {
          inference.addError(func, "Type of parameter [${ref.format()}] is ${actual.format()}, expected ${param.ensures.format()}}")
        } else {
          inference.addError(func, "[${ref.format()}] did not complete its protocol (found: ${actual.format()})")
        }
      }
    }
  }

  private fun analyzeExit(exit: CodeExpr, store: Store) {
    for ((ref, info) in store) {
      val type = info.type
      if (!type.canDrop()) {
        if (ref is CodeExprReference && ref.code is MethodCall) {
          inference.addError(ref.code, "Returned value did not complete its protocol (found: ${type.format()})")
        } else {
          inference.addError(exit, "[${ref.format()}] did not complete its protocol (found: ${type.format()})")
        }
      }
    }
  }

  fun getBooleanValue(node: CodeExpr): Boolean? = when {
    node is BooleanLiteral -> node.value
    node is UnaryExpr && node.operator == UnaryOP.Not -> getBooleanValue(node.expr)?.not()
    node is Assign -> getBooleanValue(node.right)
    else -> null
  }

  private fun isEnumValue(code: CodeExpr): Boolean {
    return code is Select && code.expr is SymbolResolveExpr && code.expr.javaType.isEnum()
  }

  private fun getLabel(code: CodeExpr): String? {
    return if (code is Select && code.expr is SymbolResolveExpr && code.expr.javaType.isEnum()) {
      "${code.expr.qualifiedName}.${code.id}"
    } else if (code is BooleanLiteral) {
      if (code.value) "true" else "false"
    } else null
  }

  private fun literalOnTheRight(binary: BinaryExpr): Pair<CodeExpr, CodeExpr> {
    return if (binary.left is Literal || isEnumValue(binary.left)) {
      Pair(binary.right, binary.left)
    } else {
      Pair(binary.left, binary.right)
    }
  }

  private fun getInnerExpr(code_: CodeExpr): CodeExpr {
    var code = code_
    // Prefer the casted expression,
    // except when the type is primitive (in that case the cast is a conversion)
    while (code is CastExpr && code.type !is JTCPrimitiveType) {
      code = code.expr
    }
    return code
  }

  private fun showType(func: FuncDeclaration, node: CodeExpr, currentType: TypeInfo) {
    if (node is Id && (node.name == "this" || node.name.contains("#"))) {
      return
    }
    if (!utils.shouldReportTypeInfo()) {
      return
    }
    if (currentType.debugIsPrimitive()) {
      return
    }
    val ref = Reference.make(node)
    inference.addWarning(node, "${ref.format()}: ${currentType.format()}")
  }
}
