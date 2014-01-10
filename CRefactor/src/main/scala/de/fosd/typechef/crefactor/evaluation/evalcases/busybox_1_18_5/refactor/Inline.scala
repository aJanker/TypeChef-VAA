package de.fosd.typechef.crefactor.evaluation.evalcases.busybox_1_18_5.refactor

import de.fosd.typechef.crefactor.Morpheus
import de.fosd.typechef.crefactor.evaluation.busybox_1_18_5.BusyBoxEvaluation
import de.fosd.typechef.crefactor.evaluation.busybox_1_18_5.linking.CLinking
import de.fosd.typechef.parser.c._
import de.fosd.typechef.crefactor.backend.refactor.CInlineFunction
import scala.util.Random
import de.fosd.typechef.featureexpr.FeatureExpr
import de.fosd.typechef.crefactor.evaluation.Refactoring
import de.fosd.typechef.parser.c.PostfixExpr
import de.fosd.typechef.parser.c.Id
import de.fosd.typechef.parser.c.FunctionCall

object Inline extends BusyBoxEvaluation with Refactoring {

    private def isFunctionCall(p: PostfixExpr): Boolean = {
        p match {
            case PostfixExpr(Id(_), FunctionCall(_)) => true
            case _ => false
        }
    }

    def refactor(morpheus: Morpheus, linkInterface: CLinking): (Boolean, AST, List[FeatureExpr], List[(String, AST)]) = {
        val psExpr = filterAllASTElems[PostfixExpr](morpheus.getAST)
        val funcCalls = psExpr.par.filter(isFunctionCall)
        val availableFuncCalls = funcCalls.par.filter(p => {
            p.p match {
                case i: Id => CInlineFunction.isAvailable(morpheus, i)
                case _ => false
            }
        }).toList

        println("+++ Function calls found to inline: " + availableFuncCalls.size)

        if (availableFuncCalls.isEmpty) return (false, null, List(), List())

        val callIdToInline = availableFuncCalls(Random.nextInt(availableFuncCalls.size)).p.asInstanceOf[Id]

        println("+++ Trying to inline call: " + callIdToInline)

        try {
            val refAST = CInlineFunction.inline(morpheus, callIdToInline, true, true)
            val callDeclDef = CInlineFunction.divideCallDeclDef(callIdToInline, morpheus)

            val callFeatures = callDeclDef._1.map(_.feature)
            val declFeatures = callDeclDef._2.flatMap(filterAllFeatureExpr(_))
            val defFeatures = callDeclDef._3.flatMap(filterAllFeatureExpr(_))

            val features = (callFeatures ::: declFeatures ::: defFeatures).distinct

            println("+++ Affected features: " + features)

            (true, refAST, features, List())

        } catch {
            case e: Exception => {
                println("+++ Inlining failed!")
                e.printStackTrace
                return (false, null, List(), List())
            }
        }
    }
}