package de.fosd.typechef

import conditional.Choice
import conditional.Opt
import conditional.{Choice, Opt}
import crewrite.{IfdefToIf, CAnalysisFrontend}
import featureexpr.sat.SATFeatureModel
import featureexpr.{FeatureModel, SingleFeatureExpr}
import java.io.{File, FileWriter}
import options.FrontendOptions
import parser.c._
import parser.c.FunctionDef
import parser.c.PostfixExpr
import parser.c.TranslationUnit
import scala.Some

/**
 * Created with IntelliJ IDEA.
 * User: rhein
 * Date: 17.09.13
 * Time: 10:44
 * To change this template use File | Settings | File Templates.
 */
object Extras {
    /**
     * Returns a sorted list of all features in this AST, including Opt and Choice Nodes
     * @param root input element
     * @return
     */
    def getAllFeatures(root: Product): List[SingleFeatureExpr] = {
        var featuresSorted: List[SingleFeatureExpr] = getAllFeaturesRec(root).toList
        // sort to eliminate any non-determinism caused by the set
        featuresSorted = featuresSorted.sortWith({
            (x: SingleFeatureExpr, y: SingleFeatureExpr) => x.feature.compare(y.feature) > 0
        })
        println("found " + featuresSorted.size + " features")
        featuresSorted //.map({s:String => FeatureExprFactory.createDefinedExternal(s)});
    }

    private def getAllFeaturesRec(root: Any): Set[SingleFeatureExpr] = {
        root match {
            case x: Opt[_] => x.feature.collectDistinctFeatureObjects.toSet ++ getAllFeaturesRec(x.entry)
            case x: Choice[_] => x.feature.collectDistinctFeatureObjects.toSet ++ getAllFeaturesRec(x.thenBranch) ++ getAllFeaturesRec(x.elseBranch)
            case l: List[_] => {
                var ret: Set[SingleFeatureExpr] = Set()
                for (x <- l) {
                    ret = ret ++ getAllFeaturesRec(x)
                }
                ret
            }
            case x: Product => {
                var ret: Set[SingleFeatureExpr] = Set()
                for (y <- x.productIterator.toList) {
                    ret = ret ++ getAllFeaturesRec(y)
                }
                ret
            }
            case o => Set()
        }
    }

    /**
     * save which features are used as ifdef-variables in the AST (maybe they are still not needed in the control flow)
     * @param ast
     */
    def saveFileFeatures(ast: AST) {
        val fileWriter = new FileWriter("usedFeatures.txt")
        try {
            fileWriter.write(getAllFeatures(ast).mkString("\n"))
            println("saved usedFeatures as " + (new File("usedFeatures.txt")).getAbsolutePath)
        } finally {
            fileWriter.close()
        }
    }

    def createDimacsFileFromSATFeatureModel(fm: SATFeatureModel) {
//        opt.getFeatureModelTypeSystem.asInstanceOf[SATFeatureModel].writeToDimacsFile(new File(
            //"/tmp/BB_fm.dimacs"))
        fm.writeToDimacsFile(new File("/tmp/savedFM.dimacs"))
        println("saved fm as " + (new File("/tmp/savedFM.dimacs")).getAbsolutePath)

    }

    def getSimpleCFGfeatures(ast:AST, fm :FeatureModel) : Set[SingleFeatureExpr] = {
        def getCalledFunctions(ast:Any) : Set[String] = {
            ast match {
                case PostfixExpr(Id(fname:String), FunctionCall(exprs)) => Set(fname) ++ getCalledFunctions(exprs)
                case x: Opt[_] => getCalledFunctions(x.entry)
                case x: Choice[_] => getCalledFunctions(x.thenBranch) ++ getCalledFunctions(x.elseBranch)
                case l: List[_] => {
                    var ret: Set[String] = Set()
                    for (x <- l) {
                        ret = ret ++ getCalledFunctions(x)
                    }
                    ret
                }
                case x: Product => {
                    var ret: Set[String] = Set()
                    for (y <- x.productIterator.toList) {
                        ret = ret ++ getCalledFunctions(y)
                    }
                    ret
                }
                case o => Set()
            }
        }
        def getUsedFeaturesRec(fName:String,
                               functionToCalledFunctionsMap:Map[String,Set[String]],
                               functionToASTMap : Map[String, FunctionDef],
                               scannedFunctions : Set[String] = Set()) : Set[SingleFeatureExpr] = {
            if (scannedFunctions.contains(fName)) {
                Set()
            } else {
                val thisScannedFunctions = scannedFunctions + fName
                var usedFeatures = getAllFeaturesRec(functionToASTMap.get(fName))
                functionToCalledFunctionsMap.get(fName) match {
                    case None => println ("no function definition found for called function " + fName)
                    case Some(calledFunctions) => {
                        for (calledF : String <- calledFunctions) {
                            usedFeatures = usedFeatures ++ getUsedFeaturesRec(calledF, functionToCalledFunctionsMap, functionToASTMap, thisScannedFunctions)
                        }
                    }
                }
                usedFeatures
            }
        }

        val cf = new CAnalysisFrontend(ast.asInstanceOf[TranslationUnit], fm)
        val lst : List[FunctionDef] = cf.filterAllASTElems[FunctionDef](ast)
        //val functionNames : Set[String] = lst.map(x => x.declarator.getId.name).toSet
        var functionToCalledFunctionsMap : Map[String, Set[String]] = Map()
        var functionToASTMap : Map[String, FunctionDef] = Map()
        for (x: FunctionDef <- lst) {
            // problem: function overloading is not handled
            functionToCalledFunctionsMap = functionToCalledFunctionsMap.updated(x.declarator.getId.name, getCalledFunctions(x))
            functionToASTMap = functionToASTMap.updated(x.declarator.getId.name, x)
        }
        val startFunction:String = "ldv_main0_sequence_infinite_withcheck_stateful"
        getUsedFeaturesRec(startFunction, functionToCalledFunctionsMap, functionToASTMap)
    }
}
