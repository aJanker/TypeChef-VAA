package de.fosd.typechef.crewrite

import scala.collection.mutable.ListBuffer
import scala.collection.mutable

import java.util
import java.util.{Collections, IdentityHashMap}
import java.util.regex.Pattern
import java.io._
import io.Source

import org.apache.logging.log4j.LogManager

import de.fosd.typechef.parser.c._
import de.fosd.typechef.featureexpr._
import de.fosd.typechef.featureexpr.bdd.BDDFeatureExpr
import de.fosd.typechef.featureexpr.sat._
import de.fosd.typechef.conditional._
import de.fosd.typechef.lexer.FeatureExprLib
import de.fosd.typechef.typesystem.CTypeSystemFrontend

import org.kiama.rewriting.Rewriter._
import scala.reflect.ClassTag
import de.fosd.typechef.parser.c.PlainParameterDeclaration
import de.fosd.typechef.parser.c.SwitchStatement
import de.fosd.typechef.parser.c.EnumSpecifier
import scala.Some
import de.fosd.typechef.parser.c.NAryExpr
import de.fosd.typechef.parser.c.DoStatement
import de.fosd.typechef.parser.c.VoidSpecifier
import de.fosd.typechef.parser.c.DeclarationStatement
import de.fosd.typechef.parser.c.TypelessDeclaration
import de.fosd.typechef.parser.c.ExprList
import de.fosd.typechef.parser.c.CompoundStatement
import de.fosd.typechef.conditional.Opt
import de.fosd.typechef.parser.c.PostfixExpr
import de.fosd.typechef.parser.c.AtomicNamedDeclarator
import de.fosd.typechef.parser.c.ExternSpecifier
import de.fosd.typechef.conditional.Choice
import de.fosd.typechef.parser.c.TranslationUnit
import de.fosd.typechef.parser.c.NArySubExpr
import de.fosd.typechef.parser.c.WhileStatement
import de.fosd.typechef.parser.c.InitDeclaratorI
import de.fosd.typechef.parser.c.UnaryOpExpr
import de.fosd.typechef.parser.c.LabelStatement
import de.fosd.typechef.parser.c.ExprStatement
import de.fosd.typechef.parser.c.StructDeclaration
import de.fosd.typechef.parser.c.IntSpecifier
import de.fosd.typechef.parser.c.GotoStatement
import de.fosd.typechef.parser.c.FunctionDef
import de.fosd.typechef.parser.c.NestedFunctionDef
import de.fosd.typechef.parser.c.NestedNamedDeclarator
import de.fosd.typechef.parser.c.Enumerator
import de.fosd.typechef.parser.c.CTypeContext
import de.fosd.typechef.parser.c.TypeDefTypeSpecifier
import de.fosd.typechef.parser.c.PointerPostfixSuffix
import de.fosd.typechef.parser.c.AssignExpr
import de.fosd.typechef.conditional.One
import de.fosd.typechef.parser.c.ForStatement
import de.fosd.typechef.parser.c.DeclParameterDeclList
import de.fosd.typechef.parser.c.Id
import de.fosd.typechef.parser.c.Constant
import de.fosd.typechef.parser.c.Pragma
import de.fosd.typechef.parser.c.StructDeclarator
import de.fosd.typechef.parser.c.ReturnStatement
import de.fosd.typechef.parser.c.StructOrUnionSpecifier
import de.fosd.typechef.parser.c.FunctionCall
import de.fosd.typechef.parser.c.IfStatement
import de.fosd.typechef.parser.c.EmptyExternalDef
import de.fosd.typechef.parser.c.Declaration
import de.fosd.typechef.parser.c.DeclIdentifierList
import de.fosd.typechef.parser.c.EmptyStatement
import de.fosd.typechef.parser.c.ElifStatement
import de.fosd.typechef.parser.c.ParameterDeclarationD
import de.fosd.typechef.error.TypeChefError


/**
 * strategies to rewrite ifdefs to ifs
 */

class IfdefToIf extends ASTNavigation with ConditionalNavigation {
    private lazy val logger = LogManager.getLogger(this.getClass.getName)
    val trueF = FeatureExprFactory.True
    var fm = FeatureExprLib.featureModelFactory.empty

    var analysisResults = ""

    val path = new File("..").getCanonicalPath ++ "/ifdeftoif/"

    val parameterForFeaturesOutsideOfConfigFile = "0"

    val createFunctionsForModelChecking = false

    val CONFIGPREFIX = "v_"
    var counter = 0
    var defuse: IdentityHashMap[Id, List[Id]] = new IdentityHashMap()
    var usedef: IdentityHashMap[Id, List[Id]] = new IdentityHashMap()
    var idMap: Map[FeatureExpr, Int] = Map()
    var fctMap: Map[Id, Map[FeatureExpr, String]] = Map()
    var jmpMap: Map[String, Map[FeatureExpr, String]] = Map()
    var replaceId: IdentityHashMap[Id, FeatureExpr] = new IdentityHashMap()
    var typeDefs: ListBuffer[Id] = ListBuffer()
    var alreadyReplaced: ListBuffer[Id] = ListBuffer()
    val toBeReplaced: util.IdentityHashMap[Product, Product] = new IdentityHashMap()
    var liftOptReplaceMap: Map[Opt[_], List[Opt[_]]] = Map()
    val idsToBeReplaced: IdentityHashMap[Id, Set[FeatureExpr]] = new IdentityHashMap()
    val writeOptionsIntoFile = true

    val exponentialComputationThreshold = 10
    val numberOfVariantThreshold = 1024
    val nstoms = 1000000

    val isBusyBox = false
    // Variables for statistics

    // Features
    var noOfFeatures = 0
    var noOfTotalFeatures = 0
    var featureSet: Set[SingleFeatureExpr] = Set()

    // Declarations
    var noOfOptionalDeclarations = 0
    var noOfDeclarations = 0
    var noOfDeclarationDuplications = 0
    var noOfDeclarationDuplicationsSpecifiers = 0
    var noOfDeclarationDuplicationsInits = 0

    // Functions
    var noOfFunctions = 0
    var noOfOptionalFunctions = 0
    var noOfFunctionDuplicationsSpecifiers = 0
    var noOfFunctionDuplicationsDeclarators = 0
    var noOfFunctionDuplicationsParameters = 0
    var noOfFunctionDuplications = 0

    // Statements
    var noOfStatements = 0
    var noOfStatementDuplications = 0
    var noOfStatementsVariable = 0

    // StructDeclarations
    var noOfStructDeclarations = 0
    var noOfStructDeclarationsRenamed = 0

    // Enumerators
    var noOfEnumerators = 0
    var noOfEnumeratorsVariable = 0

    // Techniques
    var noOfRenamings = 0
    var noOfRenamingUsages = 0
    var noOfEmbeddings = 0
    var noOfDuplications = 0

    // Choices
    var noOfChoiceNodes = 0

    def resetValues() {
        // Features
        noOfFeatures = 0

        // Declarations
        noOfOptionalDeclarations = 0
        noOfDeclarations = 0
        noOfDeclarationDuplications = 0
        noOfDeclarationDuplicationsSpecifiers = 0
        noOfDeclarationDuplicationsInits = 0

        // Functions
        noOfFunctions = 0
        noOfOptionalFunctions = 0
        noOfFunctionDuplicationsSpecifiers = 0
        noOfFunctionDuplicationsDeclarators = 0
        noOfFunctionDuplicationsParameters = 0
        noOfFunctionDuplications = 0

        // Statements
        noOfStatements = 0
        noOfStatementDuplications = 0
        noOfStatementsVariable = 0

        // Techniques
        noOfRenamings = 0
        noOfRenamingUsages = 0
        noOfEmbeddings = 0
        noOfDuplications = 0

        // Choices
        noOfChoiceNodes = 0
    }

    /**
     * Converts a feature expression to a condition in the c programming language. def(x64) becomes options.x64.
     * @param feature
     * @return
     */
    def featureToCExpr(feature: FeatureExpr): Expr = feature match {
        case d: DefinedExternal => PostfixExpr(Id("options"), PointerPostfixSuffix(".", Id(d.feature.toLowerCase)))
        case d: DefinedMacro => featureToCExpr(d.presenceCondition)
        case b: BDDFeatureExpr =>
            bddFexToCExpr(b,
                ((fName: String) => PostfixExpr(Id("options"), PointerPostfixSuffix(".", Id(fName.toLowerCase))))
            )
        case a: And =>
            val l = a.clauses.toList
            var del = List[Opt[NArySubExpr]]()
            if (l.size < 1) {
                print("")
            }
            for (e <- l.tail)
                del = del ++ List(Opt(trueF, NArySubExpr("&&", featureToCExpr(e))))
            NAryExpr(featureToCExpr(l.head), del)
        case o: Or =>
            val l = o.clauses.toList
            var del = List[Opt[NArySubExpr]]()
            if (l.size < 1) {
                print("")
            }
            for (e <- l.tail)
                del = del ++ List(Opt(trueF, NArySubExpr("||", featureToCExpr(e))))
            NAryExpr(featureToCExpr(l.head), del)
        case Not(n) => UnaryOpExpr("!", featureToCExpr(n))
    }

    /**
     * Same as featureToCExpr for BDDs.
     * @param bdd
     * @param transformFName
     * @return
     */
    def bddFexToCExpr(bdd: BDDFeatureExpr, transformFName: String => Expr): Expr = {
        if (bdd.isTautology()) Constant("1")
        else if (bdd.isContradiction()) Constant("0")
        else {
            def clause(d: Array[(Byte, String)]): Expr = NAryExpr(clauseForHead(d.head), clauseForTailElements(d.tail))
            def clauseForTailElements(d: Array[(Byte, String)]): List[Opt[NArySubExpr]] = d.map(
                x => (if (x._1 == 0)
                    List(Opt(trueF, NArySubExpr("&&", UnaryOpExpr("!", transformFName(x._2)))))
                else
                    List(Opt(trueF, NArySubExpr("&&", transformFName(x._2))))
                    )).foldLeft(List(): List[Opt[NArySubExpr]])((a, b) => a ++ b)
            def clauseForHead(x: (Byte, String)): Expr = (if (x._1 == 0)
                UnaryOpExpr("!", transformFName(x._2))
            else
                transformFName(x._2)
                )
            val cnfClauses: List[Expr] = bdd.getBddAllSat.map(clause(_)).toList
            NAryExpr(cnfClauses.head,
                cnfClauses.tail.foldLeft(List(): List[Opt[NArySubExpr]])((a, b: Expr) => a ++ List(Opt(trueF, NArySubExpr("||", b))))
            )
        }
    }

    /**
     * Retrieves an abstract syntax tree for a given file.
     * @param fileToAnalyse
     * @return
     */
    def getAstFromFile(fileToAnalyse: File): TranslationUnit = {
        def parseFile(stream: InputStream, file: String, dir: String): TranslationUnit = {
            val ast: AST = new ParserMain(new CParser).parserMain(
                () => CLexer.lexStream(stream, file, Collections.singletonList(dir), null), new CTypeContext, SilentParserOptions)
            ast.asInstanceOf[TranslationUnit]
        }
        val fis = new FileInputStream(fileToAnalyse)
        val ast = parseFile(fis, fileToAnalyse.getName, fileToAnalyse.getParent)
        fis.close()
        ast
    }

    def computeDifference(before: Int, after: Int): Double = {
        ((after - before) / (before.toDouble))
    }

    def computeDifference(before: Long, after: Long): Double = {
        ((after - before) / (before.toDouble))
    }

    def getAnalysisResults: String = {
        analysisResults
    }

    /**
     * Used for reading/writing to database, files, etc.
     * Code From the book "Beginning Scala"
     * http://www.amazon.com/Beginning-Scala-David-Pollak/dp/1430219890
     */
    def using[A <: {def close()}, B](param: A)(f: A => B): B =
        try {
            f(param)
        } finally {
            param.close()
        }

    /**
     * Creates a new file with name fileName and content data.
     * @param fileName
     * @param data
     */
    def writeToFile(fileName: String, data: String) {
        using(new FileWriter(fileName)) {
            fileWriter => fileWriter.write(data)
        }
    }

    /**
     * Appends textData to the file fileName.
     * @param fileName
     * @param textData
     */
    def appendToFile(fileName: String, textData: String) {
        using(new FileWriter(fileName, true)) {
            fileWriter => using(new PrintWriter(fileWriter)) {
                printWriter => printWriter.print(textData)
            }
        }
    }

    /**
     * Returns a new CTypeSystemFrontend for a given AST.
     * @param ast
     * @return
     */
    def getTypeSystem(ast: AST): CTypeSystemFrontend = {
        new CTypeSystemFrontend(ast.asInstanceOf[TranslationUnit])
    }


    /**
     * Creates a file including an external int, a function, a struct with all features and an init function for
     * that struct.
     */
    def writeOptionFile(ast: AST) {
        val features = filterFeatures(ast)
        val optionsAst = definedExternalToAst(features)

        PrettyPrinter.printF(optionsAst, "opt.h")
    }

    /**
     * Returns the header string for the csv file which includes various statistics of the ifdef to if transformation
     * process.
     * @return
     */
    def getCSVHeader: String = {
        "File name,Number of features,Number of AST nodes before,Number of AST nodes after,AST node difference,Declarations before,Annotated declarations,Annotated declaration ratio,Declarations afterwards,Declaration growth,Functions,Annotated functions,Annotated function ratio,Functions afterwards,Function growth,If/Elif statements before,If/Elif statements afterwards,If/Elif statement growth,Renamed identifier declarations,Renamed identifier usages,Parsing time,Ifdeftoif time\n"
    }

    /**
     * Creates a csv friendly line with all the statistical information from one transformation
     */
    def createCsvString(): String = {
        val s = ","
        noOfFeatures + s + noOfDeclarations + s + noOfOptionalDeclarations + s + noOfDeclarationDuplications + s + noOfFunctions + s + noOfOptionalFunctions + s + noOfFunctionDuplications + s + noOfStatements + s + noOfStatementsVariable + s + noOfStatementDuplications + s + noOfRenamings + s + noOfRenamingUsages + s + noOfChoiceNodes
    }

    /**
     * Creates an AST including an external int, a function, a struct with all features and an init function for that struct
     */
    def getOptionFile(ast: AST): TranslationUnit = {
        val features = filterFeatures(ast)
        val optionsAst = definedExternalToAst(features)
        optionsAst
    }

    /**
     * Creates an option struct for all collected FeatureExpressions
     */
    def getTotalOptionFile: TranslationUnit = {
        definedExternalToAst(featureSet)
    }

    /**
     * Converts a set of FeatureExpressions into an option struct
     */
    def definedExternalToAst(defExSet: Set[SingleFeatureExpr]): TranslationUnit = {
        val structDeclList = defExSet.map(x => {
            Opt(trueF, StructDeclaration(List(Opt(trueF, IntSpecifier())), List(Opt(trueF, StructDeclarator(AtomicNamedDeclarator(List(), Id(x.feature.toLowerCase), List()), None, List())))))
        }).toList
        val structDeclaration = Opt(trueF, Declaration(List(Opt(trueF, StructOrUnionSpecifier(false, Some(Id("ifdef_options")), Some(structDeclList)))), List(Opt(trueF, InitDeclaratorI(AtomicNamedDeclarator(List(), Id("options"), List()), List(), None)))))

        if (!createFunctionsForModelChecking) {
            TranslationUnit(List(structDeclaration))
        } else {
            val externDeclaration = Opt(trueF, Declaration(List(Opt(trueF, ExternSpecifier()), Opt(trueF, IntSpecifier())), List(Opt(trueF, InitDeclaratorI(AtomicNamedDeclarator(List(), Id("__VERIFIER_NONDET_INT"), List(Opt(trueF, DeclParameterDeclList(List(Opt(trueF, PlainParameterDeclaration(List(Opt(trueF, VoidSpecifier()))))))))), List(), None)))))

            val function = Opt(trueF, FunctionDef(List(Opt(trueF, IntSpecifier())), AtomicNamedDeclarator(List(), Id("select_one"), List(Opt(trueF, DeclIdentifierList(List())))), List(), CompoundStatement(List(Opt(trueF, IfStatement(One(PostfixExpr(Id("__VERIFIER_NONDET_INT"), FunctionCall(ExprList(List())))), One(CompoundStatement(List(Opt(trueF, ReturnStatement(Some(Constant("1"))))))), List(), Some(One(CompoundStatement(List(Opt(trueF, ReturnStatement(Some(Constant("0"))))))))))))))

            val cmpStmt = defExSet.map(x => {
                Opt(trueF, ExprStatement(AssignExpr(PostfixExpr(Id("options"), PointerPostfixSuffix(".", Id(x.feature.toLowerCase))), "=", PostfixExpr(Id("select_one"), FunctionCall(ExprList(List()))))))
            }).toList
            val initFunction = Opt(trueF, FunctionDef(List(Opt(trueF, VoidSpecifier())), AtomicNamedDeclarator(List(), Id("initOptions"), List(Opt(trueF, DeclIdentifierList(List())))), List(), CompoundStatement(cmpStmt)))
            TranslationUnit(List(externDeclaration, function, structDeclaration, initFunction))
        }
    }

    /**
     * Filteres a given product for feature expressions which are not True and returns a set including each single feature expression
     */
    def filterFeatures(a: Any): Set[SingleFeatureExpr] = {
        var featureSet: Set[FeatureExpr] = Set()
        val r = manytd(query {
            case Opt(ft, entry) =>
                featureSet += ft
            case Choice(ft, a, b) =>
                featureSet += ft
        })
        r(a).get
        featureSet.flatMap(x => x.collectDistinctFeatureObjects)
    }

    /**
     * Retrieves a list of tuples out of a choice node. Also takes choices inside choices into account
     */
    def conditionalToTuple[T <: Product](choice: Conditional[T], currentContext: FeatureExpr = trueF, count: Boolean = true): List[(FeatureExpr, T)] = {
        def addOne[T <: Product](entry: One[T], ft: FeatureExpr): List[(FeatureExpr, T)] = {
            entry match {
                case One(null) =>
                    List()
                case One(a) =>
                    if (count) {
                        noOfChoiceNodes = noOfChoiceNodes + 1
                    }
                    val finalFeature = ft.and(currentContext)
                    if (!finalFeature.isSatisfiable()) {
                        List()
                    } else {
                        List((ft.and(currentContext), a))
                    }
            }
        }
        choice match {
            case One(null) =>
                List()
            case o@One(something) =>
                addOne(o, currentContext)
            case Choice(ft, first@One(_), second@One(_)) =>
                addOne(first, ft.and(currentContext)) ++ addOne(second, ft.not().and(currentContext))
            case Choice(ft, first@Choice(_, _, _), second@Choice(_, _, _)) =>
                conditionalToTuple(first, currentContext) ++ conditionalToTuple(second, currentContext)
            case Choice(ft, first@One(a), second@Choice(_, _, _)) =>
                addOne(first, ft.and(currentContext)) ++ conditionalToTuple(second, currentContext)
            case Choice(ft, first@Choice(_, _, _), second@One(_)) =>
                conditionalToTuple(first, currentContext) ++ addOne(second, ft.not().and(currentContext))
        }
    }

    /**
     * Retrieves a list of feature expressions out of a choice node. Also takes choices inside choices into account
     */
    private def choiceToFeatures[T <: Product](c: Conditional[T], currentContext: FeatureExpr = trueF): List[FeatureExpr] = {
        def addOne[T <: Product](entry: One[T], ft: FeatureExpr): List[FeatureExpr] = {
            entry match {
                case One(null) =>
                    List()
                case One(a) =>
                    //noOfChoiceNodes = noOfChoiceNodes + 1
                    List(ft)
            }
        }
        c match {
            case One(null) =>
                List()
            case One(a) =>
                if (currentContext.equals(trueF)) {
                    List()
                } else {
                    List(currentContext)
                }
            case Choice(ft, first, second) =>
                choiceToFeatures(first, ft) ++ choiceToFeatures(second, ft.not)
        }
    }

    /**
     * Filters a given product for feature expressions which are not True and returns a set of all different feature expressions.
     */
    def getSingleFeatureSet(a: Any): List[FeatureExpr] = {
        def getFeatureExpressions(a: Any): List[FeatureExpr] = {
            a match {
                case o: Opt[_] => (if (o.feature == trueF) List() else List(o.feature)) ++ o.productIterator.toList.flatMap(getFeatureExpressions(_))
                case l: List[_] => l.flatMap(getFeatureExpressions(_))
                case p: Product => p.productIterator.toList.flatMap(getFeatureExpressions(_))
                case t: FeatureExpr => if (t == trueF) List() else List(t)
                case _ => List()
            }
        }
        val result = getFeatureExpressions(a).distinct
        result
    }

    def getFeatureExpressions(a: Any): List[FeatureExpr] = {
        var lst: ListBuffer[FeatureExpr] = ListBuffer()
        val r = breadthfirst(query {
            case Opt(f, _) =>
                if (!f.equivalentTo(trueF) && !f.equivalentTo(FeatureExprFactory.False) && !lst.contains(f)) {
                    lst += f
                }
        })
        r(a).get
        lst.toList
    }

    /**
     * This method fills the IdMap which is used to map a feature expression to a number. This number is used for
     * for renaming identifiers e.g. #ifdef A int a #endif -> int _1_a     feature A is mapped to number 1.
     */
    def fillIdMap(a: Any) {
        if (idMap.size == 0) {
            idMap += (trueF -> idMap.size)
        }

        if (new File(path ++ "featureMap.csv").exists) {
            val featureMap = scala.io.Source.fromFile(path ++ "featureMap.csv").mkString.split("\n")
            featureMap.foreach(x => {
                val tuple = x.split(",")
                val feature = new FeatureExprParser().parse(tuple.head)
                val number = tuple.tail.head.toInt
                idMap += (feature -> number)
            })
        }
    }

    def getFromIdMap(feat: FeatureExpr): Int = {
        if (!idMap.contains(feat)) {
            idMap += (feat -> idMap.size)
        }
        idMap.get(feat).get
    }

    /**
     * Creates all possible 2 power n combinations for a list of n raw (single) feature expressions. List(def(x64), def(x86))
     * becomes List(def(x64)&def(x86),!def(x64)&def(x86),def(x64)&!def(x86),!def(x64)&!def(x86).
     */
    def getFeatureCombinations(lst: List[FeatureExpr]): List[FeatureExpr] = {
        if (lst.size == 0) {
            List()
        } else {
            lst.tail.foldLeft(List(lst.head, lst.head.not()))((first, second) => {
                first.flatMap(x => List(x.and(second), x.and(second.not())))
            })
        }
    }

    /**
     * Retrieves the FeatureExpression which is mapped to the given number.
     */
    def getFeatureForId(id: Int): Option[FeatureExpr] = {
        if (idMap.size < id || id < 0) {
            None
        } else {
            val it = idMap.iterator
            while (it.hasNext) {
                val next = it.next()
                if (next._2.equals(id)) {
                    return Some(next._1)
                }
            }
            None
        }
    }

    def replaceFeatureByTrue[T <: Product](t: T, feat: FeatureExpr): T = {
        val r = manytd(rule {
            case l: List[Opt[_]] =>
                l.flatMap(o =>
                    if (o.feature.equivalentTo(trueF)) {
                        List(o)
                    } else if (feat.&(o.feature).isContradiction()) {
                        List()
                    } else if (o.feature.equivalentTo(feat)) {
                        List(o.copy(feature = trueF))
                    } else if (feat.implies(o.feature).isTautology()) {
                        List(o.copy(feature = trueF))
                    } else {
                        List(o)
                    })
        })

        /*
         Check if initial element is an Opt node and remove the feature because the rewriting rule in that case
         only handles opt lists inside the initial element.
          */
        t match {
            case o@Opt(ft, entry) =>
                if (ft.equals(trueF)) {
                    r(o) match {
                        case None => t
                        case _ => r(o).get.asInstanceOf[T]
                    }
                } else if (ft.equivalentTo(feat)) {
                    val newOpt = Opt(trueF, entry)
                    r(newOpt) match {
                        case None => newOpt.asInstanceOf[T]
                        case _ => r(newOpt).get.asInstanceOf[T]
                    }
                } else {
                    r(o) match {
                        case None => t
                        case _ => r(o).get.asInstanceOf[T]
                    }
                }
            case _ =>
                r(t) match {
                    case None => t
                    case k => k.get.asInstanceOf[T]
                }
        }
    }

    def addIdUsages(i: Id, ft: FeatureExpr) {
        noOfRenamings = noOfRenamings + 1
        if (defuse.containsKey(i)) {
            val idUsages = defuse.get(i)
            noOfRenamingUsages = noOfRenamingUsages + idUsages.size
            idUsages.foreach(x => {
                if (idsToBeReplaced.containsKey(x)) {
                    idsToBeReplaced.put(x, idsToBeReplaced.get(x) + ft)
                } else {
                    idsToBeReplaced.put(x, Set(ft))
                }
            })
        } else if (usedef.containsKey(i)) {
            val idUsages = usedef.get(i).flatMap(x => defuse.get(x))
            idUsages.foreach(x => {
                if (idsToBeReplaced.containsKey(x)) {
                    idsToBeReplaced.put(x, idsToBeReplaced.get(x) + ft)
                } else {
                    idsToBeReplaced.put(x, Set(ft))
                }
            })
        }
    }

    def convertIds[T <: Product](t: T, ft: FeatureExpr): T = {
        if (ft.equals(trueF)) {
            t
        } else {
            val r = alltd(rule {
                case init@InitDeclaratorI(decl@AtomicNamedDeclarator(a, i: Id, b), attr, inits) =>
                    if (i.name != "main") {
                        addIdUsages(i, ft)
                        replaceId.put(i, ft)
                        if (!idMap.contains(ft)) {
                            idMap += (ft -> idMap.size)
                        }
                        InitDeclaratorI(AtomicNamedDeclarator(a, Id("_" + getFromIdMap(ft) + "_" + i.name), b), attr, inits)
                    } else {
                        init
                    }
                case init@InitDeclaratorI(nnd@NestedNamedDeclarator(l, decl@AtomicNamedDeclarator(a, i: Id, b), r), attr, inits) =>
                    if (i.name != "main") {
                        addIdUsages(i, ft)
                        replaceId.put(i, ft)
                        if (!idMap.contains(ft)) {
                            idMap += (ft -> idMap.size)
                        }
                        InitDeclaratorI(NestedNamedDeclarator(l, AtomicNamedDeclarator(a, Id("_" + getFromIdMap(ft) + "_" + i.name), b), r), attr, inits)
                    } else {
                        init
                    }
                /*case i: Id =>
                  if (i.name != "main") {
                    if (defuse.containsKey(i)) {
                      if (i.name.equals("security_context_t")) {
                          val test = 0
                      }
                      val idUsages = defuse.get(i)
                      idUsages.foreach(x => {
                        if (idsToBeReplaced.containsKey(x)) {
                          idsToBeReplaced.put(x, ft :: idsToBeReplaced.get(x))
                        } else {
                          idsToBeReplaced.put(x, List(ft))
                        }
                      })
                    }
                    replaceId.put(i, ft)
                    if (!IdMap.contains(ft)) {
                      IdMap += (ft -> IdMap.size)
                    }
                    Id("_" + IdMap.get(ft).get + "_" + i.name)
                  } else {
                    i
                  }*/

            })
            r(t) match {
                case None => t
                case k => k.get.asInstanceOf[T]
            }
        }
    }

    def convertId[T <: Product](t: T, ft: FeatureExpr): T = {
        val r = oncetd(rule {
            case init@InitDeclaratorI(decl@AtomicNamedDeclarator(a, i: Id, b), attr, inits) =>
                if (i.name != "main") {
                    addIdUsages(i, ft)
                    replaceId.put(i, ft)
                    if (!idMap.contains(ft)) {
                        idMap += (ft -> idMap.size)
                    }
                    InitDeclaratorI(AtomicNamedDeclarator(a, Id("_" + getFromIdMap(ft) + "_" + i.name), b), attr, inits)
                } else {
                    init
                }
            case init@InitDeclaratorI(nnd@NestedNamedDeclarator(l, decl@AtomicNamedDeclarator(a, i: Id, b), r), attr, inits) =>
                if (i.name != "main") {
                    addIdUsages(i, ft)
                    replaceId.put(i, ft)
                    if (!idMap.contains(ft)) {
                        idMap += (ft -> idMap.size)
                    }
                    InitDeclaratorI(NestedNamedDeclarator(l, AtomicNamedDeclarator(a, Id("_" + getFromIdMap(ft) + "_" + i.name), b), r), attr, inits)
                } else {
                    init
                }
            /*case i: Id =>
              if (i.name != "main") {
                if (defuse.containsKey(i)) {
                  if (i.name.equals("security_context_t")) {
                      val test = 0
                  }
                  val idUsages = defuse.get(i)
                  idUsages.foreach(x => {
                    if (idsToBeReplaced.containsKey(x)) {
                      idsToBeReplaced.put(x, ft :: idsToBeReplaced.get(x))
                    } else {
                      idsToBeReplaced.put(x, List(ft))
                    }
                  })
                }
                replaceId.put(i, ft)
                if (!IdMap.contains(ft)) {
                  IdMap += (ft -> IdMap.size)
                }
                Id("_" + IdMap.get(ft).get + "_" + i.name)
              } else {
                i
              }*/

        })
        r(t) match {
            case None => t
            case k => k.get.asInstanceOf[T]
        }
    }

    def convertStructId[T <: Product](t: T, ft: FeatureExpr): T = {
        val r = oncetd(rule {
            case decl@AtomicNamedDeclarator(a, i: Id, b) =>
                if (i.name != "main") {
                    addIdUsages(i, ft)
                    replaceId.put(i, ft)
                    if (!idMap.contains(ft)) {
                        idMap += (ft -> idMap.size)
                    }
                    AtomicNamedDeclarator(a, Id("_" + getFromIdMap(ft) + "_" + i.name), b)
                } else {
                    decl
                }
        })
        r(t) match {
            case None => t
            case k =>
                if (ft.equals(trueF)) {
                    t
                } else {
                    k.get.asInstanceOf[T]
                }
        }
    }

    def convertEnumId(enu: Enumerator, ft: FeatureExpr): Enumerator = {
        addIdUsages(enu.id, ft)
        if (!idMap.contains(ft)) {
            idMap += (ft -> idMap.size)
        }
        Enumerator(Id("_" + getFromIdMap(ft) + "_" + enu.id.name), enu.assignment)
    }

    def convertAllIds[T <: Product](t: T, ft: FeatureExpr): T = {
        val r = manytd(rule {
            case i: Id =>
                // TODO auf Funktionen beschränken
                if (i.name != "main") {
                    addIdUsages(i, ft)
                    replaceId.put(i, ft)
                    Id("_" + getFromIdMap(ft) + "_" + i.name)
                } else {
                    i
                }

        })
        r(t) match {
            case None =>
                t
            case _ =>
                r(t).get.asInstanceOf[T]
        }
    }

    /*
    Filters given Elements Opt Lists by Opt nodes where given feature implies Opt.feature and replaces these by True.
     */
    def filterOptsByFeature[T <: Product](t: T, feat: FeatureExpr): T = {
        val r = manytd(rule {
            case l: List[Opt[_]] =>
                l.flatMap(o => {
                    if (feat.mex(o.feature).isTautology()) {
                        List()
                    } else if (feat.equivalentTo(o.feature) || feat.implies(o.feature).isTautology()) {
                        List(Opt(trueF, o.entry))
                    } else {
                        List()
                    }
                })
        })
        r(t) match {
            case None => t
            case k => k.get.asInstanceOf[T]
        }
    }

    /*
    Replaces given Elements Opt Lists Opt nodes which are the same as given feature by True.
    */
    def replaceFeature[T <: Product](t: T, feat: FeatureExpr): T = {
        val r = manytd(rule {
            case l: List[Opt[_]] =>
                l.flatMap(o =>
                    if (feat.mex(o.feature).isTautology()) {
                        List()
                    } else if (o.feature.equivalentTo(feat) || feat.implies(o.feature).isTautology()) {
                        List(Opt(trueF, o.entry))
                    } else {
                        List(o)
                    })
        })
        r(t) match {
            case None => t
            case k => k.get.asInstanceOf[T]
        }
    }

    /*
    Replaces given FeatureExpression recursively from given Element by True. Also removes Opt nodes which should not occur
    in this given context. Also renames Ids if they have a declaration annotated by given FeatureExpression.
    */
    def replaceOptAndId[T <: Product](t: T, feat: FeatureExpr): T = {
        val r = manytd(rule {
            case l: List[Opt[_]] =>
                l.flatMap(o =>
                    if (feat.mex(o.feature).isTautology()) {
                        List()
                    } else if (o.feature.equivalentTo(feat) || feat.implies(o.feature).isTautology) {
                        List(Opt(trueF, o.entry))
                    } else {
                        // TODO: To list(o) or not
                        List(o)
                    })
            case i: Id =>
                if (idsToBeReplaced.containsKey(i)) {
                    // Increase number of expanded statements
                    if (!idMap.contains(feat)) {
                        idMap += (feat -> idMap.size)
                    }
                    val matchingId = idsToBeReplaced.get(i).find(x => feat.implies(x).isTautology())
                    matchingId match {
                        case None =>
                            // TODO: this should not happen?
                            val lst = idsToBeReplaced.get(i)
                            Id("_" + getFromIdMap(feat) + "_" + i.name)
                            i
                        case Some(x: FeatureExpr) =>
                            if (x.equals(trueF)) {
                                i
                            } else {
                                Id("_" + getFromIdMap(x) + "_" + i.name)
                            }
                        case k =>
                            Id("")
                    }
                } else {
                    i
                }
        })
        if (feat.equals(trueF)) {
            t
        } else {
            t match {
                case o@Opt(ft, entry) =>
                    if (ft.equals(trueF)) {
                        r(o) match {
                            case None => t
                            case _ => r(o).get.asInstanceOf[T]
                        }
                    } else if (ft.equals(feat)) {
                        val newOpt = Opt(trueF, entry)
                        r(newOpt) match {
                            case None => newOpt.asInstanceOf[T]
                            case _ => r(newOpt).get.asInstanceOf[T]
                        }
                    } else {
                        r(o) match {
                            case None => t
                            case _ => r(o).get.asInstanceOf[T]
                        }
                    }
                case _ =>
                    r(t) match {
                        case None => t
                        case k =>
                            k.get.asInstanceOf[T]
                    }
            }
        }
    }

    def replaceIdTest[T <: Product](t: T, feat: FeatureExpr): T = {
        val r = alltd(rule {
            case s: Statement =>
                s
            case i: Id =>
                if (idsToBeReplaced.containsKey(i)) {
                    // Increase number of expanded statements
                    if (!idMap.contains(feat)) {
                        idMap += (feat -> idMap.size)
                    }
                    val matchingId = idsToBeReplaced.get(i).find(x => feat.implies(x).isTautology())
                    matchingId match {
                        case None =>
                            // TODO: this should not happen?
                            val lst = idsToBeReplaced.get(i)
                            val test = lst.filter(x => feat.implies(x).isTautology())
                            Id("_" + getFromIdMap(feat) + "_" + i.name)
                            i
                        case Some(x: FeatureExpr) =>
                            Id("_" + getFromIdMap(x) + "_" + i.name)
                        case k =>
                            Id("")
                    }
                } else {
                    i
                }
        })

        r(t) match {
            case None => t
            case k => k.get.asInstanceOf[T]
        }
    }

    def replaceTrueByFeature[T <: Product](t: T, feat: FeatureExpr): T = {
        val r = manytd(rule {
            case l: List[Opt[_]] =>
                l.flatMap(o =>
                    if (feat.&(o.feature).isContradiction()) {
                        List()
                    } else if (o.feature.equivalentTo(feat) || feat.implies(o.feature).isTautology || o.feature.equivalentTo(trueF)) {
                        List(o.copy(feature = feat))
                    } else {
                        List(o)
                    })
        })
        r(t) match {
            case None => t
            case k => k.get.asInstanceOf[T]
        }
    }

    def ifdeftoif(ast: AST, decluse: IdentityHashMap[Id, List[Id]], usedecl: IdentityHashMap[Id, List[Id]], featureModel: FeatureModel = FeatureExprLib.featureModelFactory.empty, outputStem: String = "unnamed", lexAndParseTime: Long = 0, writeStatistics: Boolean = true, newPath: String = ""): (Option[AST], Long, List[TypeChefError]) = {
        new File(path).mkdirs()
        val tb = java.lang.management.ManagementFactory.getThreadMXBean

        //val prepareSt = tb.getCurrentThreadCpuTime()
        val source_ast = prepareAST(ast)
        //println("Prepare time: " + ((tb.getCurrentThreadCpuTime() - prepareSt) / nstoms).toString())

        // Sets the feature model to the busybox feature model in case we're not testing files from the frontend
        if (featureModel.equals(FeatureExprLib.featureModelFactory.empty) && isBusyBox && (new File("../TypeChef-BusyboxAnalysis/busybox/featureModel")).exists()) {
            fm = FeatureExprLib.featureModelFactory.create(new FeatureExprParser(FeatureExprLib.l).parseFile("../TypeChef-BusyboxAnalysis/busybox/featureModel"))
        } else {
            fm = featureModel
        }
        fillIdMap(source_ast)
        defuse = decluse
        usedef = usedecl
        val fileName = outputStemToFileName(outputStem)

        val time = tb.getCurrentThreadCpuTime()
        val new_ast = transformRecursive(source_ast)
        val featureStruct = definedExternalToAst(filterFeatures(source_ast))
        val result_ast = TranslationUnit(featureStruct.defs ++ new_ast.asInstanceOf[TranslationUnit].defs)
        val transformTime = (tb.getCurrentThreadCpuTime() - time) / nstoms

        var ifdeftoif_file = ""
        if (newPath.equals("")) {
            ifdeftoif_file = outputStem + "_ifdeftoif.c"
        } else {
            ifdeftoif_file = newPath
        }
        PrettyPrinter.printF(result_ast, ifdeftoif_file)

        lazy val typeCheckSuccessful = getTypeSystem(result_ast).checkASTSilent

        val featureMap = idMap.-(trueF).map(x => x._1.toTextExpr + "," + x._2) mkString "\n"
        writeToFile(path ++ "featureMap.csv", featureMap)

        if (writeStatistics) {
            if (!(new File(path ++ "statistics.csv").exists)) {
                writeToFile(path ++ "statistics.csv", getCSVHeader)
            }

            val csvEntry = createCsvEntry(source_ast, new_ast, fileName, lexAndParseTime, transformTime)
            appendToFile(path ++ "statistics.csv", csvEntry)
        }

        if (typeCheckSuccessful) {
            if (writeStatistics) {
                if (!(new File(path ++ "statistics.csv").exists)) {
                    writeToFile(path ++ "statistics.csv", getCSVHeader)
                }

                val csvEntry = createCsvEntry(source_ast, new_ast, fileName, lexAndParseTime, transformTime)
                appendToFile(path ++ "statistics.csv", csvEntry)
            }
            (Some(result_ast), transformTime, List())
        } else {
            val result_ast_with_position = getAstFromFile(new File(ifdeftoif_file))
            if (result_ast_with_position == null) {
                val errorHeader = "-+ ParseErrors in " + fileName + " +-\n"
                if (!(new File(path ++ "type_errors.txt").exists)) {
                    writeToFile(path ++ "type_errors.txt", errorHeader + "\n\n")
                } else {
                    appendToFile(path ++ "type_errors.txt", errorHeader + "\n\n")
                }
                (None, 0, List())
            } else {
                val errors = getTypeSystem(result_ast_with_position).getASTerrors()
                val errorHeader = "-+ TypeErrors in " + fileName + " +-\n"
                val errorString = errors mkString "\n"
                if (!(new File(path ++ "type_errors.txt").exists)) {
                    writeToFile(path ++ "type_errors.txt", errorHeader + errorString + "\n\n")
                } else {
                    appendToFile(path ++ "type_errors.txt", errorHeader + errorString + "\n\n")
                }
                (None, 0, errors)
            }
        }
    }

    def outputStemToFileName(outputStem: String): String = {
        val lastSepIndex = outputStem.lastIndexOf(System.getProperty("file.separator"))
        if (lastSepIndex == -1) {
            outputStem
        } else {
            outputStem.substring(lastSepIndex + 1)
        }
    }

    /*
    Makes #ifdef to if transformation on given AST element. Returns new AST element and a statistics String.
     */
    def transformAst[T <: Product](t: T, decluse: IdentityHashMap[Id, List[Id]], usedecl: IdentityHashMap[Id, List[Id]], featureModel: FeatureModel = FeatureExprLib.featureModelFactory.empty): (T, String) = {
        if (featureModel.equals(FeatureExprLib.featureModelFactory.empty) && isBusyBox) {
            fm = FeatureExprLib.featureModelFactory.create(new FeatureExprParser(FeatureExprLib.l).parseFile("C:/Users/Flo/Dropbox/HiWi/busybox/TypeChef-BusyboxAnalysis/busybox/featureModel"))
        } else {
            fm = featureModel
        }
        fillIdMap(t)
        defuse = decluse
        usedef = usedecl
        val result = transformRecursive(t)
        val features = filterFeatures(t)
        val csvNumbers = createCsvString()
        resetValues()
        if (writeOptionsIntoFile) {
            (TranslationUnit(definedExternalToAst(features).defs ++ result.asInstanceOf[TranslationUnit].defs).asInstanceOf[T], csvNumbers)
        } else {
            (result, csvNumbers)
        }
    }

    var noOfStmts = 0
    var noOfOptStmts = 0
    var noOfFuncts = 0
    var noOfOptFuncts = 0
    var noOfDecls = 0
    var noOfOptDecls = 0

    def generateStatistics[T <: Product](t: T, ft: FeatureExpr = trueF) {
        val r = alltd(query {
            case o@Opt(feat, entry) =>
                if (feat.equivalentTo(trueF) || feat.equivalentTo(ft)) {
                    /* A node without new context */
                    entry match {
                        case declStmt@DeclarationStatement(decl: Declaration) => noOfDecls = noOfDecls + 1
                        case decl: Declaration => noOfDecls = noOfDecls + 1
                        case e: Enumerator => noOfDecls = noOfDecls + 1
                        case sd: StructDeclaration => noOfDecls = noOfDecls + 1
                        case fd: FunctionDef => noOfFuncts = noOfFuncts + 1
                        case nfd: NestedFunctionDef => noOfFuncts = noOfFuncts + 1
                        case cs: CompoundStatement =>
                        case s: Statement => noOfStmts = noOfStmts + 1
                    }
                } else {
                    /* A new optional node */

                }
        })
    }

    /*
    Transforms given AST element.
     */
    def transformRecursive[T <: Product](t: T, currentContext: FeatureExpr = trueF): T = {
        val r = alltd(rule {
            case l: List[Opt[_]] =>
                l.flatMap(x => {
                    x match {
                        case o@Opt(ft: FeatureExpr, entry) =>
                            /*
                           Handle opt nodes which occur under a certain condition
                            */
                            if (ft != trueF) {
                                entry match {
                                    case declStmt@DeclarationStatement(decl: Declaration) =>
                                        handleDeclarations(Opt(ft, decl), currentContext).map(x => Opt(trueF, DeclarationStatement(x.entry)))
                                    case decl: Declaration =>
                                        handleDeclarations(o.asInstanceOf[Opt[Declaration]], currentContext)

                                    case i@Initializer(elem, expr) =>
                                        val features = computeNextRelevantFeatures(i, o.feature)
                                        if (!features.isEmpty) {
                                            features.map(x => transformRecursive(replaceOptAndId(Opt(trueF, Initializer(elem, convertAllIds(expr, x))), x), x))
                                        } else {
                                            List(replaceOptAndId(Opt(trueF, Initializer(elem, convertAllIds(expr, o.feature))), o.feature))
                                        }
                                    case e: Enumerator =>
                                        noOfOptionalDeclarations = noOfOptionalDeclarations + 1
                                        noOfDeclarations = noOfDeclarations + 1
                                        noOfEnumerators = noOfEnumerators + 1
                                        noOfEnumeratorsVariable = noOfEnumeratorsVariable + 1
                                        val features = computeNextRelevantFeatures(e, o.feature)
                                        if (!features.isEmpty) {
                                            features.map(x => Opt(trueF, transformRecursive(convertEnumId(replaceOptAndId(e, x), x), x)))
                                        } else {
                                            List(Opt(trueF, transformRecursive(convertEnumId(replaceOptAndId(e, o.feature), o.feature), o.feature)))
                                        }
                                    case sd@StructDeclaration(qual, decl) =>
                                        noOfStructDeclarations = noOfStructDeclarations + 1
                                        noOfStructDeclarationsRenamed = noOfStructDeclarationsRenamed + 1
                                        val features = computeNextRelevantFeatures(sd, o.feature)
                                        if (!features.isEmpty) {
                                            features.map(x => transformRecursive(replaceOptAndId(Opt(trueF, StructDeclaration(qual, convertStructId(decl, x))), x), x))
                                        } else {
                                            List(replaceOptAndId(Opt(trueF, StructDeclaration(qual, convertStructId(decl, o.feature))), o.feature))
                                        }

                                    case fd: FunctionDef =>
                                        noOfFunctions = noOfFunctions + 1
                                        handleFunctions(o)
                                    case nfd: NestedFunctionDef =>
                                        noOfFunctions = noOfFunctions + 1
                                        handleFunctions(o)


                                    case i@IfStatement(_, _, _, _) =>
                                        noOfStatements = noOfStatements + 1
                                        handleIfStatements(o, ft)
                                    case r: ReturnStatement =>
                                        noOfStatements = noOfStatements + 1
                                        noOfStatementsVariable = noOfStatementsVariable + 1
                                        val features = computeNextRelevantFeatures(r, ft)
                                        if (!features.isEmpty) {
                                            val result = features.map(x => Opt(trueF, statementToIf(replaceOptAndId(r, x), ft)))
                                            result
                                        } else {
                                            List(Opt(trueF, statementToIf(replaceOptAndId(r, ft), ft)))
                                        }
                                    case w: WhileStatement =>
                                        noOfStatements = noOfStatements + 1
                                        noOfStatementsVariable = noOfStatementsVariable + 1
                                        handleStatements(o, currentContext)
                                    case s: SwitchStatement =>
                                        noOfStatements = noOfStatements + 1
                                        noOfStatementsVariable = noOfStatementsVariable + 1
                                        handleStatements(o, currentContext)
                                    case d: DoStatement =>
                                        noOfStatements = noOfStatements + 1
                                        noOfStatementsVariable = noOfStatementsVariable + 1
                                        handleStatements(o, currentContext)
                                    case g: GotoStatement =>
                                        noOfStatements = noOfStatements + 1
                                        noOfStatementsVariable = noOfStatementsVariable + 1
                                        val features = computeNextRelevantFeatures(g, ft)
                                        if (!features.isEmpty) {
                                            val result = features.map(x => Opt(trueF, statementToIf(replaceOptAndId(g, x), ft)))
                                            result
                                        } else {
                                            List(Opt(trueF, statementToIf(replaceOptAndId(g, ft), ft)))
                                        }
                                    case f: ForStatement =>
                                        noOfStatements = noOfStatements + 1
                                        noOfStatementsVariable = noOfStatementsVariable + 1
                                        handleForStatements(o.asInstanceOf[Opt[Statement]])
                                    case elif@ElifStatement(One(expr: Expr), thenBranch) =>
                                        // TODO: should not happen?
                                        noOfStatements = noOfStatements + 1
                                        noOfStatementsVariable = noOfStatementsVariable + 1
                                        //val features = computeNextRelevantFeatures
                                        List(Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(ft), List(Opt(trueF, NArySubExpr("&&", replaceOptAndId(expr, ft)))))), transformRecursive(replaceOptAndId(thenBranch, ft), ft))))
                                    case e: ExprStatement =>
                                        noOfStatements = noOfStatements + 1
                                        noOfStatementsVariable = noOfStatementsVariable + 1
                                        val realFeature = currentContext.and(o.feature)
                                        val features = computeNextRelevantFeatures(e, realFeature)
                                        if (!features.isEmpty) {
                                            features.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x.and(realFeature))), One(CompoundStatement(List(Opt(trueF, replaceOptAndId(e, x.and(realFeature)))))), List(), None)))
                                        } else {
                                            List(Opt(trueF, IfStatement(One(featureToCExpr(realFeature)), One(CompoundStatement(List(Opt(trueF, replaceOptAndId(e, realFeature))))), List(), None)))
                                        }
                                    case label: LabelStatement =>
                                        noOfStatements = noOfStatements + 1
                                        noOfStatementsVariable = noOfStatementsVariable + 1
                                        val features = computeNextRelevantFeatures(label, ft)
                                        if (!features.isEmpty) {
                                            val result = features.map(x => Opt(trueF, statementToIf(replaceOptAndId(label, x), ft)))
                                            result
                                        } else {
                                            List(Opt(trueF, statementToIf(replaceOptAndId(label, ft), ft)))
                                        }
                                    case typeless: TypelessDeclaration =>
                                        // TODO: Umwandlung
                                        List(o)

                                    case p: Pragma =>
                                        // TODO: Eventuell variabel lassen
                                        List(o.copy(feature = trueF))
                                    case s: Specifier =>
                                        List(o.copy(feature = trueF))
                                    case s: String =>
                                        List(o.copy(feature = trueF))
                                    case es: EmptyStatement =>
                                        List()
                                    case ee: EmptyExternalDef =>
                                        List()
                                    case cs: CompoundStatement =>
                                        List(Opt(trueF, IfStatement(One(featureToCExpr(o.feature)), One(transformRecursive(replaceFeatureByTrue(cs, o.feature))), List(), None)))
                                    case k =>
                                        // println("Missing Opt: " + o + "\nFrom: " + k.asInstanceOf[AST].getPositionFrom + "\n")
                                        List(o)
                                }
                            } else {

                                /*
                               Handle opt nodes which occur under condition true
                                */
                                entry match {
                                    case declStmt@DeclarationStatement(decl: Declaration) =>
                                        handleDeclarations(Opt(ft, decl), currentContext).map(x => Opt(trueF, DeclarationStatement(x.entry)))
                                    case d@Declaration(declSpecs, init) =>
                                        handleDeclarations(o.asInstanceOf[Opt[Declaration]], currentContext)

                                    case e@Enumerator(id, any) =>
                                        noOfDeclarations = noOfDeclarations + 1
                                        noOfEnumerators = noOfEnumerators + 1
                                        val features = computeNextRelevantFeatures(e, currentContext)
                                        if (!features.isEmpty) {
                                            features.map(x => Opt(trueF, transformRecursive(convertEnumId(replaceOptAndId(e, x), x), x)))
                                        } else {
                                            List(transformRecursive(o, currentContext))
                                        }
                                    case sd@StructDeclaration(qual, decl) =>
                                        noOfDeclarations = noOfDeclarations + 1
                                        noOfStructDeclarations = noOfStructDeclarations + 1
                                        val features = computeNextRelevantFeatures(sd, o.feature)
                                        if (!features.isEmpty) {
                                            features.map(x => transformRecursive(replaceOptAndId(Opt(trueF, StructDeclaration(qual, convertStructId(decl, x))), x), x))
                                        } else {
                                            List(transformRecursive(o, currentContext))
                                        }

                                    case fd: FunctionDef =>
                                        noOfFunctions = noOfFunctions + 1
                                        handleFunctions(o)
                                    case nfd: NestedFunctionDef =>
                                        noOfFunctions = noOfFunctions + 1
                                        handleFunctions(o)


                                    case cmpStmt: CompoundStatement =>
                                        List(Opt(trueF, transformRecursive(cmpStmt, currentContext)))
                                    case f: ForStatement =>
                                        noOfStatements = noOfStatements + 1
                                        handleForStatements(o.asInstanceOf[Opt[Statement]], currentContext)
                                    case d: DoStatement =>
                                        noOfStatements = noOfStatements + 1
                                        handleStatements(o, currentContext)
                                    case r: ReturnStatement =>
                                        noOfStatements = noOfStatements + 1
                                        val features = computeNextRelevantFeatures(r, currentContext)
                                        if (!features.isEmpty) {
                                            val result = features.map(x => Opt(trueF, statementToIf(replaceOptAndId(r, x), x)))
                                            result
                                        } else {
                                            if (currentContext.equivalentTo(trueF)) {
                                                List(o)
                                            } else {
                                                List(Opt(trueF, replaceOptAndId(r, currentContext)))
                                            }
                                        }
                                    case g: GotoStatement =>
                                        noOfStatements = noOfStatements + 1
                                        val features = computeNextRelevantFeatures(g, currentContext)
                                        if (!features.isEmpty) {
                                            val result = features.map(x => Opt(trueF, statementToIf(replaceOptAndId(g, x), x)))
                                            result
                                        } else {
                                            if (currentContext.equivalentTo(trueF)) {
                                                List(o)
                                            } else {
                                                List(Opt(trueF, replaceOptAndId(g, currentContext)))
                                            }
                                        }
                                    case l: LabelStatement =>
                                        noOfStatements = noOfStatements + 1
                                        val features = computeNextRelevantFeatures(l, currentContext)
                                        if (!features.isEmpty) {
                                            val result = features.map(x => Opt(trueF, statementToIf(replaceOptAndId(l, x), x)))
                                            result
                                        } else {
                                            if (currentContext.equivalentTo(trueF)) {
                                                List(o)
                                            } else {
                                                List(Opt(trueF, replaceOptAndId(l, currentContext)))
                                            }
                                        }
                                    case e: ExprStatement =>
                                        noOfStatements = noOfStatements + 1
                                        val features = computeNextRelevantFeatures(e, currentContext)
                                        if (!features.isEmpty) {
                                            features.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, replaceOptAndId(e, x.and(o.feature)))))), List(), None)))
                                        } else {
                                            if (currentContext.equivalentTo(trueF)) {
                                                List(o)
                                            } else {
                                                List(Opt(trueF, ExprStatement(replaceOptAndId(e.expr, currentContext))))
                                            }
                                        }
                                    case w@WhileStatement(expr: Expr, s: Conditional[_]) =>
                                        noOfStatements = noOfStatements + 1
                                        val result = handleStatements(o, currentContext)
                                        result
                                    case ss: SwitchStatement =>
                                        noOfStatements = noOfStatements + 1
                                        handleStatements(o, currentContext)
                                    case i@IfStatement(_, _, _, _) =>
                                        noOfStatements = noOfStatements + 1
                                        handleIfStatements(o, currentContext)
                                    case elif@ElifStatement(One(cond), thenBranch) =>
                                        noOfStatements = noOfStatements + 1
                                        val feat = computeNextRelevantFeatures(cond)
                                        if (!feat.isEmpty) {
                                            noOfStatementDuplications = noOfStatementDuplications - 1 + feat.size
                                            feat.map(x => transformRecursive(replaceOptAndId(Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(x), List(Opt(trueF, NArySubExpr("&&", cond))))), thenBranch)), x), currentContext))
                                        } else {
                                            List(transformRecursive(o, currentContext))
                                        }
                                    case elif@ElifStatement(c@Choice(ft, thenBranch, elseBranch), thenStmt) =>
                                        noOfStatements = noOfStatements + 1
                                        val choices = conditionalToTuple(c, currentContext).map(x => (x._1.and(currentContext), x._2)).filterNot(x => x._1.equivalentTo(FeatureExprFactory.False))
                                        if (!choices.isEmpty) {
                                            noOfStatementDuplications = noOfStatementDuplications - 1 + choices.size
                                        }
                                        choices.map(x => {
                                            if (containsIdUsage(thenBranch)) {
                                                transformRecursive(replaceFeature(Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(x._1), List(Opt(trueF, NArySubExpr("&&", convertIdUsagesFromDefuse(x._2, x._1)))))), thenStmt)), x._1), currentContext)
                                            } else {
                                                transformRecursive(replaceFeature(Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(x._1), List(Opt(trueF, NArySubExpr("&&", x._2))))), thenStmt)), x._1), currentContext)
                                            }
                                        })

                                    case td: TypelessDeclaration =>
                                        List(o)
                                    case k: Product => List(transformRecursive(o, currentContext))
                                    case _ => List(o)
                                }
                            }
                        case k => List(transformRecursive(k))
                    }
                })
        })
        r(t) match {
            case None => t
            case k => k.get.asInstanceOf[T]
        }
    }

    def nextLevelContainsVariability(t: Any): Boolean = {
        val optList = getNextOptList(t)
        val result = optList.exists(x => (x.feature != trueF))
        result
    }

    def secondNextLevelContainsVariability(t: Any): Boolean = {
        val optList = getNextOptList(t)
        var result = false

        // TODO florian: isEmpty check is not necessary
        if (!optList.isEmpty) {
            val finalOptList = optList.flatMap(x => getNextOptList(x))
            result = finalOptList.exists(x => (x.feature != trueF))
        }
        result
    }

    def containsDeclaration(a: Any): Boolean = {
        !filterASTElems[Declaration](a).isEmpty
    }

    def containsIdUsage(a: Any): Boolean = {
        val ids = filterASTElems[Id](a)
        ids.foreach(x => if (idsToBeReplaced.containsKey(x)) return true)
        false
    }

    def getIdUsageFeatureList(a: Any): List[List[FeatureExpr]] = {
        val ids = filterASTElems[Id](a)
        val features = ids.filter(x => idsToBeReplaced.containsKey(x)).map(x => idsToBeReplaced.get(x).toList)
        features.distinct
    }

    def computeIdUsageFeatures(a: Any, currentContext: FeatureExpr = trueF): List[FeatureExpr] = {
        if (currentContext.equivalentTo(trueF)) {
            val res = getIdUsageFeatureList(a, currentContext).foldLeft(List(trueF))((first, second) => first.flatMap(x => second.diff(first).map(y => y.and(x))))
            res
        } else {
            val res = getIdUsageFeatureList(a, currentContext).foldLeft(List(trueF))((first, second) => first.flatMap(x => second.diff(first).map(y => y.and(x)))).flatMap(x => if (currentContext.implies(x).isTautology()) List(x) else List())
            res
        }
    }

    def getNextOptList(a: Any): List[Opt[_]] = {
        a match {
            case d: Opt[_] => List(d)
            case l: List[_] => l.flatMap(getNextOptList(_))
            case p: Product => p.productIterator.toList.flatMap(getNextOptList(_))
            case _ => List()
        }
    }

    def getSecondNextOptList(a: Any): List[Opt[_]] = {
        val optList = getNextOptList(a)
        if (!optList.isEmpty) {
            optList.flatMap(x => getNextOptList(x))
        } else {
            List()
        }
    }

    def fixTypeChefsFeatureExpressions(feature: FeatureExpr, context: FeatureExpr): FeatureExpr = {
        if (feature.implies(context).isTautology()) {
            feature
        } else {
            feature.and(context)
        }
    }

    /**
     * Removes dead opt nodes (I don't know if this is still a problem) which can never be evaluated to true.
     * Fixes feature expressions so that each opt element has its current total feature expression as feature.
     * Replaces Conditional[Statements] inside e.g. IfStatements with CompoundStatements, so that we can actually
     * perform StatementDuplications.
     */
    def prepareAST[T <: Product](t: T, currentContext: FeatureExpr = trueF): T = {
        val r = alltd(rule {
            case l: List[Opt[_]] =>
                l.flatMap(x => x match {
                    case o@Opt(ft: FeatureExpr, entry) =>
                        if (ft.mex(currentContext).isTautology()) {
                            List()
                        } else if (ft.implies(currentContext).isTautology()) {
                            List(prepareAST(o, ft))
                        } else {
                            List(prepareAST(Opt(ft.and(currentContext), entry), ft.and(currentContext)))
                        }
                })
            case o@One(st: Statement) =>
                st match {
                    case cs: CompoundStatement =>
                        One(prepareAST(st, currentContext))
                    case k =>
                        One(CompoundStatement(List(Opt(trueF, prepareAST(k, currentContext)))))
                }
        })
        r(t) match {
            case None =>
                t
            case k =>
                k.get.asInstanceOf[T]
        }
    }

    /**
     * Computes the cartesian product of a list of lists of FeatureExpressions using the boolean 'and' operator.
     * List( List(a, b), List(c, d, e)) becomes List(a&c, a&d, a&e, b&c, b&d, b&e).
     * @param listOfLists
     * @return
     */
    def computeCarthesianProduct(listOfLists: List[List[FeatureExpr]]): List[FeatureExpr] = {
        if (listOfLists.isEmpty) {
            List()
        } else if (listOfLists.size == 1) {
            listOfLists.head
        } else {
            listOfLists.tail.foldLeft(listOfLists.head)((first, second) => {
                if (!first.isEmpty && !second.isEmpty) {
                    val result = first.flatMap(x => second.map(y => y.and(x))).filterNot(x => x.equivalentTo(FeatureExprFactory.False) || !x.isSatisfiable(fm))
                    result
                } else if (second.isEmpty && !first.isEmpty) {
                    first
                } else if (first.isEmpty && !second.isEmpty) {
                    second
                } else {
                    List()
                }
            })
        }
    }

    /**
     * Returns a list of FeatureExpressions for the given AST Element a. This list contains features under which a
     * has to be duplicated. Example: condition inside an IfStatement has a variable Identifier -> we have to create
     * two different IfStatements and the function returns these two distinct features.
     * @param a
     * @param currentContext
     * @return
     */
    def computeNextRelevantFeatures(a: Any, currentContext: FeatureExpr = trueF): List[FeatureExpr] = {
        def computationHelper(a: Any, currentContext: FeatureExpr = trueF, expectAtLeastOneResult: Boolean = false): List[FeatureExpr] = {
            val featureList = getNextVariableFeaturesCondition(a, currentContext).filterNot(x => x.equivalentTo(currentContext)) ++ List(FeatureExprFactory.False)
            val identFeatureList = getNextFeaturesForVariableIdentifiers(a, currentContext)
            if (featureList.size == 1 && identFeatureList.isEmpty) {
                if (expectAtLeastOneResult) {
                    List(trueF)
                } else {
                    List()
                }
            } else {
                val featureBuffer: ListBuffer[List[FeatureExpr]] = ListBuffer()
                val currentFeatures: mutable.HashSet[FeatureExpr] = new mutable.HashSet
                featureList.foldLeft(List(): List[FeatureExpr])((first, second) => {
                    // Reached end of list
                    if (second.equivalentTo(FeatureExprFactory.False)) {
                        if (!first.isEmpty) {
                            if (!currentFeatures.contains(first.head)) {
                                /*first.foreach(x => x.collectDistinctFeatureObjects.foreach(y => currentFeatures.add(y)))*/
                                currentFeatures.add(first.head)
                                currentFeatures.add(first.head.or(currentContext.not()).not())
                                featureBuffer += List(first.head, first.head.or(currentContext.not()).not())
                            }
                        }
                        List()
                    } else if (first.isEmpty) {
                        second :: first
                    } else {
                        var result = true

                        // Change var result to reflect if all collected features mutually exclude each other
                        first.foldLeft(second)((a, b) => {
                            if (b.equivalentTo(FeatureExprFactory.False)) {
                                b
                            } else if (a.mex(b).isTautology()) {
                                b
                            } else {
                                result = false
                                b
                            }
                        })
                        val orResult = first.foldLeft(second)((a, b) => a.or(b))
                        if (result && currentContext.implies(orResult).isTautology()) {
                            // All collected features are mutually exclusive and the context implies the or result of all of them
                            featureBuffer += (second :: first)
                            List()
                        } else if (result) {
                            // Continue collecting mutually exclusive expressions
                            second :: first
                        } else {
                            if (!currentFeatures.contains(first.head)) {
                                currentFeatures.add(first.head)
                                currentFeatures.add(first.head.or(currentContext.not()).not())
                                featureBuffer += List(first.head, first.head.or(currentContext.not()).not())
                                /*first.foreach(x => x.collectDistinctFeatureObjects.foreach(y => currentFeatures.add(y)))*/
                            }

                            if (second.equivalentTo(FeatureExprFactory.False)) {
                                if (!currentFeatures.contains(second)) {
                                    currentFeatures += second
                                    currentFeatures += second.or(currentContext.not()).not()
                                    featureBuffer += List(second, second.or(currentContext.not()).not())
                                    /*second.collectDistinctFeatureObjects.foreach(x => currentFeatures.add(x))*/
                                }
                            }
                            List(second)
                        }
                    }
                })

                currentFeatures.clear()
                if (featureBuffer.isEmpty) {
                    if (!identFeatureList.isEmpty) {
                        identFeatureList
                    } else {
                        List()
                    }
                } else if (featureBuffer.size == 1) {
                    val result = featureBuffer.toList.head
                    result
                } else {
                    val featureBufferList = featureBuffer.toList
                    // Workaround for exponential explosion
                    val result = featureBufferList.tail.foldLeft(featureBufferList.head)((first, second) => {
                        if (!first.isEmpty) {
                            first.flatMap(x => second.map(y => y.and(x))).filterNot(x => x.equivalentTo(FeatureExprFactory.False) || !x.isSatisfiable(fm))
                        } else {
                            List()
                        }
                    }).distinct
                    /*if (result.size > 100) {
                      val test = result.filterNot(x => !x.isSatisfiable(fm))
                    }*/
                    if (result.size > numberOfVariantThreshold) {
                        List()
                    } else {
                        result
                    }
                }
            }
        }
        a match {
            case cs: CompoundStatement =>
                List()
            case ws: WhileStatement =>
                computationHelper(ws.expr, currentContext)
            case fs: ForStatement =>
                val features1 = computationHelper(fs.expr1, currentContext, true)
                var features2 = computationHelper(fs.expr2, currentContext, true).diff(features1)
                if (features2.isEmpty) {
                    features2 = List(trueF)
                }
                var features3 = computationHelper(fs.expr3, currentContext, true).diff(features2).diff(features1)
                if (features3.isEmpty) {
                    features3 = List(trueF)
                }
                val result = features1.flatMap(x => features2.map(y => y.and(x))).flatMap(x => features3.map(y => y.and(x)))
                result
            case is@IfStatement(One(statement), thenBranch, elif, els) =>
                computationHelper(statement, currentContext)
            case is@IfStatement(c: Choice[Product], thenBranch, elif, els) =>
                val choices = conditionalToTuple(c, currentContext)
                choices.flatMap(x => computationHelper(x._2, x._1)).distinct
            case ss: SwitchStatement =>
                computationHelper(ss.expr, currentContext)
            case es: ExprStatement =>
                computationHelper(es.expr, currentContext)
            case ds: DoStatement =>
                computationHelper(ds.expr, currentContext)
            case rs@ReturnStatement(Some(x)) =>
                computationHelper(x, currentContext)
            case gs: GotoStatement =>
                computationHelper(gs.target, currentContext)
            case fd: FunctionDef =>
                val features1 = computationHelper(fd.specifiers, currentContext, true)
                var features2 = computationHelper(fd.declarator, currentContext, true).diff(features1)
                if (features2.isEmpty) {
                    features2 = List(trueF)
                }
                var features3 = computationHelper(fd.oldStyleParameters, currentContext, true).diff(features2).diff(features1)
                if (features3.isEmpty) {
                    features3 = List(trueF)
                }
                val result = features1.flatMap(x => features2.map(y => y.and(x))).flatMap(x => features3.map(y => y.and(x)))
                result.filterNot(x => x.equivalentTo(trueF))
            case d@Declaration(declSpecs, init) =>
                val features1 = computationHelper(declSpecs, currentContext, true)
                val features2 = computationHelper(init, currentContext, true).diff(features1)
                val result = computeCarthesianProduct(List(features1, features2)).filterNot(x => x.equals(trueF))
                result
            case nfd: NestedFunctionDef =>
                val features1 = computationHelper(nfd.specifiers, currentContext, true)
                var features2 = computationHelper(nfd.declarator, currentContext, true).diff(features1)
                if (features2.isEmpty) {
                    features2 = List(trueF)
                }
                var features3 = computationHelper(nfd.parameters, currentContext, true).diff(features2).diff(features1)
                if (features3.isEmpty) {
                    features3 = List(trueF)
                }
                val result = features1.flatMap(x => features2.map(y => y.and(x))).flatMap(x => features3.map(y => y.and(x)))
                result.filterNot(x => x.equivalentTo(trueF))
            case k =>
                computationHelper(k, currentContext)
        }
    }

    /**
     * Retrieves a list of feature expressions which represent the different variants according to the feature
     * expressions that are found in the given AST element a. This also checks subelements of a unless they are new
     * statements like for example an ExpressionStatement inside an IfStatement.
     * @param a
     * @param currentContext
     * @return
     */
    def getNextVariableFeaturesCondition(a: Any, currentContext: FeatureExpr = trueF): List[FeatureExpr] = {
        def getNextFeatureHelp(a: Any, currentContext: FeatureExpr = trueF): List[FeatureExpr] = {
            a match {
                case d@Opt(ft, entry: NArySubExpr) =>
                    if (ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) entry.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext)) else List(fixTypeChefsFeatureExpressions(ft, currentContext)) ++ entry.productIterator.toList.flatMap(getNextFeatureHelp(_, fixTypeChefsFeatureExpressions(ft, currentContext)))
                case d@Opt(ft, entry: Expr) =>
                    if (ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) entry.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext)) else List(fixTypeChefsFeatureExpressions(ft, currentContext)) ++ entry.productIterator.toList.flatMap(getNextFeatureHelp(_, fixTypeChefsFeatureExpressions(ft, currentContext)))
                case d@Opt(ft, entry: DeclParameterDeclList) =>
                    if (ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) entry.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext)) else List(fixTypeChefsFeatureExpressions(ft, currentContext)) ++ entry.productIterator.toList.flatMap(getNextFeatureHelp(_, fixTypeChefsFeatureExpressions(ft, currentContext)))
                case d@Opt(ft, entry: ParameterDeclarationD) =>
                    if (ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) entry.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext)) else List(fixTypeChefsFeatureExpressions(ft, currentContext)) ++ entry.productIterator.toList.flatMap(getNextFeatureHelp(_, fixTypeChefsFeatureExpressions(ft, currentContext)))
                case d@Opt(ft, entry: InitDeclaratorI) =>
                    (if (!ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) List(fixTypeChefsFeatureExpressions(ft, currentContext)) else List()) ++ entry.declarator.productIterator.toList.flatMap(getNextFeatureHelp(_, fixTypeChefsFeatureExpressions(ft, currentContext))) ++ entry.attributes.productIterator.toList.flatMap(getNextFeatureHelp(_, fixTypeChefsFeatureExpressions(ft, currentContext)))
                case d@Opt(ft, entry) =>
                    if (!ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) List(fixTypeChefsFeatureExpressions(ft, currentContext)) else List()
                case l: List[_] =>
                    l.flatMap(getNextFeatureHelp(_, currentContext))
                case p: Product =>
                    p.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext))
                case _ =>
                    List()
            }
        }
        /*case i: Id =>
      if (idsToBeReplaced.containsKey(i)) {
        val tmp = idsToBeReplaced.get(i) //.filter(x => )
        idsToBeReplaced.get(i)
      } else {
        List()
      }*/
        val result = getNextFeatureHelp(a, currentContext).distinct
        result
    }

    /**
     * Retrieves a list of feature expressions which represent the different variants according to the feature
     * expressions that are found for identifiers with multiple declarations. This also checks subelements of a unless
     * they are new statements like for example an ExpressionStatement inside an IfStatement.
     * @param a
     * @param currentContext
     * @return
     */
    def getNextFeaturesForVariableIdentifiers(a: Any, currentContext: FeatureExpr = trueF): List[FeatureExpr] = {
        def getNextFeatureHelp(a: Any): List[Id] = {
            a match {
                case l: List[_] =>
                    l.flatMap(getNextFeatureHelp(_))
                case i: Id =>
                    if (idsToBeReplaced.containsKey(i)) {
                        List(i)
                    } else {
                        List()
                    }
                case d@Opt(ft, i: Id) =>
                    if (idsToBeReplaced.containsKey(i)) {
                        List(i)
                    } else {
                        List()
                    }
                case d@Opt(ft, entry: StructOrUnionSpecifier) =>
                    entry.productIterator.toList.flatMap(getNextFeatureHelp(_))
                case d@Opt(ft, entry: NArySubExpr) =>
                    entry.productIterator.toList.flatMap(getNextFeatureHelp(_))
                case d@Opt(ft, entry: Expr) =>
                    entry.productIterator.toList.flatMap(getNextFeatureHelp(_))
                case d@Opt(ft, entry: ParameterDeclarationD) =>
                    entry.productIterator.toList.flatMap(getNextFeatureHelp(_))
                case d@Opt(ft, entry: TypeDefTypeSpecifier) =>
                    entry.productIterator.toList.flatMap(getNextFeatureHelp(_))
                case d@Opt(ft, entry: DeclParameterDeclList) =>
                    entry.productIterator.toList.flatMap(getNextFeatureHelp(_))
                case d@Opt(ft, entry: InitDeclaratorI) =>
                    entry.productIterator.toList.flatMap(getNextFeatureHelp(_))
                case d@Opt(ft, entry: AtomicNamedDeclarator) =>
                    entry.productIterator.toList.flatMap(getNextFeatureHelp(_))
                case d@Opt(ft, entry: StructDeclarator) =>
                    entry.productIterator.toList.flatMap(getNextFeatureHelp(_))
                case d@Opt(ft, entry) =>
                    List()
                case p: Product =>
                    p.productIterator.toList.flatMap(getNextFeatureHelp(_))
                case _ =>
                    List()
            }
        }
        val ids = getNextFeatureHelp(a)
        val listOfLists = ids.map(x => idsToBeReplaced.get(x).toList.map(y => y.and(currentContext)))
        computeCarthesianProduct(listOfLists).filter(z => z.isSatisfiable(fm) && !z.equals(trueF))
    }

    /**
     * New implementation of the lift opt function. This method looks at all Opt(True, entry) nodes and checks if the
     * next lower level of opt nodes is variable. This node is then copied for the different feature combinations of
     * his next level of opt nodes.
     */
    def liftOpts[T <: Product](t: T): T = {
        val r = manytd(rule {
            case l: List[Opt[_]] =>
                l.flatMap(x => x match {
                    case o@Opt(ft: FeatureExpr, entry) =>
                        if (ft == trueF && nextLevelContainsVariability(entry)) {
                            val nextLevel = getNextOptList(entry)
                            val features = nextLevel.flatMap(x => if (x.feature != trueF) List(x.feature) else List()).toSet
                            var needTrueExpression = false
                            features.foreach(x => if (!features.exists(y => x.&(y).isContradiction())) {
                                needTrueExpression = true
                            })
                            val result = features.map(x => replaceTrueByFeature(o, x).copy(feature = x)).toList
                            if (needTrueExpression) {
                                replaceTrueByFeature(o, trueF) :: result
                            } else {
                                result
                            }
                        } else {
                            List(o)
                        }
                })
        })
        val newAst = r(t).get.asInstanceOf[T]
        newAst
    }

    def convertIdUsagesFromDefuse[T <: Product](t: T, feat: FeatureExpr): T = {
        val r = manytd(rule {
            case i: Id =>
                if (idsToBeReplaced.containsKey(i)) {
                    // Increase number of expanded statements
                    if (!idMap.contains(feat)) {
                        idMap += (feat -> idMap.size)
                    }
                    val test = idsToBeReplaced.get(i).find(x => feat.implies(x).isTautology())
                    test match {
                        case None =>
                            // TODO: this should not happen?
                            Id("_" + getFromIdMap(feat) + "_" + i.name)
                        case Some(x: FeatureExpr) => Id("_" + getFromIdMap(x) + "_" + i.name)
                        case _ => Id("")
                    }
                } else {
                    i
                }
        })
        r(t) match {
            case None => t
            case k => k.get.asInstanceOf[T]
        }
    }

    def exprStatementToIf(e: ExprStatement, ft: FeatureExpr): IfStatement = {
        IfStatement(One(featureToCExpr(ft)), One(CompoundStatement(List(Opt(trueF, replaceOptAndId(replaceFeature(e, ft), ft))))), List(), None)
    }

    def statementToIf(e: Statement, ft: FeatureExpr): IfStatement = {
        IfStatement(One(featureToCExpr(ft)), One(CompoundStatement(List(Opt(trueF, replaceOptAndId(replaceFeature(e, ft), ft))))), List(), None)
    }

    def optStatementToIf(o: Opt[Statement]): Opt[IfStatement] = {
        Opt(trueF, IfStatement(One(featureToCExpr(o.feature)), One(CompoundStatement(List(Opt(trueF, replaceOptAndId(replaceFeature(o.entry, o.feature), o.feature))))), List(), None))
    }

    def choiceToIf(c: Choice[Statement]): One[Statement] = {
        def conditionalToStatement(c: Conditional[Statement], ft: FeatureExpr = FeatureExprFactory.False): List[(Statement, FeatureExpr)] = {
            c match {
                case One(null) => List()
                case Choice(choiceFeature, first: Conditional[_], second: Conditional[_]) =>
                    conditionalToStatement(first, choiceFeature) ++ conditionalToStatement(second, choiceFeature.not())
                case One(value) =>
                    List((value, ft))
            }
        }
        One(CompoundStatement(conditionalToStatement(c).map(x => Opt(trueF, statementToIf(x._1, x._2)))))

        /*c match {
          case Choice(ft, One(first: Statement), One(second: Statement)) =>
            One(CompoundStatement(List(Opt(trueF, statementToIf(first, ft)), Opt(trueF, statementToIf(second, ft.not())))))
          case _ =>
            println("ChoiceToIf not exhaustive: " + c)
            null
        }*/
    }

    def convertThenBody(optIf: Opt[_]): Opt[_] = {
        optIf.entry match {
            case i@IfStatement(a, One(statement), b, c) =>
                statement match {
                    case cs: CompoundStatement =>
                        optIf
                    case k =>
                        Opt(optIf.feature, IfStatement(a, One(CompoundStatement(List(Opt(trueF, statement)))), b, c))
                }
            case f@ForStatement(expr1, expr2, expr3, One(statement)) =>
                statement match {
                    case cs: CompoundStatement =>
                        optIf
                    case k =>
                        Opt(optIf.feature, ForStatement(expr1, expr2, expr3, One(CompoundStatement(List(Opt(trueF, statement))))))
                }
            case w@WhileStatement(expr, One(statement)) =>
                statement match {
                    case cs: CompoundStatement =>
                        optIf
                    case k =>
                        Opt(optIf.feature, WhileStatement(expr, One(CompoundStatement(List(Opt(trueF, statement))))))
                }
            case k =>
                optIf
        }
    }

    def convertStatementToCompound(stmt: Statement): CompoundStatement = {
        stmt match {
            case cs: CompoundStatement =>
                cs
            case k =>
                CompoundStatement(List(Opt(trueF, stmt)))
        }
    }

    def handleStatements(opt: Opt[_], currentContext: FeatureExpr = trueF): List[Opt[_]] = {
        opt.entry match {
            case i: IfStatement =>
                handleIfStatements(opt, currentContext)
            case f: ForStatement =>
                handleForStatements(opt.asInstanceOf[Opt[Statement]], currentContext)
            case w: WhileStatement =>
                handleWSDStatements(opt.asInstanceOf[Opt[Statement]], currentContext)
            case d: DoStatement =>
                handleWSDStatements(opt.asInstanceOf[Opt[Statement]], currentContext)
            case s: SwitchStatement =>
                handleWSDStatements(opt.asInstanceOf[Opt[Statement]], currentContext)

            case k =>
                List()
        }
    }

    /**
     * Handles IfStatements in different steps:
     * 1. Transform optional IfStatements
     * 2. Transform conditionals in the if-condition and thenBranch
     * 3. Transform usual if-statement (possible variable ID definition in the condition!) recursive call for thenBranch
     * 4. Transform ElifStatements
     *
     */
    def handleIfStatements(optIf: Opt[_], currentContext: FeatureExpr = trueF): List[Opt[_]] = {
        // 1. Step
        if (!optIf.feature.equals(trueF)) {
            optIf.entry match {
                case IfStatement(cond, thenBranch, elifs, elseBranch) =>
                    List(Opt(trueF, IfStatement(One(featureToCExpr(optIf.feature)), One(CompoundStatement(handleIfStatements(replaceOptAndId(optIf, optIf.feature), optIf.feature).asInstanceOf[List[Opt[Statement]]])), List(), None)))
                case _ =>
                    List()
            }
        } else {
            optIf.entry match {

                // 3. Step
                case i@IfStatement(One(expr), One(stmt), elif, els) =>
                    val features = computeNextRelevantFeatures(expr, currentContext)
                    if (features.isEmpty) {
                        List(Opt(trueF, IfStatement(One(replaceOptAndId(expr, currentContext)), One(transformRecursive(stmt, currentContext)), elif.flatMap(x => handleIfStatements(replaceOptAndId(x, currentContext), currentContext)).asInstanceOf[List[Opt[ElifStatement]]], transformRecursive(replaceOptAndId(els, currentContext), currentContext))))
                    } else {
                        features.flatMap(x => List(Opt(trueF, (IfStatement(One(NAryExpr(featureToCExpr(x), List(Opt(trueF, NArySubExpr("&&", replaceOptAndId(expr, x)))))), transformRecursive(replaceOptAndId(One(convertStatementToCompound(stmt)), x), x), elif.flatMap(y => handleIfStatements(replaceOptAndId(y, x), x)).asInstanceOf[List[Opt[ElifStatement]]], transformRecursive(replaceOptAndId(els, x), x))))))
                    }

                // 2. Step
                case i@IfStatement(c: Conditional[Expr], thenBranch: Conditional[Statement], elif, els) =>
                    val conditionalTuple = conditionalToTuple(c, currentContext)
                    val statementTuple = conditionalToTuple(thenBranch, currentContext)
                    var elseTuple = List((FeatureExprFactory.True, None.asInstanceOf[Option[Conditional[Statement]]]))
                    els match {
                        case None =>
                        case Some(One(stmt)) =>
                        case Some(c: Choice[Statement]) =>
                            elseTuple = conditionalToTuple(c, currentContext).map(x => (x._1, Some(One(x._2))))
                    }
                    val first = conditionalTuple.map(x => x._1)
                    val second = statementTuple.map(x => x._1).diff(first)
                    val third = elseTuple.map(x => x._1).diff(second)
                    val totalScalar = computeCarthesianProduct(List(first, second, third))
                    totalScalar.flatMap(x => {
                        val cond = conditionalTuple.find(y => x.implies(y._1).isTautology()).get._2
                        val stmt = One(statementTuple.find(z => x.implies(z._1).isTautology()).get._2)
                        val elsBranch = elseTuple.find(e => x.implies(e._1).isTautology()).getOrElse((currentContext, None.asInstanceOf[Option[Conditional[Statement]]]))._2
                        handleIfStatements(Opt(trueF, IfStatement(One(NAryExpr(featureToCExpr(x), List(Opt(trueF, NArySubExpr("&&", replaceOptAndId(cond, x)))))), replaceOptAndId(stmt, x), replaceOptAndId(elif, x), replaceOptAndId(elsBranch, x))), x)
                    })

                // 4. Step
                case e@ElifStatement(c: Conditional[Expr], thenBranch) =>
                    val conditionalTuple = conditionalToTuple(c, currentContext)
                    if (conditionalTuple.size == 1 && conditionalTuple.head._1.equals(trueF)) {
                        List(optIf)
                    } else {
                        conditionalTuple.map(x => Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(x._1), List(Opt(trueF, NArySubExpr("&&", replaceOptAndId(x._2, x._1)))))), transformRecursive(replaceOptAndId(thenBranch, x._1), x._1))))
                    }
            }
        }
    }

    def handleForStatements(opt: Opt[Statement], currentContext: FeatureExpr = trueF): List[Opt[Statement]] = {

        // 1. Step
        if (!opt.feature.equals(trueF)) {
            opt.entry match {
                case ForStatement(expr1, expr2, expr3, cond) =>
                    List(Opt(trueF, IfStatement(One(featureToCExpr(opt.feature)), One(CompoundStatement(handleForStatements(replaceOptAndId(opt, opt.feature), opt.feature))), List(), None)))
                case _ =>
                    List()
            }
        } else {
            opt.entry match {

                // 2. Step
                case f@ForStatement(expr1, expr2, expr3, c: Choice[Statement]) =>
                    val conditionalTuple = conditionalToTuple(c, currentContext)
                    conditionalTuple.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x._1)), One(CompoundStatement(handleForStatements(Opt(trueF, ForStatement(expr1, expr2, expr3, One(x._2))), x._1))), List(), None)))

                // 3. Step
                case f@ForStatement(expr1, expr2, expr3, One(stmt: Statement)) =>
                    val features1 = computeNextRelevantFeatures(expr1.getOrElse(EmptyStatement()))
                    val features2 = computeNextRelevantFeatures(expr2.getOrElse(EmptyStatement()))
                    val features3 = computeNextRelevantFeatures(expr3.getOrElse(EmptyStatement()))
                    val features = computeCarthesianProduct(List(features1, features2.diff(features1), features3.diff(features2 ++ features1)))
                    if (features.isEmpty) {
                        List(Opt(trueF, ForStatement(replaceOptAndId(expr1, currentContext), replaceOptAndId(expr2, currentContext), replaceOptAndId(expr3, currentContext), One(transformRecursive(stmt)))))
                    } else {
                        features.map(x => Opt(trueF, (IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, ForStatement(replaceOptAndId(expr1, x), replaceOptAndId(expr2, x), replaceOptAndId(expr3, x), One(transformRecursive(stmt))))))), List(), None))))
                    }
            }
        }
    }

    def handleWSDStatements(opt: Opt[Statement], currentContext: FeatureExpr = trueF): List[Opt[Statement]] = {
        // 1. Step
        if (!opt.feature.equals(trueF)) {
            opt.entry match {
                case WhileStatement(expr, cond) =>
                    List(Opt(trueF, IfStatement(One(featureToCExpr(opt.feature)), One(CompoundStatement(handleWSDStatements(replaceOptAndId(opt, opt.feature), opt.feature))), List(), None)))
                case SwitchStatement(expr, cond) =>
                    List(Opt(trueF, IfStatement(One(featureToCExpr(opt.feature)), One(CompoundStatement(handleWSDStatements(replaceOptAndId(opt, opt.feature), opt.feature))), List(), None)))
                case DoStatement(expr, cond) =>
                    List(Opt(trueF, IfStatement(One(featureToCExpr(opt.feature)), One(CompoundStatement(handleWSDStatements(replaceOptAndId(opt, opt.feature), opt.feature))), List(), None)))
                case _ =>
                    List()
            }
        } else {
            opt.entry match {

                // 3. Step
                case w@WhileStatement(expr, One(stmt: Statement)) =>
                    val features = computeNextRelevantFeatures(expr)
                    if (features.isEmpty) {
                        List(Opt(trueF, WhileStatement(replaceOptAndId(expr, currentContext), One(transformRecursive(stmt)))))
                    } else {
                        features.map(x => Opt(trueF, (IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, WhileStatement(replaceOptAndId(expr, x), One(transformRecursive(stmt))))))), List(), None))))
                    }
                case s@SwitchStatement(expr, One(stmt: Statement)) =>
                    val features = computeNextRelevantFeatures(expr)
                    if (features.isEmpty) {
                        List(Opt(trueF, SwitchStatement(replaceOptAndId(expr, currentContext), One(transformRecursive(stmt)))))
                    } else {
                        features.map(x => Opt(trueF, (IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, SwitchStatement(replaceOptAndId(expr, x), One(transformRecursive(stmt))))))), List(), None))))
                    }
                case d@DoStatement(expr, One(stmt: Statement)) =>
                    val features = computeNextRelevantFeatures(expr)
                    if (features.isEmpty) {
                        List(Opt(trueF, DoStatement(replaceOptAndId(expr, currentContext), One(transformRecursive(stmt, currentContext)))))
                    } else {
                        features.map(x => Opt(trueF, (IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, DoStatement(replaceOptAndId(expr, x), One(transformRecursive(stmt))))))), List(), None))))
                    }

                // 2. Step
                case w@WhileStatement(expr, c: Conditional[Statement]) =>
                    val conditionalTuple = conditionalToTuple(c, currentContext)
                    conditionalTuple.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x._1)), One(CompoundStatement(handleWSDStatements(Opt(trueF, WhileStatement(expr, One(x._2))), x._1))), List(), None)))
                case s@SwitchStatement(expr, c: Conditional[Statement]) =>
                    val conditionalTuple = conditionalToTuple(c, currentContext)
                    conditionalTuple.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x._1)), One(CompoundStatement(handleWSDStatements(Opt(trueF, SwitchStatement(expr, One(x._2))), x._1))), List(), None)))
                case d@DoStatement(expr, c: Conditional[Statement]) =>
                    val conditionalTuple = conditionalToTuple(c, currentContext)
                    conditionalTuple.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x._1)), One(CompoundStatement(handleWSDStatements(Opt(trueF, DoStatement(expr, One(x._2))), x._1))), List(), None)))

                case k =>
                    logger.error("Missed statement transformation: " + k)
                    List()
            }
        }
    }

    /*
    def handleWhileStatements(opt: Opt[Statement], currentContext: FeatureExpr = trueF): List[Opt[Statement]] = {
        // 1. Step
        if (!opt.feature.equals(trueF)) {
            opt.entry match {
                case WhileStatement(expr, cond) =>
                    List(Opt(trueF, IfStatement(One(featureToCExpr(opt.feature)), One(CompoundStatement(handleWhileStatements(replaceOptAndId(opt, opt.feature), opt.feature))), List(), None)))
                case _ =>
                    List()
            }
        } else {
            opt.entry match {

                // 3. Step
                case w@WhileStatement(expr, One(stmt: Statement)) =>
                    val features = computeNextRelevantFeatures(expr)
                    if (features.isEmpty) {
                        List(Opt(trueF, WhileStatement(replaceOptAndId(expr, currentContext), One(transformRecursive(stmt)))))
                    } else {
                        features.map(x => Opt(trueF, (IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, WhileStatement(replaceOptAndId(expr, x), One(transformRecursive(stmt))))))), List(), None))))
                    }

                // 2. Step
                case w@WhileStatement(expr, c: Conditional[Statement]) =>
                    val conditionalTuple = conditionalToTuple(c, currentContext)
                    conditionalTuple.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x._1)), One(CompoundStatement(handleWhileStatements(Opt(trueF, WhileStatement(expr, One(x._2))), x._1))), List(), None)))
            }
        }
    }

    def handleSwitchStatements(opt: Opt[Statement], currentContext: FeatureExpr = trueF): List[Opt[Statement]] = {
        // 1. Step
        if (!opt.feature.equals(trueF)) {
            opt.entry match {
                case SwitchStatement(expr, cond) =>
                    List(Opt(trueF, IfStatement(One(featureToCExpr(opt.feature)), One(CompoundStatement(handleSwitchStatements(replaceOptAndId(opt, opt.feature), opt.feature))), List(), None)))
                case _ =>
                    List()
            }
        } else {
            opt.entry match {

                // 3. Step
                case s@SwitchStatement(expr, One(stmt: Statement)) =>
                    val features = computeNextRelevantFeatures(expr)
                    if (features.isEmpty) {
                        List(Opt(trueF, SwitchStatement(replaceOptAndId(expr, currentContext), One(transformRecursive(stmt)))))
                    } else {
                        features.map(x => Opt(trueF, (IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, SwitchStatement(replaceOptAndId(expr, x), One(transformRecursive(stmt))))))), List(), None))))
                    }

                // 2. Step
                case s@SwitchStatement(expr, c: Conditional[Statement]) =>
                    val conditionalTuple = conditionalToTuple(c, currentContext)
                    conditionalTuple.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x._1)), One(CompoundStatement(handleSwitchStatements(Opt(trueF, SwitchStatement(expr, One(x._2))), x._1))), List(), None)))
            }
        }
    }

    def handleDoStatements(opt: Opt[Statement], currentContext: FeatureExpr = trueF): List[Opt[Statement]] = {
        // 1. Step
        if (!opt.feature.equals(trueF)) {
            opt.entry match {
                case DoStatement(expr, cond) =>
                    List(Opt(trueF, IfStatement(One(featureToCExpr(opt.feature)), One(CompoundStatement(handleDoStatements(replaceOptAndId(opt, opt.feature), opt.feature))), List(), None)))
                case _ =>
                    List()
            }
        } else {
            opt.entry match {

                // 3. Step
                case d@DoStatement(expr, One(stmt: Statement)) =>
                    val features = computeNextRelevantFeatures(expr)
                    if (features.isEmpty) {
                        List(Opt(trueF, DoStatement(replaceOptAndId(expr, currentContext), One(transformRecursive(stmt)))))
                    } else {
                        features.map(x => Opt(trueF, (IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, DoStatement(replaceOptAndId(expr, x), One(transformRecursive(stmt))))))), List(), None))))
                    }

                // 2. Step
                case d@DoStatement(expr, c: Conditional[Statement]) =>
                    val conditionalTuple = conditionalToTuple(c, currentContext)
                    conditionalTuple.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x._1)), One(CompoundStatement(handleDoStatements(Opt(trueF, DoStatement(expr, One(x._2))), x._1))), List(), None)))
            }
        }
    }*/

    def handleIfStatements_old(optIf: Opt[_], currentFeature: FeatureExpr = trueF): List[Opt[_]] = {

        optIf.entry match {
            case i@IfStatement(c@Choice(ft, cThen, cEls), thenBranch, elif, els) =>
                val choices = conditionalToTuple(c, currentFeature).map(tuple => (tuple._1.and(currentFeature), tuple._2)).filterNot(x => x._1.equivalentTo(FeatureExprFactory.False))
                val result = choices.flatMap(x => handleIfStatements_old(replaceOptAndId(Opt(trueF, IfStatement(One(NAryExpr(featureToCExpr(x._1), List(Opt(trueF, NArySubExpr("&&", x._2))))), thenBranch, elif, els)), x._1), x._1))
                result
            //handleIfStatements_old(Opt(trueF, IfStatement(One(NAryExpr(featureToCExpr(choices.head._1), List(Opt(trueF, NArySubExpr("&&", choices.head._2))))), then, choices.tail.map(x => Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(x._1), List(Opt(trueF, NArySubExpr("&&", x._2.asInstanceOf[Expr]))))), then))) ++ elif, els)), currentContext)
            case i@IfStatement(One(cond), One(thenBranch: CompoundStatement), elif, els) =>
                val tst = computeNextRelevantFeatures(i, currentFeature)
                if (containsIdUsage(cond)) {
                    //val feat = computeNextRelevantFeatures(i)
                    val feat = computeIdUsageFeatures(cond).filterNot(x => x.equivalentTo(FeatureExprFactory.False))
                    if (!feat.isEmpty) {
                        noOfStatementDuplications = noOfStatementDuplications - 1 + feat.size
                    }
                    feat.flatMap(x => handleIfStatements_old(replaceFeature(Opt(optIf.feature, IfStatement(One(NAryExpr(featureToCExpr(x), List(Opt(trueF, NArySubExpr("&&", convertIdUsagesFromDefuse(cond, x)))))), One(thenBranch), elif, els)), x), x))
                } else {
                    if (optIf.feature.equivalentTo(trueF)) {
                        if (isVariable(cond)) {
                            noOfStatementsVariable = noOfStatementsVariable + 1
                            val feat = computeNextRelevantFeatures(i) // TODO: .filterNot(x => x.equals(FeatureExprFactory.False))
                            if (!feat.isEmpty) {
                                noOfStatementDuplications = noOfStatementDuplications - 1 + feat.size
                            }
                            feat.flatMap(x => handleIfStatements_old(filterOptsByFeature(Opt(optIf.feature, IfStatement(One(NAryExpr(featureToCExpr(x), List(Opt(trueF, NArySubExpr("&&", convertIdUsagesFromDefuse(cond, x)))))), One(thenBranch), elif, els)), x), x))
                        } else if (isVariable(elif)) {

                            /*
                           Case #1: Always occurring if statement with variability in elif statements
                            */
                            noOfStatementsVariable = noOfStatementsVariable + 1
                            List(optIf.copy(entry = i.copy(elifs = transformRecursive(elif, currentFeature), thenBranch = One(transformRecursive(thenBranch, currentFeature)))))
                        } else {

                            /*
                            Case #2: Always occurring if statement without further variability
                             */
                            //List(Opt(trueF, IfStatement(One(cond), One(transformRecursive(then, env, defuse)), transformRecursive(elif, env, defuse), els)))
                            List(transformRecursive(optIf, currentFeature))
                            //List(opt)
                        }
                    } else {
                        noOfStatementsVariable = noOfStatementsVariable + 1
                        handleIfStatements_old(replaceFeature(Opt(trueF, IfStatement(One(NAryExpr(featureToCExpr(optIf.feature), List(Opt(trueF, NArySubExpr("&&", cond))))), One(thenBranch), elif, els)), optIf.feature), optIf.feature)
                    }
                }
            case k =>
                List()
        }
    }

    def handleWhileStatements_old(opt: Opt[Statement], currentContext: FeatureExpr = trueF): List[Opt[Statement]] = {
        opt.entry match {
            case w@WhileStatement(expr, conditional) =>
                if (!opt.feature.equivalentTo(trueF)) {
                    noOfStatementsVariable = noOfStatementsVariable + 1
                    var realFeature = fixTypeChefsFeatureExpressions(opt.feature, currentContext)
                    List((Opt(trueF, IfStatement(One(featureToCExpr(realFeature)), One(CompoundStatement(handleWhileStatements_old(replaceOptAndId(replaceOptAndId(Opt(trueF, w), realFeature), currentContext), realFeature))), List(), None))))
                } else {
                    conditional match {
                        case One(statement) =>
                            val feat = computeNextRelevantFeatures(expr, currentContext)
                            if (!feat.isEmpty) {
                                val result = feat.map(x => {
                                    Opt(trueF, IfStatement(One(featureToCExpr(x)), One(CompoundStatement(handleWhileStatements_old(replaceOptAndId(Opt(trueF, WhileStatement(expr, conditional)), x), x))), List(), None))
                                })
                                if (!result.isEmpty) {
                                    noOfStatementDuplications = noOfStatementDuplications - 1 + result.size
                                }
                                result
                            } else {
                                List(transformRecursive(replaceOptAndId(opt, currentContext), currentContext)).asInstanceOf[List[Opt[Statement]]]
                            }
                        case c@Choice(ft, one, second) =>
                            val choices = conditionalToTuple(c, currentContext).filterNot(x => x._1.equivalentTo(FeatureExprFactory.False))
                            if (!choices.isEmpty) {
                                noOfStatementDuplications = noOfStatementDuplications - 1 + choices.size
                            }
                            List(Opt(trueF, IfStatement(One(featureToCExpr(choices.head._1)), One(CompoundStatement(handleWhileStatements_old(replaceOptAndId(Opt(trueF, WhileStatement(expr, One(choices.head._2))), choices.head._1), choices.head._1))), choices.tail.map(y => Opt(trueF, ElifStatement(One(featureToCExpr(y._1)), One(CompoundStatement(handleWhileStatements_old(replaceOptAndId(Opt(trueF, WhileStatement(expr, One(y._2))), y._1), y._1)))))), None)))
                    }
                }
            case k =>
                List()
        }
    }

    def handleDoStatements_old(opt: Opt[Statement], currentContext: FeatureExpr = trueF): List[Opt[Statement]] = {
        opt.entry match {
            case d@DoStatement(expr, conditional) =>
                if (!opt.feature.equivalentTo(trueF)) {
                    noOfStatementsVariable = noOfStatementsVariable + 1
                    List((Opt(trueF, IfStatement(One(featureToCExpr(opt.feature)), One(CompoundStatement(handleDoStatements_old(replaceFeature(Opt(trueF, d), opt.feature), opt.feature))), List(), None))))
                } else {
                    conditional match {
                        case One(statement) =>
                            if (containsIdUsage(expr)) {
                                val feat = computeIdUsageFeatures(expr)
                                val result = feat.map(x => {
                                    Opt(trueF, IfStatement(One(featureToCExpr(x)), One(CompoundStatement(handleDoStatements_old(Opt(trueF, WhileStatement(convertIdUsagesFromDefuse(expr, x), conditional)), x))), List(), None))
                                })
                                if (!result.isEmpty) {
                                    noOfStatementDuplications = noOfStatementDuplications - 1 + result.size
                                }
                                result
                            } else {
                                List(transformRecursive(opt, currentContext))
                            }
                        case c@Choice(ft, one, second) =>
                            val choices = conditionalToTuple(c, currentContext)
                            if (!choices.isEmpty) {
                                noOfStatementDuplications = noOfStatementDuplications - 1 + choices.size
                            }
                            List(Opt(trueF, IfStatement(One(featureToCExpr(choices.head._1)), One(CompoundStatement(handleDoStatements_old(Opt(trueF, WhileStatement(expr, One(choices.head._2))), choices.head._1))), choices.tail.map(y => Opt(trueF, ElifStatement(One(featureToCExpr(y._1)), One(CompoundStatement(handleDoStatements_old(Opt(trueF, WhileStatement(expr, One(y._2))), y._1)))))), None)))
                    }
                }
            case k =>
                List()
        }
    }

    def handleForStatements_old(opt: Opt[Statement], currentContext: FeatureExpr = trueF): List[Opt[Statement]] = {
        opt.entry match {
            case f@ForStatement(expr1, expr2, expr3, conditional) =>
                if (!opt.feature.equivalentTo(trueF)) {
                    noOfStatementsVariable = noOfStatementsVariable + 1
                    List((Opt(trueF, IfStatement(One(featureToCExpr(opt.feature)), One(CompoundStatement(handleForStatements_old(replaceFeature(Opt(trueF, f), opt.feature), opt.feature))), List(), None))))
                } else {
                    conditional match {
                        case One(statement) =>
                            // TODO: check expr2 and expr3
                            // val test = computeNextRelevantFeatures(f)
                            if (containsIdUsage(expr1) /*|| containsIdUsage(expr2) || containsIdUsage(expr3)*/ ) {
                                val feat = computeIdUsageFeatures(expr1)
                                val result = feat.map(x => {
                                    if (!currentContext.equivalentTo(trueF) && currentContext.implies(x).isTautology()) {
                                        transformRecursive(replaceOptAndId(opt, x))
                                    } else {
                                        Opt(trueF, IfStatement(One(featureToCExpr(x)), One(CompoundStatement(handleForStatements_old(Opt(trueF, ForStatement(convertIdUsagesFromDefuse(expr1, x), convertIdUsagesFromDefuse(expr2, x), convertIdUsagesFromDefuse(expr3, x), conditional)), x))), List(), None))
                                    }
                                })
                                if (!result.isEmpty) {
                                    noOfStatementDuplications = noOfStatementDuplications - 1 + result.size
                                }
                                result
                            } else {
                                List(transformRecursive(opt, currentContext))
                            }
                        case c@Choice(ft, one, second) =>
                            val choices = conditionalToTuple(c, currentContext)
                            if (!choices.isEmpty) {
                                noOfStatementDuplications = noOfStatementDuplications - 1 + choices.size
                            }
                            List(Opt(trueF, IfStatement(One(featureToCExpr(choices.head._1)), One(CompoundStatement(handleForStatements_old(Opt(trueF, ForStatement(expr1, expr2, expr3, One(choices.head._2))), choices.head._1))), choices.tail.map(y => Opt(trueF, ElifStatement(One(featureToCExpr(y._1)), One(CompoundStatement(handleForStatements_old(Opt(trueF, ForStatement(expr1, expr2, expr3, One(y._2))), y._1)))))), None)))
                    }
                }
            case k =>
                List()
        }
    }

    def handleDeclarations(optDeclaration: Opt[Declaration], currentContext: FeatureExpr = trueF): List[Opt[Declaration]] = {
        noOfDeclarations = noOfDeclarations + 1
        // TODO convert multiple IDs from variable_typedef a, b, c, d;
        if (optDeclaration.feature.equivalentTo(trueF)) {
            optDeclaration.entry match {
                case d@Declaration(declSpecs, init) =>
                    val features = computeNextRelevantFeatures(d).map(x => x.and(currentContext))
                    if (!features.isEmpty) {
                        val result = features.map(x => Opt(trueF, transformRecursive(replaceOptAndId(Declaration(declSpecs, convertIds(init, x)), x), x)))
                        noOfDeclarationDuplications = noOfDeclarationDuplications - 1 + features.size
                        result
                    } else {
                        List(transformRecursive(optDeclaration))
                    }
            }
        } else {
            optDeclaration.entry match {
                case d@Declaration(declSpecs, init) =>
                    noOfOptionalDeclarations = noOfOptionalDeclarations + 1
                    val feat = optDeclaration.feature
                    val newDeclSpecs = declSpecs.map(x => x match {
                        case o@Opt(ft, EnumSpecifier(Some(i: Id), k)) =>
                            if (defuse.containsKey(i)) {
                                addIdUsages(i, feat)
                                Opt(ft, EnumSpecifier(Some(Id("_" + getFromIdMap(feat) + "_" + i.name)), k))
                            } else {
                                o
                            }
                        case o@Opt(ft, StructOrUnionSpecifier(a, Some(i: Id), b)) =>
                            if (defuse.containsKey(i)) {
                                addIdUsages(i, feat)
                                Opt(ft, StructOrUnionSpecifier(a, Some(Id("_" + getFromIdMap(feat) + "_" + i.name)), b))
                            } else {
                                o
                            }

                        case k =>
                            k
                    })
                    val tmpDecl = filterOptsByFeature(Declaration(newDeclSpecs, init), feat)
                    val features = computeNextRelevantFeatures(tmpDecl, feat)
                    if (!features.isEmpty) {
                        val result = features.map(x => Opt(trueF, transformRecursive(replaceOptAndId(convertId(tmpDecl, x), x), x)))
                        noOfDeclarationDuplications = noOfDeclarationDuplications - 1 + features.size
                        result
                    } else {
                        val result = List(Opt(trueF, transformRecursive(replaceOptAndId(convertId(tmpDecl, feat), feat), feat)))
                        result
                    }
            }
        }
    }

    def handleDeclarations_new(optDeclaration: Opt[Declaration], currentContext: FeatureExpr = trueF): List[Opt[Declaration]] = {
        def convertSpecifiers(declSpecs: List[Opt[Specifier]], feat: FeatureExpr = trueF): List[Opt[Specifier]] = {
            if (!feat.equals(trueF)) {
                declSpecs.map(x => x match {
                    case o@Opt(ft, EnumSpecifier(Some(i: Id), k)) =>
                        if (defuse.containsKey(i)) {
                            addIdUsages(i, feat)
                            Opt(ft, EnumSpecifier(Some(Id("_" + getFromIdMap(feat) + "_" + i.name)), k))
                        } else {
                            o
                        }
                    case o@Opt(ft, StructOrUnionSpecifier(a, Some(i: Id), b)) =>
                        if (defuse.containsKey(i)) {
                            addIdUsages(i, feat)
                            Opt(ft, StructOrUnionSpecifier(a, Some(Id("_" + getFromIdMap(feat) + "_" + i.name)), b))
                        } else {
                            o
                        }

                    case k =>
                        k
                })
            } else {
                declSpecs
            }
        }

        noOfDeclarations = noOfDeclarations + 1

        var newOptDecl = optDeclaration
        var context = currentContext

        // 1. Step
        if (!optDeclaration.feature.equals(trueF)) {
            newOptDecl = replaceOptAndId(Opt(trueF, optDeclaration.entry), optDeclaration.feature)
            context = optDeclaration.feature
        } else {
            context = trueF
        }

        // 2. Step
        val features = computeNextRelevantFeatures(newOptDecl.entry, context)
        val specs = convertSpecifiers(newOptDecl.entry.declSpecs, context)
        val inits = newOptDecl.entry.init
        if (!features.isEmpty) {
            features.map(x => replaceOptAndId(Opt(trueF, transformRecursive(Declaration(convertSpecifiers(specs, x), convertIds(inits, x)), x)), x))
        } else {
            List(replaceOptAndId(Opt(trueF, transformRecursive(Declaration(convertSpecifiers(specs, context), convertIds(inits, context)), context)), context))
        }
    }

    def handleFunctions_old(optFunction: Opt[_]): List[Opt[_]] = {
        optFunction.entry match {
            case fd: FunctionDef =>
                if (optFunction.feature.equals(trueF)) {
                    val tst = computeNextRelevantFeatures(fd)
                    if (isVariable(fd.specifiers) || isVariable(fd.oldStyleParameters) || isVariable(fd.declarator)) {

                        /*
                        Case #1: Always occuring function with variability outside of the function body
                         */
                        val features = computeNextRelevantFeatures(fd)
                        if (isVariable(fd.specifiers)) {
                            // features = features ++ computeNextRelevantFeatures(fd.specifiers)
                            noOfFunctionDuplicationsSpecifiers = noOfFunctionDuplicationsSpecifiers + 1
                        }
                        if (isVariable(fd.declarator)) {
                            // features = features ++ computeNextRelevantFeatures(fd.declarator)
                            noOfFunctionDuplicationsDeclarators = noOfFunctionDuplicationsDeclarators + 1
                        }
                        if (isVariable(fd.oldStyleParameters)) {
                            // features = features ++ computeNextRelevantFeatures(fd.oldStyleParameters)
                            noOfFunctionDuplicationsParameters = noOfFunctionDuplicationsParameters + 1
                        }
                        // val features = computeNextRelevantFeatures(functionWithoutBody)
                        // val features = getFeatureCombinations(removeList(getNextFeatures(fd).flatMap(x => x.collectDistinctFeatures2).toList, optFunction.feature.collectDistinctFeatures2.toList))
                        val result = features.map(x => {
                            val tmpResult = filterOptsByFeature(convertStructId(replaceFeatureByTrue(optFunction, optFunction.feature), x.&(optFunction.feature)), x).asInstanceOf[Opt[FunctionDef]]
                            tmpResult.copy(entry = tmpResult.entry.copy(stmt = transformRecursive(tmpResult.entry.stmt)))
                            //transformRecursive(filterOptsByFeature(convertId(replaceFeatureByTrue(optFunction, optFunction.feature), x.&(optFunction.feature), defuse), x), env, defuse)
                        })
                        if (!result.isEmpty) {
                            noOfOptionalFunctions = noOfOptionalFunctions + 1
                            noOfFunctionDuplications = noOfFunctionDuplications + result.size - 1
                        }
                        result
                    } else {

                        /*
                        Case #2: Always occuring function without variability outside of the function body
                         */
                        List(transformRecursive(optFunction))
                    }
                } else {
                    val tempOpt = replaceOptAndId(optFunction, optFunction.feature).asInstanceOf[Opt[FunctionDef]]
                    //println(PrettyPrinter.print(replaceOptAndIdTest(optFunction, optFunction.feature).entry.asInstanceOf[FunctionDef]))
                    val functionWithoutBody = tempOpt.entry.copy(stmt = CompoundStatement(List()))
                    if (isVariable(tempOpt.entry.specifiers) || isVariable(tempOpt.entry.oldStyleParameters) || isVariable(tempOpt.entry.declarator)) {

                        /*
                        Case #3: Annotated function with variability outside of the function body
                         */
                        // var features: List[FeatureExpr] = List()
                        if (isVariable(tempOpt.entry.specifiers)) {
                            //features = features ++ computeNextRelevantFeatures(tempOpt.entry.specifiers)
                            noOfFunctionDuplicationsSpecifiers = noOfFunctionDuplicationsSpecifiers + 1
                        }
                        if (isVariable(tempOpt.entry.declarator)) {
                            //features = features ++ computeNextRelevantFeatures(tempOpt.entry.declarator)
                            noOfFunctionDuplicationsDeclarators = noOfFunctionDuplicationsDeclarators + 1
                        }
                        if (isVariable(tempOpt.entry.oldStyleParameters)) {
                            //features = features ++ computeNextRelevantFeatures(tempOpt.entry.oldStyleParameters)
                            noOfFunctionDuplicationsParameters = noOfFunctionDuplicationsParameters + 1
                        }
                        //val features = computeNextRelevantFeatures(functionWithoutBody)
                        val features = computeNextRelevantFeatures(fd, optFunction.feature).map(x => x.and(optFunction.feature))
                        // features = features.toSet.toList
                        val result = features.map(x => {
                            transformRecursive(replaceOptAndId(convertStructId(tempOpt, x), x), x)
                        })
                        if (!result.isEmpty) {
                            noOfOptionalFunctions = noOfOptionalFunctions + 1
                            noOfFunctionDuplications = noOfFunctionDuplications + result.size - 1
                        }
                        result
                    } else {

                        /*
                       Case #4: Annotated function without variability outside of the function body
                        */
                        noOfOptionalFunctions = noOfOptionalFunctions + 1
                        val tmpResult = convertStructId(tempOpt, optFunction.feature)
                        List(tmpResult.copy(entry = tmpResult.entry.copy(stmt = transformRecursive(tmpResult.entry.stmt, optFunction.feature))))
                    }
                }
            case nfd: NestedFunctionDef =>
                if (optFunction.feature.equals(trueF)) {
                    if (isVariable(nfd.specifiers) || isVariable(nfd.parameters) || isVariable(nfd.declarator)) {

                        /*
                        Case #1: Always occuring function with variability outside of the function body
                         */
                        val features = computeNextRelevantFeatures(nfd)
                        if (isVariable(nfd.specifiers)) {
                            // features = features ++ computeNextRelevantFeatures(fd.specifiers)
                            noOfFunctionDuplicationsSpecifiers = noOfFunctionDuplicationsSpecifiers + 1
                        }
                        if (isVariable(nfd.declarator)) {
                            // features = features ++ computeNextRelevantFeatures(fd.declarator)
                            noOfFunctionDuplicationsDeclarators = noOfFunctionDuplicationsDeclarators + 1
                        }
                        if (isVariable(nfd.parameters)) {
                            // features = features ++ computeNextRelevantFeatures(fd.oldStyleParameters)
                            noOfFunctionDuplicationsParameters = noOfFunctionDuplicationsParameters + 1
                        }
                        // val features = computeNextRelevantFeatures(functionWithoutBody)
                        // val features = getFeatureCombinations(removeList(getNextFeatures(fd).flatMap(x => x.collectDistinctFeatures2).toList, optFunction.feature.collectDistinctFeatures2.toList))
                        val result = features.map(x => {
                            val tmpResult = filterOptsByFeature(convertStructId(replaceFeatureByTrue(optFunction, optFunction.feature), x.&(optFunction.feature)), x).asInstanceOf[Opt[FunctionDef]]
                            tmpResult.copy(entry = tmpResult.entry.copy(stmt = transformRecursive(tmpResult.entry.stmt)))
                            //transformRecursive(filterOptsByFeature(convertId(replaceFeatureByTrue(optFunction, optFunction.feature), x.&(optFunction.feature), defuse), x), env, defuse)
                        })
                        if (!result.isEmpty) {
                            noOfOptionalFunctions = noOfOptionalFunctions + 1
                            noOfFunctionDuplications = noOfFunctionDuplications + result.size - 1
                        }
                        result
                    } else {

                        /*
                        Case #2: Always occuring function without variability outside of the function body
                         */
                        List(transformRecursive(optFunction))
                    }
                } else {
                    val tempOpt = replaceFeatureByTrue(optFunction, optFunction.feature).asInstanceOf[Opt[FunctionDef]]
                    val functionWithoutBody = tempOpt.entry.copy(stmt = CompoundStatement(List()))
                    if (isVariable(tempOpt.entry.specifiers) || isVariable(tempOpt.entry.oldStyleParameters) || isVariable(tempOpt.entry.declarator)) {

                        /*
                        Case #3: Annotated function with variability outside of the function body
                         */
                        // var features: List[FeatureExpr] = List()
                        if (isVariable(tempOpt.entry.specifiers)) {
                            //features = features ++ computeNextRelevantFeatures(tempOpt.entry.specifiers)
                            noOfFunctionDuplicationsSpecifiers = noOfFunctionDuplicationsSpecifiers + 1
                        }
                        if (isVariable(tempOpt.entry.declarator)) {
                            //features = features ++ computeNextRelevantFeatures(tempOpt.entry.declarator)
                            noOfFunctionDuplicationsDeclarators = noOfFunctionDuplicationsDeclarators + 1
                        }
                        if (isVariable(tempOpt.entry.oldStyleParameters)) {
                            //features = features ++ computeNextRelevantFeatures(tempOpt.entry.oldStyleParameters)
                            noOfFunctionDuplicationsParameters = noOfFunctionDuplicationsParameters + 1
                        }
                        //val features = computeNextRelevantFeatures(functionWithoutBody)
                        val features = computeNextRelevantFeatures(nfd, optFunction.feature).map(x => x.and(optFunction.feature))
                        // features = features.toSet.toList
                        val result = features.map(x => {
                            transformRecursive(filterOptsByFeature(convertStructId(tempOpt, x), x))
                        })
                        if (!result.isEmpty) {
                            noOfOptionalFunctions = noOfOptionalFunctions + 1
                            noOfFunctionDuplications = noOfFunctionDuplications + result.size - 1
                        }
                        result
                    } else {

                        /*
                       Case #4: Annotated function without variability outside of the function body
                        */
                        noOfOptionalFunctions = noOfOptionalFunctions + 1
                        val tmpResult = convertStructId(tempOpt, optFunction.feature)
                        List(tmpResult.copy(entry = tmpResult.entry.copy(stmt = transformRecursive(tmpResult.entry.stmt))))
                    }
                }
            case _ => List()
        }
    }

    def handleFunctions(optFunction: Opt[_], currentContext: FeatureExpr = trueF): List[Opt[_]] = {
        // 1. Step
        if (!optFunction.feature.equals(trueF)) {
            optFunction.entry match {
                case fd@FunctionDef(spec, decl, par, stmt) =>
                    handleFunctions(Opt(trueF, replaceOptAndId(fd, optFunction.feature)), optFunction.feature)
                case nfd@NestedFunctionDef(isAuto, spec, decl, par, stmt) =>
                    handleFunctions(Opt(trueF, replaceOptAndId(nfd, optFunction.feature)), optFunction.feature)
            }
        } else {
            // 2. Step
            optFunction.entry match {
                case fd@FunctionDef(spec, decl, par, stmt) =>
                    if (fd.getName.equals("wc_main")) {
                        print("")
                    }
                    val features = computeNextRelevantFeatures(fd, currentContext)
                    if (features.isEmpty) {
                        List(Opt(trueF, FunctionDef(replaceOptAndId(spec, currentContext), replaceOptAndId(convertStructId(decl, currentContext), currentContext), replaceOptAndId(par, currentContext), transformRecursive(replaceOptAndId(stmt, currentContext), currentContext))))
                    } else {
                        features.map(x => Opt(trueF, FunctionDef(replaceOptAndId(spec, x), replaceOptAndId(convertStructId(decl, x), x), replaceOptAndId(par, x), transformRecursive(replaceOptAndId(stmt, x), x))))
                    }
                case nfd@NestedFunctionDef(isAuto, spec, decl, par, stmt) =>
                    val features = computeNextRelevantFeatures(nfd, currentContext)
                    if (features.isEmpty) {
                        List(Opt(trueF, NestedFunctionDef(isAuto, replaceOptAndId(spec, currentContext), replaceOptAndId(convertStructId(decl, currentContext), currentContext), replaceOptAndId(par, currentContext), transformRecursive(replaceOptAndId(stmt, currentContext), currentContext))))
                    } else {
                        features.map(x => Opt(trueF, NestedFunctionDef(isAuto, replaceOptAndId(spec, x), replaceOptAndId(convertStructId(decl, x), x), replaceOptAndId(par, x), transformRecursive(replaceOptAndId(stmt, x), x))))
                    }
            }
        }
    }

    def countNumberOfASTElements(ast: AST): Long = {
        def countNumberOfASTElementsHelper(a: Any): Long = {
            a match {
                case l: List[_] => l.map(countNumberOfASTElementsHelper).sum
                case _: FeatureExpr => 0
                case p: Product => 1 + p.productIterator.toList.map(countNumberOfASTElementsHelper).sum
                case _ => 1
            }
        }
        countNumberOfASTElementsHelper(ast)
    }

    def countNumberOfElements[T <: AST](ast: AST)(implicit m: ClassTag[T]): Long = {
        def countNumberHelper(a: Any): Long = {
            a match {
                case l: List[_] => l.map(countNumberHelper).sum
                case _: FeatureExpr => 0
                case p: Product =>
                    if (m.runtimeClass.isInstance(p)) {
                        1 + p.productIterator.toList.map(countNumberHelper).sum
                    } else {
                        p.productIterator.toList.map(countNumberHelper).sum
                    }
                case _ =>
                    0
            }
        }
        countNumberHelper(ast)
    }

    def countNumberOfVariableElements[T <: AST](ast: AST)(implicit m: ClassTag[T]): Long = {
        def countNumberHelper(a: Any, currentContext: FeatureExpr = trueF): Long = {
            val i = 0
            a match {
                case l: List[_] => l.map(x => countNumberHelper(x, currentContext)).sum
                case _: FeatureExpr => 0
                case o@Opt(ft, entry: AST) =>
                    if ((ft.implies(currentContext).isTautology() && !ft.equivalentTo(currentContext)) && m.runtimeClass.isInstance(entry)) {
                        1 + entry.productIterator.toList.map(x => countNumberHelper(x, ft)).sum
                    } else {
                        entry.productIterator.toList.map(x => countNumberHelper(x, ft)).sum
                    }
                case p: Product =>
                    p.productIterator.toList.map(x => countNumberHelper(x, currentContext)).sum
                case _ =>
                    0
            }
        }
        countNumberHelper(ast)
    }

    def countNumberOfDeclarations(ast: AST): Long = {
        def countNumberHelper(a: Any): Long = {
            a match {
                case l: List[_] => l.map(countNumberHelper).sum
                case _: FeatureExpr => 0
                case p: Product =>
                    if (p.isInstanceOf[Declaration] || p.isInstanceOf[Enumerator] || p.isInstanceOf[StructDeclaration]) {
                        1 + p.productIterator.toList.map(countNumberHelper).sum
                    } else {
                        p.productIterator.toList.map(countNumberHelper).sum
                    }
                case _ =>
                    0
            }
        }
        countNumberHelper(ast)
    }

    def countNumberOfIfsAndElifs(ast: AST): Long = {
        def countNumberHelper(a: Any): Long = {
            a match {
                case l: List[_] => l.map(countNumberHelper).sum
                case _: FeatureExpr => 0
                case p: Product =>
                    if (p.isInstanceOf[IfStatement] || p.isInstanceOf[ElifStatement]) {
                        1 + p.productIterator.toList.map(countNumberHelper).sum
                    } else {
                        p.productIterator.toList.map(countNumberHelper).sum
                    }
                case _ =>
                    0
            }
        }
        countNumberHelper(ast)
    }

    def createCsvEntry(source_ast: AST, new_ast: AST, fileName: String, lexAndParseTime: Long, transformTime: Long): String = {
        val numberOfAstElements = countNumberOfASTElements(source_ast)
        val newNumberOfAstElements = countNumberOfASTElements(new_ast)
        val astGrowth = computeDifference(numberOfAstElements, newNumberOfAstElements)

        val numberOfDecls = countNumberOfDeclarations(source_ast)
        val numberOfVariableDecls = countNumberOfVariableDeclarations(source_ast)
        val numberOfFunctions = countNumberOfElements[FunctionDef](source_ast)
        val numberOfVariableFunctions = countNumberOfVariableElements[FunctionDef](source_ast)
        val numberOfIfsAndElifs = countNumberOfIfsAndElifs(source_ast)

        val newNumberOfDecls = countNumberOfDeclarations(new_ast)
        val newNumberOfFunctions = countNumberOfElements[FunctionDef](new_ast)
        val newNumberOfIfsAndElifs = countNumberOfIfsAndElifs(new_ast)

        val variableToTotalDecls = numberOfVariableDecls / numberOfDecls.toDouble
        val declarationGrowth = computeDifference(numberOfDecls, newNumberOfDecls)

        val variableToTotalFunctions = numberOfVariableFunctions / numberOfFunctions.toDouble
        val functionGrowth = computeDifference(numberOfFunctions, newNumberOfFunctions)

        val ifAndElifGrowth = computeDifference(numberOfIfsAndElifs, newNumberOfIfsAndElifs)

        createCommaSeparatedString(List(fileName, noOfFeatures, numberOfAstElements, newNumberOfAstElements, astGrowth, numberOfDecls, numberOfVariableDecls, variableToTotalDecls, newNumberOfDecls, declarationGrowth, numberOfFunctions, numberOfVariableFunctions, variableToTotalFunctions, newNumberOfFunctions, functionGrowth, numberOfIfsAndElifs, newNumberOfIfsAndElifs, ifAndElifGrowth, noOfRenamings, noOfRenamingUsages, lexAndParseTime, transformTime)) ++ "\n"
    }

    def countNumberOfVariableDeclarations(ast: AST): Long = {
        def countNumberHelper(a: Any, currentContext: FeatureExpr = trueF): Long = {
            val i = 0
            a match {
                case l: List[_] => l.map(x => countNumberHelper(x, currentContext)).sum
                case _: FeatureExpr => 0
                case o@Opt(ft, entry: AST) =>
                    if ((ft.implies(currentContext).isTautology() && !ft.equivalentTo(currentContext)) && (entry.isInstanceOf[Declaration] || entry.isInstanceOf[DeclarationStatement] || entry.isInstanceOf[Enumerator] || entry.isInstanceOf[StructDeclaration])) {
                        1 + entry.productIterator.toList.map(x => countNumberHelper(x, ft)).sum
                    } else {
                        entry.productIterator.toList.map(x => countNumberHelper(x, ft)).sum
                    }
                case p: Product =>
                    p.productIterator.toList.map(x => countNumberHelper(x, currentContext)).sum
                case _ =>
                    0
            }
        }
        countNumberHelper(ast)
    }

    def createCommaSeparatedString(input: List[Any]): String = {
        input.map(x => x.toString) mkString ","
    }

    def analyseDeclarations[T <: Product](t: T) = {
        val r = manytd(query {
            case o@Opt(entry, Declaration(declSpecs, init)) =>
                init.foreach(x => x match {
                    case Opt(ft, iDecl: InitDeclaratorI) =>
                        iDecl.declarator match {
                            case a: AtomicNamedDeclarator =>
                            case n: NestedNamedDeclarator =>
                            case k => println(k)
                        }
                    case k => val i = 0
                })
        })
        r(t)
    }

    def getFunctionFromConfiguration(@SuppressWarnings(Array("unchecked")) features: Set[SingleFeatureExpr], file: File, fm: FeatureModel): AST = {
        val correctFeatureModelIncompatibility = false
        var ignoredFeatures = 0
        var changedAssignment = 0
        var totalFeatures = 0
        var fileEx: FeatureExpr = FeatureExprFactory.True
        var trueFeatures: Set[SingleFeatureExpr] = Set()
        var falseFeatures: Set[SingleFeatureExpr] = Set()

        val enabledPattern: Pattern = java.util.regex.Pattern.compile("([^=]*)=y")
        val disabledPattern: Pattern = java.util.regex.Pattern.compile("([^=]*)=n")
        for (line <- Source.fromFile(file).getLines().filterNot(_.startsWith("#")).filterNot(_.isEmpty)) {
            totalFeatures += 1
            var matcher = enabledPattern.matcher(line)
            if (matcher.matches()) {
                val name = matcher.group(1)
                val feature = FeatureExprFactory.createDefinedExternal(name)
                var fileExTmp = fileEx.and(feature)
                if (correctFeatureModelIncompatibility) {
                    val isSat = fileExTmp.isSatisfiable(fm)
                    println(name + " " + (if (isSat) "sat" else "!sat"))
                    if (!isSat) {
                        fileExTmp = fileEx.andNot(feature)
                        println("disabling feature " + feature)
                        //fileExTmp = fileEx; println("ignoring Feature " +feature)
                        falseFeatures += feature
                        changedAssignment += 1
                    } else {
                        trueFeatures += feature
                    }
                } else {
                    trueFeatures += feature
                }
                fileEx = fileExTmp
            } else {
                matcher = disabledPattern.matcher(line)
                if (matcher.matches()) {
                    val name = matcher.group(1)
                    val feature = FeatureExprFactory.createDefinedExternal(name)
                    var fileExTmp = fileEx.andNot(feature)
                    if (correctFeatureModelIncompatibility) {
                        val isSat = fileEx.isSatisfiable(fm)
                        println("! " + name + " " + (if (isSat) "sat" else "!sat"))
                        if (!isSat) {
                            fileExTmp = fileEx.and(feature)
                            println("SETTING " + name + "=y")
                            trueFeatures += feature
                            changedAssignment += 1
                        } else {
                            falseFeatures += feature
                        }
                    } else {
                        falseFeatures += feature
                    }
                    fileEx = fileExTmp
                } else {
                    ignoredFeatures += 1
                    //println("ignoring line: " + line)
                }
            }
            //println(line)
        }
        val trueFeaturesInSet = features.filter(trueFeatures.contains)
        val falseFeaturesInSet = features.filter(falseFeatures.contains)
        val featuresOutsideFm = features.filterNot((trueFeatures ++ falseFeatures).contains)
        /*for (x <- featuresOutsideFm) {
            println(x.feature)
        }*/
        if (correctFeatureModelIncompatibility) {
            // save corrected file
            val fw = new FileWriter(new File(file.getParentFile, file.getName + "_corrected"))
            fw.write("# configFile written by typechef, based on " + file.getAbsoluteFile)
            fw.write("# ignored " + ignoredFeatures + " features of " + totalFeatures + " features")
            fw.write("# changed assignment for " + changedAssignment + " features of " + totalFeatures + " features")
            for (feature <- trueFeatures)
                fw.append(feature.feature + "=y\n")
            fw.close()
        }
        val exprStmts = (trueFeaturesInSet.map(x => Opt(trueF, ExprStatement(AssignExpr(PostfixExpr(Id("options"), PointerPostfixSuffix(".", Id("config_" + x.toString.toLowerCase()))), "=", Constant("1"))))) ++ falseFeaturesInSet.map(x => Opt(trueF, ExprStatement(AssignExpr(PostfixExpr(Id("options"), PointerPostfixSuffix(".", Id("config_" + x.toString.toLowerCase()))), "=", Constant("0"))))) ++ featuresOutsideFm.map(x => Opt(trueF, ExprStatement(AssignExpr(PostfixExpr(Id("options"), PointerPostfixSuffix(".", Id("config_" + x.toString.toLowerCase()))), "=", Constant(parameterForFeaturesOutsideOfConfigFile)))))).toList
        val functionDef = FunctionDef(List(Opt(trueF, VoidSpecifier())), AtomicNamedDeclarator(List(), Id("initConfig"), List(Opt(True, DeclIdentifierList(List())))), List(), CompoundStatement(exprStmts))
        println(PrettyPrinter.print(functionDef))
        assert(exprStmts.size == features.size)
        return functionDef
    }

    def getConfigsFromFiles(@SuppressWarnings(Array("unchecked")) ast: AST, file: File, fm: FeatureModel): AST = {
        getFunctionFromConfiguration(filterFeatures(ast), file, fm)
    }
}