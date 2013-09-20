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

// @fgarbe: In general many functions can be private, since they are not used (or should not be used) externally.
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
    val renamedIdentifierMap: util.IdentityHashMap[String, String] = new IdentityHashMap()
    var liftOptReplaceMap: Map[Opt[_], List[Opt[_]]] = Map()

    //TODO: alex: print variable renaming map
    val idsToBeReplaced: IdentityHashMap[Id, Set[FeatureExpr]] = new IdentityHashMap()
    val writeOptionsIntoFile = true

    val featureStructInitializedName = "id2i_opt"
    val featureStructName = "ifdef_options"

    val exponentialComputationThreshold = 10
    val numberOfVariantThreshold = 1024
    val nstoms = 1000000

    val isBusyBox = false
    // Variables for statistics

    // Features
    var noOfFeatures = 0

    // Techniques
    var noOfRenamings = 0
    var noOfRenamingUsages = 0

    /*
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



    var noOfEmbeddings = 0
    var noOfDuplications = 0

    // Choices
    var noOfChoiceNodes = 0*/

    def resetValues() {
        // Features
        noOfFeatures = 0

        // Techniques
        noOfRenamings = 0
        noOfRenamingUsages = 0

        /*// Declarations
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


        noOfEmbeddings = 0
        noOfDuplications = 0

        // Choices
        noOfChoiceNodes = 0*/
    }

    /**
     * Converts a feature expression to a condition in the c programming language. def(x64) becomes options.x64.
     * @param feature
     * @return
     */
    // @fgarbe: Maybe change name to satFextoCExpr??
    def featureToCExpr(feature: FeatureExpr): Expr = feature match {
        case d: DefinedExternal => PostfixExpr(Id(featureStructInitializedName), PointerPostfixSuffix(".", Id(d.feature.toLowerCase)))
        case d: DefinedMacro => featureToCExpr(d.presenceCondition)
        case b: BDDFeatureExpr =>
            bddFexToCExpr(b,
                ((fName: String) => PostfixExpr(Id(featureStructInitializedName), PointerPostfixSuffix(".", Id(fName.toLowerCase))))
            )
        case a: And =>
            val l = a.clauses.toList
            var del = List[Opt[NArySubExpr]]()
            // @fgarbe: This is for debugging only, right?
            if (l.size < 1) {
                print("")
            }
            // @farbe: Looks like a standard map function. l.tail.map(x => Opt(trueF, NAraySubExpr("&&", featureToCExpr(x)))) or similar.
            for (e <- l.tail)
                del = del ++ List(Opt(trueF, NArySubExpr("&&", featureToCExpr(e))))
            NAryExpr(featureToCExpr(l.head), del)
        case o: Or =>
            val l = o.clauses.toList
            var del = List[Opt[NArySubExpr]]()
            // @fgarbe: see above.
            if (l.size < 1) {
                print("")
            }
            // @fgarbe: see above.
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
                    )).foldLeft(List[Opt[NArySubExpr]]())((a, b) => a ++ b)
            // @fgarbe: The foldLeft construction on line earlier seems not to be necessary. in featureToCExpr the creation of the c-expression is easier to understand.
            def clauseForHead(x: (Byte, String)): Expr = (if (x._1 == 0)
                UnaryOpExpr("!", transformFName(x._2))
            else
                transformFName(x._2)
                )
            val cnfClauses: List[Expr] = bdd.getBddAllSat.map(clause(_)).toList
            NAryExpr(cnfClauses.head,
                cnfClauses.tail.foldLeft(List[Opt[NArySubExpr]]())((a, b: Expr) => a ++ List(Opt(trueF, NArySubExpr("||", b))))
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

    // @fgarbe; a generic function for the following two seems to be appropriate.
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
    // @fgarbe: Since TranslationUnit is required as a type anyway, change ast: AST to ast: TranslationUnit.
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
     * fgarbe: What does "external int" here mean?
     * Creates an AST including an external int, a function, a struct with all features and an init function for that struct.
     */
    def getOptionFile(ast: AST): TranslationUnit = {
        val features = filterFeatures(ast)
        val optionsAst = definedExternalToAst(features)
        optionsAst
    }

    /**
     * Converts a set of FeatureExpressions into an option struct.
     */
    // @fgarbe: The name of the function seems not to reflect its purpose.
    def definedExternalToAst(defExSet: Set[SingleFeatureExpr]): TranslationUnit = {
        val structDeclList = defExSet.map(x => {
            Opt(trueF, StructDeclaration(List(Opt(trueF, IntSpecifier())), List(Opt(trueF, StructDeclarator(AtomicNamedDeclarator(List(), Id(x.feature.toLowerCase), List()), None, List())))))
        }).toList
        val structDeclaration = Opt(trueF, Declaration(List(Opt(trueF, StructOrUnionSpecifier(false, Some(Id(featureStructName)), Some(structDeclList)))), List(Opt(trueF, InitDeclaratorI(AtomicNamedDeclarator(List(), Id(featureStructInitializedName), List()), List(), None)))))

        if (!createFunctionsForModelChecking) {
            TranslationUnit(List(structDeclaration))
        } else {
            val externDeclaration = Opt(trueF, Declaration(List(Opt(trueF, ExternSpecifier()), Opt(trueF, IntSpecifier())), List(Opt(trueF, InitDeclaratorI(AtomicNamedDeclarator(List(), Id("__VERIFIER_NONDET_INT"), List(Opt(trueF, DeclParameterDeclList(List(Opt(trueF, PlainParameterDeclaration(List(Opt(trueF, VoidSpecifier()))))))))), List(), None)))))

            val function = Opt(trueF, FunctionDef(List(Opt(trueF, IntSpecifier())), AtomicNamedDeclarator(List(), Id("select_one"), List(Opt(trueF, DeclIdentifierList(List())))), List(), CompoundStatement(List(Opt(trueF, IfStatement(One(PostfixExpr(Id("__VERIFIER_NONDET_INT"), FunctionCall(ExprList(List())))), One(CompoundStatement(List(Opt(trueF, ReturnStatement(Some(Constant("1"))))))), List(), Some(One(CompoundStatement(List(Opt(trueF, ReturnStatement(Some(Constant("0"))))))))))))))

            val cmpStmt = defExSet.map(x => {
                Opt(trueF, ExprStatement(AssignExpr(PostfixExpr(Id(featureStructInitializedName), PointerPostfixSuffix(".", Id(x.feature.toLowerCase))), "=", PostfixExpr(Id("select_one"), FunctionCall(ExprList(List()))))))
            }).toList
            val initFunction = Opt(trueF, FunctionDef(List(Opt(trueF, VoidSpecifier())), AtomicNamedDeclarator(List(), Id("initOptions"), List(Opt(trueF, DeclIdentifierList(List())))), List(), CompoundStatement(cmpStmt)))
            TranslationUnit(List(externDeclaration, function, structDeclaration, initFunction))
        }
    }

    /**
     * Filters a given product for feature expressions which are not True and returns a set including each single feature expression.
     */
    // @fgarbe: The name of the function does not reflect its purpose. Suggestion: "getFeatureNames".
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
     * Retrieves a list of tuples out of a choice node which include the corresponding FeatureExpr and AST node.
     * Also takes choices inside choices into account.
     */
    // @fgarbe: The generic type T is not necessary. We work on Conditional[AST] only, right? Simplifies the code a bit.
    def conditionalToTuple[T <: Product](choice: Conditional[T], currentContext: FeatureExpr = trueF, count: Boolean = true): List[(FeatureExpr, T)] = {
        def addOne[T <: Product](entry: One[T], ft: FeatureExpr): List[(FeatureExpr, T)] = {
            entry match {
                case One(null) =>
                    List()
                case One(a) =>
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

    /**
     * Creates a prefix for identifiers from the presence condition under which they occur.
     * Format is _x_ where x is an Integer which represents the presence condition.
     * @param feat
     * @return
     */
    def getPrefixFromIdMap(feat: FeatureExpr): String = {
        def getFromIdMap(feat: FeatureExpr): Int = {
            if (!idMap.contains(feat)) {
                idMap += (feat -> idMap.size)
            }
            idMap.get(feat).get
        }
        "_" + getFromIdMap(feat) + "_"
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
    // @fgarbe: Maybe it's easier to maintain the reverse map Map[Int, FeatureExpr] to Map[FeatureExpr, Int] also.
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

    /**
     * Whenever we rename a declaration of a variable/field/etc. we call this function.
     * Using the Declaration-Use-Map we store the usages of renamed declarations and the presence conditions under which
     * they were renamed. Later on this information will be used to rename the corresponding usages of identifiers.
     * @param i
     * @param ft
     */
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

    /**
     * Renames identifiers inside declarations.
     * @param t
     * @param ft
     * @tparam T
     * @return
     */
    // @fgarbe: Is the input t really generic?
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
                        InitDeclaratorI(AtomicNamedDeclarator(a, Id(getPrefixFromIdMap(ft) + i.name), b), attr, inits)
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
                        InitDeclaratorI(NestedNamedDeclarator(l, AtomicNamedDeclarator(a, Id(getPrefixFromIdMap(ft) + i.name), b), r), attr, inits)
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

            // @fgarbe: r(t).get.asInstanceOf[T] should be sufficient, or can None occur?
            r(t) match {
                case None => t
                case k => k.get.asInstanceOf[T]
            }
        }
    }

    /**
     * Renames the first identifier inside a declaration.
     * @param t
     * @param ft
     * @tparam T
     * @return
     */
    // @fgarbe: What is the difference between convertIds and convertId?
    def convertId[T <: Product](t: T, ft: FeatureExpr): T = {
        val r = oncetd(rule {
            case init@InitDeclaratorI(decl@AtomicNamedDeclarator(a, i: Id, b), attr, inits) =>
                if (i.name != "main") {
                    addIdUsages(i, ft)
                    replaceId.put(i, ft)
                    if (!idMap.contains(ft)) {
                        idMap += (ft -> idMap.size)
                    }
                    InitDeclaratorI(AtomicNamedDeclarator(a, Id(getPrefixFromIdMap(ft) + i.name), b), attr, inits)
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
                    InitDeclaratorI(NestedNamedDeclarator(l, AtomicNamedDeclarator(a, Id(getPrefixFromIdMap(ft) + i.name), b), r), attr, inits)
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

    /**
     * Renames identifiers inside of StructDeclarations.
     * @param t
     * @param ft
     * @tparam T
     * @return
     */
    def convertStructId[T <: Product](t: T, ft: FeatureExpr): T = {
        val r = oncetd(rule {
            case decl@AtomicNamedDeclarator(a, i: Id, b) =>
                if (i.name != "main") {
                    addIdUsages(i, ft)
                    replaceId.put(i, ft)
                    if (!idMap.contains(ft)) {
                        idMap += (ft -> idMap.size)
                    }
                    AtomicNamedDeclarator(a, Id(getPrefixFromIdMap(ft) + i.name), b)
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

    /**
     * Renames Enumerators.
     * @param enu
     * @param ft
     * @return
     */
    def convertEnumId(enu: Enumerator, ft: FeatureExpr): Enumerator = {
        addIdUsages(enu.id, ft)
        if (!idMap.contains(ft)) {
            idMap += (ft -> idMap.size)
        }
        Enumerator(Id(getPrefixFromIdMap(ft) + enu.id.name), enu.assignment)
    }

    /**
     * Renames all identifiers.
     * @param t
     * @param ft
     * @tparam T
     * @return
     */
    def convertAllIds[T <: Product](t: T, ft: FeatureExpr): T = {
        val r = manytd(rule {
            case i: Id =>
                // TODO auf Funktionen beschränken
                if (i.name != "main") {
                    addIdUsages(i, ft)
                    replaceId.put(i, ft)
                    Id(getPrefixFromIdMap(ft) + i.name)
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

    /**
     * Replaces given FeatureExpression recursively from given Element by True. Also removes Opt nodes which should not
     * occur in this given context. Also renames identifiers if they have a declaration annotated by given FeatureExpression.
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
                    if (!idMap.contains(feat)) {
                        idMap += (feat -> idMap.size)
                    }
                    val matchingId = idsToBeReplaced.get(i).find(x => feat.implies(x).isTautology())
                    matchingId match {
                        case None =>
                            // TODO: this should not happen?
                            val lst = idsToBeReplaced.get(i)
                            Id(getPrefixFromIdMap(feat) + i.name)
                            i
                        case Some(x: FeatureExpr) =>
                            if (x.equals(trueF)) {
                                i
                            } else {
                                Id(getPrefixFromIdMap(x) + i.name)
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
                    // @fgarbe: the following line checks structural equivalence, but misses so A && B == B && A, right?
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

    /**
     * Calls the replaceOptAndId function first and then the transformRecursive function.
     * @param t
     * @param feat
     * @tparam T
     * @return
     */
    def replaceAndTransform[T <: Product](t: T, feat: FeatureExpr): T = {
        transformRecursive(replaceOptAndId(t, feat), feat)
    }

    def ifdeftoif(ast: AST, decluse: IdentityHashMap[Id, List[Id]], usedecl: IdentityHashMap[Id, List[Id]], featureModel: FeatureModel = FeatureExprLib.featureModelFactory.empty, outputStem: String = "unnamed", lexAndParseTime: Long = 0, writeStatistics: Boolean = true, newPath: String = ""): (Option[AST], Long, List[TypeChefError]) = {
        new File(path).mkdirs()
        val tb = java.lang.management.ManagementFactory.getThreadMXBean

        //val prepareSt = tb.getCurrentThreadCpuTime()
        val source_ast = prepareAST(ast)
        //println("Prepare time: " + ((tb.getCurrentThreadCpuTime() - prepareSt) / nstoms).toString())

        // Sets the feature model to the busybox feature model in case we're not testing files from the frontend
        // @fgarbe: The default to busybox should not be here. It's probably implemented for running corresponding tests, but then the definition of the feature model should be in there and not here.
        if (featureModel.equals(FeatureExprLib.featureModelFactory.empty) && isBusyBox && (new File("../TypeChef-BusyboxAnalysis/busybox/featureModel")).exists()) {
            fm = FeatureExprLib.featureModelFactory.create(new FeatureExprParser(FeatureExprLib.l).parseFile("../TypeChef-BusyboxAnalysis/busybox/featureModel"))
        } else {
            fm = featureModel
        }
        fillIdMap(source_ast)
        defuse = decluse
        usedef = usedecl
        val fileName = outputStemToFileName(outputStem)

        var ifdeftoif_file = ""
        if (newPath.equals("")) {
            ifdeftoif_file = outputStemToifdeftoif(outputStem)
        } else {
            ifdeftoif_file = newPath
        }

        val time = tb.getCurrentThreadCpuTime()
        val new_ast = transformRecursive(source_ast)
        val transformTime = (tb.getCurrentThreadCpuTime() - time) / nstoms
        val features = filterFeatures(source_ast)
        noOfFeatures = features.size
        val featureStruct = definedExternalToAst(features)
        val result_ast = TranslationUnit(featureStruct.defs ++ new_ast.asInstanceOf[TranslationUnit].defs)
        exportRenamings()

        PrettyPrinter.printF(result_ast, ifdeftoif_file)

        // @fgarbe: lazy can be removed, since typeCheckSuccessful is always used, i.e., it's not part of a conditional branch.
        lazy val typeCheckSuccessful = getTypeSystem(result_ast).checkASTSilent

        val featureMap = idMap.-(trueF).map(x => x._1.toTextExpr + "," + x._2) mkString "\n"
        writeToFile(path ++ "featureMap.csv", featureMap)

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

    /**
     * Returns the filename of given absolute path (including file extension).
     * @param outputStem
     * @return
     */
    def outputStemToFileName(outputStem: String): String = {
        val lastSepIndex = outputStem.lastIndexOf(System.getProperty("file.separator"))
        if (lastSepIndex == -1) {
            outputStem
        } else {
            outputStem.substring(lastSepIndex + 1)
        }
    }

    def outputStemToDirectory(outputStem: String): String = {
        val lastSepIndex = outputStem.lastIndexOf(System.getProperty("file.separator"))
        if (lastSepIndex == -1) {
            outputStem
        } else {
            outputStem.substring(0, lastSepIndex)
        }
    }

    /**
     * Returns the new absolute file path for the resulting transformation file.
     * @param outputStem
     * @return
     */
    def outputStemToifdeftoif(outputStem: String): String = {
        def outputStemToFileNameWithoutExtension(outputStem: String): String = {
            val lastSepIndex = outputStem.lastIndexOf(".")
            if (lastSepIndex == -1) {
                outputStem
            } else {
                outputStem.substring(0, lastSepIndex)
            }
        }
        if ((new File(outputStem)).getName.contains(".")) // if the filename has a extension, remove it
            outputStemToFileNameWithoutExtension(outputStem) + "_ifdeftoif.c"
        else
            outputStem + "_ifdeftoif.c"
    }

    /**
     * Makes #ifdef to if transformation on given AST element. Returns new AST element and a statistics String.
     */
    def transformAst[T <: Product](t: AST, decluse: IdentityHashMap[Id, List[Id]], usedecl: IdentityHashMap[Id, List[Id]], featureModel: FeatureModel = FeatureExprLib.featureModelFactory.empty): (AST, String) = {
        if (featureModel.equals(FeatureExprLib.featureModelFactory.empty) && isBusyBox) {
            fm = FeatureExprLib.featureModelFactory.create(new FeatureExprParser(FeatureExprLib.l).parseFile("C:/Users/Flo/Dropbox/HiWi/busybox/TypeChef-BusyboxAnalysis/busybox/featureModel"))
        } else {
            fm = featureModel
        }
        val tb = java.lang.management.ManagementFactory.getThreadMXBean
        val source_ast = prepareAST(t)



        fillIdMap(t)
        defuse = decluse
        usedef = usedecl
        val time = tb.getCurrentThreadCpuTime()
        val result = transformRecursive(source_ast)
        val transformTime = (tb.getCurrentThreadCpuTime() - time) / nstoms
        val features = filterFeatures(source_ast)
        noOfFeatures = features.size

        val csvEntry = createCsvEntry(source_ast, result, "unnamed", 0, transformTime)
        resetValues()
        if (writeOptionsIntoFile) {
            (TranslationUnit(definedExternalToAst(features).defs ++ result.asInstanceOf[TranslationUnit].defs).asInstanceOf[AST], csvEntry)
        } else {
            (result, csvEntry)
        }
    }

    /**
     * This is the core of the #ifdef to if transformation. This function is called recursively on all opt nodes inside the
     * given AST element. The general strategy is to look at opt nodes:
     * - statements which need to be duplicated or embedded inside if statements
     * - declarations which need to be duplicated/renamed
     */
    def transformRecursive[T <: Product](t: T, currentContext: FeatureExpr = trueF): T = {
        val r = alltd(rule {
            case l: List[Opt[_]] =>
                l.flatMap(x => {
                    x match {
                        case o@Opt(ft: FeatureExpr, entry) =>
                            if (x.entry.isInstanceOf[AST] && !x.entry.asInstanceOf[AST].range.getOrElse(None).equals(None)) {

                                /*
                                Exports the current code position in the source file. Can be used to find out
                                where the #ifdef to if progress stopped.
                                 */
                                writeToFile("ifdeftoif_progress.txt", x.entry.asInstanceOf[AST].range.get.toString())
                            }

                            /*
                           Handle opt nodes which occur under a certain presence condition
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
                                            features.map(x => replaceAndTransform(Opt(trueF, Initializer(elem, convertAllIds(expr, x))), x))
                                        } else {
                                            List(replaceOptAndId(Opt(trueF, Initializer(elem, convertAllIds(expr, o.feature))), o.feature))
                                        }
                                    case e: Enumerator =>
                                        val features = computeNextRelevantFeatures(e, o.feature)
                                        if (!features.isEmpty) {
                                            features.map(x => Opt(trueF, transformRecursive(convertEnumId(replaceOptAndId(e, x), x), x)))
                                        } else {
                                            List(Opt(trueF, transformRecursive(convertEnumId(replaceOptAndId(e, o.feature), o.feature), o.feature)))
                                        }
                                    case sd@StructDeclaration(qual, decl) =>
                                        val features = computeNextRelevantFeatures(sd, o.feature)
                                        if (!features.isEmpty) {
                                            features.map(x => replaceAndTransform(Opt(trueF, StructDeclaration(qual, convertStructId(decl, x))), x))
                                        } else {
                                            List(replaceOptAndId(Opt(trueF, StructDeclaration(qual, convertStructId(decl, o.feature))), o.feature))
                                        }

                                    case fd: FunctionDef =>
                                        handleFunctions(o)
                                    case nfd: NestedFunctionDef =>
                                        handleFunctions(o)


                                    case i@IfStatement(_, _, _, _) =>
                                        handleIfStatements(o, ft)
                                    case r: ReturnStatement =>
                                        val features = computeNextRelevantFeatures(r, ft)
                                        if (!features.isEmpty) {
                                            val result = features.map(x => Opt(trueF, statementToIf(replaceAndTransform(r, x), x)))
                                            result
                                        } else {
                                            List(Opt(trueF, statementToIf(replaceAndTransform(r, ft), ft)))
                                        }
                                    case w: WhileStatement =>
                                        handleStatements(o, currentContext)
                                    case s: SwitchStatement =>
                                        handleStatements(o, currentContext)
                                    case d: DoStatement =>
                                        handleStatements(o, currentContext)
                                    case g: GotoStatement =>
                                        val features = computeNextRelevantFeatures(g, ft)
                                        if (!features.isEmpty) {
                                            val result = features.map(x => Opt(trueF, statementToIf(replaceOptAndId(g, x), ft)))
                                            result
                                        } else {
                                            List(Opt(trueF, statementToIf(replaceOptAndId(g, ft), ft)))
                                        }
                                    case f: ForStatement =>
                                        handleStatements(o, currentContext)
                                    case elif@ElifStatement(One(expr: Expr), thenBranch) =>
                                        // TODO: should not happen because handleIfStatements should take care of this?
                                        // @fgarbe: So then adding an assert may be a good strategy.
                                        //val features = computeNextRelevantFeatures
                                        List(Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(ft), List(Opt(trueF, NArySubExpr("&&", replaceOptAndId(expr, ft)))))), replaceAndTransform(thenBranch, ft))))
                                    case e: ExprStatement =>
                                        val realFeature = currentContext.and(o.feature)
                                        val features = computeNextRelevantFeatures(e, realFeature)
                                        if (!features.isEmpty) {
                                            features.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x.and(realFeature))), One(CompoundStatement(List(replaceAndTransform(Opt(trueF, e), x.and(realFeature))))), List(), None)))
                                        } else {
                                            List(Opt(trueF, IfStatement(One(featureToCExpr(realFeature)), One(CompoundStatement(List(replaceAndTransform(Opt(trueF, e), realFeature)))), List(), None)))
                                        }
                                    case label: LabelStatement =>
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
                                        List(Opt(trueF, IfStatement(One(featureToCExpr(o.feature)), One(replaceAndTransform(cs, o.feature)), List(), None)))
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
                                        val features = computeNextRelevantFeatures(e, currentContext)
                                        if (!features.isEmpty) {
                                            features.map(x => Opt(trueF, transformRecursive(convertEnumId(replaceOptAndId(e, x), x), x)))
                                        } else {
                                            List(transformRecursive(o, currentContext))
                                        }
                                    case sd@StructDeclaration(qual, decl) =>
                                        val features = computeNextRelevantFeatures(sd, o.feature)
                                        if (!features.isEmpty) {
                                            features.map(x => replaceAndTransform(Opt(trueF, StructDeclaration(qual, convertStructId(decl, x))), x))
                                        } else {
                                            List(transformRecursive(o, currentContext))
                                        }

                                    case fd: FunctionDef =>
                                        handleFunctions(o)
                                    case nfd: NestedFunctionDef =>
                                        handleFunctions(o)


                                    case cmpStmt: CompoundStatement =>
                                        List(Opt(trueF, transformRecursive(cmpStmt, currentContext)))
                                    case f: ForStatement =>
                                        handleStatements(o, currentContext)
                                    case d: DoStatement =>
                                        handleStatements(o, currentContext)
                                    case r: ReturnStatement =>
                                        val features = computeNextRelevantFeatures(r, currentContext)
                                        if (!features.isEmpty) {
                                            val result = features.map(x => Opt(trueF, statementToIf(replaceAndTransform(r, x), x)))
                                            result
                                        } else {
                                            List(transformRecursive(o, currentContext))
                                        }
                                    case g: GotoStatement =>
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
                                    /*case cs@ CaseStatement(e: Expr) =>
                                        val features = computeNextRelevantFeatures(cs, currentContext)
                                        if (!features.isEmpty) {
                                            features.map(x => Opt(trueF, CaseStatement(replaceOptAndId(e, x))))
                                        } else {
                                            List(o)
                                        }*/
                                    case e: ExprStatement =>
                                        val features = computeNextRelevantFeatures(e, currentContext)
                                        if (!features.isEmpty) {
                                            features.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(replaceAndTransform(Opt(trueF, e), x.and(o.feature))))), List(), None)))
                                        } else {
                                            if (currentContext.equivalentTo(trueF)) {
                                                List(transformRecursive(o, currentContext))
                                            } else {
                                                List(replaceAndTransform(Opt(trueF, ExprStatement(e.expr)), currentContext))
                                            }
                                        }
                                    case w@WhileStatement(expr: Expr, s: Conditional[_]) =>
                                        val result = handleStatements(o, currentContext)
                                        result
                                    case ss: SwitchStatement =>
                                        handleStatements(o, currentContext)
                                    case i@IfStatement(_, _, _, _) =>
                                        handleIfStatements(o, currentContext)
                                    case elif@ElifStatement(One(cond), thenBranch) =>
                                        val feat = computeNextRelevantFeatures(cond)
                                        if (!feat.isEmpty) {
                                            feat.map(x => transformRecursive(replaceOptAndId(Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(x), List(Opt(trueF, NArySubExpr("&&", cond))))), thenBranch)), x), currentContext))
                                        } else {
                                            List(transformRecursive(o, currentContext))
                                        }
                                    case elif@ElifStatement(c@Choice(ft, thenBranch, elseBranch), thenStmt) =>
                                        // TODO: should not happen because handleIfStatements should take care of ElifStatements
                                        val choices = conditionalToTuple(c, currentContext).map(x => (x._1.and(currentContext), x._2)).filterNot(x => x._1.equivalentTo(FeatureExprFactory.False))
                                        choices.map(x => {
                                            if (containsIdUsage(thenBranch)) {
                                                replaceAndTransform(Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(x._1), List(Opt(trueF, NArySubExpr("&&", convertIdUsagesFromDefuse(x._2, x._1)))))), thenStmt)), x._1)
                                            } else {
                                                replaceAndTransform(Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(x._1), List(Opt(trueF, NArySubExpr("&&", x._2))))), thenStmt)), x._1)
                                            }
                                        })

                                    case td: TypelessDeclaration =>
                                        List(o)
                                    case k: Product =>
                                        List(transformRecursive(o, currentContext))
                                    case _ =>
                                        List(o)
                                }
                            }
                        case k => List(transformRecursive(k, currentContext))
                    }
                })
        })
        r(t) match {
            case None => t
            case k => k.get.asInstanceOf[T]
        }
    }

    def containsIdUsage(a: Any): Boolean = {
        val ids = filterASTElems[Id](a)
        // @fgarbe: ids.exists should be the right function here
        ids.foreach(x => if (idsToBeReplaced.containsKey(x)) return true)
        false
    }

    def getIdUsageFeatureList(a: Any): List[List[FeatureExpr]] = {
        val ids = filterASTElems[Id](a)
        val features = ids.filter(x => idsToBeReplaced.containsKey(x)).map(x => idsToBeReplaced.get(x).toList)
        features.distinct
    }

    def computeIdUsageFeatures(a: Any, currentContext: FeatureExpr = trueF): List[FeatureExpr] = {
        // @fgarbe: Can be simplified to:
        // var res = ...
        // if (currentContext.equivalentTo(trueF)) {
        //   res = res.flatMap ...
        // }
        // res
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

    def getRealFeatureForContext(feature: FeatureExpr, context: FeatureExpr): FeatureExpr = {
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
    // @fgarbe: http://stackoverflow.com/questions/8217764/cartesian-product-of-two-lists simplifies the computation a bit.
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
     * Returns a list of FeatureExpressions for the given AST Element a. This list contains FeatureExpressions that
     * require code duplications. Example: condition inside an IfStatement has a variable Identifier -> we have to create
     * two different IfStatements and the function returns these two distinct features.
     * @param a
     * @param currentContext
     * @return
     */
    // @fgarbe: Function name does not reveal the purpose. Change a: Any to a: AST??
    // @fgarbe: I understand the purpose of this function, but not how its implemented. I would a expect a check whether the code contains only patterns of #ifdef to if transformations that can be transformed without duplication and then lists the remaining feature expressions that could not be transformed.
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
                    val firstResult = featureBuffer.toList.head
                    val result = computeCarthesianProduct(List(firstResult, identFeatureList.diff(firstResult)))
                    result
                } else {
                    val featureBufferList = featureBuffer.toList
                    // Workaround for exponential explosion
                    val firstResult = featureBufferList.tail.foldLeft(featureBufferList.head)((first, second) => {
                        if (!first.isEmpty) {
                            first.flatMap(x => second.map(y => y.and(x))).filterNot(x => x.equivalentTo(FeatureExprFactory.False) || !x.isSatisfiable(fm))
                        } else {
                            List()
                        }
                    }).distinct
                    if (firstResult.size > numberOfVariantThreshold) {
                        println("aborted handling because of number of variants ("+firstResult.size+")"+ "\n"+
                        "\t ast element: " + a.toString.substring(0,20) + " ...\n" +
                        "\t context: " + currentContext.toTextExpr)
                        List()
                    } else {
                        val result = computeCarthesianProduct(List(firstResult, identFeatureList.diff(firstResult)))
                        result
                    }
                }
            }
        }
        a match {
            /*case optDefault@ Opt(ft, ds: DefaultStatement) =>
                if (currentContext.implies(ft).isTautology()) {
                    List()
                } else {
                    List(ft, ft.not().and(currentContext))
                }
            case optCase@ Opt(ft, cs: CaseStatement) =>
                val result = computeNextRelevantFeatures(cs, getRealFeatureForContext(ft, currentContext))
                if (currentContext.implies(ft).isTautology()) {
                    result
                } else {
                    ft.not().and(currentContext) :: result
                }
            case cs: CompoundStatement =>
                List()*/
            case o: Opt[_] =>
                if (currentContext.implies(o.feature).isTautology()) {
                    computeNextRelevantFeatures(o.entry, currentContext)
                } else {
                    val features = computeNextRelevantFeatures(o.entry, o.feature)
                    if (features.isEmpty) {
                        List(o.feature)
                    } else {
                        features
                    }
                }
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
            case ss@SwitchStatement(e, One(stmt: CompoundStatement)) =>
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
     * Takes a look at the CaseStatements and CompoundStatements inside a SwitchStatement in order to determine
     * the list of FeatureExpressions needed for duplication.
     * @param cmpStmt
     * @param currentContext
     * @return
     */
    def computeCaseFeatures(cmpStmt: CompoundStatement, currentContext: FeatureExpr = trueF): List[FeatureExpr] = {
        /*def collectCaseStatements(compStmt: CompoundStatement, currentList: List[List[Opt[CaseStatement]]] = List(List())) : List[List[Opt[CaseStatement]]] = {
            val stmts = compStmt.innerStatements
            if (stmts.isEmpty){
                currentList
            } else if (stmts.head.entry.isInstanceOf[CaseStatement]) {
                collectCaseStatements(CompoundStatement(stmts.tail), ((stmts.head.asInstanceOf[Opt[CaseStatement]] :: currentList.head) :: currentList.tail))
            } else if (stmts.head.entry.isInstanceOf[CompoundStatement]) {
                collectCaseStatements(CompoundStatement(stmts.tail), (List() :: currentList))
            } else {
                currentList.drop(1)
            }
        }
        val test = collectCaseStatements(cmpStmt).map(x => x.flatMap(y => computeNextRelevantFeatures(y, currentContext))).filter(x => !x.isEmpty)
        val test2 = collectCaseStatements(cmpStmt).map(x => x.flatMap(y => computeNextRelevantFeatures(y, currentContext))).filter(x => !x.isEmpty)
        println("T:\n" + test)
        val caseStatements = cmpStmt.innerStatements.filter(x => x.entry.isInstanceOf[CaseStatement]).map(x => computeNextRelevantFeatures(x, currentContext))
        val defaultStatements = cmpStmt.innerStatements.filter(x => x.entry.isInstanceOf[DefaultStatement]).map(x => computeNextRelevantFeatures(x, currentContext))
        val totalStatements = (caseStatements ++ defaultStatements).filter(x => !x.isEmpty)
        computeCarthesianProduct(totalStatements)*/
        val caseFeatures = getFeatureCombinations(cmpStmt.innerStatements.map(x => {x.feature}).filter(x => !x.equals(trueF)).flatMap(x => x.collectDistinctFeatureObjects).distinct).filter(x => x.implies(currentContext).isTautology())
        caseFeatures
    }

    /**
     * Takes a look at the CompoundStatements and CaseStatements AS WELL as the expression inside the CaseStatements
     * in a SwitchStatement in order to determine the list of FeatureExpressions needed for duplication purposes.
     * @param cmpStmt
     * @param currentContext
     * @return
     */
    def computeTotalCaseFeatures(cmpStmt: CompoundStatement, currentContext: FeatureExpr = trueF): List[FeatureExpr] = {
        val caseFeatures = getFeatureCombinations(cmpStmt.innerStatements.flatMap(x => {
            x.entry match {
                case cs: CaseStatement =>
                    val features = computeNextRelevantFeatures(x, currentContext)
                    features
                case _ =>
                    if (x.feature.equals(trueF)) {
                        List()
                    } else {
                        List(x.feature)
                    }
            }
        }).distinct.flatMap(x => x.collectDistinctFeatureObjects).distinct).filter(x => x.implies(currentContext).isTautology())
        caseFeatures
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
        def debugGetNextFeatureHelp(ast : Any, foundFeatures : List[FeatureExpr]) {
            val astElem: String = ast.toString
            for (i <- (1 to astElem.length-1)) {
                if (astElem.substring(i).startsWith("def(")) {
                    val end = astElem.substring(i).indexOf(")")
                    val featureEx = astElem.substring(i , i+end+1)
                    if (! foundFeatures.toString.contains(featureEx)) {
                        println(ast.toString)
                        println("\t-> " + foundFeatures)
                        println("\t\t" + featureEx + " missing")
                    }
                }
            }
        }
        def getNextFeatureHelp(a: Any, currentContext: FeatureExpr = trueF): List[FeatureExpr] = {
            a match {
                case d@Opt(ft, entry: NArySubExpr) =>
                    if (ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) entry.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext)) else List(getRealFeatureForContext(ft, currentContext)) ++ entry.productIterator.toList.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext)))
                case d@Opt(ft, entry: Expr) =>
                    if (ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) entry.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext)) else List(getRealFeatureForContext(ft, currentContext)) ++ entry.productIterator.toList.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext)))
                case d@Opt(ft, entry: DeclParameterDeclList) =>
                    if (ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) entry.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext)) else List(getRealFeatureForContext(ft, currentContext)) ++ entry.productIterator.toList.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext)))
                case d@Opt(ft, entry: ParameterDeclarationD) =>
                    if (ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) entry.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext)) else List(getRealFeatureForContext(ft, currentContext)) ++ entry.productIterator.toList.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext)))
                case d@Opt(ft, entry: InitDeclaratorI) =>
                    (if (!ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) List(getRealFeatureForContext(ft, currentContext)) else List()) ++ entry.declarator.productIterator.toList.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext))) ++ entry.attributes.productIterator.toList.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext)))
                    case d@Opt(ft, entry: StructDeclarator) =>
                        if (ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) entry.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext)) else List(getRealFeatureForContext(ft, currentContext)) ++ entry.productIterator.toList.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext)))
                    case d@Opt(ft, entry: Statement) =>
                        if (ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) entry.productIterator.toList.flatMap(getNextFeatureHelp(_, currentContext)) else List(getRealFeatureForContext(ft, currentContext)) ++ entry.productIterator.toList.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext)))
    // Attribute Stuff
                    case d@Opt(ft, entry: GnuAttributeSpecifier) =>
                        entry.attributeList.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext)))
                    case d@Opt(ft, entry: AttributeSequence) =>
                        entry.attributes.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext)))
                    case d@Opt(ft, entry: CompoundAttribute) =>
                        entry.inner.flatMap(getNextFeatureHelp(_, getRealFeatureForContext(ft, currentContext)))
    //End - Attribute Stuff
                case d@Opt(ft, entry) =>
                    if (!ft.equals(trueF) || ft.equals(FeatureExprFactory.False)) List(getRealFeatureForContext(ft, currentContext)) else List()
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
                case d@Opt(ft, entry: DeclArrayAccess) =>
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
                            Id(getPrefixFromIdMap(feat) + i.name)
                        case Some(x: FeatureExpr) => Id(getPrefixFromIdMap(x) + i.name)
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

    def statementToIf(e: Statement, ft: FeatureExpr): IfStatement = {
        IfStatement(One(featureToCExpr(ft)), One(CompoundStatement(List(Opt(trueF, replaceOptAndId(e, ft))))), List(), None)
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

    // @fgarbe: Change function name to handleStatement?
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
     */
    // @fgarbe: Change function name to handleIfStatement?
    def handleIfStatements(optIf: Opt[_], currentContext: FeatureExpr = trueF): List[Opt[_]] = {
        // 1. Step
        // @fgarbe: You frequently use equals trueF, but so feature expressions such as A v !A are missed.
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
                        List(transformRecursive(optIf, currentContext))
                    } else {
                        conditionalTuple.flatMap(x => {
                            val features = computeNextRelevantFeatures(x._2, x._1)
                            if (features.isEmpty) {
                                List(Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(x._1), List(Opt(trueF, NArySubExpr("&&", replaceOptAndId(x._2, x._1)))))), transformRecursive(replaceOptAndId(thenBranch, x._1), x._1))))
                            } else {
                                features.map(y => Opt(trueF, ElifStatement(One(NAryExpr(featureToCExpr(y), List(Opt(trueF, NArySubExpr("&&", replaceOptAndId(x._2, y)))))), transformRecursive(replaceOptAndId(thenBranch, y), y))))
                            }
                        })
                    }
            }
        }
    }

    // @fgarbe: I don't understand why computeNextRelevantFeatures is not always computed for expr1, expr2, and expr3. All three expressions could contain optional elements.
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
                        List(Opt(trueF, ForStatement(replaceOptAndId(expr1, currentContext), replaceOptAndId(expr2, currentContext), replaceOptAndId(expr3, currentContext), One(transformRecursive(stmt, currentContext)))))
                    } else {
                        features.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, ForStatement(replaceOptAndId(expr1, x), replaceOptAndId(expr2, x), replaceOptAndId(expr3, x), One(transformRecursive(stmt))))))), List(), None)))
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
                        List(Opt(trueF, WhileStatement(replaceOptAndId(expr, currentContext), One(transformRecursive(replaceOptAndId(stmt, currentContext), currentContext)))))
                    } else {
                        features.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, WhileStatement(replaceOptAndId(expr, x), One(transformRecursive(replaceOptAndId(stmt, x), x))))))), List(), None)))
                    }
                case s@SwitchStatement(expr, One(stmt: Statement)) =>
                    val exprFeatures = computeNextRelevantFeatures(expr)
                    // val caseFeatures = computeCaseFeatures(stmt.asInstanceOf[CompoundStatement], currentContext)
                    val caseFeatures = computeTotalCaseFeatures(stmt.asInstanceOf[CompoundStatement], currentContext)
                    val features = computeCarthesianProduct(List(exprFeatures, caseFeatures))
                    if (features.isEmpty) {
                        List(Opt(trueF, SwitchStatement(replaceOptAndId(expr, currentContext), One(transformRecursive(replaceOptAndId(stmt, currentContext))))))
                    } else {
                        features.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, SwitchStatement(replaceOptAndId(expr, x), One(transformRecursive(replaceOptAndId(stmt, x), x))))))), List(), None)))
                    }
                case d@DoStatement(expr, One(stmt: Statement)) =>
                    val features = computeNextRelevantFeatures(expr)
                    if (features.isEmpty) {
                        List(Opt(trueF, DoStatement(replaceOptAndId(expr, currentContext), One(transformRecursive(replaceOptAndId(stmt, currentContext), currentContext)))))
                    } else {
                        features.map(x => Opt(trueF, IfStatement(One(featureToCExpr(x)), One(CompoundStatement(List(Opt(trueF, DoStatement(replaceOptAndId(expr, x), One(transformRecursive(replaceOptAndId(stmt, x), x))))))), List(), None)))
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

    def handleDeclarations(optDeclaration: Opt[Declaration], currentContext: FeatureExpr = trueF): List[Opt[Declaration]] = {
        // TODO convert multiple IDs from variable_typedef a, b, c, d;
        if (optDeclaration.feature.equivalentTo(trueF)) {
            optDeclaration.entry match {
                case d@Declaration(declSpecs, init) =>
                    val features = computeNextRelevantFeatures(d).map(x => x.and(currentContext))
                    if (!features.isEmpty) {
                        val result = features.map(x => Opt(trueF, transformRecursive(replaceOptAndId(Declaration(declSpecs, convertIds(init, x)), x), x)))
                        result
                    } else {
                        List(transformRecursive(optDeclaration))
                    }
            }
        } else {
            optDeclaration.entry match {
                case d@Declaration(declSpecs, init) =>
                    val feat = optDeclaration.feature
                    val newDeclSpecs = declSpecs.map(x => x match {
                        case o@Opt(ft, EnumSpecifier(Some(i: Id), k)) =>
                            if (defuse.containsKey(i)) {
                                addIdUsages(i, feat)
                                Opt(ft, EnumSpecifier(Some(Id(getPrefixFromIdMap(feat) + i.name)), k))
                            } else {
                                o
                            }
                        case o@Opt(ft, StructOrUnionSpecifier(a, Some(i: Id), b)) =>
                            if (defuse.containsKey(i)) {
                                addIdUsages(i, feat)
                                Opt(ft, StructOrUnionSpecifier(a, Some(Id(getPrefixFromIdMap(feat) + i.name)), b))
                            } else {
                                o
                            }

                        case k =>
                            k
                    })
                    val tmpDecl = Declaration(newDeclSpecs, init)
                    val features = computeNextRelevantFeatures(tmpDecl, feat)
                    if (!features.isEmpty) {
                        val result = features.map(x => Opt(trueF, transformRecursive(convertId(replaceOptAndId(tmpDecl, x), x), x)))
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
                            Opt(ft, EnumSpecifier(Some(Id(getPrefixFromIdMap(feat) + i.name)), k))
                        } else {
                            o
                        }
                    case o@Opt(ft, StructOrUnionSpecifier(a, Some(i: Id), b)) =>
                        if (defuse.containsKey(i)) {
                            addIdUsages(i, feat)
                            Opt(ft, StructOrUnionSpecifier(a, Some(Id(getPrefixFromIdMap(feat) + i.name)), b))
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

        var newOptDecl = optDeclaration
        var context = currentContext

        // 1. Step
        if (!optDeclaration.feature.equals(trueF)) {
            newOptDecl = replaceOptAndId(Opt(trueF, optDeclaration.entry), optDeclaration.feature)
            context = optDeclaration.feature
        } else {
            context = trueF
        }
        if(context == FeatureExprFactory.False) {
            println("False context found for " + optDeclaration)
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
                    if (fd.getName.equals("input_backward")) {
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

    // @fgarbe: Can be simplified with a query.
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

    // @fgarbe: Can be simplified with a query.
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

    // @fgarbe: Can be simplified with a query.
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

    // @fgarbe: Can be simplified with a query.
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

    // @fgarbe: Can be simplified with a query.
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

    // @fgarbe: Can be simplified with a query.
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

    // @fgarbe: What does this function do?
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
        val exprStmts = (trueFeaturesInSet.map(x => Opt(trueF, ExprStatement(AssignExpr(PostfixExpr(Id(featureStructInitializedName), PointerPostfixSuffix(".", Id("config_" + x.toString.toLowerCase()))), "=", Constant("1"))))) ++ falseFeaturesInSet.map(x => Opt(trueF, ExprStatement(AssignExpr(PostfixExpr(Id(featureStructInitializedName), PointerPostfixSuffix(".", Id("config_" + x.toString.toLowerCase()))), "=", Constant("0"))))) ++ featuresOutsideFm.map(x => Opt(trueF, ExprStatement(AssignExpr(PostfixExpr(Id(featureStructInitializedName), PointerPostfixSuffix(".", Id("config_" + x.toString.toLowerCase()))), "=", Constant(parameterForFeaturesOutsideOfConfigFile)))))).toList
        val functionDef = FunctionDef(List(Opt(trueF, VoidSpecifier())), AtomicNamedDeclarator(List(), Id("initConfig"), List(Opt(True, DeclIdentifierList(List())))), List(), CompoundStatement(exprStmts))
        println(PrettyPrinter.print(functionDef))
        assert(exprStmts.size == features.size)
        functionDef
    }

    def getConfigsFromFiles(@SuppressWarnings(Array("unchecked")) ast: AST, file: File, fm: FeatureModel): AST = {
        getFunctionFromConfiguration(filterFeatures(ast), file, fm)
    }

    def exportRenamings() = {
        if (!replaceId.isEmpty) {
            writeToFile("renamings.txt", (replaceId.keySet().toArray().toList.map(x => {
                val id = x.asInstanceOf[Id]
                id.name + " -> " + getPrefixFromIdMap(replaceId.get(x)) + id.name +
                " if " + replaceId.get(x).toTextExpr
            }).sorted) mkString ("\n"))
        } else {
            ""
        }
    }
}