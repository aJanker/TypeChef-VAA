package de.fosd.typechef

import io.Source
import java.io._
import util.Random
import java.util.Collections

import de.fosd.typechef.conditional._
import de.fosd.typechef.crewrite._
import de.fosd.typechef.featureexpr._
import de.fosd.typechef.featureexpr.sat._
import de.fosd.typechef.parser.c._
import de.fosd.typechef.typesystem._

/**
 *
 * User: rhein
 * Date: 4/2/12
 * Time: 3:45 PM
 *
 */
object FamilyBasedVsSampleBased extends EnforceTreeHelper with ASTNavigation with CFGHelper {



    private def buildConfigurationsSingleConf(tunit: TranslationUnit, ff: FileFeatures, fm: FeatureModel,
                                              opt: FamilyBasedVsSampleBasedOptions, configDir: File,
                                              caseStudy: String, extasks: List[Task]): (String, List[Task]) = {
        var tasks: List[Task] = List()
        var log = ""
        var msg = ""
        var startTime: Long = 0

        if (extasks.exists(_._1.equals("fileconfig"))) {
            msg = "omitting fileconfig generation, because a serialized version was loaded"
        } else {
            val configFile = if (caseStudy.equals("linux"))
                opt.getRootFolder + "Linux_allyes_modified.config"
            else if (caseStudy.equals("busybox"))
                opt.getRootFolder + "BusyboxBigConfig.config"
            else if (caseStudy.equals("openssl"))
                opt.getRootFolder + "OpenSSL.config"
            else if (caseStudy.equals("sqlite"))
                opt.getRootFolder + "SQLite.config"
            else
                throw new Exception("unknown case Study, give linux, busybox, openssl, or sqlite")
            startTime = System.currentTimeMillis()
            val (configs, logmsg) = ConfigurationHandling.loadConfigurationFromKconfigFile(ff, fm,
                new File(configFile))
            tasks :+= Pair("fileconfig", configs)
            msg = "Time for config generation (singleconf): " + (System.currentTimeMillis() - startTime) +
                " ms\n" + logmsg
        }
        println(msg)
        log = log + msg + "\n"
        (log, tasks)
    }

    private def buildConfigurationsPairwise(tunit: TranslationUnit, ff: FileFeatures, fm: FeatureModel,
                                            opt: FamilyBasedVsSampleBasedOptions, configDir: File,
                                            caseStudy: String, extasks: List[Task]): (String, List[Task]) = {
        var tasks: List[Task] = List()
        var log = ""
        var msg = ""
        var startTime: Long = 0

        if (extasks.exists(_._1.equals("pairwise"))) {
            msg = "omitting pairwise generation, because a serialized version was loaded"
        } else {
            var productsFile: File = null
            var dimacsFM: File = null
            var featureprefix = ""
            if (caseStudy == "linux") {
                productsFile = new File(opt.getRootFolder + "TypeChef-LinuxAnalysis/linux_pairwise_configs.csv")
                dimacsFM = new File(opt.getRootFolder + "TypeChef-LinuxAnalysis/2.6.33.3-2var.dimacs")
                featureprefix = "CONFIG_"
            } else if (caseStudy == "busybox") {
                productsFile = new File(opt.getRootFolder + "TypeChef-BusyboxAnalysis/busybox_pairwise_configs.csv")
                dimacsFM = new File(opt.getRootFolder + "TypeChef-BusyboxAnalysis/BB_fm.dimacs")
                featureprefix = "CONFIG_"
            } else if (caseStudy == "openssl") {
                productsFile = new File(opt.getRootFolder +
                    "TypeChef-OpenSSLAnalysis/openssl-1.0.1c/openssl_pairwise_configs.csv")
                dimacsFM = new File(opt.getRootFolder +
                    "TypeChef-OpenSSLAnalysis/openssl-1.0.1c/openssl.dimacs")
            } else if (caseStudy == "sqlite") {
                productsFile = new File(opt.getRootFolder +
                    "cRefactor-SQLiteEvaluation/sqlite_pairwise_configs.csv")
                dimacsFM = new File(opt.getRootFolder + "cRefactor-SQLiteEvaluation/sqlite.dimacs")
            } else {
                throw new Exception("unknown case Study, give linux or busybox")
            }
            startTime = System.currentTimeMillis()

            val (configs, logmsg) = ConfigurationHandling.loadConfigurationsFromCSVFile(productsFile, dimacsFM, ff,
                fm, featureprefix)

            tasks :+= Pair("pairwise", configs)
            msg = "Time for config generation (pairwise): " + (System.currentTimeMillis() - startTime) +
                " ms\n" + logmsg
        }
        println(msg)
        log = log + msg + "\n"
        (log, tasks)
    }

    private def buildConfigurationsCodecoverageNH(tunit: TranslationUnit, ff: FileFeatures, fm: FeatureModel,
                                                  configDir: File, caseStudy: String, extasks: List[Task])
    : (String, List[Task]) = {
        var tasks: List[Task] = List()
        var log = ""
        var msg = ""
        var startTime: Long = 0
        if (extasks.exists(_._1.equals("coverage_noHeader"))) {
            msg = "omitting coverage_noHeader generation, because a serialized version was loaded"
        } else {
            startTime = System.currentTimeMillis()
            val (configs, logmsg) = configurationCoverage(tunit, fm, ff, List(),
                preferDisabledFeatures = false, includeVariabilityFromHeaderFiles = false)
            tasks :+= Pair("coverage_noHeader", configs)
            msg = "Time for config generation (coverage_noHeader): " +
                (System.currentTimeMillis() - startTime) + " ms\n" + logmsg
        }
        println(msg)
        log = log + msg + "\n"

        (log, tasks)
    }

    private def buildConfigurationsCodecoverage(tunit: TranslationUnit, ff: FileFeatures, fm: FeatureModel,
                                                configDir: File, caseStudy: String, extasks: List[Task])
    : (String, List[Task]) = {
        var tasks: List[Task] = List()
        var log = ""
        var msg = ""
        var startTime: Long = 0
        if (caseStudy != "linux") {
            if (extasks.exists(_._1.equals("coverage"))) {
                msg = "omitting coverage generation, because a serialized version was loaded"
            } else {
                startTime = System.currentTimeMillis()
                val (configs, logmsg) = configurationCoverage(tunit, fm, ff, List(),
                    preferDisabledFeatures = false, includeVariabilityFromHeaderFiles = true)
                tasks :+= Pair("coverage", configs)
                msg = "Time for config generation (coverage): " +
                    (System.currentTimeMillis() - startTime) + " ms\n" + logmsg
            }
            println(msg)
            log = log + msg + "\n"
        } else {
            println("omit code coverage for case study linux; computation is too expensive!")
        }

        (log, tasks)
    }

    /**
     * returns: (log:String, configs: List[Pair[String,List[SimpleConfiguration] ] ])
     * log is a compilation of the log messages
     * the configs-list contains pairs of the name of the config-generation method and
     * the respective generated configs
     */
    def buildConfigurations(tunit: TranslationUnit, ff: FileFeatures, fm: FeatureModel,
                            opt: FamilyBasedVsSampleBasedOptions,
                            configdir: File, caseStudy: String): (String, List[Task]) = {
        var msg: String = ""
        var log: String = ""
        println("generating configurations.")
        var startTime: Long = 0

        var tasks: List[Task] = List()

        /** try to load tasks from existing files */
        if (configdir.exists()) {

            startTime = System.currentTimeMillis()
            println("loading tasks from serialized files")
            tasks = ConfigurationHandling.loadSerializedConfigurations(ff.features, configdir)
            msg = "Time for serialization loading: " + (System.currentTimeMillis() - startTime) + " ms\n"
            println(msg)
            log = log + msg + "\n"
        }

        /** pairwise configurations */
        if (opt.pairwise) {
            val (plog, ptasks) = buildConfigurationsPairwise(tunit, ff, fm, opt, configdir, caseStudy, tasks)
            log = log + plog
            tasks ++= ptasks
        } else {
            tasks = tasks.filterNot(_._1 == "pairwise")
        }

        /** code coverage - no Header files */
        if (opt.codecoverageNH) {
            val (clog, ctasks) = buildConfigurationsCodecoverageNH(tunit, ff, fm, configdir, caseStudy, tasks)
            log = log + clog
            tasks ++= ctasks
        } else {
            tasks = tasks.filterNot(_._1 == "coverage_noHeader")
        }

        /** code coverage - including Header files */
        if (opt.codecoverage) {
            val (clog, ctasks) = buildConfigurationsCodecoverage(tunit, ff, fm, configdir, caseStudy, tasks)
            log = log + clog
            tasks ++= ctasks
        } else {
            tasks = tasks.filterNot(_._1 == "coverage")
        }

        /** singleconf */
        if (opt.singleconf) {
            val (flog, ftasks) = buildConfigurationsSingleConf(tunit, ff, fm, opt, configdir, caseStudy, tasks)
            log = log + flog
            tasks ++= ftasks
        } else {
            tasks = tasks.filterNot(_._1 == "fileconfig")
        }

        /** family */
        if (opt.family) {
            val (flog, ftasks) = ("", List(Pair("family", List(new SimpleConfiguration(ff, List(), List())))))
            log = log + flog
            tasks ++= ftasks
        } else {
            tasks = tasks.filterNot(_._1 == "family")
        }

        (log, tasks)
    }



    private def countNumberOfASTElements(ast: AST): Long = {
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

    def initSampling(fm_scanner: FeatureModel, fm: FeatureModel, ast: TranslationUnit, ff: FileFeatures,
                     opt: FamilyBasedVsSampleBasedOptions, logMessage: String): (String, String, List[Task]) = {
        var caseStudy = ""
        var thisFilePath: String = ""
        val fileAbsPath = new File(new File(".").getAbsolutePath, opt.getFile).toString
        if (fileAbsPath.contains("linux-2.6.33.3")) {
            thisFilePath = fileAbsPath.substring(fileAbsPath.lastIndexOf("linux-2.6.33.3"))
            caseStudy = "linux"
        } else if (fileAbsPath.contains("busybox-1.18.5")) {
            thisFilePath = fileAbsPath.substring(fileAbsPath.lastIndexOf("busybox-1.18.5"))
            caseStudy = "busybox"
        } else if (fileAbsPath.contains("openssl-1.0.1c")) {
            thisFilePath = fileAbsPath.substring(fileAbsPath.lastIndexOf("openssl-1.0.1c"))
            caseStudy = "openssl"
        } else if (fileAbsPath.contains("SQLite")) {
            thisFilePath = fileAbsPath
            caseStudy = "sqlite"
        } else {
            thisFilePath = opt.getFile
        }

        val configSerializationDir = new File(thisFilePath.substring(0, thisFilePath.length - 2))

        val (configGenLog: String, typecheckingTasks: List[Task]) =
            buildConfigurations(ast, ff, fm, opt, configSerializationDir, caseStudy)
        ConfigurationHandling.saveSerializedConfigurations(typecheckingTasks,
            ff.features, configSerializationDir, opt.getFile)
        (configGenLog, thisFilePath, typecheckingTasks)
    }

    private class StopWatch {
        var lastStart: Long = 0
        var currentPeriod: String = "none"
        var currentPeriodId: Int = 0
        var times: Map[(Int, String), Long] = Map()
        val tb = java.lang.management.ManagementFactory.getThreadMXBean
        val nstoms = 1000000

        private def genId(): Int = { currentPeriodId += 1; currentPeriodId }

        def start(period: String) {
            val now = tb.getCurrentThreadCpuTime
            val lastTime = (now - lastStart) / nstoms
            times = times + ((genId(), currentPeriod) -> lastTime)
            lastStart = now
            currentPeriod = period
        }

        def get(period: String): Long = times.filter(v => v._1._2 == period).headOption.map(_._2).getOrElse(0)

        override def toString = {
            var res = "timing "
            val switems = times.toList.filterNot(x => x._1._2 == "none" || x._1._2 == "done").sortBy(_._1._1)

            if (switems.size > 0) {
                res = res + "("
                res = res + switems.map(_._1._2).reduce(_ + ", " + _)
                res = res + ")\n"
                res = res + switems.map(_._2.toString).reduce(_ + ";" + _)
            }
            res
        }
    }

    def checkErrorsAgainstSamplingConfigs(fm_scanner: FeatureModel, fm: FeatureModel, ast: TranslationUnit,
                                          opt: FamilyBasedVsSampleBasedOptions,
                                          logMessage: String) {
        val ff: FileFeatures = new FileFeatures(ast)
        val (log, fileID, samplingTasks) = initSampling(fm_scanner, fm, ast, ff, opt, logMessage)
        val samplingTastsWithoutFamily = samplingTasks.filterNot {x => x._1 == "family"}
        println("starting error checking.")
        val sw = new StopWatch()

        sw.start("typechecking")
        val ts = new CTypeSystemFrontend(ast, fm, opt) with CTypeCache with CDeclUse
        ts.checkASTSilent
        sw.start("initsa")
        val sa = new CIntraAnalysisFrontend(ast,
            ts.asInstanceOf[CTypeSystemFrontend with CTypeCache with CDeclUse], fm)

        val outFilePrefix: String = fileID.substring(0, fileID.length - 2)

        sw.start("doublefree")
        sa.doubleFree()
        sw.start("uninitializedmemory")
        sa.uninitializedMemory()
        sw.start("casetermination")
        sa.caseTermination()
        sw.start("xfree")
        sa.xfree()
        sw.start("danglingswitchcode")
        sa.danglingSwitchCode()
        sw.start("cfginnonvoidfunc")
        sa.cfgInNonVoidFunc()
        sw.start("checkstdlibfuncreturn")
        sa.stdLibFuncReturn()
        sw.start("deadstore")
        sa.deadStore()
        sw.start("done")

        val file: File = new File(outFilePrefix + ".errreport")
        file.getParentFile.mkdirs()
        val fw: FileWriter = new FileWriter(file)
        fw.write("File : " + fileID + "\n")
        fw.write("Features : " + ff.features.size + "\n")
        fw.write(log + "\n")

        fw.write("Potential number of data-flow errors: " + sa.errors.size + "\n\n")

        for (e <- sa.errors) fw.write(e + "\n\n")

        var caughterrorsmap = Map[String, Integer]()
        for ((name, _) <- samplingTastsWithoutFamily) caughterrorsmap += ((name, 0))


        // check for each error whether the tasklist of an sampling approach contains a configuration
        // that fulfills the error condition (using evaluate)
        for (e <- sa.errors) {
            for ((name, tasklist) <- samplingTastsWithoutFamily) {
                if (tasklist.exists {x => e.condition.evaluate(x.getTrueSet.map(_.feature))})
                    caughterrorsmap += ((name, 1 + caughterrorsmap(name)))
            }
        }

        val reslist = ("all", sa.errors.size) :: caughterrorsmap.toList.sortBy(_._1)
        fw.write(reslist.map(_._1).mkString(";") + "\n")
        fw.write(reslist.map(_._2).mkString(";") + "\n")

        println(sw.toString)

        fw.close()
    }

    def typecheckProducts(fm_scanner: FeatureModel, fm: FeatureModel, ast: TranslationUnit,
                          opt: FamilyBasedVsSampleBasedOptions, logMessage: String) {
        val ff: FileFeatures = new FileFeatures(ast)
        val (configGenLog, thisFilePath, typecheckingTasks) = initSampling(fm_scanner, fm, ast, ff, opt, logMessage)
        analyzeTasks(typecheckingTasks, ast, ff, fm, opt, thisFilePath, startLog = configGenLog)
    }

    def parseFile(stream: InputStream, file: String, dir: String): TranslationUnit = {
        val ast: AST = new ParserMain(new CParser).parserMain(
            () => CLexer.lexStream(stream, file, Collections.singletonList(dir), null),
            new CTypeContext, SilentParserOptions)
        ast.asInstanceOf[TranslationUnit]
    }

    private def liveness(tunit: AST, udm: UseDeclMap, env: ASTEnv, fm: FeatureModel = FeatureExprFactory.empty) {
        val fdefs = filterAllASTElems[FunctionDef](tunit)
        fdefs.map(x => intraDataflowAnalysis(x, udm, env, fm))
    }

    private def intraDataflowAnalysis(f: FunctionDef, udm: UseDeclMap, env: ASTEnv, fm: FeatureModel) {
        if (f.stmt.innerStatements.isEmpty) return

        val pp = getAllPred(f, env)
        val li = new Liveness(f, env, udm, FeatureExprFactory.empty)

        val nss = pp.map(_._1).filterNot(x => x.isInstanceOf[FunctionDef])

        for (s <- nss) {
            li.out(s)
        }
    }

    def analyzeTasks(tasks: List[Task], tunit: TranslationUnit, ff: FileFeatures, fm: FeatureModel,
                     opt: FamilyBasedVsSampleBasedOptions, fileID: String, startLog: String = "") {
        val log: String = startLog
        val nstoms = 1000000
        println("start analysis.")

        // measurement
        val tb = java.lang.management.ManagementFactory.getThreadMXBean

        if (tasks.size > 0) println("start task - checking (" + tasks.size + " tasks)")
        // results (taskName, (NumConfigs, productDerivationTimes, errors, typecheckingTimes, dataflowTimes))
        var configCheckingResults: List[(String, (Int, List[Long], Int, List[Long], List[Long]))] = List()
        for ((taskDesc: String, configs: List[SimpleConfiguration]) <- tasks) {
            var configurationsWithErrors = 0
            var current_config = 0
            var productDerivationTimes: List[Long] = List()
            var tcProductTimes: List[Long] = List()
            var dfProductTimes: List[Long] = List()
            for (config <- configs) {
                current_config += 1

                // product derivation
                val productDerivationStart = tb.getCurrentThreadCpuTime
                val selectedFeatures = config.getTrueSet.map(_.feature)
                val product: TranslationUnit =
                    if (taskDesc == "family") tunit
                    else ProductDerivation.deriveProduct[TranslationUnit](tunit, selectedFeatures)

                val productDerivationDiff = tb.getCurrentThreadCpuTime - productDerivationStart
                productDerivationTimes ::= (productDerivationDiff / nstoms)
                println("checking configuration " + current_config + " of " + configs.size + " (" +
                    fileID + " , " + taskDesc + ")" + "(" + countNumberOfASTElements(product) + ")" +
                    "(" + selectedFeatures.size + ")"
                )

                val ts = if (taskDesc == "family") new CTypeSystemFrontend(product, fm) with CDeclUse
                else new CTypeSystemFrontend(product) with CDeclUse

                // typechecking measurement
                var foundError: Boolean = false
                var lastTime: Long = 0
                var curTime: Long = 0

                lastTime = tb.getCurrentThreadCpuTime
                foundError |= !ts.checkASTSilent
                curTime = tb.getCurrentThreadCpuTime - lastTime
                val productTime: Long = curTime / nstoms

                tcProductTimes ::= productTime // append to the beginning of tcProductTimes

                // liveness measurement
                var lastTimeDf: Long = 0
                var curTimeDf: Long = 0

                lastTimeDf = tb.getCurrentThreadCpuTime
                val env = CASTEnv.createASTEnv(product)
                liveness(product, ts.getUseDeclMap, env)
                curTimeDf = tb.getCurrentThreadCpuTime - lastTimeDf
                val timeDataFlowProduct = curTimeDf / nstoms

                dfProductTimes ::= timeDataFlowProduct // add to the head - reverse later

                if (foundError) configurationsWithErrors += 1
            }
            // reverse tcProductTimes to get the ordering correct
            configCheckingResults ::=(taskDesc, (configs.size, productDerivationTimes.reverse,
                configurationsWithErrors, dfProductTimes.reverse, tcProductTimes.reverse))
        }

        val file: File = new File(fileID + "_" + tasks.map(_._1).mkString + ".vaareport")
        file.getParentFile.mkdirs()
        val fw: FileWriter = new FileWriter(file)
        fw.write("File : " + fileID + "\n")
        fw.write("Features : " + ff.features.size + "\n")
        fw.write(log + "\n")

        for ((taskDesc, (numConfigs, productDerivationTimes, errors, dfProductTimes,
        tcProductTimes)) <- configCheckingResults) {
            fw.write("\n -- Task: " + taskDesc + "\n")
            fw.write("(" + taskDesc + ")Processed configurations: " + numConfigs + "\n")
            fw.write("(" + taskDesc + ")Product Derivation Times: " + productDerivationTimes.mkString(",") + "\n")
            fw.write("(" + taskDesc + ")Configurations with errors: " + errors + "\n")
            fw.write("(" + taskDesc + ")TypecheckingSum Products: " + tcProductTimes.filter(_ > 0).sum + " ms\n")
            fw.write("(" + taskDesc + ")Typechecking Products: " + tcProductTimes.mkString(",") + "\n")
            fw.write("(" + taskDesc + ")DataflowSum Products: " + dfProductTimes.filter(_ > 0).sum + " ms\n")
            fw.write("(" + taskDesc + ")Dataflow Products: " + dfProductTimes.mkString(",") + "\n")
            fw.write("\n")
        }
        fw.close()

    }

    def configListContainsFeaturesAsEnabled(lst: List[SimpleConfiguration],
                                            features: Set[SingleFeatureExpr]): Boolean = {
        for (conf <- lst) {
            if (conf.containsAllFeaturesAsEnabled(features))
                return true
        }
        false
    }


    /**
     * Creates configurations based on the variability nodes found in the given AST.
     * Searches for variability nodes and generates enough configurations to cover all nodes.
     * Configurations do always satisfy the FeatureModel fm.
     * If existingConfigs is non-empty, no config will be created for nodes already covered by these
     * configurations.
     * @param astRoot root of the AST
     * @param fm The Feature Model
     * @param ff The set of "interestingFeatures". Only these features will be set in the configs.
     *                 (Normally the set of all features appearing in the file.)
     * @param existingConfigs described above
     * @param preferDisabledFeatures the sat solver will prefer (many) small configs instead of (fewer) large ones
     * @param includeVariabilityFromHeaderFiles if set to false (default) we will ignore variability in
     *                                          files not ending with ".c".
     *                                          This corresponds to the view of the developer of a ".c" file.
     * @return
     */
    def configurationCoverage(astRoot: TranslationUnit, fm: FeatureModel, ff: FileFeatures,
                              existingConfigs: List[SimpleConfiguration] = List(), preferDisabledFeatures: Boolean,
                              includeVariabilityFromHeaderFiles: Boolean = false):
    (List[SimpleConfiguration], String) = {
        val unsatCombinationsCacheFile = new File("unsatCombinationsCache.txt")
        // using this is not correct when different files have different presence conditions
        val useUnsatCombinationsCache = false
        val unsatCombinationsCache: scala.collection.immutable.HashSet[String] =
            if (useUnsatCombinationsCache && unsatCombinationsCacheFile.exists()) {
                new scala.collection.immutable.HashSet[String] ++
                    Source.fromFile(unsatCombinationsCacheFile).getLines().toSet
            } else {
                scala.collection.immutable.HashSet()
            }
        var unsatCombinations = 0
        var alreadyCoveredCombinations = 0
        var complexNodes = 0
        var simpleOrNodes = 0
        var simpleAndNodes = 0
        var nodeExpressions: Set[List[FeatureExpr]] = Set()

        def collectAnnotationLeafNodes(root: Any, previousFeatureExprs: List[FeatureExpr] =
        List(FeatureExprFactory.True), previousFile: String = null) {
            root match {
                case x: Opt[_] => {
                    if (x.feature.equals(previousFeatureExprs.head)) {
                        collectAnnotationLeafNodes(x.entry, previousFeatureExprs, previousFile)
                    } else {
                        collectAnnotationLeafNodes(x.entry, previousFeatureExprs.::(x.feature), previousFile)
                    }
                }
                case x: Choice[_] => {
                    collectAnnotationLeafNodes(x.thenBranch, previousFeatureExprs.::(x.feature), previousFile)
                    collectAnnotationLeafNodes(x.elseBranch, previousFeatureExprs.::(x.feature.not()), previousFile)
                }
                case l: List[_] =>
                    for (x <- l) {
                        collectAnnotationLeafNodes(x, previousFeatureExprs, previousFile)
                    }
                case x: AST => {
                    val newPreviousFile = if (x.getFile.isDefined) x.getFile.get else previousFile
                    if (x.productArity == 0) {
                        // termination point of recursion
                        if (includeVariabilityFromHeaderFiles ||
                            (newPreviousFile == null || newPreviousFile.endsWith(".c"))) {
                            if (!nodeExpressions.contains(previousFeatureExprs)) {
                                nodeExpressions += previousFeatureExprs
                            }
                        }
                    } else {
                        for (y <- x.productIterator.toList) {
                            collectAnnotationLeafNodes(y, previousFeatureExprs, newPreviousFile)
                        }
                    }
                }
                case Some(x) => {
                    collectAnnotationLeafNodes(x, previousFeatureExprs, previousFile)
                }
                case None => {}
                case One(x) => {
                    collectAnnotationLeafNodes(x, previousFeatureExprs, previousFile)
                }
                case o => {
                    // termination point of recursion
                    if (includeVariabilityFromHeaderFiles ||
                        (previousFile == null || previousFile.endsWith(".c"))) {
                        if (!nodeExpressions.contains(previousFeatureExprs)) {
                            nodeExpressions += previousFeatureExprs
                        }
                    }
                }
            }
        }
        collectAnnotationLeafNodes(astRoot, List(FeatureExprFactory.True),
            if (astRoot.getFile.isDefined) astRoot.getFile.get else null)

        // now optNodes contains all Opt[..] nodes in the file, and choiceNodes all Choice nodes.
        // True node never needs to be handled
        val handledExpressions = scala.collection.mutable.HashSet(FeatureExprFactory.True)
        var retList: List[SimpleConfiguration] = List()

        // inner function
        def handleFeatureExpression(fex: FeatureExpr) = {
            if (!handledExpressions.contains(fex) &&
                !(useUnsatCombinationsCache &&
                    unsatCombinationsCache.contains(fex.toTextExpr))) {
                // search for configs that imply this node
                var isCovered: Boolean = false
                fex.getConfIfSimpleAndExpr() match {
                    case None => {
                        fex.getConfIfSimpleOrExpr() match {
                            case None => {
                                complexNodes += 1
                                isCovered = (retList ++ existingConfigs).exists(
                                {
                                    conf: SimpleConfiguration => conf.toFeatureExpr.implies(fex).isTautology(fm)
                                }
                                )
                            }
                            case Some((enabled: Set[SingleFeatureExpr], disabled: Set[SingleFeatureExpr])) => {
                                simpleOrNodes += 1
                                isCovered = (retList ++ existingConfigs).exists({
                                    conf: SimpleConfiguration => conf.containsAtLeastOneFeatureAsEnabled(enabled) ||
                                        conf.containsAtLeastOneFeatureAsDisabled(disabled)
                                })
                            }
                        }
                    }
                    case Some((enabled: Set[SingleFeatureExpr], disabled: Set[SingleFeatureExpr])) => {
                        simpleAndNodes += 1
                        isCovered = (retList ++ existingConfigs).exists({
                            conf: SimpleConfiguration => conf.containsAllFeaturesAsEnabled(enabled) &&
                                conf.containsAllFeaturesAsDisabled(disabled)
                        })
                    }
                }
                if (!isCovered) {
                    val completeConfig = completeConfiguration(fex, ff, fm, preferDisabledFeatures)
                    if (completeConfig != null) {
                        retList ::= completeConfig
                    } else {
                        if (useUnsatCombinationsCache) {
                            val fw = new FileWriter(unsatCombinationsCacheFile, true)
                            fw.write(fex.toTextExpr + "\n")
                            fw.close()
                        }
                        unsatCombinations += 1
                    }
                } else {
                    alreadyCoveredCombinations += 1
                }
                handledExpressions.add(fex)
            }
        }
        if (nodeExpressions.isEmpty ||
            (nodeExpressions.size == 1 && nodeExpressions.head.equals(List(FeatureExprFactory.True)))) {
            // no feature variables in this file, build one random config and return it
            val completeConfig = completeConfiguration(FeatureExprFactory.True, ff,
                fm, preferDisabledFeatures)
            if (completeConfig != null) {
                retList ::= completeConfig
            } else {
                if (useUnsatCombinationsCache) {
                    val fw = new FileWriter(unsatCombinationsCacheFile, true)
                    fw.write(FeatureExprFactory.True + "\n")
                    fw.close()
                }
                unsatCombinations += 1
            }
        } else {
            for (featureList: List[FeatureExpr] <- nodeExpressions) {
                val fex: FeatureExpr = featureList.fold(FeatureExprFactory.True)(_ and _)
                handleFeatureExpression(fex)
            }
        }
        def getFeaturesInCoveredExpressions: Set[SingleFeatureExpr] = {
            // how many features have been found in this file (only the .c files)?
            var features: Set[SingleFeatureExpr] = Set()
            for (exLst <- nodeExpressions)
                for (ex <- exLst)
                    for (feature <- ex.collectDistinctFeatureObjects)
                        features += feature
            features
        }
        (retList,
            " unsatisfiableCombinations:" + unsatCombinations + "\n" +
                " already covered combinations:" + alreadyCoveredCombinations + "\n" +
                " created combinations:" + retList.size + "\n" +
                (if (!includeVariabilityFromHeaderFiles) " Features in CFile: " +
                    getFeaturesInCoveredExpressions.size + "\n" else "") +
                " found " + nodeExpressions.size + " NodeExpressions\n" +
                " found " + simpleAndNodes + " simpleAndNodes, " + simpleOrNodes +
                " simpleOrNodes and " + complexNodes + " complex nodes.\n")
    }




    /**
     * Optimzed version of the completeConfiguration method. Uses FeatureExpr.getSatisfiableAssignment
     * to need only one SAT call.
     * @param expr input feature expression
     * @param ff file features
     * @param model input feature model
     * @return
     */
    def completeConfiguration(expr: FeatureExpr, ff: FileFeatures, model: FeatureModel,
                              preferDisabledFeatures: Boolean = false):
    SimpleConfiguration = {
        expr.getSatisfiableAssignment(model, ff.features.toSet, preferDisabledFeatures) match {
            case Some(ret) => new SimpleConfiguration(ff, ret._1, ret._2)
            case None => null
        }
    }

    /**
     * This method generates and tests random configurations:
     * 1. load feature model fm
     * 2. create configuration based on selection/deselection of all features
     * 3. check whether configuration is satisfiable; increase tested
     * 3.1 if satisfiable increase valid
     * 4. repeat until timeout or after a number of tested configurations
     * 5. return pair (valid, tested)
     * @param fm input feature model (used for parsing; smaller than fmts)
     * @param fmts input feature model (used for type checking); this model can be null,
     *             since only Linux has both models
     * @return
     */
    def generateAndTestRandomConfigurations(fm: FeatureModel, fmts: FeatureModel): (Long, Long) = {
        val rndGen: Random = new Random(42)

        var tested: Long = 0
        var valid: Long = 0

        val featureMap = (if (fmts == null) fm else fmts).asInstanceOf[SATFeatureModel].variables
        val startTime = System.currentTimeMillis()
        val configsUpperBound = math.pow(2, featureMap.size)
        val numTestsMax = math.min(Int.MaxValue, configsUpperBound)

        println("start report:")
        println("|features|  : " + featureMap.size)
        println("2^|features|: " + configsUpperBound)

        while (tested < numTestsMax) {
            var enabledSet: Set[SingleFeatureExpr] = Set()
            var disabledSet: Set[SingleFeatureExpr] = Set()

            enabledSet = Set()
            disabledSet = Set()

            for ((id, key) <- featureMap) {
                if (rndGen.nextBoolean()) enabledSet += SATFeatureExprFactory.createDefinedExternal(id)
                else disabledSet += SATFeatureExprFactory.createDefinedExternal(id)
            }
            // check first fm since it is smaller the check should take less time
            // and if fexpr is not valid for fm it is not valid for fmts either
            val fexpr = SATFeatureExprFactory.createFeatureExprFast(enabledSet, disabledSet)
            if (fexpr.isSatisfiable(fm)) {
                println("fexpr maybe valid! #" + tested + " tested!")
                if (fmts != null && fexpr.isSatisfiable(fmts))
                    valid += 1
            }
            tested += 1
            if (tested % 1000 == 0) {
                println("intermediate report:")
                println("elapsed time (sec): " + ((System.currentTimeMillis() - startTime) / 1000))
                println("tested configs: " + tested + " (" + ((tested * 100) / configsUpperBound) +
                    "% of all possible)")
                println("valid configs: " + valid)
            }
        }
        println("end-of-method:")
        println("elapsed time (sec): " + ((System.currentTimeMillis() - startTime) / 1000))
        println("tested configs: " + tested + " (" + ((tested * 100) / configsUpperBound) + "% of all possible)")
        println("valid configs: " + valid)
        println("|features|: " + featureMap.size)
        println("2^|features|: " + configsUpperBound)
        (valid, tested)
    }
}