package de.fosd.typechef.crefactor.evaluation.evalcases.busybox_1_18_5

import de.fosd.typechef.crefactor.evaluation.{Refactoring, StatsJar, Refactor}
import de.fosd.typechef.parser.c.AST
import de.fosd.typechef.featureexpr.FeatureModel
import de.fosd.typechef.crefactor.Morpheus
import java.io.File
import de.fosd.typechef.crefactor.evaluation.busybox_1_18_5.linking.CLinking
import de.fosd.typechef.crefactor.evaluation.util.TimeMeasurement
import de.fosd.typechef.crefactor.evaluation.Stats._
import de.fosd.typechef.crefactor.evaluation.busybox_1_18_5.{PrepareASTforVerification, BusyBoxVerification, BusyBoxEvaluation}
import de.fosd.typechef.crefactor.evaluation.evalcases.busybox_1_18_5.refactor.{Rename, Inline, Extract}


object BusyBoxRefactor extends BusyBoxEvaluation with Refactor {

    def rename(ast: AST, fm: FeatureModel, file: String, linkInterface: CLinking) = evaluate(ast, fm, file, linkInterface, Rename)
    def extract(ast: AST, fm: FeatureModel, file: String, linkInterface: CLinking) = evaluate(ast, fm, file, linkInterface, Extract)
    def inline(ast: AST, fm: FeatureModel, file: String, linkInterface: CLinking) = evaluate(ast, fm, file, linkInterface, Inline)

    private def evaluate(ast: AST, fm: FeatureModel, file: String, linkInterface: CLinking, r: Refactoring): Unit = {
        println("+++ File to refactor: " + getFileName(file) + " +++")
        val resultDir = getResultDir(file)
        val path = resultDir.getCanonicalPath + File.separatorChar + getFileName(file)
        if (ast == null) println("+++ AST is null! +++")
        else if (blackListFiles.exists(getFileName(file).equalsIgnoreCase)) println("+++ File is blacklisted and cannot be build +++")
        else {
            try {
                val morpheus = new Morpheus(ast, fm, file)
                // reset test environment
                runScript("./cleanAndReset.sh", sourcePath)
                val result = r.refactor(morpheus, linkInterface)
                if (result._1) {
                    write(result._2, morpheus.getFile)
                    PrepareASTforVerification.makeConfigs(result._2, morpheus.getFeatureModel, morpheus.getFile, features)
                    val time = new TimeMeasurement
                    StatsJar.addStat(file, AffectedFeatures, result._2)
                    // run refactored first
                    BusyBoxVerification.verify(file, fm, "_ref")
                    runScript("./cleanAndReset.sh", sourcePath)
                    BusyBoxVerification.verify(file, fm, "_org")
                    runScript("./cleanAndReset.sh", sourcePath)
                    StatsJar.addStat(file, TestingTime, time.getTime)
                } else writeError("Could not refactor file.", path)
                StatsJar.write(path + ".stats")
            } catch {
                case e: Exception => {
                    e.printStackTrace
                    writeException(e.getCause.toString + "\n" + e.getMessage + "\n" + e.getStackTrace.mkString("\n"), new File(path).getCanonicalPath)
                }
            }
        }
    }
}