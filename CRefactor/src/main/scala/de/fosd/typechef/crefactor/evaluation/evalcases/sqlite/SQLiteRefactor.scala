package de.fosd.typechef.crefactor.evaluation.evalcases.sqlite

import de.fosd.typechef.crefactor.evaluation.sqlite.SQLiteEvaluation
import de.fosd.typechef.crefactor.evaluation.{StatsCan, Refactoring, Refactor}
import de.fosd.typechef.parser.c.TranslationUnit
import de.fosd.typechef.featureexpr.FeatureModel
import java.io.{FileWriter, File}
import de.fosd.typechef.crefactor.Morpheus
import de.fosd.typechef.crefactor.evaluation.evalcases.sqlite.refactor.{Extract, Inline, Rename}
import de.fosd.typechef.crefactor.evaluation.util.StopClock
import de.fosd.typechef.crefactor.evaluation.Stats._
import de.fosd.typechef.crefactor.backend.CModuleInterface


object SQLiteRefactor extends SQLiteEvaluation with Refactor {
    def rename(tunit: TranslationUnit, fm: FeatureModel, file: String, linkInterface: CModuleInterface) =
        evaluate(tunit, fm, file, linkInterface, Rename)
    def inline(tunit: TranslationUnit, fm: FeatureModel, file: String, linkInterface: CModuleInterface) =
        evaluate(tunit, fm, file, linkInterface, Inline)
    def extract(tunit: TranslationUnit, fm: FeatureModel, file: String, linkInterface: CModuleInterface) =
        evaluate(tunit, fm, file, linkInterface, Extract)

    private def evaluate(tunit: TranslationUnit, fm: FeatureModel, file: String, linkInterface: CModuleInterface, r: Refactoring): Unit = {
        println("+++ File to engine: " + getFileName(file) + " +++")
        val resultDir = getResultDir(file)
        val path = resultDir.getCanonicalPath + File.separatorChar
        val resDir = new File(path)
        resDir.mkdirs()
        if (tunit == null) println("+++ AST is null! +++")
        else if (blackListFiles.exists(getFileName(file).equalsIgnoreCase)) println("+++ File is blacklisted and cannot be build +++")
        else {
            try {
                val morpheus = new Morpheus(tunit, fm, linkInterface, file)
                // reset test environment
                runScript("./clean.sh", sourcePath)
                val result = r.refactor(morpheus)
                if (result._1) {
                    write(result._2, morpheus.getFile)
                    val time = new StopClock
                    StatsCan.addStat(file, AffectedFeatures, result._2)
                    SQLiteVerification.verify(morpheus.getFile, morpheus.getFM, "first")
                    runScript("./clean.sh", sourcePath)
                    StatsCan.addStat(file, TestingTime, time.getTime)
                } else writeError("Could not engine file.", path)
                val writer = new FileWriter(path + ".stats")
                StatsCan.write(writer)
                writer.flush()
                writer.close()
            } catch {
                case e: Exception => {
                    e.printStackTrace()
                    writeException(e.getCause.toString + "\n" + e.getMessage + "\n" + e.getStackTrace.mkString("\n"), resDir.getCanonicalPath)
                }
            }
        }
    }
}
