package de.fosd.typechef.crefactor.evaluation.busybox_1_18_5.refactor

import java.io.File
import de.fosd.typechef.parser.c._
import de.fosd.typechef.featureexpr.{FeatureExprFactory, FeatureModel, FeatureExpr}
import de.fosd.typechef.crefactor.Morpheus
import de.fosd.typechef.crefactor.backend.refactor.CRenameIdentifier
import de.fosd.typechef.parser.c.Id
import de.fosd.typechef.parser.c.FunctionDef
import de.fosd.typechef.parser.c.Declaration
import de.fosd.typechef.crefactor.evaluation.busybox_1_18_5.{BusyBoxVerification, PrepareASTforVerification, BusyBoxRefactor}
import de.fosd.typechef.crefactor.evaluation.util.TimeMeasurement

object Rename extends BusyBoxRefactor {

    private val REFACTOR_NAME = "refactoredID"

    def runRefactor(morpheus: Morpheus, stats: List[Any], bb_file: File, fm: FeatureModel, run: Int, max: Int, lastResult: Boolean = true): Boolean = {
        if (run >= max) return lastResult
        val result = applyRefactor(morpheus, stats)
        if (result._1 == null) println("AST IS NULL!")
        if (result._2) {
            val dir = getResultDir(bb_file.getCanonicalPath, run)
            val path = dir.getCanonicalPath + File.separatorChar + getFileName(bb_file.getCanonicalPath)
            writeAST(result._1, path)
            writePlainAST(result._1, path + ".ast")
            PrepareASTforVerification.makeConfigs(result._1, morpheus.getFeatureModel, bb_file.getCanonicalPath, result._3, run)
        }

        val verify = BusyBoxVerification.verify(bb_file, run, fm)
        var stat2 = result._4
        stat2 = stat2.::(result._2 + "\n" + verify)
        writeStats(stat2, bb_file.getCanonicalPath, run)
        verify && runRefactor(morpheus, stats, bb_file, fm, run + 1, MAX)
    }

    private def applyRefactor(morpheus: Morpheus, stat: List[Any]): (AST, Boolean, List[FeatureExpr], List[Any]) = {
        def getVariableIdToRename: (Id, Int, List[FeatureExpr]) = {
            def isValidId(id: Id, morpheus: Morpheus): Boolean = {
                val isFunc = findPriorASTElem[FunctionDef](id, morpheus.getASTEnv) match {
                    case None => false
                    case entry => entry.get.declarator.getId.eq(id)
                }
                val isExternalFunc = findPriorASTElem[Declaration](id, morpheus.getASTEnv) match {
                    case None => false
                    case entry => entry.get.declSpecs.exists(spec => spec.entry match {
                        case ExternSpecifier() => true
                        case _ => false
                    })
                }
                !(id.name.equals("main") || isFunc || isExternalFunc)
            }

            val ids = morpheus.getUseDeclMap.values().toArray(Array[List[Id]]()).par.foldLeft(List[Id]())((list, entry) => list ::: entry)

            val writeAbleIds = ids.filter(id =>
                CRenameIdentifier.getAllConnectedIdentifier(id, morpheus.getDeclUseMap, morpheus.getUseDeclMap).par.forall(i =>
                    new File(i.getFile.get.replaceFirst("file ", "")).canWrite && isValidId(i, morpheus)))

            val variableIds = writeAbleIds.par.filter(id => {
                val associatedIds = CRenameIdentifier.getAllConnectedIdentifier(id, morpheus.getDeclUseMap, morpheus.getUseDeclMap)
                val features = associatedIds.map(x => morpheus.getASTEnv.featureExpr(x))
                !(features.distinct.length == 1 && features.distinct.contains(FeatureExprFactory.True))
            })

            val id = if (!variableIds.isEmpty) variableIds.apply((math.random * variableIds.size).toInt) else writeAbleIds.apply((math.random * writeAbleIds.size).toInt)
            val associatedIds = CRenameIdentifier.getAllConnectedIdentifier(id, morpheus.getDeclUseMap, morpheus.getUseDeclMap)
            (id, associatedIds.length, associatedIds.map(morpheus.getASTEnv.featureExpr(_)).distinct)
        }

        val toRename = getVariableIdToRename
        val id = toRename._1
        val features = toRename._3

        val startRenaming = new TimeMeasurement
        val refactored = CRenameIdentifier.rename(id, REFACTOR_NAME, morpheus)
        val renamingTime = startRenaming.getTime
        var stats = stat.::(renamingTime)
        stats = stats.::(id)
        stats = stats.::(toRename._2)
        stats = stats.::(features)

        val morpheus_ref = new Morpheus(refactored, morpheus.getFeatureModel)

        val originAmount = analsyeDeclUse(morpheus.getDeclUseMap).sorted
        val newAmount = analsyeDeclUse(morpheus_ref.getDeclUseMap).sorted

        (refactored, originAmount == newAmount, features, stats)
    }
}