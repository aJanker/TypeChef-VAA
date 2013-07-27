package de.fosd.typechef.crefactor.evaluation.busybox_1_18_5.refactor

import de.fosd.typechef.crefactor.Morpheus
import java.io.File
import de.fosd.typechef.featureexpr.FeatureModel
import de.fosd.typechef.crefactor.evaluation.busybox_1_18_5.BusyBoxRefactor

object Inline extends BusyBoxRefactor {
    def runRefactor(morpheus: Morpheus, stats: List[Any], bb_file: File, fm: FeatureModel, run: Int, max: Int, lastResult: Boolean = true): Boolean = {
        lastResult
    }
}
