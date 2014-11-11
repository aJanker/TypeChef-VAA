package de.fosd.typechef.crewrite

import de.fosd.typechef.featureexpr.FeatureExpr
import de.fosd.typechef.featureexpr.bdd.BDDFeatureExpr
import scala.collection.JavaConversions._
import java.util


object CAnalysisStatistics {

    def calculateInteractionDegree(fexpr: FeatureExpr): Int = {
        //interaction degree is the smallest number of variables that need to be set to reproduce the problem
        //we use the shortest path in a BDD as simple way of computing this

        //this does not always return the optimal solution, because variable ordering matters!
        //for example (fa and fb) or (fa andNot fb and fc) or (fa.not and fb) will produce a result 2 instead of 1

        //also does not consider the feature model

        val bdd = fexpr.asInstanceOf[BDDFeatureExpr]
        val allsat = bdd.leak().allsat().asInstanceOf[util.LinkedList[Array[Byte]]]

        if (allsat.isEmpty) 0
        else allsat.map(_.count(_ >= 0)).min
    }
}


