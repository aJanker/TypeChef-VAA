package de.fosd.typechef.featureexpr

import java.io.File
import java.util
import java.util.Collections

import scala.collection.mutable
import scala.collection.mutable.HashMap
import scala.io.Source


object FeatureToSimplifyModelMap {

    private lazy val featureToSimpleModelMap: mutable.HashMap[String, List[FeatureExpr]] = new HashMap[String, List[FeatureExpr]]
    private lazy val itemIdentifier : String = "#item "

    def fill(simplifyFM : File) : mutable.HashMap[String, List[FeatureExpr]] = {
        if (featureToSimpleModelMap.nonEmpty) clear()

        var currentName : String = null
        val parser = new FeatureExprParser()

        for (line <- Source.fromFile(simplifyFM).getLines) {
            if (line.startsWith(itemIdentifier)) currentName = line.substring(itemIdentifier.length)
            else add(currentName, parser.parse(line))
        }

        featureToSimpleModelMap
    }

    def get() : mutable.HashMap[String, List[FeatureExpr]] = featureToSimpleModelMap

    def clear() = featureToSimpleModelMap.clear

    private def add(name: String, fExpr : FeatureExpr) =
        featureToSimpleModelMap.get(name) match {
            case Some(l) => featureToSimpleModelMap + (name -> (fExpr :: l))
            case _ => featureToSimpleModelMap + (name -> List(fExpr))
        }

}


