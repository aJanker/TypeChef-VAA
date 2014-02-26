package de.fosd.typechef

import java.io.{FileWriter, File}
import de.fosd.typechef.featureexpr.{FeatureExprFactory, FeatureExpr, SingleFeatureExpr, FeatureModel}
import scala.io.Source
import java.util.regex.Pattern

object ConfigurationHandling {
    def loadConfigurationsFromCSVFile(csvFile: File, dimacsFile: File,
                                              ff: FileFeatures, fm: FeatureModel, fnamePrefix: String = ""):
    (List[SimpleConfiguration], String) = {
        var retList: List[SimpleConfiguration] = List()

        // determine the feature ids used by the sat solver from the dimacs file
        // dimacs format (c stands for comment) is "c 3779 AT76C50X_USB"
        // we have to pre-set index 0, so that the real indices start with 1
        var featureNamesTmp: List[String] = List("--dummy--")
        val featureMap: scala.collection.mutable.HashMap[String, SingleFeatureExpr] = new scala.collection.mutable.HashMap()
        var currentLine: Int = 1

        for (line: String <- Source.fromFile(dimacsFile).getLines().takeWhile(_.startsWith("c"))) {
            val lineElements: Array[String] = line.split(" ")
            if (!lineElements(1).endsWith("$")) {
                // feature indices ending with $ are artificial and can be ignored here
                assert(augmentString(lineElements(1)).toInt.equals(currentLine), "\"" + lineElements(1) + "\"" + " != " + currentLine)
                featureNamesTmp ::= lineElements(2)
            }
            currentLine += 1
        }

        // maintain a hashmap that maps feature names to corresponding feature expressions (SingleFeatureExpr)
        // we only store those features that occur in the file (keeps configuration small);
        // the rest is not important for the configuration;
        val featureNames: Array[String] = featureNamesTmp.reverse.toArray
        featureNamesTmp = null
        for (i <- 0.to(featureNames.length - 1)) {
            val searchResult = ff.features.find(_.feature.equals(fnamePrefix + featureNames(i)))
            if (searchResult.isDefined) {
                featureMap.update(featureNames(i), searchResult.get)
            }
        }

        // parse configurations
        // format is:
        // Feature\Product;0;..;N;       // number of Products (N+1)
        // FeatureA;-;X;....;            // exclusion of FeatureA in Product 0 and inclusion of FeatureA in Product 1
        // FeatureB                      // additional features
        // ...
        val csvLines = Source.fromFile(csvFile).getLines()
        val numProducts = csvLines.next().split(";").last.toInt + 1

        // create and initialize product configurations array
        val pconfigurations = new Array[(List[SingleFeatureExpr], List[SingleFeatureExpr])](numProducts)
        for (i <- 0 to numProducts - 1) {
            pconfigurations.update(i, (List(), List()))
        }

        // iterate over all lines with Features, determine the selection/deselection
        // in available products and add it to product configurations (true features / false features)
        while (csvLines.hasNext) {
            val featureLine = csvLines.next().split(";")

            for (i <- 1 to numProducts) {
                if (featureMap.contains(featureLine(0))) {
                    var product = pconfigurations(i - 1)
                    if (featureLine(i) == "X") {
                        product = product.copy(_1 = featureMap(featureLine(0)) :: product._1)
                    } else {
                        product = product.copy(_2 = featureMap(featureLine(0)) :: product._2)
                    }
                    pconfigurations.update(i - 1, product)
                }
            }
        }

        // create a single configuration from the true features and false features list
        for (i <- 0 to pconfigurations.length - 1) {
            val config = new SimpleConfiguration(ff, pconfigurations(i)._1, pconfigurations(i)._2)

            // need to check the configuration here again.
            if (!config.toFeatureExpr.getSatisfiableAssignment(fm, ff.features.toSet, 1 == 1).isDefined) {
                println("no satisfiable solution for product (" + i + "): " + csvFile)
            } else {
                retList ::= config
            }
        }

        (retList, "Generated Configs: " + retList.size + "\n")
    }

    def loadConfigurationFromKconfigFile(ff: FileFeatures, fm: FeatureModel,
                                         file: File): (List[SimpleConfiguration], String) = {
        val features = ff.features
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
                val name = "CONFIG_" + matcher.group(1)
                val feature = FeatureExprFactory.createDefinedExternal(name)
                var fileExTmp = fileEx.and(feature)
                if (correctFeatureModelIncompatibility) {
                    val isSat = fileExTmp.isSatisfiable(fm)
                    println(name + " " + (if (isSat) "sat" else "!sat"))
                    if (!isSat) {
                        fileExTmp = fileEx.andNot(feature)
                        println("disabling feature " + feature)
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
                    val name = "CONFIG_" + matcher.group(1)
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
                }
            }
        }
        println("features mentioned in c-file but not in config: ")
        for (x <- features.filterNot((trueFeatures ++ falseFeatures).contains)) {
            println(x.feature)
        }
        if (correctFeatureModelIncompatibility) {
            // save corrected file
            val fw = new FileWriter(new File(file.getParentFile, file.getName + "_corrected"))
            fw.write("# configFile written by typechef, based on " + file.getAbsoluteFile)
            fw.write("# ignored " + ignoredFeatures + " features of " + totalFeatures + " features")
            fw.write("# changed assignment for " + changedAssignment + " features of " +
                totalFeatures + " features")
            for (feature <- trueFeatures)
                fw.append(feature.feature + "=y\n")
            fw.close()
        }
        val interestingTrueFeatures = trueFeatures.filter(features.contains(_)).toList
        val interestingFalseFeatures = falseFeatures.filter(features.contains(_)).toList

        fileEx.getSatisfiableAssignment(fm, features.toSet, 1 == 1) match {
            case None => println("configuration not satisfiable"); return (List(), "")
            case Some((en, dis)) => return (List(new SimpleConfiguration(ff, en, dis)), "")
        }
        (List(new SimpleConfiguration(ff, interestingTrueFeatures, interestingFalseFeatures)), "")
    }

}
