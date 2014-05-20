package de.fosd.typechef

import de.fosd.typechef.parser.c._
import parser.TokenReader
import de.fosd.typechef.parser.c.TranslationUnit
import de.fosd.typechef.parser.c.CTypeContext
import de.fosd.typechef.options.OptionException
import java.io.File

object Sampling extends EnforceTreeHelper {
    def main(args: Array[String]) {
        // load options
        val opt = new FamilyBasedVsSampleBasedOptions()
        try {
            try {
                opt.parseOptions(args)
            } catch {
                case o: OptionException => if (!opt.isPrintVersion) throw o
            }

            if (opt.isPrintVersion) {
                var version = "development build"
                try {
                    val cl = Class.forName("de.fosd.typechef.Version")
                    version = "version " + cl.newInstance().asInstanceOf[VersionInfo].getVersion
                } catch {
                    case e: ClassNotFoundException =>
                }

                println("TypeChef " + version)
                return
            }
        }

        catch {
            case o: OptionException =>
                println("Invocation error: " + o.getMessage)
                println("use parameter --help for more information.")
                return
        }

        processFile(opt)
    }

    def processFile(opt: FamilyBasedVsSampleBasedOptions) {
        val errorXML = new ErrorXML(opt.getErrorXMLFile)
        opt.setRenderParserError(errorXML.renderParserError)

        val smallFM = opt.getSmallFeatureModel.and(opt.getLocalFeatureModel).and(opt.getFilePresenceCondition)
        opt.setSmallFeatureModel(smallFM)
        val fullFM = opt.getFullFeatureModel.and(opt.getLocalFeatureModel).and(opt.getFilePresenceCondition)
        if (!opt.getFilePresenceCondition.isSatisfiable(smallFM)) {
            println("file has contradictory presence condition. existing.")
            return
        }

        var ast: TranslationUnit = null
        if (opt.reuseAST && opt.parse && new File(opt.getSerializedTUnitFilename).exists()) {
            println("loading AST.")
            try {
                ast = Frontend.loadSerializedAST(opt.getSerializedTUnitFilename)

            } catch {
                case e: Throwable => println(e.getMessage); ast = null
            }
            if (ast == null)
                println("... failed reading AST\n")
        } else {
            new lexer.LexerFrontend().run(opt, opt.parse)
            val in = lex(opt)
            val parserMain = new ParserMain(new CParser(smallFM))
            ast = parserMain.parserMain(in, opt, fullFM)

            if (ast != null && opt.serializeAST) {
                Frontend.serializeAST(ast, opt.getSerializedTUnitFilename)
            }
        }

        ast = prepareAST[TranslationUnit](ast)

        if (ast != null && opt.analyze) {
            val treeast = prepareAST[TranslationUnit](ast)
            FamilyBasedVsSampleBased.typecheckProducts(fullFM, fullFM, treeast, opt, "")
        }
    }

    def lex(opt: FamilyBasedVsSampleBasedOptions): TokenReader[CToken, CTypeContext] = {
        val tokens = new lexer.LexerFrontend().run(opt, opt.parse)
        val in = CLexerAdapter.prepareTokens(tokens)
        in
    }
}
