package de.fosd.typechef.crewrite

import org.kiama.rewriting.Rewriter._

import de.fosd.typechef.parser.c._
import de.fosd.typechef.typesystem.UseDeclMap
import de.fosd.typechef.featureexpr.{FeatureExpr, FeatureModel}

// implements a simple analysis of freeing memory that was not dynamically allocated
// https://www.securecoding.cert.org/confluence/display/seccode/MEM34-C.+Only+free+memory+allocated+dynamically
//
// major limitations:
//   - we use intraprocedural control flow (IntraCFG) which
//     is a conservative analysis for program flow
//     so the analysis will likely produce a lot
//     of false positives
class XFree(env: ASTEnv, udm: UseDeclMap, fm: FeatureModel, casestudy: String) extends MonotoneFW[Id](env, udm, fm) with IntraCFG with CFGHelper with ASTNavigation with UsedDefinedDeclaredVariables {

    val freecalls = {
        if (casestudy == "linux") List("free", "kfree")
        else if (casestudy == "openssl") List("free", "CRYPTO_free")
        else List("free")
    }

    val memcalls = {
        if (casestudy == "linux") List("malloc", "kmalloc")
        else List("malloc")
    }

    // get all declared variables without an initialization
    def gen(a: AST): Map[FeatureExpr, Set[Id]] = {
        var res = Set[Id]()
        val variables = manytd(query {
            case InitDeclaratorI(AtomicNamedDeclarator(_, i, _), _, None) => res += i
            case InitDeclaratorI(AtomicNamedDeclarator(_, i, _), _, Some(initializer)) => {
                val pmallocs = filterASTElems[PostfixExpr](initializer)

                if (pmallocs.isEmpty) res += i
                else pmallocs.map(pe => {
                    pe match {
                        case PostfixExpr(m@Id(_), _) if (memcalls.contains(m.name)) =>
                            if (env.featureExpr(m) equivalentTo (env.featureExpr(i))) {}
                            else {
                                res += i
                            }
                    }
                })
            }
        })

        variables(a)
        addAnnotation2ResultSet(res)
    }

    // get variables that get an assignment with malloc
    def kill(a: AST): Map[FeatureExpr, Set[Id]] = {
        var res = Set[Id]()
        val assignments = manytd(query {
            case AssignExpr(target@Id(_), "=", source) => {
                val pmallocs = filterASTElems[PostfixExpr](source)

                pmallocs.map(pe => {
                    pe match {
                        case PostfixExpr(i@Id(_), _) if (memcalls.contains(i.name)) =>
                            if (env.featureExpr(i) equivalentTo (env.featureExpr(target))) {}
                            else {res += target}
                        case _ =>
                    }
                })
            }
        })

        assignments(a)
        addAnnotation2ResultSet(res)
    }

    // returns a list of Ids with names of variables that a freed
    // by call to free or realloc
    // using the terminology of liveness we return pointers that have that are in use
    def freedVariables(a: AST) = {

        var res = Set[Id]()

        // add a free target independent of & and *
        def addFreeTarget(e: Expr) {
            // free(a->b)
            val sp = filterAllASTElems[PointerPostfixSuffix](e)
            if (!sp.isEmpty) {
                for (spe <- filterAllASTElems[Id](sp.reverse.head))
                    res += spe

                return
            }

            // free(a[b])
            val ap = filterAllASTElems[ArrayAccess](e)
            if (!ap.isEmpty) {
                for (ape <- filterAllASTElems[PostfixExpr](e)) {
                    ape match {
                        case PostfixExpr(i@Id(_), ArrayAccess(_)) => res += i
                        case _ =>
                    }
                }

                return
            }

            // free(a)
            val fp = filterAllASTElems[Id](e)

            for (ni <- fp)
                res += ni
        }


        val freedvariables = manytd(query {
            // realloc(*ptr, size) is used for reallocation of memory
            case PostfixExpr(i@Id("realloc"), FunctionCall(l)) => {
                // realloc has two arguments but more than two elements may be passed to
                // the function. this is the case when elements form alternative groups, such as,
                // realloc(#ifdef A aptr #else naptr endif, ...)
                // so we check from the start whether parameter list elements
                // form alternative groups. if so we look for Ids in each
                // of the alternative elements. if not we stop, because then we encounter
                // a size element.
                var actx = List(l.exprs.head.feature)
                var finished = false

                for (ni <- filterAllASTElems[Id](l.exprs.head.entry))
                    res += ni

                for (ce <- l.exprs.tail) {
                    if (actx.reduce(_ or _) isTautology (fm))
                        finished = true

                    if (!finished && actx.forall(_ and ce.feature isContradiction (fm))) {
                        for (ni <- filterAllASTElems[Id](ce.entry))
                            res += ni
                        actx ::= ce.feature
                    } else {
                        finished = true
                    }

                }

            }
            // calls to free or to derivatives of free
            case PostfixExpr(Id(n), FunctionCall(l)) => {

                if (freecalls.contains(n)) {
                    for (e <- l.exprs) {
                        addFreeTarget(e.entry)
                    }
                }
            }

        })

        freedvariables(a)
        addAnnotation2ResultSet(res)
    }

    // flow functions (flow => succ and flowR => pred)
    protected def flow(e: AST) = flowPred(e)

    protected def unionio(e: AST) = incached(e)
    protected def genkillio(e: AST) = outcached(e)

    // we create fresh T elements (here Id) using a counter
    private var freshTctr = 0

    private def getFreshCtr: Int = {
        freshTctr = freshTctr + 1
        freshTctr
    }

    def t2T(i: Id) = Id(getFreshCtr + "_" + i.name)

    def t2SetT(i: Id) = {
        var freshidset = Set[Id]()

        if (udm.containsKey(i)) {
            for (vi <- udm.get(i)) {
                freshidset = freshidset.+(createFresh(vi))
            }
            freshidset
        } else {
            Set(addFreshT(i))
        }
    }
}