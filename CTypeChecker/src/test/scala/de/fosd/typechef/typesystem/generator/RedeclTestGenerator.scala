package de.fosd.typechef.typesystem.generator

import java.io.File

/**
  * there are too many cases and the declaration isn't understandable.
  *
  * instead, we generate test cases and check with gcc whether those test
  * cases should fail or not (differential testing)
  *
  * we consider a number of possible changes in a test and use a sampling
  * strategy to cover many combinations of the changes
  */
object RedeclTestGenerator extends App with AbstractGenerator {

    override def configSpace = List(Opt(5), Opt(5), Opt(10), Opt(10), Opt(10), Opt(10), Opt(2), Opt(2), Opt(2))


    val STRUCT = 3
    val ASTRUCT = 4
    val DEF = 1
    val DECL = 0
    var VAR = 2

    def _firstDeclKind(c: Config): Int = c.vals(0)

    def _firstReturnType(c: Config): Int = c.vals(2)

    def _firstParamType(c: Config): Int = c.vals(3)

    def _secondDeclKind(c: Config): Int = c.vals(1)

    def _secondReturnType(c: Config): Int = c.vals(4)

    def _secondParamType(c: Config): Int = c.vals(5)

    def _extraParam(c: Config): Boolean = c.vals(6) > 0

    def _renamedParam(c: Config): Boolean = c.vals(7) > 0

    def _call(c: Config): Boolean = c.vals(8) > 0

    override def genTest(c: Config): String = {

        //first is [0 declaration, 1 definition, 2 variable, 3 struct, 4 abstract struct]
        //second is [declaration,definition,variable,struct]
        //return type is [0 int, 1 long, 2 double, 3 int[], 4 struct1, 5 struct2, 6 struct3, 7 const int, 8 volatile, 9 pointer]
        //extra parameter
        //renamed parameter
        //first parameter type [int, long, double, int[], struct1, struct2]
        //second parameter type [int, long, double, int[], struct1, struct2]
        //gets called (requires first or second as definition or declaration)

        val first = genDecl(_firstDeclKind(c), _firstReturnType(c), _firstParamType(c), false, false)
        val second = genDecl(_secondDeclKind(c), _secondReturnType(c), _secondParamType(c), _extraParam(c), _renamedParam(c))

        val main = "int main() {" + (if (_call(c)) "foo(0);" else "") + "}"

        var t = first + "\n                " + second + "\n                " + main

        if (t contains "struct S")
            t = "              struct S { int x; int y; };\n\n" + t
        if (t contains "struct T")
            t = "              struct T { int x; int y; int z; };\n\n" + t
        t
    }

    def genDecl(declKind: Int, returnType: Int, paramType: Int, extraParam: Boolean, renamedParam: Boolean) = {
        var result = ""
        if (declKind == STRUCT || declKind == ASTRUCT)
            result += "struct"
        else
            result += genType(returnType)
        result += " foo"
        if (declKind == DECL || declKind == DEF)
            result += "(" + genParam(paramType, extraParam, renamedParam).mkString(", ") + ")"
        if (declKind == STRUCT)
            result += "{" + genParam(paramType, extraParam, renamedParam).mkString("", "; ", ";") + "}"

        if (declKind == DEF) result += " {}"
        result += ";"
        result
    }

    def genParam(paramType: Int, extraParam: Boolean, renamed: Boolean): List[String] =
        List(genType(paramType) + " " + (if (renamed) "b" else "a")) ++
            (if (extraParam) List("int c") else Nil)

    def genType(t: Int) = t match {
        case 0 => "int"
        case 1 => "long"
        case 2 => "double"
        case 3 => "void"
        case 4 => "struct { int a; }"
        case 5 => "struct S"
        case 6 => "struct T"
        case 7 => "const int"
        case 8 => "volatile int"
        case 9 => "int*"
    }

    generate("GeneratedRedeclTests", pairwiseConfigs ++ pairwiseRandConfigs)

}
