package de.fosd.typechef.typesystem.generator

/**
  * Created by ckaestne on 11/14/2015.
  */
object GenAll extends App {
    AddExprTestGenerator.main(args)
    RedeclTestGenerator.main(args)
    CoerceTestGenerator.main(args)
    CastTestGenerator.main(args)
}
