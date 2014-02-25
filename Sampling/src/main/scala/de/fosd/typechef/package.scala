package de.fosd

import de.fosd.typechef.FamilyBasedVsSampleBased.SimpleConfiguration

package object typechef {
    type Task = Pair[String, List[SimpleConfiguration]]
}
