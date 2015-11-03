package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, Blah}
import org.scalatest.{FlatSpec, Matchers}

/**
  * Created by nfulton on 11/3/15.
  */
class CombinatorSemanticsTest extends FlatSpec with Matchers {
  "blah" should "blah" in {
    Blah.asdf.asInstanceOf[BelleProvable].p.prettyString
  }
}
