package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase

/**
  * Created by smitsch on 6/14/17.
  */
class UIKeYmaeraXPrettyPrinterTests extends TacticTestBase {

  "Diamond modality" should "be printed correctly" in {
    UIKeYmaeraXPrettyPrinter("0", plainText=false)("<x:=x+1;>x=1".asFormula) should
      (include ("""<span class="k4-mod-open">&lt;""") and not include """<span class="k4-mod-open">&#8743;lt;"""
        and include ("""<span class="k4-mod-close">&gt;""") and not include """<span class="k4-mod-close">&#8743;gt;""")
  }
}
