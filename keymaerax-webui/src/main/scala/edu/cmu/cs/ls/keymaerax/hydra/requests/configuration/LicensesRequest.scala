/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.{PlainResponse, ReadRequest, Request, Response}
import edu.cmu.cs.ls.keymaerax.info.{FullCopyright, License, ShortCopyright, ThirdPartyLicenses}
import spray.json.JsString

class LicensesRequest extends Request with ReadRequest {
  override def resultingResponse(): Response = {
    new PlainResponse(
      "copyright" -> JsString(FullCopyright),
      "copyrightShort" -> JsString(ShortCopyright),
      "license" -> JsString(License),
      "licensesThirdParty" -> JsString(ThirdPartyLicenses),
    )
  }
}
