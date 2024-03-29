/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.hydra.{PlainResponse, ReadRequest, Request, Response}
import spray.json.{JsArray, JsObject, JsString}

import scala.collection.immutable.{List, Nil, StringOps}
import scala.io.Source

class LicensesRequest() extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val reader = this.getClass.getResourceAsStream("/license/tools_licenses")
    // StringOps for JDK 11 compatibility
    val lines = (Source.fromInputStream(reader).mkString: StringOps).lines.toList
    val header = lines.head
    val licenseStartPos = header.indexOf("License")
    val licenses = lines.tail.tail.map(l => l.splitAt(licenseStartPos)).map({ case (tool, license) =>
      JsObject(
        "tool" -> JsString(tool.trim),
        "license" -> JsString(license.trim)
      )
    })
    new PlainResponse("licenses" -> JsArray(licenses: _*)) :: Nil
  }
}
