/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.info

import java.util.Locale

// TODO Convert to Scala 3 enum
sealed trait OsType
object OsType {
  case object Windows extends OsType
  case object Linux extends OsType
  case object MacOs extends OsType
  case object Unknown extends OsType
}

object Os {
  val Name: String = System.getProperty("os.name")
  val Version: String = System.getProperty("os.version")

  // Detect OS based on os.name.
  //
  // On Windows, os.name is set here:
  // https://github.com/openjdk/jdk/blob/97ee2ffb89257a37a178b70c8fee96a1d831deb6/src/java.base/windows/native/libjava/java_props_md.c#L414-L544
  // The name always starts with "Windows".
  //
  // On macOs, os.name is set here:
  // https://github.com/openjdk/jdk/blob/97ee2ffb89257a37a178b70c8fee96a1d831deb6/src/java.base/macosx/native/libjava/java_props_macosx.c#L234-L235
  // The name is always "Mac OS X".
  //
  // On Unix, os.name is set here:
  // https://github.com/openjdk/jdk/blob/97ee2ffb89257a37a178b70c8fee96a1d831deb6/src/java.base/unix/native/libjava/java_props_md.c#L410-L412
  // This calls uname(2), which will usually be "Linux".
  //
  // Finally, some links to OS checks in the JDK itself:
  // https://github.com/openjdk/jdk/blob/97ee2ffb89257a37a178b70c8fee96a1d831deb6/test/jdk/jdk/internal/util/OSTest.java#L58-L65
  // https://github.com/openjdk/jdk/blob/97ee2ffb89257a37a178b70c8fee96a1d831deb6/src/jdk.internal.le/share/classes/jdk/internal/org/jline/utils/OSUtils.java#L15-L22
  // https://github.com/openjdk/jdk/blob/97ee2ffb89257a37a178b70c8fee96a1d831deb6/src/jdk.hotspot.agent/share/classes/sun/jvm/hotspot/utilities/PlatformInfo.java#L32-L49
  val Type: OsType = Name.toLowerCase(Locale.ROOT) match {
    case name if name.startsWith("windows") => OsType.Windows
    case name if name.startsWith("linux") => OsType.Linux
    case name if name.startsWith("mac") => OsType.MacOs
    case _ => OsType.Unknown
  }
}
