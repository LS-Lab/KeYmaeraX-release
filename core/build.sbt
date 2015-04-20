name := "KeYmaeraX Core"

version := "4.0a1"

scalaVersion := "2.10.4"

////////////////////////////////////////////////////////////////////////////////
// Mathematica Interop
////////////////////////////////////////////////////////////////////////////////
// >= 10.0.2
unmanagedJars in Compile += file("/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/JLink.jar")

// <= 10.0.1
unmanagedJars in Compile += file("/Applications/Mathematica.app/SystemFiles/Links/JLink/JLink.jar")

// Linux
unmanagedJars in Compile += file("/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink/JLink.jar")

unmanagedJars in Compile += file("/usr/local/Wolfram/Mathematica/10.0/SystemFiles/Links/JLink/JLink.jar")