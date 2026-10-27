# KeYmaera X JLink Stub

This sbt module provides a compile- and runtime-only **stub** of the
`com.wolfram.jlink` API (Mathematica's J/Link).

## Why it exists

KeYmaera X's source code references `com.wolfram.jlink.{Expr, KernelLink, ...}`
classes. Building and running KeYmaera X therefore normally requires the real
`JLink.jar` shipped with a Mathematica or Wolfram Engine installation
(property `mathematica.jlink.path` in `local.properties`).

If no real `JLink.jar` is findable, this stub module is used instead, so that
KeYmaera X can be built **and run without a Mathematica/Wolfram Engine
installation** — using Z3 as the arithmetic backend.

## Runtime behavior

The stub classes are inert: constructing `Expr` objects works (so code paths
that merely build or inspect them keep working), but no real Mathematica
kernel is ever started. KeYmaera X runs fully with its Z3-based tooling in
this configuration; Mathematica-only features are unavailable.

## Selecting the stub vs. the real JLink

Selection happens automatically in `build.sbt`:

- If `local.properties` contains a `mathematica.jlink.path` pointing to an
  existing `JLink.jar`, that jar is used as an unmanaged dependency
  (normal Mathematica-enabled build).
- Otherwise (missing `local.properties`, missing property, or nonexistent
  file), the build falls back to this stub module.

## Contents

Maintained API surface (mirrors exactly what KeYmaera X's main sources use):

- `com.wolfram.jlink.Expr` (+ `ExprFormatException`)
- `com.wolfram.jlink.KernelLink`
- `com.wolfram.jlink.MathLinkException`
- `com.wolfram.jlink.MathLinkFactory`
