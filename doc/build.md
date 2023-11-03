# Build instructions

This is a guide to building the various artifacts this repository provides.

You will need the following tools for most artifacts:

- JDK 8
- [sbt](https://www.scala-sbt.org/)
- [Mathematica](https://www.wolfram.com/mathematica/)
  or the [Wolfram Engine](https://www.wolfram.com/engine/)

## KeYmaera X with web UI

Copy the `default.properties` file to `local.properties`
and edit `mathematica.jlink.path` to point to the `JLink.jar` from your Mathematica or Wolfram Engine installation.
If you installed Mathematica at the
[default path](https://reference.wolfram.com/language/tutorial/WolframSystemFileOrganization.html),
the `JLink.jar` file is located at

- `/usr/local/Wolfram/Mathematica/13.0/SystemFiles/Links/JLink/JLink.jar` on Linux
- `/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/JLink.jar` on macOS
- `C:\Program Files\Wolfram Research\Mathematica\13.0\SystemFiles\Links\Jlink\Jlink.jar` on Windows

Finally, run `sbt --mem 2048 clean assembly` in the project root to create `keymaerax.jar`.

## Documentation

Run `sbt unidoc` in the project root.
This will generate offline documentation at
[`target/scala-2.12/unidoc/index.html`](target/scala-2.12/unidoc/index.html).
