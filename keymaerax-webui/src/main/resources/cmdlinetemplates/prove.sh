#!/bin/sh
java -Xss20M -jar keymaerax-4.2b1.jar -mathkernel /path/to/MathKernel -jlink /path/to/jlinkNativeLib -prove model.kyx -tactic tactic.scala -out modelproof.kyx.proof