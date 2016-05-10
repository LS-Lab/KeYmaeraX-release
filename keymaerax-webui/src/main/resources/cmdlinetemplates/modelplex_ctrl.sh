#!/bin/sh
java -Xss20M -jar keymaerax-4.2b1.jar -mathkernel /path/to/MathKernel -jlink /path/to/jlinkNativeLib -modelplex model.kyx -kind ctrl -out monitor.mx