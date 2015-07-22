#!/bin/sh
echo Please run the following command first
echo ln -s keymaerax-webui/target/scala-2.10/KeYmaeraX-assembly-0.1-SNAPSHOT.jar KeYmaeraX.jar
java -Xss20M -jar KeYmaeraX.jar -modelplex keymaerax-webui/src/test/resources//examples/casestudies/acasx/nodelay.key -vars dhf,w,ao -out nodelay.mx
