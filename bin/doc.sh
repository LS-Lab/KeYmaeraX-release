#!/bin/bash
cd ../;
sbt unidoc;
scp -r target/scala-2.11/unidoc/ nathanfu@linux.gp.cs.cmu.edu:KeYmaeraXwww/scaladoc;
