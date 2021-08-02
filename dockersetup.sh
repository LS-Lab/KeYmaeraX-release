#!/bin/bash

mkdir -p Licensing

docker rm -f kyx
docker build -t keymaerax .
docker create -it -v $PWD/Licensing:/root/.WolframEngine/Licensing -p 8090:8090 --name kyx keymaerax bash
docker start kyx

# activate Wolfram Engine, comment out to re-initialize the container when Wolfram Engine was activated earlier already
docker exec -it kyx wolframscript "-activate"

# uncomment below to run with locally compiled jar
# sbt clean assembly
# docker cp ./keymaerax-webui/target/scala-2.12/KeYmaeraX-Web-assembly-*.jar kyx:/root/keymaerax.jar

# find Wolfram Engine version
docker exec -it -w /root/ kyx bash -c "ls /usr/local/Wolfram/WolframEngine > weversion.txt"

# initialize .keymaerax directory with Z3
docker exec -it -w /root/ kyx bash -c 'export LD_PRELOAD=/lib/x86_64-linux-gnu/libuuid.so.1.3.0;java -da -jar keymaerax.jar -launch -setup'

# modify configuration
docker exec -it -w /root/ kyx bash -c 'echo "WOLFRAMENGINE_LINK_NAME = /usr/local/Wolfram/WolframEngine/$(<weversion.txt)/Executables/MathKernel" >> .keymaerax/keymaerax.conf'
docker exec -it -w /root/ kyx bash -c 'echo "WOLFRAMENGINE_JLINK_LIB_DIR = /usr/local/Wolfram/WolframEngine/$(<weversion.txt)/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64" >> .keymaerax/keymaerax.conf'
docker exec -it -w /root/ kyx bash -c 'echo "WOLFRAMENGINE_TCPIP = false" >> .keymaerax/keymaerax.conf'
docker exec -it -w /root/ kyx sed -i "s/QE_TOOL = z3/QE_TOOL = wolframengine/g" .keymaerax/keymaerax.conf
docker inspect -f '{{ .NetworkSettings.IPAddress }}' kyx > dockerip.txt
docker exec -it -w /root/ kyx sed -i "s/HOST = 127.0.0.1/HOST = $(<dockerip.txt)/g" .keymaerax/keymaerax.conf

docker stop kyx
