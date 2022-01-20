#!/bin/bash

# run example: dockersetup.sh -l path/to/matlab.lic

while getopts "l:" flag; do
    case $flag in
        l) license=${OPTARG};;
    esac
done

unameOut="$(uname -s)"
case "${unameOut}" in
    Linux*)     machine=Linux;;
    Darwin*)    machine=Mac;;
    *)          machine="UNKNOWN:${unameOut}"
esac
echo "Running on $machine"
case "$machine" in
  Linux)  ethif=eth0;;
  Mac)    ethif=en0;;
esac

user="$(whoami)"
macaddr="$(ifconfig $ethif | grep -o -E '([[:xdigit:]]{1,2}:){5}[[:xdigit:]]{1,2}')"
echo "Using Matlab license tied to:"
echo $user
echo $macaddr
echo $license

mkdir -p Licensing

# copy license file into current directory, Docker container has only access to local files
cp "$license" matlab.lic

docker rm -f kyx
docker build --build-arg LICENSE_FILE=matlab.lic --build-arg USER_NAME=$user -t keymaerax .
docker create --mac-address $macaddr -it -v $PWD/Licensing:/home/$user/.WolframEngine/Licensing -w /home/$user/ -p 8090:8090 --name kyx keymaerax bash
docker start kyx

# install MATLAB packages
install_packages_cmd="\"addpath /home/$user/mpm-3.1.0/;mpm install sedumi -u https://github.com/sqlp/sedumi.git -t v1.3.5;addpath(genpath('/home/$user/SOSTOOLS-4.01'));savepath;quit\""
docker exec -it kyx bash -c "matlab -r $install_packages_cmd"

# activate Wolfram Engine, comment out to re-initialize the container when Wolfram Engine was activated earlier already
docker exec -it kyx wolframscript "-activate"

# uncomment below to run with locally compiled jar
# sbt clean assembly
# docker cp ./keymaerax-webui/target/scala-2.12/KeYmaeraX-Web-assembly-*.jar kyx:/home/$user/keymaerax.jar

# find Wolfram Engine version
docker exec -it kyx bash -c "ls /usr/local/Wolfram/WolframEngine > weversion.txt"

# initialize .keymaerax directory with Z3
docker exec -it kyx bash -c 'export LD_PRELOAD=/lib/x86_64-linux-gnu/libuuid.so.1.3.0;java -da -jar keymaerax.jar -launch -setup'

# modify configuration
docker exec -it kyx bash -c 'echo "WOLFRAMENGINE_LINK_NAME = /usr/local/Wolfram/WolframEngine/$(<weversion.txt)/Executables/MathKernel" >> .keymaerax/keymaerax.conf'
docker exec -it kyx bash -c 'echo "WOLFRAMENGINE_JLINK_LIB_DIR = /usr/local/Wolfram/WolframEngine/$(<weversion.txt)/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64" >> .keymaerax/keymaerax.conf'
docker exec -it kyx bash -c 'echo "WOLFRAMENGINE_TCPIP = false" >> .keymaerax/keymaerax.conf'
docker exec -it kyx sed -i "s/QE_TOOL = z3/QE_TOOL = wolframengine/g" .keymaerax/keymaerax.conf
docker inspect -f '{{ .NetworkSettings.IPAddress }}' kyx > dockerip.txt
docker exec -it kyx sed -i "s/HOST = 127.0.0.1/HOST = $(<dockerip.txt)/g" .keymaerax/keymaerax.conf

# modify MATLink build file
docker exec -it kyx sed -i "s/-lML64i3/-lML64i4/g" .WolframEngine/Applications/MATLink/Engine/src/Makefile.lin64
docker exec -it kyx sed -i "s/CFLAGS = -Wall/CFLAGS = -Wall -DMX_COMPAT_32/g" .WolframEngine/Applications/MATLink/Engine/src/Makefile.lin64
docker exec -it kyx sed -i "s/DMLINTERFACE=3/DMLINTERFACE=4/g" .WolframEngine/Applications/MATLink/Engine/src/Makefile.lin64

docker stop kyx