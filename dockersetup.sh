#!/bin/bash

# The script can be invoked with -u, -l, and -m options

# -u USERNAME specifies the username to be used in the Docker image (which must be tied to your MATLAB license)
# If not specified, the script will try to use your current username

# -m MAC_ADDRESS specifies the MAC address (which must be tied to your MATLAB license)
# If not specified, the script will try to guess a default address

# -l path/to/matlab.lic specifies the full path to the MATLAB network license
# The username and MAC address above must be tied to your MATLAB license

# run example (with MATLAB license tied to current user):
# dockersetup.sh -l path/to/matlab.lic -m MAC_ADDRESS

# run example (without MATLAB license):
# dockersetup.sh -m MAC_ADDRESS

set -e

while getopts "l:m:u:" flag; do
    case $flag in
        l) license=${OPTARG};;
        m) macaddr=${OPTARG};;
        u) user=${OPTARG};;
    esac
done

unameOut="$(uname -s)"
case "${unameOut}" in
    Linux*)     machine=Linux;;
    Darwin*)    machine=Mac;;
    # *)          machine="UNKNOWN:${unameOut}"
esac
echo "Running on $machine"
case "$machine" in
  Linux)  ethif=eth0;;
  Mac)    ethif=en0;;
esac


if [ -z "$user" ]
then
  user="$(whoami)"
  if [ -z "$user" ]
  then
    echo "Failed to detect \$user for setup and licenses. Provide username with -u."
    exit 1
  fi
fi

if [ -z "$macaddr" ]
then
  macaddr="$(ifconfig $ethif | grep -o -E '([[:xdigit:]]{1,2}:){5}[[:xdigit:]]{1,2}')"
  if [ -z "$macaddr" ]
  then
    echo "Failed to detect \$macaddr for setup and licenses. Provide MAC address with -m."
    exit 1
  fi
fi

if [ -z "$license" ]
then
  echo "WARNING: MATLAB license path is empty. MATLAB will not be enabled unless a path to your license file is provided with -l."
  # make a dummy file
  touch matlab.lic
else
  echo "Using Matlab license tied to:"
  echo $user
  echo $macaddr
  echo $license
  # copy license file into current directory, Docker container has only access to local files
  cp "$license" matlab.lic
fi

# Set up licensing for WolframEngine
# The folder for Licensing is given lax permissions so that WolframEngine's activation process inside Docker can write to it
mkdir -p Licensing
chmod -R 757 "$PWD/Licensing"

docker rm -f kyx
docker build --build-arg LICENSE_FILE=matlab.lic --build-arg USER_NAME=$user -t keymaerax .
docker create --mac-address $macaddr -it -v $PWD/Licensing:/home/$user/.WolframEngine/Licensing -w /home/$user/ -p 8090:8090 --name kyx keymaerax bash
docker start kyx

# install MATLAB packages
install_packages_cmd="\"addpath /home/$user/mpm-3.1.0/;mpm install sedumi -u https://github.com/sqlp/sedumi.git -t v1.3.5;addpath(genpath('/home/$user/SOSTOOLS-4.01'));savepath;quit\""
docker exec -it kyx bash -c "matlab -r $install_packages_cmd"

# activate Wolfram Engine, comment out or abort this step with Ctrl-d to re-initialize the container
# if Wolfram Engine was activated earlier already
echo ""
echo "If you want to re-initialize the container but keep an earlier Wolfram Engine license: abort Wolfram Engine activation with Ctrl-d"
echo ""
docker exec -it kyx wolframscript "-activate"

# uncomment below to run with locally compiled jar
#sbt clean assembly
#docker cp ./keymaerax-webui/target/scala-2.12/KeYmaeraX-Web-assembly-*.jar kyx:/home/$user/keymaerax.jar

# initialize .keymaerax directory with Z3
docker exec -it kyx bash -c 'java -da -jar keymaerax.jar -launch -setup'

# modify configuration
docker exec -it kyx bash -c 'echo "WOLFRAMENGINE_LINK_NAME = /usr/local/Wolfram/WolframEngine/$(<weversion.txt)/Executables/MathKernel" >> .keymaerax/keymaerax.conf'
docker exec -it kyx bash -c 'echo "WOLFRAMENGINE_JLINK_LIB_DIR = /usr/local/Wolfram/WolframEngine/$(<weversion.txt)/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64" >> .keymaerax/keymaerax.conf'
docker exec -it kyx bash -c 'echo "WOLFRAMENGINE_TCPIP = false" >> .keymaerax/keymaerax.conf'
docker exec -it kyx bash -c 'echo "IS_DOCKER = true" >> .keymaerax/keymaerax.conf'
docker exec -it kyx sed -i "s/QE_TOOL = z3/QE_TOOL = wolframengine/g" .keymaerax/keymaerax.conf
docker inspect -f '{{ .NetworkSettings.IPAddress }}' kyx > dockerip.txt
docker exec -it kyx sed -i "s/HOST = 127.0.0.1/HOST = $(<dockerip.txt)/g" .keymaerax/keymaerax.conf

# modify MATLink build file
docker exec -it kyx sed -i "s/-lML64i3/-lML64i4/g" .WolframEngine/Applications/MATLink/Engine/src/Makefile.lin64
docker exec -it kyx sed -i "s/CFLAGS = -Wall/CFLAGS = -Wall -DMX_COMPAT_32/g" .WolframEngine/Applications/MATLink/Engine/src/Makefile.lin64
docker exec -it kyx sed -i "s/DMLINTERFACE=3/DMLINTERFACE=4/g" .WolframEngine/Applications/MATLink/Engine/src/Makefile.lin64

docker stop kyx
