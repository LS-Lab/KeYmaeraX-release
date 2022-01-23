#!/bin/bash

docker start kyx
docker exec kyx bash -c 'PATH=$PATH:$(<wepath.txt); java -da -jar keymaerax.jar -launch -ui'
docker stop kyx
