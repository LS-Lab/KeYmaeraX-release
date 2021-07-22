#!/bin/bash

docker start kyx
docker exec -it -w /root/ kyx bash -c "export LD_PRELOAD=/lib/x86_64-linux-gnu/libuuid.so.1.3.0;java -da -jar keymaerax.jar -launch -ui"
docker stop kyx
