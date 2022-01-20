#!/bin/bash

docker start kyx
docker exec -d kyx bash -c "export LD_PRELOAD=/lib/x86_64-linux-gnu/libuuid.so.1.3.0;java -da -jar keymaerax.jar -launch -ui"
echo "Starting KeYmaera X"
until $(curl --output /dev/null --silent --head --fail http://localhost:8090); do
    printf '.'
    sleep 5
done
echo "done"
echo "Please point your browser to http://localhost:8090"
while $(curl --output /dev/null --silent --head --fail http://localhost:8090); do
    sleep 5
done
docker stop kyx
