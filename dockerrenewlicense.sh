#!/bin/bash

docker start kyx
docker exec -it kyx wolframscript "-activate"
docker stop kyx
