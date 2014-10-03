#!/bin/bash
#From project root:
echo "Creating a new model:";
curl --form upload=@examples/dev/t/parsing/positive/test.key localhost:8090/user/t/model/test;
echo; echo

echo "Getting the mode list: "
curl --cookie "userId=t" localhost:8090/models/users/t;
echo
