#!/bin/bash
# This is how the form upload call goes; for now I'm just stuffing raw files
# in the data portion of the http request because actual file uploads are a
# huge pain...
#From project root:
echo "Creating a new model:";
curl --form upload=@examples/dev/t/parsing/positive/test.key localhost:8090/user/t/model/test;
echo; echo

echo "Creating a new model:";
curl --form upload=@examples/dev/t/parsing/positive/test.key localhost:8090/user/t/model/test2;
echo; echo



echo "Getting the mode list: "
curl --cookie "userId=t" localhost:8090/models/users/t;
echo
