#!/bin/sh -l

# https://docs.github.com/en/actions/creating-actions/creating-a-docker-container-action#accessing-files-created-by-a-container-action
cp /usr/local/Wolfram/WolframEngine/*/SystemFiles/Links/JLink/JLink.jar /github/workspace/
