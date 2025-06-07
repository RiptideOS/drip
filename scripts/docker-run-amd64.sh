#!/bin/bash

EXECUTABLE=$1

if [[ -z $EXECUTABLE ]]; then
    echo 'must specify executable path'
    exit
fi

docker run --rm -ti --platform linux/amd64 -v ./$EXECUTABLE:/a.out ubuntu:latest /a.out
