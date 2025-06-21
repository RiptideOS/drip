#!/bin/bash

EXECUTABLE=$1

if [[ -z $EXECUTABLE ]]; then
    echo 'must specify executable path'
    exit
fi

docker run --rm -ti --platform linux/amd64 -v ./$EXECUTABLE:/a.out ubuntu:latest /a.out

# docker run -it --platform linux/amd64 --cap-add=SYS_PTRACE --security-opt seccomp=unconfined -v ./$EXECUTABLE:/a.out ubuntu:latest bash
