#!/bin/bash

COQ_PATH=/c/coq
PATH="$COQ_PATH/bin:$PATH"

coq_makefile -f Make -o Makefile
