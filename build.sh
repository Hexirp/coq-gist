#!/bin/bash

COQ_PATH=/c/coq
PATH="$COQ_PATH/bin:$PATH"

coqc A.v
coqc B.v
