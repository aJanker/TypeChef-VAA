#!/bin/bash

cd $(dirname $0)

./sbt clean update compile
./sbt mkrun
./sbt publish-local
