#!/bin/bash

./sbt clean update compile
./sbt mkrun
./sbt publish-local
