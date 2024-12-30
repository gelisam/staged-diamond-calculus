#!/bin/bash
set -e

./run.sh
fswatcher --throttle 300 --path src -- ./run.sh
