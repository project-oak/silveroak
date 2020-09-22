#!/bin/bash

git ls-files $(git rev-parse --show-toplevel) | grep "\.v$" | xargs sed -i -E 's/\s+$//g'
