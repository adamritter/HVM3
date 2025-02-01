#!/bin/bash
fswatch -o src/HVML/*.hs | xargs -n1 cabal run hvml
