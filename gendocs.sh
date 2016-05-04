#!/bin/bash

make 
coqdoc *.v -d docs/
sed -i '' 's/ICFP\.//g' docs/index.html
