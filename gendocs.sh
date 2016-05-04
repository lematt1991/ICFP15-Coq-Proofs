#!/bin/bash

make 
coqdoc *.v -d docs/
sed -i '' 's/ICFP\.//g' docs/index.html
sed -i '' 's/[a-zA-Z]*\.html/https:\/\/rawgit.com\/ml9951\/ICFP15-Coq-Proofs\/JFP-Proofs\/docs\/&/g' docs/index.html


#add `https://rawgit.com/ml9951/ICFP15-Coq-Proofs/JFP-Proofs/docs/` on to every URL
