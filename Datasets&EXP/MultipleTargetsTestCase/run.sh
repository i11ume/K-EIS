#!/bin/bash
g++ -O2 -mcmodel=medium -std=c++17 -pthread -o Framework K-EIS.cpp
g++ -O2 -mcmodel=medium -std=c++17 -pthread -o Ultra Mix-EIS.cpp
g++ -O2 -mcmodel=medium -std=c++17 -pthread -o KBMIGS KBM-IGS2.cpp

declare -a regular_files=("wiki_edits" "ACM_CCS" "ProductClassification" "amazon" "ImageNet")
declare -a kbmigs_files=("amazon" "ProductClassification")
declare -a other_files=("wiki_edits")

for str in "${other_files[@]}"; do
    ./Framework "$str" &
done

for str in "${regular_files[@]}"; do
    ./Ultra "$str" &
done
wait
echo "All processes have completed"