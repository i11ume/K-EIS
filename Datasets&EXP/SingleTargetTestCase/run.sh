#!/bin/bash
g++ -O2 -mcmodel=medium -std=c++17 -pthread -o IGS IGS.cpp
g++ -O2 -mcmodel=medium -std=c++17 -pthread -o TSIGS TS-IGS.cpp
g++ -O2 -mcmodel=medium -std=c++17 -pthread -o KBMIGS KBM-IGS1.cpp
g++ -O2 -mcmodel=medium -std=c++17 -pthread -o BinG BinG.cpp
g++ -O2 -mcmodel=medium -std=c++17 -pthread -o advance 1-EIS.cpp

declare -a regular_files=("ACM_CCS" "ProductClassification" "amazon" "ImageNet""wiki_edits")
declare -a kbmigs_files=("amazon" "ProductClassification")
declare -a other_files=("ACM_CCS" "ImageNet""wiki_edits")

echo "Running KBMIGS with datasets..."
for str in "${kbmigs_files[@]}"; do
    ./KBMIGS "$str" &
done

echo "Running IGS with datasets..."
for str in "${regular_files[@]}"; do
    ./IGS "$str" &
done

echo "Running TSIGS with datasets..."
for str in "${regular_files[@]}"; do
    ./TSIGS "$str" &
done

echo "Running BinG with datasets..."
for str in "${kbmigs_files[@]}"; do
    ./BinG "$str" &
done

echo "Running advance with datasets..."
for str in "${regular_files[@]}"; do
    ./advance "$str" 
done
wait
echo "All processes have completed"