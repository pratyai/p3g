#!/bin/bash
set -x

# Directory 1
INPUT_DIR_1="tools/demo/npbench-sdfg/"
OUTPUT_DIR_1="tools/demo/npbench-sdfg/"

# Directory 2
INPUT_DIR_2="tools/demo/cloudsc-sdfg/"
OUTPUT_DIR_2="tools/demo/cloudsc-sdfg/"

echo "Generating .pcode files for ${INPUT_DIR_1}"
find "$INPUT_DIR_1" -type f \( -name "*.sdfg" -o -name "*.sdfgz" \) | while read -r filepath; do
    echo "Processing $filepath"
    python3 tools/generate_pcode.py -i "$filepath" -o "$OUTPUT_DIR_1"
done

echo "Generating .pcode files for ${INPUT_DIR_2}"
find "$INPUT_DIR_2" -type f \( -name "*.sdfg" -o -name "*.sdfgz" \) | while read -r filepath; do
    echo "Processing $filepath"
    python3 tools/generate_pcode.py -i "$filepath" -o "$OUTPUT_DIR_2"
done

echo "Pcode generation complete."