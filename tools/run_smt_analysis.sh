#!/bin/bash

# Explicitly run SMT generation for marked loops in npbench demo files

DB="tools/demo/npbench/results.db"
OUT="tools/demo/npbench"

mkdir -p "$OUT"

echo "Running adi..."
python3 tools/generate_smt.py -i tools/demo/npbench/adi.pcode -l 0 -db "$DB" -o "$OUT/adi_l0.smt2" -t 60

echo "Running azmint..."
python3 tools/generate_smt.py -i tools/demo/npbench/azmint.pcode -l 1 -db "$DB" -o "$OUT/azmint_l1.smt2" -t 60

echo "Running cavity_flow..."
python3 tools/generate_smt.py -i tools/demo/npbench/cavity_flow.pcode -l 0 -db "$DB" -o "$OUT/cavity_flow_l0.smt2" -t 60

echo "Running channel_flow..."
python3 tools/generate_smt.py -i tools/demo/npbench/channel_flow.pcode -l 0 -db "$DB" -o "$OUT/channel_flow_l0.smt2" -t 60

echo "Running cholesky..."
python3 tools/generate_smt.py -i tools/demo/npbench/cholesky.pcode -l 0 -db "$DB" -o "$OUT/cholesky_l0.smt2" -t 60

echo "Running correlation..."
python3 tools/generate_smt.py -i tools/demo/npbench/correlation.pcode -l 5 -db "$DB" -o "$OUT/correlation_l5.smt2" -t 60

echo "Running covariance..."
python3 tools/generate_smt.py -i tools/demo/npbench/covariance.pcode -l 3 -db "$DB" -o "$OUT/covariance_l3.smt2" -t 60

echo "Running deriche..."
python3 tools/generate_smt.py -i tools/demo/npbench/deriche.pcode -l 2 -db "$DB" -o "$OUT/deriche_l2.smt2" -t 60

echo "Running durbin..."
python3 tools/generate_smt.py -i tools/demo/npbench/durbin.pcode -l 0 -db "$DB" -o "$OUT/durbin_l0.smt2" -t 60

echo "Running ftdt_2d..."
python3 tools/generate_smt.py -i tools/demo/npbench/ftdt_2d.pcode -l 0 -db "$DB" -o "$OUT/ftdt_2d_l0.smt2" -t 60

echo "Running gram_schmidt..."
python3 tools/generate_smt.py -i tools/demo/npbench/gram_schmidt.pcode -l 0 -db "$DB" -o "$OUT/gram_schmidt_l0.smt2" -t 60

echo "Running lu..."
python3 tools/generate_smt.py -i tools/demo/npbench/lu.pcode -l 0 -db "$DB" -o "$OUT/lu_l0.smt2" -t 60

echo "Running ludcmp..."
python3 tools/generate_smt.py -i tools/demo/npbench/ludcmp.pcode -l 0 -db "$DB" -o "$OUT/ludcmp_l0.smt2" -t 60

echo "Running nussinov..."
python3 tools/generate_smt.py -i tools/demo/npbench/nussinov.pcode -l 0 -db "$DB" -o "$OUT/nussinov_l0.smt2" -t 60

echo "Running scattering..."
python3 tools/generate_smt.py -i tools/demo/npbench/scattering.pcode -l 0 -db "$DB" -o "$OUT/scattering_l0.smt2" -t 60

echo "Running seidel_2d..."
python3 tools/generate_smt.py -i tools/demo/npbench/seidel_2d.pcode -l 0 -db "$DB" -o "$OUT/seidel_2d_l0.smt2" -t 60

echo "Running syr2k..."
python3 tools/generate_smt.py -i tools/demo/npbench/syr2k.pcode -l 0 -db "$DB" -o "$OUT/syr2k_l0.smt2" -t 60

echo "Running trisolve..."
python3 tools/generate_smt.py -i tools/demo/npbench/trisolve.pcode -l 0 -db "$DB" -o "$OUT/trisolve_l0.smt2" -t 60

echo "Running trmm..."
python3 tools/generate_smt.py -i tools/demo/npbench/trmm.pcode -l 0 -db "$DB" -o "$OUT/trmm_l0.smt2" -t 60

echo "All done."