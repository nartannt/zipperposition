touch "$1"
for filename in ../tptp_benchmarks/poly_problems/TF1/COM*; do
    # with monomorphisation
    timeout 45\
    ./zipperposition.exe --mode best --try-e "./eprover-ho" --e-call-point 0.0 --output none "$filename" --timeout 30 | grep "status Theorem" >> "$1"
    echo "$filename done"
done
