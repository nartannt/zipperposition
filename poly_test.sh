touch "$1"
for filename in ../tptp_benchmarks/poly_problems/TF1/*.p; do
    # with monomorphisation
    timeout 25\
    ./zipperposition.exe --mode best --e-call-point 0.0 --try-e "./eprover-ho" --output none "$filename" --timeout 15 | grep "status Theorem" >> "$1"
    echo "$filename done"
done
