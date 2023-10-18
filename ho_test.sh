touch "$1"
for filename in ../tptp_benchmarks/poly_problems/TF1/*.p; do
    timeout 20\
    ./zipperposition.exe --mode best --steps 2500 --try-e "./eprover-ho" --output none "$filename" --timeout 10 | grep "status Theorem" >> "$1"
    echo "$filename done"
done

wc -l "$1" | echo
