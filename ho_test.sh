touch "$1"
for filename in ../tptp_benchmarks/poly_problems/*/*.p; do
    ./zipperposition.exe --mode best --steps 2500 --try-e eprover-ho --output none "$filename" --timeout 40 | grep "status Theorem" >> "$1"
    echo "$filename done"
done

wc -l "$1" | echo
