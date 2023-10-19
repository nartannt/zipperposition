touch "$1"
touch "$2"
for filename in ../tptp_benchmarks/poly_problems/TF1/*.p; do
    # with monomorphisation
    timeout 20\
    ./zipperposition.exe --mode best --steps 2500 --try-e "./eprover-ho" --output none "$filename" --timeout 10 | grep "status Theorem" >> "$1"

    #without monomorphisation
    timeout 20\
    ./portfolio/zipperposition --mode best --steps 2500 --try-e "./eprover-ho" --output none "$filename" --timeout 10 | grep "status Theorem" >> "$2"

    echo "$filename done"
done
