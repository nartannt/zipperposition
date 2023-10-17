touch "$1"
for filename in ../tptp_benchmarks/poly_problems/TF1/*.p; do
    ./portforlio/portfolio.lams.parallel.py "$filename" 30 --output none 
    #./zipperposition.exe --mode best --steps 2500 --try-e eprover-ho --output none "$filename" --timeout 40 | grep "status Theorem" >> "$1"
    echo "$filename done"
done

wc -l "$1" | echo
