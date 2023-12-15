
while read p; do
    timeout 45\
        ./portfolio/portfolio.lams.parallel.py "../tptp_benchmarks/poly_problems/TF1/$p" 30 /tmp/ true | grep "status "
    timeout 45\
        ./zipperposition.exe --mode best --progress -o none --e-call-point 0.0 --try-e "./eprover-ho" -t 60 "../tptp_benchmarks/poly_problems/TF1/$p" | grep "status "
    echo "done $p"
done < "$1"
