# with monomorphisation at the beginning
./zipperposition.exe --mode best --progress -o none --e-call-point 0.0 --try-e "./eprover-ho" -t 60 ../tptp_benchmarks/poly_problems/...
# only call e after monomorphisation
./eprover-ho ...  --pos-ext=all --neg-ext=all --auto-schedule -s
# without monomorphisation
./zipperposition.exe --mode best -o none --progress -t 60 ../tptp_benchmarks/poly_problems/...

#portfolio
./portfolio/portfolio.lams.parallel.py "$filename" 30 /tmp/ true

#connection
lazio.tcs.ifi.lmu.de -l bozect-rhiwp -p 13522
# scp command
scp -P 13522 bozect-rhiwp@lazio.tcs.ifi.lmu.de:/home/bozect-rhiwp

# record
perf record --call-graph=dwarf -- ./zipperposition.exe --mode best --progress -o none --e-call-point 0.0 --try-e "./eprover-ho" -t 60 ../tptp_benchmarks/poly_problems/...
