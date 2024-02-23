# with monomorphisation at the beginning
#./zipperposition.exe --mode best --progress -o none --e-call-step 25 --try-e "./eprover-ho" -t 30 --e-max-derived 100000  -o none --e-timeout 30 ../tptp_benchmarks/TF1/ITP021_3.p
# only call e after monomorphisation
#./eprover-ho ...  --pos-ext=all --neg-ext=all --auto-schedule -s
# without monomorphisation
#./zipperposition.exe --mode best -o none --progress -t 60 ../tptp_benchmarks/poly_problems/...

#portfolio
#./portfolio/portfolio.lams.parallel.py "$filename" 30 /tmp/ true

#connection
#lazio.tcs.ifi.lmu.de -l bozect-rhiwp -p 13522
# scp command
#scp -P 13522 bozect-rhiwp@lazio.tcs.ifi.lmu.de:/home/bozect-rhiwp

# record
#perf record --call-graph=dwarf -- ./zipperposition.exe --mode best --progress -o none --e-call-point 0.0 --try-e "./eprover-ho" -t 60 ../tptp_benchmarks/poly_problems/...


# ref run

#30_-1_2_9_-1_1_6_10_-1_30_3_-1_3_0
ZIPP_TIMEOUT=30

MONO_CAP=-1
MONO_MULT=6
MONO_FLOOR=20

POLY_CAP=-1
POLY_MULT=3
POLY_FLOOR=12

MONO_SUBST=20
SUBST_CAP=-1


E_TIMEOUT=30
CLAUSE_MULT=2
CLAUSE_CAP=2000

LOOP_NB=4
E_CALL_STEP=20


CS40_OPT=(\
  -i tptp \
  -o none \
  -nc --tptp-def-as-rewrite --rewrite-before-cnf=true \
  --mode=ho-competitive --boolean-reasoning=bool-hoist --bool-hoist-simpl=true \
  --ext-rules=ext-family --ext-rules-max-depth=2 \
  --ho-prim-enum=full --ho-prim-max=2 --bool-select=LI  \
  --ho-max-elims=1  --avatar=off \
  --recognize-injectivity=true  --ho-elim-leibniz=1 \
  --ho-unif-level=full-framework --no-max-vars \
  -q '6|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)' \                                                                                                                                                                                          
  -q '6|const|conjecture-relative-var(1.02,l,f)' \
  -q '1|prefer-processed|fifo' \
  -q '1|prefer-non-goals|conjecture-relative-var(1,l,f)' \
  -q '4|prefer-easy-ho|conjecture-relative-var(1.01,s,f)' \
  --select=e-selection7 --ho-choice-inst=true --try-e="./eprover-ho" --tmp-dir="/tmp"  \
  --sine=50 --sine-tolerance=2 --sine-depth-max=4 --sine-depth-min=1 \
  --e-encode-lambdas=keep --scan-clause-ac=false --lambdasup=0 --kbo-weight-fun=invfreqrank \
  --e-call-step=$E_CALL_STEP --timeout=$ZIPP_TIMEOUT --e-timeout=$E_TIMEOUT\
  --mono-ty-args="$MONO_CAP,$MONO_MULT,$MONO_FLOOR" \
  --poly-ty-args="$POLY_CAP,$POLY_MULT,$POLY_FLOOR" \
  --old-subst-per-clause=$(($SUBST_CAP/2)) --new-subst-per-clause=$(($SUBST_CAP/2))\
  --monomorphising-subst-per-clause=$MONO_SUBST \
  --e-max-derived=$CLAUSE_CAP --new-clauses-multiplier=$CLAUSE_MULT \
  --mono-loop=$LOOP_NB\
  "$1")

#echo "running with ${CS40_OPT[@]}"
./zipperposition.exe ${CS40_OPT[@]}

