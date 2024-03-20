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

# ref run 30_-1_2_9_-1_1_6_10_-1_30_3_-1_3_0 ZIPP_TIMEOUT=5 MONO_CAP=-1 MONO_MULT=-1 MONO_FLOOR=1000000

ZIPP_TIMEOUT=30
MONO_TO=20

SYM_MONO_CAP=50
SYM_MONO_MULT=1.0
SYM_MONO_FLOOR=7

SYM_POLY_CAP=10
SYM_POLY_MULT=0.0
SYM_POLY_FLOOR=1

CLAUSE_MONO_CAP=500
CLAUSE_MONO_MULT=10000000000
CLAUSE_MONO_FLOOR=1000

CLAUSE_POLY_CAP=500
CLAUSE_POLY_MULT=100000000000
CLAUSE_POLY_FLOOR=1000

MONO_SUBST=2
SUBST_CAP=-1


E_TIMEOUT=30
CLAUSE_MULT=-1
CLAUSE_CAP=2000

SUBST_ORDERING="age"

LOOP_NB=4
E_CALL_STEP=0


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
  --sym-mono-ty-args="$SYM_MONO_CAP,$SYM_MONO_MULT,$SYM_MONO_FLOOR" \
  --sym-poly-ty-args="$SYM_POLY_CAP,$SYM_POLY_MULT,$SYM_POLY_FLOOR" \
  --clause-mono-ty-args="$CLAUSE_MONO_CAP,$CLAUSE_MONO_MULT,$CLAUSE_MONO_FLOOR" \
  --clause-poly-ty-args="$CLAUSE_POLY_CAP,$CLAUSE_POLY_MULT,$CLAUSE_POLY_FLOOR" \
  --monomorphising-subst-per-clause=$MONO_SUBST \
  --substitution-ordering=$SUBST_ORDERING \
  --e-max-derived=$CLAUSE_CAP --new-clauses-multiplier=$CLAUSE_MULT \
  --mono-loop=$LOOP_NB\
  --monomorphisation-timeout=$MONO_TO\
  )

#echo "running with ${CS40_OPT[@]}"
find "$1" -name \*.p | xargs --max-args=1 --max-procs=3 ./zipperposition.exe ${CS40_OPT[@]}

