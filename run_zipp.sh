
ZIPP_TIMEOUT=20

SYM_MONO_CAP=-1
SYM_MONO_MULT=-1
SYM_MONO_FLOOR=999

SYM_POLY_CAP=-1
SYM_POLY_MULT=-1
SYM_POLY_FLOOR=999

CLAUSE_MONO_CAP=500
CLAUSE_MONO_MULT=0
CLAUSE_MONO_FLOOR=0

CLAUSE_POLY_CAP=500
CLAUSE_POLY_MULT=0
CLAUSE_POLY_FLOOR=10

MONO_SUBST=10
SUBST_CAP=-1


E_TIMEOUT=30
CLAUSE_MULT=1.0
CLAUSE_CAP=2000

LOOP_NB=2
E_CALL_STEP=0

MONO_TO=20
SUBST_ORDERING="age"

E_DIR="./eprover-ho"

OPT_40_B_COMB=(\
  -i tptp\
  -o none\
  --timeout $ZIPP_TIMEOUT \
  --mode=ho-comb-complete \
  --boolean-reasoning=simpl-only \
  --ext-rules=off --kbo-weight-fun=lambda-def-sqarity \
  --ho-prim-enum=none \
  --tptp-def-as-rewrite \
  -q "4|prefer-sos|orient-lmax(2,1,2,1,1)" \
  -q "4|defer-sos|conjecture-relative-var(1,s,f)" \
  -q "3|const|default" \
  -q "1|prefer-processed|fifo" \
  --ho-elim-leibniz=1 \
  --select=NoSelection --solve-formulas=true \
  --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=8 \
  --sine=60 --sine-tolerance=2 --sine-depth-max=5 --sine-depth-min=1 \
  --e-encode-lambdas=drop \
  --scan-clause-ac=false --presaturate=true \
  --comb-b-penalty=3 --comb-c-penalty=3 --comb-k-penalty=1 --comb-s-penalty=5 --subvarsup=false \
  --try-e="$E_DIR" --tmp-dir="/tmp" \
  --e-call-step=$E_CALL_STEP --timeout=$ZIPP_TIMEOUT --e-timeout=$E_TIMEOUT\
  --e-call-point=1.0
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

OPT_40_B_COMB_2=(\
  -i tptp\
  -o none\
  --timeout $ZIPP_TIMEOUT \
  --mode=ho-comb-complete \
  --boolean-reasoning=simpl-only \
  --e-encode-lambdas=drop \
  --presaturate=true \
  --try-e="$E_DIR" --tmp-dir="/tmp" \
  --e-call-step=$E_CALL_STEP --timeout=$ZIPP_TIMEOUT --e-timeout=$E_TIMEOUT\
)

ZIPP_OPT=(\
  -i tptp\
  -o none\
  --try-e="./binaries/eprover-ho" --tmp-dir="/tmp" \
  --e-call-step=0 --timeout=30 --e-timeout=0\
  --e-call-point=1.0\
  --sym-mono-ty-args="-1,-1,999" \
  --sym-poly-ty-args="-1,-1,999" \
  --clause-mono-ty-args="500,0,0" \
  --clause-poly-ty-args="500,0,10" \
  --monomorphising-subst-per-clause=10 \
  --substitution-ordering="age" \
  --e-max-derived=2000 --new-clauses-multiplier=1 \
  --mono-loop=2\
  --monomorphisation-timeout=20\
)


#echo "running with ${????[@]}"
#find "$1" -name \*.p | xargs --max-args=1 --max-procs=1 timeout 30 ./zipperposition.exe ${L_40_C_S[@]}
#echo "done 40_c.s"
#
#find "$1" -name \*.p | xargs --max-args=1 --max-procs=1 timeout 30 ./zipperposition.exe ${L_35_FULL_UNIF[@]}
#echo "done 35_full_unif"

#find "$1" -name \*.p | xargs --max-args=1 --max-procs=1 timeout 30 ./zipperposition.exe ${L_40_C_IC[@]}
#echo "done 40_c_ic"

#find "$1" -name \*.p | xargs --max-args=1 --max-procs=1 timeout 30 ./zipperposition.exe ${L_40_NOFORMS[@]}
#echo "done 40_noforms"
#
#find "$1" -name \*.p | xargs --max-args=1 --max-procs=1 timeout 30 ./zipperposition.exe ${L_30_B_L[@]}
#echo "done 30_b.l"
#
#find "$1" -name \*.p | xargs --max-args=1 --max-procs=1 timeout 3000000 ./zipperposition.exe ${L_40_E_LIFT[@]}
find "$1" -name \*.p | xargs --max-args=1 --max-procs=1 timeout 5 ./zipperposition.exe ${ZIPP_OPT[@]}

