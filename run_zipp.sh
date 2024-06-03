
ZIPP_TIMEOUT=30
MONO_TO=10

SYM_MONO_CAP=-1
SYM_MONO_MULT=-1
SYM_MONO_FLOOR=0

SYM_POLY_CAP=-1
SYM_POLY_MULT=-1
SYM_POLY_FLOOR=0

CLAUSE_MONO_CAP=-1
CLAUSE_MONO_MULT=-1
CLAUSE_MONO_FLOOR=0

CLAUSE_POLY_CAP=-1
CLAUSE_POLY_MULT=-1
CLAUSE_POLY_FLOOR=0

MONO_SUBST=10000
SUBST_CAP=-1


E_TIMEOUT=30
CLAUSE_MULT=-1
CLAUSE_CAP=2000

SUBST_ORDERING="age"

LOOP_NB=5
E_CALL_STEP=0


L_40_C_S=(\
 -i tptp\
 -o none\
 -nc --tptp-def-as-rewrite --rewrite-before-cnf=true \
 --mode=ho-competitive --boolean-reasoning=bool-hoist --bool-hoist-simpl=true \
 --ext-rules=ext-family --ext-rules-max-depth=2 \
 --ho-prim-enum=full --ho-prim-max=2 --bool-select=LI  \
 --ho-max-elims=1  --avatar=off \
 --recognize-injectivity=true  --ho-elim-leibniz=1 \
 --ho-unif-level=full-framework --no-max-vars  \
 -q "6|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)" \     
 -q "6|const|conjecture-relative-var(1.02,l,f)" \
 -q "1|prefer-processed|fifo" \
 -q "1|prefer-non-goals|conjecture-relative-var(1,l,f)" \
 -q "4|prefer-easy-ho|conjecture-relative-var(1.01,s,f)" \                                                                                                                                                                               
 --select=e-selection7 --ho-choice-inst=true \                                                                                                                                   
 --sine=50 --sine-tolerance=2 --sine-depth-max=4 --sine-depth-min=1 \
 --e-encode-lambdas=keep --scan-clause-ac=false --lambdasup=0 --kbo-weight-fun=invfreqrank \
 --try-e="./eprover-ho" --tmp-dir="/tmp" \
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

L_35_FULL_UNIF=(\
  -i tptp\
  -o none\
  --mode=ho-pragmatic --boolean-reasoning=simpl-only\
  --ext-rules=off\
  --ho-prim-enum=neg --ho-prim-enum-early-bird=true --ho-prim-max=1 --ho-choice-inst=true\
  --select=ho-selection4 --ho-selection-restriction=none\
  --lazy-cnf=true --lazy-cnf-kind=inf --lazy-cnf-renaming-threshold=2\
  --tptp-def-as-rewrite --rewrite-before-cnf=true --ho-unif-level=full-framework --stream-queue-ratio=20 --stream-queue-guard=300\
  -q "3|prefer-goals|pnrefined(1,1,1,2,2,2,0.5)"\    
  -q "1|prefer-ho-steps|clauseweight(1,1,1)"\
  -q "1|prefer-processed|fifo"\ 
  -q "1|prefer-non-goals|conjecture-relative-var(1,l,f)"\ 
  -q "3|prefer-easy-ho|conjecture-relative-var(1.01,s,f)"\                                                                                                                                                                                
  --ho-solid-decider=false --ho-fixpoint-decider=true\                                                                                                                                                                            
  --trigger-bool-inst=1 --ho-pattern-decider=true --trigger-bool-include-quants=false
)

L_40_C_IC=(\
  -i tptp\
  -o none\
  --mode=ho-pragmatic\
  -nc --tptp-def-as-rewrite --rewrite-before-cnf=true \                                                                                                                                                                                   
  --mode=ho-competitive --boolean-reasoning=simpl-only \
  --ext-rules=ext-family --ext-rules-max-depth=1 \
  --ho-prim-enum=none \
  --avatar=off \
  --recognize-injectivity=true  --ho-elim-leibniz=1 \
  --ho-unif-level=pragmatic-framework --no-max-vars  \
  --max-inferences=4 --ho-max-app-projections=1\
  --ho-max-elims=0 --ho-max-rigid-imitations=2 --ho-max-identifications=0 \
  --ho-unif-max-depth=3 \                                                                                                                                                                                                                 
  -q "6|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)" \                                                                                                                                                                                          
  -q "6|const|conjecture-relative-var(1.02,l,f)" \
  -q "1|prefer-processed|fifo" \
  -q "1|prefer-non-goals|conjecture-relative-var(1,l,f)" \
  -q "4|prefer-easy-ho|conjecture-relative-var(1.01,s,f)" \
  --select=e-selection7 --ho-choice-inst=true \
  --sine=50 --sine-tolerance=1 --sine-depth-max=2 --sine-depth-min=1 --sine-ignore-k-most-common-syms=2 --sine-trim-implications=true \
  --e-encode-lambdas=keep --scan-clause-ac=false --lambdasup=0 \
  --kbo-weight-fun=lambda-def-invfreqrank --demod-in-var-args=true --bool-demod=true --lambda-demod=true \
  --try-e="./eprover-ho" --tmp-dir="/tmp" \
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

L_40_NOFORMS=(\
  -i tptp\
  -o none \
  -nc --tptp-def-as-rewrite --rewrite-before-cnf=true --tptp-rewrite-formulas-only=true \
  --mode=ho-pragmatic --boolean-reasoning=simpl-only \
  --ext-rules=ext-family --ext-rules-max-depth=1 \
  --ho-prim-enum=neg --ho-prim-max=1\
  --recognize-injectivity=true  --ho-elim-leibniz=1 \
  --ho-unif-level=pragmatic-framework --no-max-vars  \
  -q "1|prefer-sos|conjecture-relative-var(1.02,l,f)" \
  -q "4|const|conjecture-relative-var(1,s,f)" \
  -q "1|prefer-processed|fifo" \
  -q "1|prefer-non-goals|conjecture-relative-var(1,l,f)" \
  -q "4|prefer-sos|pnrefined(2,1,1,1,2,2,2)" \
  --select=e-selection7 --ho-choice-inst=true \
  --sine=50 --sine-tolerance=10 --sine-depth-max=5 --sine-depth-min=1 \
  --e-encode-lambdas=keep --scan-clause-ac=false --prec-gen-fun=invfreq_conj --ord=derived_ho_kbo \
  --solid-subsumption=true --ignore-orphans=true\
  --try-e="./eprover-ho" --tmp-dir="/tmp" \
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

L_30_B_L=(\
  -i tptp\
  -o none \
  --mode=ho-pragmatic \
  --max-inferences=4 --ho-max-app-projections=1 --ho-max-elims=1 --ho-max-rigid-imitations=1 --ho-max-identifications=1 \
  --ho-unif-max-depth=2 \
  --boolean-reasoning=simpl-only \   
  --ext-rules=off --kbo-weight-fun=lambda-def-sqarity \
  --ho-prim-enum=none \
  --tptp-def-as-rewrite \
  --ho-unif-level=pragmatic-framework \
  -q "4|prefer-sos|orient-lmax(2,1,2,1,1)" \
  -q "4|defer-sos|conjecture-relative-var(1,s,f)" \
  -q "3|const|default" \
  -q "1|prefer-processed|fifo" \
  --ho-elim-leibniz=inf \
  --ho-fixpoint-decider=true --ho-pattern-decider=true --ho-solid-decider=true \
  --select=NoSelection --solve-formulas=true --sup-at-vars=false --sup-at-var-headed=false --fluidsup=true \
  --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=2 \
  --sine=60 --sine-tolerance=3 --sine-depth-max=5 --sine-depth-min=1 \
  --e-auto=true --e-encode-lambdas=drop \
  --scan-clause-ac=false --presaturate=true \
  --try-e="./eprover-ho" --tmp-dir="/tmp" \
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

L_40_E_LIFT=(\
  -i tptp\
  -o none\
  --mode=ho-pragmatic \
  --max-inferences=4 --ho-max-app-projections=1 --ho-max-elims=0 --ho-max-rigid-imitations=2 --ho-max-identifications=0\
  --ho-unif-max-depth=2 --max-inferences=3\
  --boolean-reasoning=bool-hoist --bool-select=LO\
  --ext-rules=off --kbo-weight-fun=lambda-def-invfreqrank\
  --ho-prim-enum=none\
  --ho-unif-level=pragmatic-framework\
  -q "1|prefer-sos|conjecture-relative-var(1.01,s,f)"\
  -q "4|const|conjecture-relative-var(1.05,l,f)"\
  -q "1|prefer-processed|fifo"\
  -q "1|prefer-non-goals|conjecture-relative-var(1.02,l,f)"\
  -q "4|prefer-sos|pnrefined(3,2,3,2,2,1.5,2)"\
  --ho-elim-leibniz=1\
  --ho-fixpoint-decider=true --ho-pattern-decider=true --ho-solid-decider=true\
  --select=e-selection2 --solve-formulas=true --lambdasup=0\
  --e-encode-lambdas=keep\
  --presaturate=true --prec-gen-fun=invfreq --sine-trim-implications=true\
  --try-e="./eprover-ho" --tmp-dir="/tmp" \
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
find "$1" -name \*.p | xargs --max-args=1 --max-procs=1 timeout 30 ./zipperposition.exe ${L_40_E_LIFT[@]}

