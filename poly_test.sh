touch "$1"
touch "$1"
for filename in $(cat res/poly_syntactic_errors); do
    # with monomorphisation
    timeout 25\
    ./zipperposition.exe --mode best --try-e "./eprover-ho" --e-call-point 0.0 --output none "$filename" --timeout 15 | grep "status Theorem" >> "$1"
    echo "$filename done"
done
