touch "$1"
for filename in ../tptp_benchmarks/poly_problems/TF1/*.p; do

    # with monomorphisation e at 0.0
    printf "\n\nwith monomorphisation, call point 0.0\n" >> "$1"
    timeout 45\
    ./zipperposition.exe --mode best --try-e "./eprover-ho" --e-timeout 30 --e-max-derived 100000 --e-call-point 0.0 --output none "$filename" --timeout 30 >> "$1"

    # with monomorphisation e at 0.05
    printf "\n\nwith monomorphisation, call point 0.05\n" >> "$1"
    timeout 45\
    ./zipperposition.exe --mode best --try-e "./eprover-ho" --e-timeout 30 --e-max-derived 100000 --e-call-point 0.05 --output none "$filename" --timeout 30 >> "$1"

    # with monomorphisation e at 0.1
    printf "\n\nwith monomorphisation, call point 0.1\n" >> "$1"
    timeout 45\
    ./zipperposition.exe --mode best --try-e "./eprover-ho" --e-timeout 30 --e-max-derived 100000 --e-call-point 0.1 --output none "$filename" --timeout 30 >> "$1"

    # without monomorphisation
    printf "\n\nwithout monomorphisation (or e)\n" >> "$1"
    timeout 45\
    ./zipperposition.exe --mode best --output none "$filename" --timeout 30 >> "$1"

    printf "\n\n ------------------------------------------------------------------------------- \n\n" >> "$1"
    printf "$filename done\n" >> "$1"
    printf "$filename done\n"
done
