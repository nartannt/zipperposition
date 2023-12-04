touch "$1"
for filename in ../tptp_benchmarks/poly_problems/TF1/*.p; do

    # with monomorphisation e at 0.0
    echo $"\n\nwith monomorphisation, call point 0.0\n" >> "$1"
    timeout 45\
    ./zipperposition.exe --mode best --try-e "./eprover-ho" --e-call-point 0.0 --output none "$filename" --timeout 30 >> "$1"

    # with monomorphisation e at 0.1
    echo $"\n\nwith monomorphisation, call point 0.1\n" >> "$1"
    timeout 45\
    ./zipperposition.exe --mode best --try-e "./eprover-ho" --e-call-point 0.1 --output none "$filename" --timeout 30 >> "$1"

    # with monomorphisation e at 0.2
    echo $"\n\nwith monomorphisation, call point 0.2\n" >> "$1"
    timeout 45\
    ./zipperposition.exe --mode best --try-e "./eprover-ho" --e-call-point 0.2 --output none "$filename" --timeout 30 >> "$1"

    # without monomorphisation
    echo $"\n\nwithout monomorphisation (or e)\n" >> "$1"
    timeout 45\
    ./zipperposition.exe --mode best --output none "$filename" --timeout 30 >> "$1"

    echo $"$filename done"
done
