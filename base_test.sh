echo "base mode"
./zipperposition.exe --mode best --progress -o none --try-e "./eprover-ho" "$1" -t 15
echo "early e"
./zipperposition.exe --mode best --progress -o none --try-e "./eprover-ho" --e-call-point 0.0 "$1" -t 15
