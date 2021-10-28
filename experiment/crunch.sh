echo 'type measure = { ref : float * float ; ct : float * float }'
echo 'let data = ['

for p in *.csv
do
    P=$(basename $p .csv)
    echo -n '"'$P'", { ref = '
    grep jasmin-2021 $p | cut -d , -f 2,3
    echo -n '; ct = '
    grep $JASMIN_CT.jasminc $p | cut -d , -f 2,3
    echo '} ;'
done

echo ']'
