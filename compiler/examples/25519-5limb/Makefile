all: ladder_nofor.s test_ladder.s
	gcc ladder_nofor.s test_ladder.s
	./a.out

ladder_nofor.s : ladder_nofor.mil
	../../jasminc.native -pasm ladder_nofor.mil > ladder_nofor.s 2> /dev/null

test_ladder.s : test_ladder.c
	gcc -S test_ladder.c
