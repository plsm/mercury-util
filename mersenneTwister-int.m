/**
 * An implementation of the Mersenne Twister pseudo-random number generator.

 * <p> The pseudo random number generator state uses type {@code int}.  In
 * 32 bit machines, some algorithm parameters are negative numbers.  The
 * algorithm also produces negative numbers.

 * <p> This version was based on the C-program for MT19937 of Makoto
 * Matsumoto and Takuji Nishimura.

 * <p> The original C code contained the following notice:

 * <p> Copyright (C) 1997 Makoto Matsumoto and Takuji Nishimura.  When you
 * use this, send an email to: matumoto@math.keio.ac.jp with an appropriate
 * reference to your work.
  
 * @author Pedro Mariano
 * @version 1.0 2009/12/22
 */
:- module mersenneTwister.

:- interface.

:- import_module bool, io, rational.

/**
 * Pseudo-random number generator state.
 */
:- type supply.

/**
 * init(Seed, Supply)

 * Unify {@code Supply} with a pseudo-random number generator using {@code
 * Seed} as the seed.  Aborts if {@code Seed} is zero.
 */
:- func init(int) = supply.

/**
 * init(Seed, Supply)

 * Unify {@code Supply} with a pseudo-random number generator using {@code
 * Seed} as the seed. Fails if {@code Seed} is zero.
 */
:- pred init(int, supply).
:- mode init(in, out) is semidet.

/**
 * Return the maximum number returned by this pseudo-random number generator.
 */
:- func maxNumber(supply) = int.

/**
 * random(Num, RS0, RS)

 * Extracts a number Num in the range [0, 0x7FFFFFFF] from the random number
 * supply RS0, and binds RS to the new state of the random number supply.
 */
:- pred random(int, supply, supply).
:- mode random(out, in, out) is det.

/**
 * random(Min, Max, Number, SupplyIn, SupplyOut)
 */
:- pred random(int, int, int, supply, supply).
:- mode random(in, in, out, in, out) is det.
%:- mode random(in, in, out, di, uo) is det.

/**
 * Return a random floating point number from the interval [0,1].
 */
:- pred randomFloat_c0_c1(float, supply, supply).
:- mode randomFloat_c0_c1(out, in, out) is det.

/**
 * Return a random floating point number from the interval [0,1[.
 */
:- pred randomFloat_c0_o1(float, supply, supply).
:- mode randomFloat_c0_o1(out, in, out) is det.

/**
 * Return a random floating point number from the interval ]0,1].
 */
:- pred randomFloat_o0_c1(float, supply, supply).
:- mode randomFloat_o0_c1(out, in, out) is det.

:- pred randomBool(bool, supply, supply).
:- mode randomBool(out, in, out) is det.

:- pred randomRational(rational, supply, supply).
:- mode randomRational(out, in, out) is det.

:- pred print(supply::in, io::di, io::uo) is det.

/**
 * debug(!IO)

 * Prints 1000 random number generators on the standard output stream.
 */
:- pred debug(io::di, io::uo) is det.

:- implementation.

:- import_module array, exception, float, int, list, string.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

:- type supply --->
	supply(
		stateVector::array(int),
		index::int).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of private types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of exported predicates and functions

init(Seed) = Result :-
	(if
		init(Seed, Supply)
	then
		Result = Supply
	else
		throw("init/1: Invalid seed")).

init(Seed, Supply) :-
	Seed \= 0,
	Area0 = array.init(recurrenceDegree, Seed /\ 0xFFFFFFFF),
	Area1 = initWorkingArea(Area0, 1),
	generateWordsA(0, Area1, Area2),
	Supply = supply(Area2, 0).

maxNumber(_) = 0x7FFFFFFF.

random(Number, SupplyIn, SupplyOut) :-
	periodParameters(N, _),
	(if
		SupplyIn^index = N
	then
		generateWordsA(0, SupplyIn^stateVector, NextState),
		MTI = 0
	else
		NextState = SupplyIn^stateVector,
		MTI = SupplyIn^index
	),
	temperingParameters(B, C),
	Y0 = array.lookup(NextState, MTI),
	Y1 = int.xor(Y0, int.unchecked_right_shift(Y0, 11)),
	Y2 = int.xor(Y1, int.unchecked_left_shift( Y1,  7) /\ B),
	Y3 = int.xor(Y2, int.unchecked_left_shift( Y2, 15) /\ C),
	Y4 = int.xor(Y3, int.unchecked_right_shift(Y3, 18)),
	Number = int.unchecked_right_shift(Y4, 1),
	SupplyOut = supply(NextState, MTI + 1).

random(Min, Max, Number, SupplyIn, SupplyOut) :-
	random(N, SupplyIn, SupplyOut),
	Number = Min + int.abs(N) rem (Max - Min + 1).

randomFloat_c0_c1(Number, !Supply) :-
	random(Integer, !Supply),
	Number = float(Integer) / 2147483647.0.

randomFloat_c0_o1(Number, !Supply) :-
	random(Integer, !Supply),
	Number = float(Integer) / 2147483648.0.

randomFloat_o0_c1(Number, !Supply) :-
	random(Integer, !Supply),
	Number = (1.0 + float(Integer)) / 2147483648.0.

randomBool(Value, !Supply) :-
	random(Integer, !Supply),
	(if
		Integer < 0
	then
		Value = yes
	else
		Value = no
	).

randomRational(Number, !Supply) :-
	random(Integer, !Supply),
	(if
		Integer < 0
	then
		Number = rational.rational(-Integer, int.max_int)
	else
		Number = rational.rational(Integer, int.max_int)
	).

print(Supply, !IO) :-
	io.format("mti = %d\nState vector:\n", [i(Supply^index)], !IO),
	array.foldl2(
		(pred(MT::in, I::in, (I + 1)::out, IOin::di, IOout::uo) is det :-
			io.format("%10d ", [i(MT)], IOin, IO1),
			(if
				I mod 5 = 4
			then
				io.nl(IO1, IOout)
			else
				IO1 = IOout)),
		Supply^stateVector,
		0, _,
		!IO).

debug(!IO) :-
	Seed = 19650218,
	init(Seed) = Supply,
	mersenneTwister.print(Supply, !IO),
	io.nl(!IO),
	N = 1000,
	io.format("%d random numbers returned by random/3 with seed %d\n", [i(N), i(Seed)], !IO),
	debugInt(0, N, Supply, _, !IO),
	io.format("\n\n%d random numbers returned by randomFloat/3 with seed %d\n", [i(N), i(Seed)], !IO),
	debugFloat(0, N, Supply, _, !IO),
	
	io.format("\n\nChecking generation of 0x7FFFFFFF by 'random' with seed %d\n", [i(Seed)], !IO),
	debugValue(random, 0x7FFFFFFF, 0, Supply, _, !IO),
	
	io.format("\n\nChecking generation of 1.0 by 'randomFloat_o0_c1' with seed %d\n", [i(Seed)], !IO),
	debugValue(randomFloat_o0_c1, 1.0, 0, Supply, _, !IO),
	true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of private predicates and functions

/**
 * The working area size is equal to the degree of recurrence.
 */
:- func recurrenceDegree = int.

recurrenceDegree = 624.

:- func m = int.

m = 397.

:- pred periodParameters(int, int).
:- mode periodParameters(out, out) is det.

periodParameters(recurrenceDegree, m).

:- func matrixA = int.

matrixA = 0x9908B0DF.

/**
 * Most significant {@code w - r} bits.
 */
:- func upperMask = int.

upperMask = 0x80000000.

/**
 * Least significant r bits.
 */
:- func lowerMask = int.

lowerMask = 0x7FFFFFFF.

:- func initWorkingArea(array(int), int) = array(int).

initWorkingArea(Area, Index) = Result :-
	periodParameters(N, _),
	MT_I_1 = array.lookup(Area, Index - 1),
	ShiftedMT_I_1 = int.unchecked_right_shift(MT_I_1, 30),
	NewMT_I =
		(	  1812433253
			* int.xor(MT_I_1, ShiftedMT_I_1)
		+ Index)
		/\ 0xFFFFFFFF,
%	NewMT_I = (array.lookup(Area, Index + 1) * 69069) /\ 0xFFFFFFFF,
	Area1 = array.slow_set(Area, Index, NewMT_I),
	(if
		Index = N - 1
	then
		Result = Area1
	else
		Result = initWorkingArea(Area1, Index + 1)
	).

:- pred generateWordsA(int, array(int), array(int)).
:- mode generateWordsA(in, in, out) is det.

generateWordsA(Index, AreaIn, AreaOut) :-
	periodParameters(N, M),
	(if
		Index = N - M
	then
		generateWordsB(Index, AreaIn, AreaOut)
	else
		MT_I = array.lookup(AreaIn, Index),
		MT_I_1 = array.lookup(AreaIn, Index + 1),
		Y = (MT_I /\ upperMask) \/ (MT_I_1 /\ lowerMask),
		MT_I_M = array.lookup(AreaIn, Index + M),
		ShiftedY = int.unchecked_right_shift(Y, 1),
		(if
			Y /\ 1 = 0
		then
			Mag01 = 0
		else
			Mag01 = matrixA
		),
		NewMT_I = int.xor(int.xor(MT_I_M, ShiftedY), Mag01),
		generateWordsA(Index + 1, array.slow_set(AreaIn, Index, NewMT_I), AreaOut)
	).

:- pred generateWordsB(int, array(int), array(int)).
:- mode generateWordsB(in, in, out) is det.

generateWordsB(Index, !Area) :-
	periodParameters(N, M),
	(if
		Index = N - 1
	then
		generateWordsC(!Area)
	else
		MT_I = array.lookup(!.Area, Index),
		MT_I_1 = array.lookup(!.Area, Index + 1),
		Y = (MT_I /\ upperMask) \/ (MT_I_1 /\ lowerMask),
		MT_I_M_N = array.lookup(!.Area, Index + M - N),
		ShiftedY = int.unchecked_right_shift(Y, 1),
		(if
			Y /\ 1  = 0
		then
			Mag01 = 0
		else
			Mag01 = matrixA
		),
		NewMT_I = int.xor(int.xor(MT_I_M_N, ShiftedY), Mag01),
		generateWordsB(Index + 1, array.slow_set(!.Area, Index, NewMT_I), !:Area)
	).

:- pred generateWordsC(array(int), array(int)).
:- mode generateWordsC(in, out) is det.

generateWordsC(!Area) :-
	periodParameters(N, M),
	MT_N_1 = array.lookup(!.Area, N - 1),
	MT_0 = array.lookup(!.Area, 0),
	Y = (MT_N_1 /\ upperMask) \/ (MT_0 /\ lowerMask),
	MT_M_1 = array.lookup(!.Area, M - 1),
	ShiftedY = int.unchecked_right_shift(Y, 1),
	(if
		Y /\ 1  = 0
	then
		Mag01 = 0
	else
		Mag01 = matrixA
	),
	NewMT_N_1 = int.xor(int.xor(MT_M_1, ShiftedY), Mag01),
	!:Area = array.slow_set(!.Area, N - 1, NewMT_N_1).

:- pred temperingParameters(int, int).
:- mode temperingParameters(out, out) is det.

temperingParameters(0x9D2C5680, 0xEFC60000).

:- pred debugInt(int::in, int::in, supply::in, supply::out, io::di, io::uo) is det.

debugInt(I, N, !Supply, !IO) :-
	(if
		I = N
	then
		true
	else
		random(Number, !Supply),
		io.format("%10d ", [i(Number)], !IO),
		(if
			I mod 5 = 4
		then
			io.nl(!IO)
		else
			true
		),
		debugInt(I + 1, N, !Supply, !IO)
	).

:- pred debugFloat(int::in, int::in, supply::in, supply::out, io::di, io::uo) is det.

debugFloat(I, N, !Supply, !IO) :-
	(if
		I = N
	then
		true
	else
		randomFloat_c0_c1(Number, !Supply),
		io.format("%10.8f ", [f(Number)], !IO),
		(if
			I mod 5 = 4
		then
			io.nl(!IO)
		else
			true
		),
		debugFloat(I + 1, N, !Supply, !IO)
	).

:- pred debugValue(
	pred(T, supply, supply) :: in(pred(out, in, out) is det),
	T   :: in,
	int :: in,
	supply   :: in,  supply   :: out,
	io.state :: di,  io.state :: uo
) is det.

debugValue(Generator, Target, Trial, !Supply, !IO) :-
	Generator(Value, !Supply),
	(if
		Value = Target
	then
		io.format("Got value after %d trials\n", [i(Trial)], !IO)
	else
		debugValue(Generator, Value, Trial + 1, !Supply, !IO)
	).

:- end_module mersenneTwister.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
