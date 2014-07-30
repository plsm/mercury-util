/**
 * An implementation of the Mersenne Twister pseudo-random number generator.

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

:- import_module bool, integer, io, list, rational.

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
 * random(Num, RS0, RS)

 * Extracts a number Num in the range 0 .. RandMax from the random number
 * supply RS0, and binds RS to the new state of the random number supply.
 */
:- pred random(integer, supply, supply).
:- mode random(out, in, out) is det.
%:- mode random(out, di, uo) is det.

/**
 * random(Min, Max, Number, SupplyIn, SupplyOut)
 */
:- pred random(int, int, integer, supply, supply).
:- mode random(in, in, out, in, out) is det.
%:- mode random(in, in, out, di, uo) is det.

/**
 * Return a random floating point number between 0 and 1.
 */
:- pred randomFloat(float, supply, supply).
:- mode randomFloat(out, in, out) is det.
%:- mode randomFloat(out, di, uo) is det.

/**
 * Unify {@code Value} with a random boolean value.
 */
:- pred randomBool(bool, supply, supply).
:- mode randomBool(out, in, out) is det.

/**
 * Return a random rational number between 0 and 1.
 */
:- pred randomRational(rational, supply, supply).
:- mode randomRational(out, in, out) is det.

/**
 * permutation(List, RandomList, !Supply)

 * Unifies {@code RandomList} with a random permutation of list {@code List}.
 */
:- pred permutation(list(T), list(T), supply, supply).
:- mode permutation(in, out, in, out) is det.
%:- mode permutation(in, out, di, uo) is det.

:- pred print(supply::in, io::di, io::uo) is det.

/**
 * debug(!IO)

 * Prints 1000 random number generators on the standard output stream.
 */
:- pred debug(io::di, io::uo) is det.

:- implementation.

:- import_module array, exception, float, int, string.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

:- type supply --->
	supply(
		stateVector::array(integer),
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
	Area0 = array.init(recurrenceDegree, integer(Seed) /\ det_from_base_string(16, "FFFFFFFF")),
	Area1 = initWorkingArea(Area0, 1),
	generateWordsA(0, Area1, Area2),
%	periodParameters(N, _),
	Supply = supply(Area2, 0).

random(Number, SupplyIn, SupplyOut) :-
	periodParameters(N, _),
	(if
		SupplyIn^index = N
	then
		generateWordsA(0, SupplyIn^stateVector, NextState),
		MTI = 0
	else
		NextState = SupplyIn^stateVector,
		MTI = SupplyIn^index),
	temperingParameters(B, C),
	Y0 = array.lookup(NextState, MTI),
	Y1 = integer.xor(Y0,  Y0 >> 11),
	Y2 = integer.xor(Y1, (Y1 <<  7) /\ B),
	Y3 = integer.xor(Y2, (Y2 << 15) /\ C),
	Y4 = integer.xor(Y3, (Y3 >> 18)),
	Number = Y4,
	SupplyOut = supply(NextState, MTI + 1).

random(Min, Max, Number, SupplyIn, SupplyOut) :-
	random(N, SupplyIn, SupplyOut),
	Number = integer(Min) + N * (integer(Max - Min) + integer.one) // integer.det_from_base_string(16, "FFFFFFFF").

randomFloat(Number, !Supply) :-
	random(Integer, !Supply),
	Max = integer.det_from_base_string(16, "FFFFFFFF"),
	Number = integer.float(Integer) / integer.float(Max).

randomBool(Value, !Supply) :-
	random(Integer, !Supply),
	(if
		Integer =< integer.det_from_base_string(16, "7FFFFFFF")
	then
		Value = yes
	else
		Value = no).

randomRational(Number, !Supply) :-
	random(Integer, !Supply),
	Number = rational.from_integers(Integer, integer.det_from_base_string(16, "FFFFFFFF")).

permutation(List0, List, RS0, RS) :-
	Samples = array(List0),
	Len = array.size(Samples),
	perform_sampling(Len, Samples, [], List, RS0, RS).

print(Supply, !IO) :-
	io.format("mti = %d\nState vector:\n", [i(Supply^index)], !IO),
	array.foldl2(
		(pred(MT::in, I::in, (I + 1)::out, IOin::di, IOout::uo) is det :-
			io.format("%10s ", [s(to_string(MT))], IOin, IO1),
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
	io.format("%d random natural numbers returned by random/3 with seed %d\n", [i(N), i(Seed)], !IO),
	debug(0, 0, N, Supply, _, !IO),
	io.format("%d random floating point numbers returned by randomFloat/3 with seed %d\n", [i(N), i(Seed)], !IO),
	debug(1, 0, N, Supply, _, !IO),
	io.format("%d random boolean values returned by randomBool/3 with seed %d\n", [i(N), i(Seed)], !IO),
	debug(2, 0, N, Supply, _, !IO),
	io.format("%d random rational numbers returned by randomRational/3 with seed %d\n", [i(N), i(Seed)], !IO),
	debug(3, 0, N, Supply, _, !IO),
	Min = 5,
	Max = 10,
	io.format("%d random natural numbers from the range [%d,%d] returned by random/5 with seed %d\n", [i(N), i(Min), i(Max), i(Seed)], !IO),
	debug(4, 0, N, Supply, _, !IO).

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

:- func matrixA = integer.

matrixA = integer.det_from_base_string(16, "9908B0DF").

/**
 * Most significant {@code w - r} bits.
 */
:- func upperMask = integer.

upperMask = integer.det_from_base_string(16, "80000000").

/**
 * Least significant r bits.
 */
:- func lowerMask = integer.

lowerMask = integer.det_from_base_string(16, "7FFFFFFF").

:- func initWorkingArea(array(integer), int) = array(integer).

initWorkingArea(Area, Index) = Result :-
	periodParameters(N, _),
	MT_I_1 = array.lookup(Area, Index - 1),
	ShiftedMT_I_1 = MT_I_1 >> 30,
	NewMT_I =
		(	  integer(1812433253)
			* integer.xor(MT_I_1, ShiftedMT_I_1)
		+ integer(Index))
		/\ integer.det_from_base_string(16, "FFFFFFFF"),
%	NewMT_I = (array.lookup(Area, Index + 1) * 69069) /\ 0xFFFFFFFF,
	Area1 = array.slow_set(Area, Index, NewMT_I),
	(if
		Index = N - 1
	then
		Result = Area1
	else
		Result = initWorkingArea(Area1, Index + 1)).

:- pred generateWordsA(int, array(integer), array(integer)).
:- mode generateWordsA(in, in, out) is det.
%:- mode generateWordsA(in, di, uo) is det.

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
		ShiftedY = Y >> 1,
		(if
			Y /\ integer.one = integer.zero
		then
			Mag01 = integer.zero
		else
			Mag01 = matrixA),
		NewMT_I = integer.xor(integer.xor(MT_I_M, ShiftedY), Mag01),
		generateWordsA(Index + 1, array.slow_set(AreaIn, Index, NewMT_I), AreaOut)
	).

:- pred generateWordsB(int, array(integer), array(integer)).
:- mode generateWordsB(in, in, out) is det.
%:- mode generateWordsB(in, di, uo) is det.

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
		ShiftedY = Y >> 1,
		(if
			Y /\ integer.one  = integer.zero
		then
			Mag01 = integer.zero
		else
			Mag01 = matrixA),
		NewMT_I = integer.xor(integer.xor(MT_I_M_N, ShiftedY), Mag01),
		generateWordsB(Index + 1, array.slow_set(!.Area, Index, NewMT_I), !:Area)
	).

:- pred generateWordsC(array(integer), array(integer)).
:- mode generateWordsC(in, out) is det.
%:- mode generateWordsC(di, uo) is det.

generateWordsC(!Area) :-
	periodParameters(N, M),
	MT_N_1 = array.lookup(!.Area, N - 1),
	MT_0 = array.lookup(!.Area, 0),
	Y = (MT_N_1 /\ upperMask) \/ (MT_0 /\ lowerMask),
	MT_M_1 = array.lookup(!.Area, M - 1),
	ShiftedY = Y >> 1,
	(if
		Y /\ integer.one  = integer.zero
	then
		Mag01 = integer.zero
	else
		Mag01 = matrixA),
	NewMT_N_1 = integer.xor(integer.xor(MT_M_1, ShiftedY), Mag01),
	!:Area = array.slow_set(!.Area, N - 1, NewMT_N_1).

:- pred temperingParameters(integer, integer).
:- mode temperingParameters(out, out) is det.

temperingParameters(det_from_base_string(16, "9D2C5680"), det_from_base_string(16, "EFC60000")).

:- pred perform_sampling(int, array(T), list(T), list(T), supply, supply) is det.
:- mode perform_sampling(in, array_di, in, out, in, out) is det.
%:- mode perform_sampling(in, array_di, in, out, di, uo) is det.

perform_sampling(I, Record0, Order0, Order, RS0, RS) :-
	(if
		I =< 0
	then
		Order = Order0,
		RS = RS0
	else
		I1 = I - 1,
		random(0, I - 1, Index, RS0, RS1),
		array.lookup(Record0, integer.int(Index), Next),
		array.lookup(Record0, I1, MaxImage),
		Order1 = [Next | Order0],
		array.set(integer.int(Index), MaxImage, Record0, Record1),
		array.set(I1, Next, Record1, Record2),
		perform_sampling(I1, Record2, Order1, Order, RS1, RS)
	).

:- pred debug(int::in, int::in, int::in, supply::in, supply::out, io::di, io::uo) is det.

debug(W, I, N, !Supply, !IO) :-
	(if
		I = N
	then
		true
	else
		(if
			W = 0
		then
			random(Number, !Supply),
			io.format("%10s ", [s(integer.to_string(Number))], !IO)
		else if
			W = 1
		then
			randomFloat(Number, !Supply),
			io.format("%10f ", [f(Number)], !IO)
		else if
			W = 2
		then
			randomBool(Bool, !Supply),
			io.format("%10s ", [s(string.string(Bool))], !IO)
		else if
			W = 3
		then
			true
		else % W = 4
			Min = 5,
			Max = 10,
			random(Min, Max, Number, !Supply),
			io.format("%10s ", [s(integer.to_string(Number))], !IO)
		),
		(if
			I mod 5 = 4
		then
			io.nl(!IO)
		else
			true),
		debug(W, I + 1, N, !Supply, !IO)).

:- end_module mersenneTwister.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
