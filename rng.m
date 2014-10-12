/**
 * Provides a type class that represents a pseudo-random number generator.

 * @author Pedro Mariano
 * @version 1.0 2012/06/ 4
 */
:- module rng.

:- interface.

:- include_module distribution.

:- import_module mersenneTwister.
:- import_module bool, list, random.

/**
 * Basic pseudo-random number generator.  Only provides a method to return
 * a pseudo-random integer in a given range.
  
 */
:- typeclass bPRNG(R) where
  [
	/**
	 * maxValue(Random) = Value
	  
	 * Return the maximum value that can be returned by the pseudo-random
	 * number generator.
	 */
	func maxValue(R) = int,

	/**
	 * minValue(PRNG) = Value
	 
	 * Return the minimum value that can be returned by the pseudo-random
	 * number generator.
	  
	 */
	func minValue(R) = int,
	/**
	 * nextInt(Result, !Random)

	 * Unify {@code Result} with the next integer value returned by the
	 * pseudo-random number generator {@code Random}.
	 */
	pred nextInt(int, R, R),
	mode nextInt(out, in, out) is det
].

/**
 * This type class extends class {@code bPRNG} and adds further methods to
 * return other random values.
 */
:- typeclass ePRNG(R) <= bPRNG(R) where
  [
	pred 'nextFloat[0,1]'(float, R, R),
	mode 'nextFloat[0,1]'(out, in, out) is det,

	pred 'nextFloat[0,1['(float, R, R),
	mode 'nextFloat[0,1['(out, in, out) is det,

	pred 'nextFloat]0,1]'(float, R, R),
	mode 'nextFloat]0,1]'(out, in, out) is det,

	/**
	 * nextInt(Min, Max, Result, !Random)
	 */
	pred nextInt(int, int, int, R, R),
	mode nextInt(in, in, out, in, out) is det,

	pred flipCoin(float, bool, R, R),
	mode flipCoin(in, out, in, out) is det
].

/**
 * Return a floating point in the range [0,1] inclusive using a basic
 * pseudo-random number generator.
  
 */
:- pred nextFloatB(float, R, R) <= bPRNG(R).
:- mode nextFloatB(out, in, out) is det.

/**
 * Flip a biased coin using a basic
 * pseudo-random number generator.
 */
:- pred flipCoinB(float, bool, R, R) <= bPRNG(R).
:- mode flipCoinB(in, out, in, out) is det.

/**
 * randomElementList(List, Result, !Random)
  
 * Unify {@code Result} with a random element from list {@code List}.  Fails if the list is empty.
 */
:- pred randomElementList(list(T), T, R, R)
	<= ePRNG(R).
:- mode randomElementList(in, out, in, out) is semidet.

/**
 * randomElementList_det(List, Result, !Random)
  
 * Unify {@code Result} with a random element from list {@code List}.
 * Throws an exception if the list is empty.

 * @param Random Pseudo-random number generator used to draw an element.
 */

:- pred randomElementList_det(list(T), T, R, R)
	<= ePRNG(R).
:- mode randomElementList_det(in, out, in, out) is det.

/**
 * randomElementsList(HowMany, List, Result, !Random)
  
 * Unify {@code Result} with {@code HowMany} random elements from list
 * {@code List}.

 */

:- pred randomElementsList(int, list(T), list(T), R, R)
	<= ePRNG(R).
:- mode randomElementsList(in, in, out, in, out) is det.

:- instance ePRNG(random.supply).

:- instance bPRNG(random.supply).

/**
 * The Mersenne Twister pseudo-random number generator is an instance of
 * type class {@code bPRNG}.
 */
:- instance bPRNG(mersenneTwister.supply).

/**
 * The Mersenne Twister pseudo-random number generator is an instance of
 * type class {@code ePRNG}.
 */
:- instance ePRNG(mersenneTwister.supply).

:- implementation.

:- import_module exception, int, float.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

:- instance bPRNG(random.supply) where
[
	func(maxValue/1) is randomMaxValue,
	func(minValue/1) is zero,
	pred(nextInt/3) is random
].

:- instance ePRNG(random.supply) where
[
	pred(nextInt/5) is randomNextInt,
	pred('nextFloat[0,1]'/3) is randomNextFloat_c0_c1,
	pred('nextFloat[0,1['/3) is randomNextFloat_c0_o1,
	pred('nextFloat]0,1]'/3) is randomNextFloat_o0_c1,
	pred(flipCoin/4) is randomFlipCoin
].

:- instance bPRNG(mersenneTwister.supply) where
[
	func(maxValue/1) is mersenneTwister.maxNumber,
	func(minValue/1) is zero,
	pred(nextInt/3) is mersenneTwister.random
].

:- instance ePRNG(mersenneTwister.supply) where
[
	pred(nextInt/5) is mersenneTwister.random,
	pred('nextFloat[0,1]'/3) is mersenneTwister.randomFloat_c0_c1,
	pred('nextFloat[0,1['/3) is mersenneTwister.randomFloat_c0_o1,
	pred('nextFloat]0,1]'/3) is mersenneTwister.randomFloat_o0_c1,
	pred(flipCoin/4) is mersenneTwisterFlipCoin
].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of private types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of exported predicates and functions

nextFloatB(Value, !PRNG) :-
	nextInt(Int, !PRNG),
	Min = float(minValue(!.PRNG)),
	Max = float(maxValue(!.PRNG)),
	Value = (float(Int) - Min) / (Max - Min).

flipCoinB(Probability, Result, !PRNG) :-
	(if
		Probability > 0.0
	then
		nextFloatB(Value, !PRNG),
		(if
			Value =< Probability
		then
			Result = yes
		else
			Result = no
		)
	else
		Result = no
	).

randomElementList(List, Result, !Random) :-
	nextInt(0, list.length(List) - 1, Index, !Random),
	list.index0(List, Index, Result).

randomElementList_det(List, Result, !Random) :-
	(if
		randomElementList(List, R, !Random)
	then
		Result = R
	else
		throw("randomElementList_det: list is empty")
	).

randomElementsList(HowMany, List, Result, !Random) :-
	(if
		HowMany = 0
	then
		Result = []
	else
		nextInt(0, list.length(List) - 1, Index, !Random),
		det_remove0_nth(List, Index, Element, NextList),
		randomElementsList(HowMany - 1, NextList, RestResult, !Random),
		Result = [Element | RestResult]
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of private predicates and functions

:- func randomMaxValue(random.supply) = int.

randomMaxValue(Random) = Result :-
	random.randmax(Result, Random, _).

/**
 * This function always returns zero.
 */
:- func zero(T) = int.

zero(_Random) = 0.

/**
 * This function always returns {@code int.max_int}.
 */
:- func maxint(T) = int.

maxint(_Random) = int.max_int.

:- pred randomNextFloat_c0_c1(float, random.supply, random.supply).
:- mode randomNextFloat_c0_c1(out, in, out) is det.

randomNextFloat_c0_c1(Result, !Random) :-
	random.random(Value, !Random),
	random.randmax(MaxValue, !.Random, _),
	Result = float(Value) / float(MaxValue).

:- pred randomNextFloat_c0_o1(float, random.supply, random.supply).
:- mode randomNextFloat_c0_o1(out, in, out) is det.

randomNextFloat_c0_o1(Result, !Random) :-
	random.random(Value, !Random),
	random.randcount(MaxCount, !.Random, _),
	Result = float(Value) / float(MaxCount).

:- pred randomNextFloat_o0_c1(float, random.supply, random.supply).
:- mode randomNextFloat_o0_c1(out, in, out) is det.

randomNextFloat_o0_c1(Result, !Random) :-
	random.random(Value, !Random),
	random.randcount(MaxCount, !.Random, _),
	Result = (1.0 + float(Value)) / float(MaxCount).

:- pred randomNextInt(int, int, int, random.supply, random.supply).
:- mode randomNextInt(in, in, out, in, out) is det.

randomNextInt(Min, Max, Result, !Random) :-
	random.random(Min, Max - Min + 1, Result, !Random).

:- pred randomFlipCoin(float, bool, random.supply, random.supply).
:- mode randomFlipCoin(in, out, in, out) is det.

randomFlipCoin(Probability, Result, !Random) :-
	(if
		Probability = 0.0
	then
		Result = no
	else if
		Probability = 1.0
	then
		Result = yes
	else
		random.random(Value, !Random),
		random.randmax(MaxValue, !.Random, _),
		(if
			float(Value) / float(MaxValue) =< Probability
		then
			Result = yes
		else
			Result = no
		)
	).

:- pred mersenneTwisterFlipCoin(float, bool, mersenneTwister.supply, mersenneTwister.supply).
:- mode mersenneTwisterFlipCoin(in, out, in, out) is det.

mersenneTwisterFlipCoin(Probability, Result, !Random) :-
	(if
		Probability = 0.0
	then
		Result = no
	else if
		Probability = 1.0
	then
		Result = yes
	else
		mersenneTwister.randomFloat_c0_o1(Value, !Random),
		(if
			Value < Probability
		then
			Result = yes
		else
			Result = no
		)
	).

/**
 * det_remove0_nth(List, Index, Element, Remainder)
  
 * Unify {@code Element} with the {@code Index}th element of list {@code
 * List} and unify {@code Remainders} with the remainder elements.
  
 */
:- pred det_remove0_nth(list(T), int, T, list(T)).
:- mode det_remove0_nth(in, in, out, out) is det.

det_remove0_nth(List, Index, Element, Remainder) :-
	(if
		Index = 0
	then
		List = [Element | Remainder]
		;
		List = [],
		throw("rng.det_remove0_nth/4: Invalid index")
	else
		List = [Head | Tail],
		det_remove0_nth(Tail, Index - 1, Element, RestRemainder),
		Remainder = [Head | RestRemainder]
		;
		List = [],
		throw("rng.det_remove0_nth/4: Invalid index)")
	).

:- end_module rng.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
