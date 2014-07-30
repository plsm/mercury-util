/**
 * Provides a type to represent fast rational numbers using two integers.

 * @author Pedro Mariano
 * @version 1.0 2014/01/ 9
 */
:- module fraction.

:- interface.

:- import_module userInterface, parseable.
:- import_module io, list.

:- type fraction --->
	fraction(
		numerator   :: int,
		denominator :: int
	).

:- instance parseable(fraction).

:- func zero = fraction.

:- func one = fraction.

/**
 * Convert a fraction to the most approximate floating point number.
 */
:- func float(fraction) = float.

/**
 * Convert a fraction to the most approximate natural number.
 */
:- func int(fraction) = int.

/**
 * Convert a floating point number to a fraction
 */
:- func fraction(float) = fraction.


:- func fraction ++ int = fraction.
:- func fraction -- int = fraction.
:- func fraction ** int = fraction.
:- func fraction // int = fraction.

:- func fraction + fraction = fraction.
:- func fraction - fraction = fraction.
:- func fraction * fraction = fraction.
:- func fraction / fraction = fraction.

:- func dialogAction(get(D, fraction), set(D, fraction)) = dialogAction(D).

:- pred print(io.output_stream, fraction, io.state, io.state).
:- mode print(in, in, di, uo) is det.

:- pred parse(fraction, list(int), list(int)).
:- mode parse(in, out, in) is det.
:- mode parse(out, in, out) is semidet.

:- implementation.

:- import_module char, float, int, list, math, maybe, string.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

:- instance parseable(fraction) where
[
	pred(parse/3) is fraction.parse
].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of private types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of exported predicates and functions

zero = fraction(0, 1).

one = fraction(1, 1).

float(F) = float(F^numerator) / float(F^denominator).

int(F) = F^numerator / F^denominator.

fraction(Working) = Result :-
	(if
		Working = 0.0
	then
		Result^numerator = 0,
		Result^denominator = 1
	else
		toFraction(Working, 0, Result^numerator, D),
		Result^denominator = int.pow(10, D)
	).

F ++ X = reduce(N0, D0, int.abs(N0), int.abs(D0)) :-
	N0 = F^numerator + X * F^denominator,
	D0 = F^denominator.

F -- X = reduce(N, D, int.abs(N), int.abs(D)) :-
	N = F^numerator - X * F^denominator,
	D = F^denominator.

F ** X = reduce(N, D, int.abs(N), int.abs(D)) :-
	N = F^numerator * X,
	D = F^denominator.

F // X = reduce(N, D, int.abs(N), int.abs(D)) :-
	N = F^numerator,
	D = F^denominator * X.

F1 + F2 = reduce(N, D, int.abs(N), int.abs(D)) :-
	N = F1^numerator * F2^denominator + F2^numerator * F1^denominator,
	D = F1^denominator * F2^denominator.

F1 - F2 = reduce(N, D, int.abs(N), int.abs(D)) :-
	N = F1^numerator * F2^denominator - F2^numerator * F1^denominator,
	D = F1^denominator * F2^denominator.

F1 * F2 = reduce(N, D, int.abs(N), int.abs(D)) :-
	N = F1^numerator * F2^numerator,
	D = F1^denominator * F2^denominator.

F1 / F2 = reduce(N, D, int.abs(N), int.abs(D)) :-
	N = F1^numerator * F2^denominator,
	D = F1^denominator * F2^numerator.

dialogAction(Get, Set) = updateFieldString(getStringFromFraction(Get), setFractionFromString(Set)).

print(Stream, Fraction, !IO) :-
	io.print(Stream, Fraction^numerator, !IO),
	io.print(Stream, "/", !IO),
	io.print(Stream, Fraction^denominator, !IO).

parse(Probability) -->
	parseable.int32(Probability^numerator),
	parseable.int32(Probability^denominator).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of private predicates and functions

:- func reduce(int, int, int, int) = fraction.

reduce(A0, B0, A, B) =
	(if
		B = 0
	then
		fraction(1, 0)
	else if
		A = 0
	then
		zero
	else
		reduceRec(A0, B0, A, B)
	).

:- func reduceRec(int, int, int, int) = fraction.

reduceRec(A0, B0, A, B) =
	(if
		A = B
	then
		loosePrecision(A0 / A, B0 / B)
	else if
		A > B
	then
		reduceRec(A0, B0, A - B, B)
	else
		reduceRec(A0, B0, A, B - A)
	).

:- func maxPrecision = int.

maxPrecision = 256 * 128.

/**
 * Shift the numerator and denominator until they are less than 256*128
 */
:- func loosePrecision(int, int) = fraction.

loosePrecision(A, B) =
	(if
		A > maxPrecision
		;
		A < -maxPrecision
	then
		(if
			B = 1
		then
			loosePrecision(A / 2, 1)
		else if
			B = -1
		then
			loosePrecision(A / 2, -1)
		else
			loosePrecision(A / 2, B / 2)
		)
	else if
		B > maxPrecision
		;
		B < -maxPrecision
	then
		(if
			A = 1
		then
			loosePrecision(1, B / 2)
		else if
			A = -1
		then
			loosePrecision(-1, B / 2)
		else
			loosePrecision(A / 2, B / 2)
		)
	else
		fraction(A, B)
	).

:- func getStringFromFraction(get(D, fraction), D) = string.

getStringFromFraction(Get, Data) = Result :-
	Get(Data) = Fraction,
	(if
		Fraction^numerator = 0
	then
		Result = "0"
	else if
		Fraction^numerator = Fraction^denominator
	then
		Result = "1"
	else
		Result = string(float(Fraction^numerator) / float(Fraction^denominator))
	).

:- func setFractionFromString(set(D, fraction), D, string) = setResult(D).

setFractionFromString(Set, Data, String) = Result :-
	(if
		string.to_float(String, Value)
	then
		fraction(Value) = Fraction,
		Result = Set(Data, Fraction)
	else if
		string.split_at_separator(division, String) = [SNum, SDen],
		string.to_int(SNum, Fraction^numerator),
		string.to_int(SDen, Fraction^denominator)
	then
		Result = Set(Data, Fraction)
	else
		Result = error("invalid fraction")
	).

:- pred division(char).
:- mode division(in) is semidet.

division('/').

:- pred toFraction(float, int, int, int).
:- mode toFraction(in, in, out, out) is det.

toFraction(Working, AC, Numerator, D) :-
%	trace[io(!IO)] (io.format("> toFraction(%f, %d, ?, ?)\n", [f(Working), i(AC)], !IO)),
%	trace[io(!IO)] (io.format("< toFraction(%f, %d, %d, %d)\n", [f(Working), i(AC), i(Numerator), i(D)], !IO)),
	(if
		Working = 0.0
		;
		AC > maxPrecision / 10
	then
		Numerator = AC,
		D = -1
	else
		NextAC = AC * 10 + float.truncate_to_int(Working),
		toFraction((Working - math.floor(Working)) * 10.0, NextAC, Numerator, NextD),
		D = NextD + 1
	).


:- end_module fraction.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
