/**
 * 

 * @author Pedro Mariano
 * @version 1.0 2010/01/ 8
 */
:- module probability.

:- interface.

:- import_module userInterface, fraction.
:- import_module rng, rng.distribution, mersenneTwister.
:- import_module bool, io, list.

/**
 * Represents a probability value.
 */
:- type probability.

:- func zero = probability.

:- func one = probability.

:- func inverse(probability) = probability.

:- func init(float) = probability.

:- pred init(float, probability).
:- mode init(in, out) is semidet.

%:- pred flipCoin(float, bool, mersenneTwister.supply, mersenneTwister.supply).

:- pred flipCoin(probability, bool, R, R) <= ePRNG(R).
:- mode flipCoin(in, out, in, out) is det.

%:- pred flipCoin(bool, mersenneTwister.supply, mersenneTwister.supply).

% :- pred flipCoin(bool, R, R) <= ePRNG(R).
% :- mode flipCoin(out, in, out) is det.

/**
 * Convert a probability value to a fraction.
 */
:- func fraction(probability) = fraction.

:- func float(probability) = float.

/**
 * geometric(Probability, X, !Supply)

 * Unifies {@code X} with a number drawn from a geometric distribution.
 * Numbers are calculated using a geometric distribution with success
 * probability given by parameter {@code Probability}.
 */
:- pred geometric(float, int, mersenneTwister.supply, mersenneTwister.supply).
:- mode geometric(in, out, in, out) is det.

/**
 * seedClock(Seed, !IO)

 * Unify {@code Seed} with a seed calculated using the current time.
 */
:- pred seedClock(int, io, io).
:- mode seedClock(out, di, uo) is det.

/**
 * Adds Gaussian noise to the given probability.  The normal distribution
 * has average zero.
  
 */
:- pred addGaussianNoise(float, probability, probability, distribution, distribution, R, R) <= ePRNG(R).
:- mode addGaussianNoise(in, in, out, in, out, in, out) is det.


:- func dialogAction(get(D, probability), set(D, probability)) = dialogAction(D).

:- pred print(io.output_stream, probability, io.state, io.state).
:- mode print(in, in, di, uo) is det.

:- pred parse(probability, list(int), list(int)).
:- mode parse(in, out, in) is det.
:- mode parse(out, in, out) is semidet.


:- implementation.

:- import_module fraction, parseable.
:- import_module char, exception, float, int, math, maybe, string, time.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

:- type probability == fraction.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of private types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of exported predicates and functions

zero = fraction.zero.

one = fraction.one.

inverse(P) = fraction(P^denominator - P^numerator, P^denominator).

init(Value, Probability) :-
	Value >= 0.0,
	Value =< 1.0,
	Probability = fraction.fraction(Value).

init(Value) =
	(if
		init(Value, Probability)
	then
		Probability
	else
		throw("Invalid probability value")
	).

fraction(P) = P.

float(P) = float(P^numerator) / float(P^denominator).

% flipCoin(Probability, X, !Supply) :-
% 	randomFloat(R, !Supply),
% 	(if
% 		R =< Probability
% 	then
% 		X = yes
% 	else
% 		X = no).

% flipCoin(X, !Supply) :-
% 	randomFloat(R, !Supply),
% 	(if
% 		R =< 0.5
% 	then
% 		X = yes
% 	else
% 		X = no).

flipCoin(Probability, X, !Random) :-
	(if
		Probability = probability.one
	then
		X = yes
	else if
		Probability = probability.zero
	then
		X = no
	else
		rng.nextInt(1, Probability^denominator, R, !Random),
		(if
			Probability^numerator >= R
		then
			X = yes
		else
			X = no
		)
	).

geometric(Probability, X, !Supply) :-
	mersenneTwister.randomFloat_c0_o1(R, !Supply),
	(if
		R < Probability
	then
		X = 1 + Rest,
		geometric(Probability, Rest, !Supply)
	else
		X = 0).

addGaussianNoise(StdDev, Probability, Result, !Distribution, !Random) :-
	distribution.unitGaussian(Perturb0, !Distribution, !Random),
	Perturb = Perturb0 * StdDev,
	Result = fraction.fraction(float.max(0.0, float.min(probability.float(Probability) + Perturb, 1.0)))
	.

seedClock(Seed, !IO) :-
	promise_equivalent_solutions [ERFactor, !:IO] exception.try_io(time.clock, ERFactor, !IO),
	(
		ERFactor = succeeded(Factor1)
		;
		ERFactor = exception(_),
		io.print(io.stderr_stream, "Exception in time.clock/3\n", !IO),
		Factor1 = 1223
	),
	time.time(Time, !IO),
	time.localtime(Time) = TM,
	Factor2 = TM^tm_sec + 62 * (TM^tm_min + 60 * (TM^tm_hour + 24 * (TM^tm_mday - 1 + 31 * (TM^tm_mon + 12 * TM^tm_year)))),
	TimePred =
	(pred(F::out, I::di, O::uo) is det :-
		time.times(_, F, I, O)
	),
	promise_equivalent_solutions [ERFactor3, !:IO] exception.try_io(TimePred, ERFactor3, !IO),
	(
		ERFactor3 = succeeded(Factor3)
		;
		ERFactor3 = exception(_),
		io.print(io.stderr_stream, "Exception in time.times/4\n", !IO),
		Factor3 = 17
	),
	Seed = Factor1 + Factor2 + Factor3.

dialogAction(Get, Set) = updateFieldString(getStringFromProbability(Get), setProbabilityFromString(Set)).

print(Stream, Probability, !IO) :-
	io.print(Stream, Probability^numerator, !IO),
	io.print(Stream, "/", !IO),
	io.print(Stream, Probability^denominator, !IO).

parse(Probability) -->
	parseable.int32(Probability^numerator),
	parseable.int32(Probability^denominator).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of private predicates and functions

:- func getStringFromProbability(get(D, probability), D) = string.

getStringFromProbability(Get, Data) = Result :-
	Get(Data) = Probability,
	(if
		Probability^numerator = 0
	then
		Result = "0"
	else if
		Probability^numerator = Probability^denominator
	then
		Result = "1"
	else
		Result = string(float(Probability^numerator) / float(Probability^denominator))
	).

:- func setProbabilityFromString(set(D, probability), D, string) = setResult(D).

setProbabilityFromString(Set, Data, String) = Result :-
	(if
		string.to_float(String, Value),
		Value >= 0.0,
		Value =< 1.0
	then
		probability.init(Value) = Probability,
		Result = Set(Data, Probability)
	else if
		string.split_at_separator(division, String) = [SNum, SDen],
		string.to_int(SNum, Probability^numerator),
		string.to_int(SDen, Probability^denominator)
	then
		Result = Set(Data, Probability)
	else
		Result = error("invalid probability")
	).

:- pred division(char).
:- mode division(in) is semidet.

division('/').

% :- pred toProbability(float, int, int).
% :- mode toProbability(in, out, out) is det.

% toProbability(Working, Numerator, Denominator) :-
% 	(if
% 		Working = 0.0
% 	then
% 		Numerator = 0,
% 		Denominator = 1
% 	else
% 		toProbability(Working, 0, Numerator, D),
% 		Denominator = int.pow(10, D)
% 	).

% :- import_module string, list.

% :- pred toProbability(float, int, int, int).
% :- mode toProbability(in, in, out, out) is det.

% toProbability(Working, AC, Numerator, D) :-
% %	trace[io(!IO)] (io.format("> toProbability(%f, %d, ?, ?)\n", [f(Working), i(AC)], !IO)),
% %	trace[io(!IO)] (io.format("< toProbability(%f, %d, %d, %d)\n", [f(Working), i(AC), i(Numerator), i(D)], !IO)),
% 	(if
% 		Working = 0.0
% 		;
% 		AC > 256 * 128
% 	then
% 		Numerator = AC,
% 		D = -1
% 	else
% 		NextAC = AC * 10 + float.truncate_to_int(Working),
% 		toProbability((Working - math.floor(Working)) * 10.0, NextAC, Numerator, NextD),
% 		D = NextD + 1
% 	).

:- end_module probability.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
