/**
 * Provides type {@code distribution} that is used to compute random
 * distributions.

 * @author Pedro Mariano
 * @version 1.0 2012/07/13
 */
:- module rng.distribution.

:- interface.

/**
 * This type is used to compute some random distributions.
 */
:- type distribution.

/**
 * Initialise a distribution based on a extended pseudo-random number generator.
 */
:- func init = distribution.

/**
 * unitGaussian
 */
:- pred unitGaussian(float, distribution, distribution, R, R)
	<= ePRNG(R).
:- mode unitGaussian(out, in, out, in, out) is det.

:- implementation.

:- import_module float, math, maybe.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

:- type distribution --->
	distribution(
		cachedGaussian::maybe(float)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of private types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of exported predicates and functions

init = Result :-
	Result^cachedGaussian = no.

unitGaussian(Result, DistributionIn, DistributionOut, !Random) :-
	DistributionIn^cachedGaussian = yes(Result),
	DistributionOut = 'cachedGaussian :='(DistributionIn, no)
	;
	DistributionIn^cachedGaussian = no,
	computeGaussian(Value1, Result, !Random),
	DistributionOut = 'cachedGaussian :='(DistributionIn, yes(Value1))
	.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of private predicates and functions

:- pred computeGaussian(float, float, R, R)
	<= ePRNG(R).
:- mode computeGaussian(out, out, in, out) is det.

computeGaussian(Value1, Value2, !Random) :-
	rng.nextFloat(V1, !Random),
	rng.nextFloat(V2, !Random),
	SV1 = 2.0 * V1 - 1.0,
	SV2 = 2.0 * V2 - 1.0,
	RSquare = SV1 * SV1 + SV2 * SV2,
	(if
		RSquare >= 1.0
		;
		RSquare = 0.0
	then
		computeGaussian(Value1, Value2, !Random)
	else
		Val = -2.0 * math.ln(RSquare) / RSquare,
		(if
			Val > 0.0
		then
			Factor = math.sqrt(Val)
		else
			Factor = 0.0
		),
		Value1 = Factor * SV1,
		Value2 = Factor * SV2
	).

:- end_module rng.distribution.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
