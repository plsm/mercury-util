/**
 * 

 * @author Pedro Mariano
 * @version 1.0 2014/09/25
 */
:- module debug.

:- interface.

:- import_module io.

:- pred main(io.state, io.state).
:- mode main(di, uo) is det.

:- implementation.

:- import_module rng, random, mersenneTwister.
:- import_module float, int, list, string.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of private types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of exported predicates and functions

main(!IO) :-
	random.init(10, Rnd1),
	trials(10, 0.1, Rnd1, _, !IO),
	io.nl(!IO),
	trials(10, 0.1, mersenneTwister.init(10), _, !IO),
	true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of private predicates and functions

:- pred trials(int, float, R, R, io.state, io.state)
<= ePRNG(R).
:- mode trials(in, in, in, out, di, uo) is det.

trials(HowMany, Probability, !Random, !IO) :-
	rng.flipCoin(Probability, DiessCC, !Random),
%	rng.nextFloat(Float, !Random),
	rng.nextInt(Int, !Random),
	Float = float(Int) / float(int.max_int),
	io.format("%10f  Trial #%3d => %s\n",
		[
		 %i(Int),
		 f(Float),
		 i(HowMany), s(string(DiessCC))], !IO),
	(if
		HowMany > 0
	then
		trials(HowMany - 1, Probability, !Random, !IO)
	else
		true
	).

:- end_module debug.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
