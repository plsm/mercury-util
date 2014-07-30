/**
 * This module provides a type class that represents objects capable of
 * being folded.

 * @author Pedro Mariano
 * @version 1.0 2013/05/15
 */
:- module foldable.

:- interface.

:- typeclass foldable(T, A) <= ((A -> T), (T -> A)) where
	[
	/**
	 * fold(Element, AC) = NextAC

	 * Update the accumulator with the given element.
	 */
	func fold(T, A) = A,

	/**
	 * fold = InitialAC

	 * Return the initial value of the accumulator.
	 */
	func initAC = A
].

:- implementation.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of private types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of exported predicates and functions

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of private predicates and functions

:- end_module foldable.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
