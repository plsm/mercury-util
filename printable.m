/**
 * Provides class {@code printable} which represents objects capable of
 * being written in some text stream.

 * @author Pedro Mariano
 * @version 1.0 2012/07/13
 */
:- module printable.

:- interface.

:- import_module io, unit.

/**
 * This class represents objects capable of being written in some text or binary stream.
 */
:- typeclass printable(T)
	where
[
	/**
	 * print(Stream, Value, !IO)

	 * Print value {@code Value} to text stream.
	 */
	pred print(io.output_stream, T, io, io),
	mode print(in, in, di, uo) is det
].

:- instance printable(unit).

:- instance printable(float).

:- instance printable(int).

/**
 * noprint(Stream, Element, !IO)
  
 * This predicate does not print anything in the stream.  It can be used by
 * types that do not have any data associated or that do not need to be
 * saved.
  
 */
:- pred noprint(io.output_stream, T, io, io).
:- mode noprint(in, in, di, uo) is det.

/**
 * spacePrint(Stream, Value, !IO)

 * Print a space then parameter {@code Value}. 
 */
:- pred spacePrint(io.output_stream, P, io, io)
	<= printable(P).
:- mode spacePrint(in, in, di, uo) is det.

/**
 * tabPrint(Stream, Value, !IO)

 * Print a tab character then parameter {@code Value}. 
 */
:- pred tabPrint(io.output_stream, P, io, io)
	<= printable(P).
:- mode tabPrint(in, in, di, uo) is det.

:- implementation.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

:- instance printable(unit)
	where
[
	pred(print/4) is noprint
].

:- instance printable(float)
	where
[
	pred(print/4) is io.print
].

:- instance printable(int)
	where
[
	pred(print/4) is io.print
].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of private types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of exported predicates and functions

noprint(_, _, !IO).

spacePrint(Stream, P, !IO) :-
	io.print(Stream,  ' ', !IO),
	printable.print(Stream, P, !IO).

tabPrint(Stream, P, !IO) :-
	io.print(Stream,  '\t', !IO),
	printable.print(Stream, P, !IO).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of private predicates and functions

:- end_module printable.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
