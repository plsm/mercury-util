/**
 * 

 * @author Pedro Mariano
 * @version 1.0 2013/04/15
 */
:- module parseable.

:- interface.

:- import_module bool, list.

:- typeclass parseable(T)
	where
[
	pred parse(T, list(int), list(int)),
	mode parse(in, out, in) is det,
	mode parse(out, in, out) is semidet
].

/**
 * This predicate parses a list of bytes to a list of {@code parseable}
 * elements.  The predicate tries to parse as many possible.
 */
:- pred parseList(list(T), list(int), list(int)) <= parseable(T).
:- mode parseList(in, out, in) is det.
:- mode parseList(out, in, out) is semidet.

/**
 * This predicate parses an unsigned byte containing the number of elements
 * in the list and then parses the elements of the list.
 */
:- pred parseListMax255(list(T), list(int), list(int)) <= parseable(T).
:- mode parseListMax255(in, out, in) is det.
:- mode parseListMax255(out, in, out) is semidet.

:- func toBytes(T) = list(int) <= parseable(T).

:- func listToBytes(list(T)) = list(int) <= parseable(T).

:- pred int(int, list(int), list(int)).
:- mode int(in, out, in) is det.
:- mode int(out, in, out) is semidet.

:- pred float(float, list(int), list(int)).
:- mode float(in, out, in) is det.
:- mode float(out, in, out) is semidet.

:- pred bool(bool, list(int), list(int)).
:- mode bool(in, out, in) is det.
:- mode bool(out, in, out) is semidet.

:- pred int32(int, list(int), list(int)).
:- mode int32(in, out, in) is det.
:- mode int32(out, in, out) is semidet.

:- pred int16(int, list(int), list(int)).
:- mode int16(in, out, in) is det.
:- mode int16(out, in, out) is semidet.

:- pred int8(int, list(int), list(int)).
:- mode int8(in, out, in) is det.
:- mode int8(out, in, out) is semidet.

/**
 * skip(Byte, HowMany, !ListBytes).
 */
:- pred skip(int, int, list(int), list(int)).
:- mode skip(in, in, in, out) is semidet.
:- mode skip(in, in, out, in) is det.

:- instance parseable(int).

:- instance parseable(float).


:- implementation.

:- import_module exception, int.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

:- instance parseable(int) where
[
	pred(parse/3) is int
].

:- instance parseable(float) where
[
	pred(parse/3) is float
].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of private types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of exported predicates and functions


parseList([]) -->
	[0].

parseList([Head | Tail]) -->
	[1],
	parseable.parse(Head),
	parseList(Tail).

% :- pragma promise_pure(parseList/3).

% parseList(List::in, Bytes::out, RestBytes::in) :-
% 	List = [],
% 	Bytes = RestBytes
% 	;
% 	List = [Element | RestList],
% 	parse(Element, BytesElement, BytesRestList),
% 	parseList(RestList, BytesRestList, RestBytes),
% 	Bytes = list.append(BytesElement, BytesRestList).

% parseList(List::out, Bytes::in, RestBytes::out) :-
% 	(if
% 		parse(Element, Bytes, BytesRestList)
% 	then
% 		List = [Element | RestList],
% 		parseList(RestList, BytesRestList, RestBytes)
% 	else
% 		List = [],
% 		Bytes = RestBytes
% 	).


parseListMax255(List) -->
	[Size],
	{Size = list.length(List)},
	parseList(Size, List).

/*
parseList(List::in) -->
	{List = []}
	;
	{List = [Element | RestList]},
	parse(Element),
	parseList(RestList).

parseList(List::out) -->
	(if
		parse(Element)
	then
		{List = [Element | RestList]},
		parseList(RestList)
	else
		{List = []}
	).
*/

toBytes(Element) = Result :-
 	parse(Element, Result, []).


listToBytes([]) = [].
listToBytes([Element | RestElements]) = Result :-
	Result = list.append(toBytes(Element), listToBytes(RestElements)).

% int16(Num) -->
% 	[ByteLow, ByteHigh],
% 	{Num / 256 = ByteHigh,
% 	 Num /\ 255 = ByteLow,
% 	 Num = ByteHigh << 8 + ByteLow}.

int(Num) -->
	intBytes(Num).

float(Num) -->
	floatBytes(Num).

bool(no) --> [0].
bool(yes) --> [1].

:- pragma promise_pure(int32/3).

int32(Num::in, [Byte1, Byte2, Byte3, Byte4 | Rest]::out, Rest::in) :-
	(Num >> 24) /\ 255 = Byte4,
	(Num >> 16) /\ 255 = Byte3,
	(Num >> 8) /\ 255 = Byte2,
	Num /\ 255 = Byte1.

int32(Num::out, [Byte1, Byte2, Byte3, Byte4 | Rest]::in, Rest::out) :-
	Num =
	(Byte4 << 24)
	\/ (Byte3 << 16)
	\/ (Byte2 << 8)
	\/ Byte1.


int16(Num, [B0, B1 | Rest], Rest) :-
	int16Bytes(Num, B0, B1).

% :- pragma promise_pure(int16/3).

% int16(Num::in, [ByteLow, ByteHigh | Rest]::out, Rest::in) :-
% 	(Num >> 8) /\ 255 = ByteHigh,
% 	Num /\ 255 = ByteLow.

% int16(Num::out, [ByteLow, ByteHigh | Rest]::in, Rest::out) :-
% 	Num = ByteHigh << 8 \/ ByteLow.

:- pragma promise_pure(int8/3).

int8(Num::in, [Byte | Rest]::out, Rest::in) :-
	Num = Byte.

int8(Num::out, [Byte | Rest]::in, Rest::out) :-
	(if
		Byte > 127
	then
		Num = 256 - Byte
	else
		Num = Byte
	).

skip(Byte, HowMany) -->
	(if
		{HowMany = 0}
	then
		{true}
	else
		[Byte],
		skip(Byte, HowMany - 1)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of private predicates and functions


:- pred parseList(int, list(T), list(int), list(int)) <= parseable(T).
:- mode parseList(in, in, out, in) is det.
:- mode parseList(in, out, in, out) is semidet.

parseList(Count, List) -->
	(if
		{Count = 0}
	then
		{List = []}
		;
		{List = [_|_]},
		{throw("Never reached")}
	else
		{List = [Element | RestList]},
		parse(Element),
		parseList(Count - 1, RestList)
		;
		{List = []},
		{throw("Never reached")}
	).


:- pred intBytes(int, list(int), list(int)).
:- mode intBytes(in, out, in) is det.
:- mode intBytes(out, in, out) is semidet.

:- pragma foreign_proc(
	"C",
	intBytes(Num::in, Result::out, Rest::in),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	union {
		unsigned char bytes [sizeof (int)];
		int value;
	} conv;
	conv.value = Num;
	int i;
	Result = Rest;
	for (i = sizeof (int) - 1; i >= 0; i--) {
		Result = MR_list_cons (conv.bytes [i], Result);
	}
	"
	).

:- pragma foreign_proc(
	"C",
	intBytes(Num::out, List::in, Rest::out),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	union {
		unsigned char bytes [sizeof (int)];
		int value;
	} conv;
	int i;
	int ok = 1;
	for (i = 0; i < sizeof (int); i++) {
		if (MR_list_is_empty (List)) {
			ok = 0;
			break;
		}
		else {
			conv.bytes [i] = MR_list_head (List);
			List = MR_list_tail (List);
		}
	}
	if (ok == 1) {
		Num = conv.value;
		Rest = List;
	}
	SUCCESS_INDICATOR = ok;
	"
	).

:- pragma foreign_proc(
	"Java",
	intBytes(Num::in, Result::out, Rest::in),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	Rest = list.cons (new Integer ((Num >> 24) & 0xFF), Rest);
	Rest = list.cons (new Integer ((Num >> 16) & 0xFF), Rest);
	Rest = list.cons (new Integer ((Num >> 8) & 0xFF), Rest);
	Rest = list.cons (new Integer ((Num) & 0xFF), Rest);
	Result = Rest;
	"
	).

:- pragma foreign_proc(
	"Java",
	intBytes(Num::out, List::in, Rest::out),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	Num = 0;
	boolean ok = true;
	for (int i = 0; i < 4; i++) {
		if (list.is_empty (List)) {
			ok = false;
			break;
		}
		else {
			Num = Num | (list.det_head (List).intValue () << (8 * i));
			List = list.det_tail (List);
		}
	}
	if (ok) {
		Rest = List;
	}
	else {Rest = null;}
	SUCCESS_INDICATOR = ok;
	"
	).




:- pred floatBytes(float, list(int), list(int)).
:- mode floatBytes(in, out, in) is det.
:- mode floatBytes(out, in, out) is semidet.

:- pragma foreign_proc(
	"C",
	floatBytes(Num::in, Result::out, Rest::in),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	union {
		unsigned char bytes [sizeof (float)];
		float value;
	} conv;
	conv.value = Num;
	int i;
	Result = Rest;
	for (i = sizeof (float) - 1; i >= 0; i--) {
						/*	  printf (""%d  %d\n"", i, conv.bytes [i]);*/
		Result = MR_list_cons (conv.bytes [i], Result);
	}
/*		Result = floatToBytes (Num, Rest); /* */
	"
	).

:- pragma foreign_proc(
	"C",
	floatBytes(Num::out, List::in, Rest::out),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	union {
		unsigned char bytes [sizeof (float)];
		float value;
	} conv;
	int i;
	int ok = 1;
	for (i = 0; i < sizeof (float); i++) {
		if (MR_list_is_empty (List)) {
			ok = 0;
			break;
		}
		else {
			conv.bytes [i] = MR_list_head (List);
			List = MR_list_tail (List);
		}
	}
	if (ok == 1) {
		Num = conv.value;
		Rest = List;
	}
	SUCCESS_INDICATOR = ok;
	"
	).


:- pragma foreign_proc(
	"Java",
	floatBytes(NumDouble::in, Result::out, Rest::in),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	int Num = Float.floatToRawIntBits ((float) NumDouble);
	Rest = list.cons (new Integer ((Num >> 24) & 0xFF), Rest);
	Rest = list.cons (new Integer ((Num >> 16) & 0xFF), Rest);
	Rest = list.cons (new Integer ((Num >> 8) & 0xFF), Rest);
	Rest = list.cons (new Integer ((Num) & 0xFF), Rest);
	Result = Rest;
	"
	).

:- pragma foreign_proc(
	"Java",
	floatBytes(NumDouble::out, List::in, Rest::out),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	int Num = 0;
	boolean ok = true;
	for (int i = 0; i < 4; i++) {
		if (list.is_empty (List)) {
			ok = false;
			break;
		}
		else {
			Num = Num | (list.det_head (List).intValue () << (8 * i));
			List = list.det_tail (List);
		}
	}
	if (ok) {
		Rest = List;
		NumDouble = Float.intBitsToFloat (Num);
	}
	else {
		Rest = null;
		NumDouble =0;
	}
	SUCCESS_INDICATOR = ok;
	"
	).




:- pred int32Bytes(int, int, int, int, int).
:- mode int32Bytes(in, out, out, out, out) is det.
:- mode int32Bytes(out, in, in, in, in) is det.

:- pragma foreign_proc(
	"C",
	int32Bytes(Num::in, B0::out, B1::out, B2::out, B3::out),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	union {
		unsigned char bytes[4];
		int32_t value;
	} conv;
	conv.value = (int32_t) Num;
	B0 = conv.bytes [0];
	B1 = conv.bytes [1];
	B2 = conv.bytes [2];
	B3 = conv.bytes [3];
	"
	).

:- pragma foreign_proc(
	"C",
	int32Bytes(Num::out, B0::in, B1::in, B2::in, B3::in),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	union {
		unsigned char bytes[4];
		int32_t value;
	} conv;
	conv.bytes [0] = B0;
	conv.bytes [1] = B1;
	conv.bytes [2] = B2;
	conv.bytes [3] = B3;
	Num = conv.value;
	"
	).

:- pragma foreign_proc(
	"Java",
	int32Bytes(Num::in, B0::out, B1::out, B2::out, B3::out),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	B0 = Num & 0xFF;
	B1 = (Num >> 8) & 0xFF;
	B2 = (Num >> 16) & 0xFF;
	B3 = (Num >> 32) & 0xFF;
	"
	).

:- pragma foreign_proc(
	"Java",
	int32Bytes(Num::out, B0::in, B1::in, B2::in, B3::in),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	Num = (B0 & 0xFF)
	| ((B1 &0xFF) << 8)
	| ((B2 &0xFF) << 16)
	| ((B3 &0xFF) << 24);
	"
	).


:- pred int16Bytes(int, int, int).
:- mode int16Bytes(in, out, out) is det.
:- mode int16Bytes(out, in, in) is det.

:- pragma foreign_proc(
	"C",
	int16Bytes(Num::in, B0::out, B1::out),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	union {
		unsigned char bytes[2];
		int16_t value;
	} conv;
	conv.value = (int16_t) Num;
	B0 = conv.bytes [0];
	B1 = conv.bytes [1];
	"
	).

:- pragma foreign_proc(
	"C",
	int16Bytes(Num::out, B0::in, B1::in),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	union {
		unsigned char bytes[2];
		int16_t value;
	} conv;
	conv.bytes [0] = B0;
	conv.bytes [1] = B1;
	Num = conv.value;
	"
	).

:- pragma foreign_proc(
	"Java",
	int16Bytes(Num::in, B0::out, B1::out),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	B0 = ((short) Num) & 0xFF;
	B1 = (((short) Num) >> 8) & 0xFF;
	"
	).

:- pragma foreign_proc(
	"Java",
	int16Bytes(Num::out, B0::in, B1::in),
	[will_not_call_mercury, thread_safe, promise_pure],
	"
	Num = (short) ( (((short) B0) & 0xFF)
	| (( ((short) B1) &0xFF) << 8) );
	"
	).



/*
parseList(Count, List) -->
	(if
		{Count = 0},
		{List = []}
	then
		{true}
	else if
		{List = [Element | RestList]},
		parse(Element)
	then
		parseList(Count - 1, RestList)
	else
		{throw("Never reached")}
	).
*/
:- end_module parseable.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
