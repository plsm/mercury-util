/**
 * 

 * @author Pedro Mariano
 * @version 1.0 2014/03/10
 */
:- module parseable.iou.

:- interface.

:- import_module io.

/**
 * Cache used by {@code read/8} predicate.  This predicate reads bytes from
 * a binary stream and parses the content to return a {@code parseable}
 * instance.
  
 */
:- type cache.

/**
 * This type can be used by more advance predicates that may return a value
 * from a list of bytes, but can also defer for later.  This is typical for
 * a data series with gaps.  When one is processing the series, a gap may
 * result in a parsed value that has to be returned later.
 */

:- type delayedResult(T) --->
	ok(T) ;
	delayed ;
	parseError.

:- type result(T) --->
	ok(T) ;
	parseError.

:- type advancedResult(T) --->
	no ;
	result(T) ;
	eof.

:- type ioResult(T) --->
	ok(T) ;
	parseError ;
	error(io.error).


:- func cacheInit = cache.

/**
 * read(Stream, ReadChunkSize, MMaxCache, !Cache, RIResult, !IO)

 * Parse the content of a binary stream and return a parseable value.  If
 * parsing the cache fails, {@code ReadChunkSize} bytes are read from the
 * stream and added to the cache.  Next we try parsing the new cache.  We
 * repeat until reaching the end-of-file or the cache reaches the {@code
 * MaxCacheSize} limit, if specified meaning {@code MMaxCacheSize} is equal
 * to {@code yes(MaxCacheSize)}.
  
 */
:- pred read(io.binary_input_stream, int, maybe(int), cache, cache, parseable.iou.result(io.result(T)), io.state, io.state)
	<= parseable(T).
:- mode read(in, in, in, in, out, out, di, uo) is det.

:- pred read(io.binary_input_stream, int, maybe(int), parser(T), cache, cache, parseable.iou.result(io.result(T)), io.state, io.state).
:- mode read(in, in, in, in(parserS), in, out, out, di, uo) is det.

/**
 * readAll(Stream, ReadChunkSize, MMaxCache, RResult, !IO)
  
 * Reads the entire stream into a list.
 */
:- pred readAll(io.binary_input_stream, int, maybe(int), parseable.iou.ioResult(list(T)), io.state, io.state)
	<= parseable(T).
:- mode readAll(in, in, in, out, di, uo) is det.

/**
 * readAll(Stream, ReadChunkSize, MMaxCache, Parser, RResult, !IO)
  
 * Reads the entire stream into a list.
 */
:- pred readAll(io.binary_input_stream, int, maybe(int), parser(T), parseable.iou.ioResult(list(T)), io.state, io.state).
:- mode readAll(in, in, in, in(parserS), out, di, uo) is det.

/**
 * write(Stream, Data, !IO)
  
 * Parse the instance and write the bytes to the binary stream.
  
 */
:- pred write(io.binary_output_stream, T, io.state, io.state)
	<= parseable(T).
:- mode write(in, in, di, uo) is det.

:- implementation.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of exported types

:- type cache --->
	cache(
		bytes    :: list(int),
		ioStatus :: io.result
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definition of private types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of exported predicates and functions

cacheInit = cache([], ok).

read(Stream, ReadChunkSize, MMaxCache, !Cache, RIResult, !IO) :-
	(if
		parseable.parse(Result, !.Cache^bytes, NewBytes)
	then
		RIResult = ok(ok(Result)),
		!:Cache = 'bytes :='(!.Cache, NewBytes)
	else if
		MMaxCache = yes(MaxCache),
		list.length(!.Cache^bytes) > MaxCache
		;
		!.Cache^ioStatus = eof
		;
		!.Cache^ioStatus = error(_)
	then
		!.Cache^ioStatus = ok,
		RIResult = parseError
		;
		!.Cache^ioStatus = eof,
		RIResult = ok(eof)
		;
		!.Cache^ioStatus = error(Error),
		RIResult = ok(error(Error))
	else
		readChunk(Stream, ReadChunkSize, [], Chunk, Result, !IO),
		read(Stream, ReadChunkSize, MMaxCache, cache(list.append(!.Cache^bytes, list.reverse(Chunk)), Result), !:Cache, RIResult, !IO)
	).

read(Stream, ReadChunkSize, MMaxCache, Parser, !Cache, RIResult, !IO) :-
	(if
		Parser(Result, !.Cache^bytes, NewBytes)
	then
		RIResult = ok(ok(Result)),
		!:Cache = 'bytes :='(!.Cache, NewBytes)
	else if
		MMaxCache = yes(MaxCache),
		list.length(!.Cache^bytes) > MaxCache
		;
		!.Cache^ioStatus = eof
		;
		!.Cache^ioStatus = error(_)
	then
		!.Cache^ioStatus = ok,
		RIResult = parseError
		;
		!.Cache^ioStatus = eof,
		RIResult = ok(eof)
		;
		!.Cache^ioStatus = error(Error),
		RIResult = ok(error(Error))
	else
		readChunk(Stream, ReadChunkSize, [], Chunk, Result, !IO),
		read(Stream, ReadChunkSize, MMaxCache, Parser, cache(list.append(!.Cache^bytes, list.reverse(Chunk)), Result), !:Cache, RIResult, !IO)
	).

readAll(Stream, ReadChunkSize, MMaxCache, Result, !IO) :-
	readAllLoop(Stream, ReadChunkSize, MMaxCache, Result, cacheInit, _, [], _, !IO).

readAll(Stream, ReadChunkSize, MMaxCache, Parser, Result, !IO) :-
	readAllLoop(Stream, ReadChunkSize, MMaxCache, Parser, Result, cacheInit, _, [], _, !IO).

write(Stream, Data, !IO) :-
	parse(Data, Bytes, []),
	list.foldl(io.write_byte(Stream), Bytes, !IO).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of private predicates and functions

:- pred readAllLoop(
	io.binary_input_stream :: in,
	int                    :: in,
	maybe(int)             :: in,
	ioResult(list(T)) :: out,
	cache    :: in, cache    :: out,
	list(T)  :: in, list(T)  :: out,
	io.state :: di, io.state :: uo
) is det
	<= parseable(T).

readAllLoop(Stream, ReadChunkSize, MMaxCache, Result, !Cache, !List, !IO) :-
	read(Stream, ReadChunkSize, MMaxCache, !Cache, MIResult, !IO),
	(	%
		MIResult = ok(ok(AResult)),
		list.cons(AResult, !List),
		readAllLoop(Stream, ReadChunkSize, MMaxCache, Result, !Cache, !List, !IO)
		;
		MIResult = ok(eof),
		Result = ok(list.reverse(!.List))
		;
		MIResult = ok(error(Error)),
		Result = error(Error)
		;
		MIResult = parseError,
		Result = parseError
	).
	
:- pred readAllLoop(
	io.binary_input_stream :: in,
	int                    :: in,
	maybe(int)             :: in,
	parser(T)              :: in(parserS),
	ioResult(list(T)) :: out,
	cache    :: in, cache    :: out,
	list(T)  :: in, list(T)  :: out,
	io.state :: di, io.state :: uo
) is det.

readAllLoop(Stream, ReadChunkSize, MMaxCache, Parser, Result, !Cache, !List, !IO) :-
	read(Stream, ReadChunkSize, MMaxCache, Parser, !Cache, MIResult, !IO),
	(	%
		MIResult = ok(ok(AResult)),
		list.cons(AResult, !List),
		readAllLoop(Stream, ReadChunkSize, MMaxCache, Parser, Result, !Cache, !List, !IO)
		;
		MIResult = ok(eof),
		Result = ok(list.reverse(!.List))
		;
		MIResult = ok(error(Error)),
		Result = error(Error)
		;
		MIResult = parseError,
		Result = parseError
	).
	

:- import_module string.

/**
 * readChunk(Stream, ReadChunkSize, Chunk, Result, !IO)
  
 * Read {@code ChunkSize} bytes from the binary stream or until eof is
 * reached or an IO error occurs.
  
 */
:- pred readChunk(io.binary_input_stream, int, parseable.state, parseable.state, io.result, io.state, io.state).
:- mode readChunk(in, in, in, out, out, di, uo) is det.

readChunk(Stream, ChunkSize, !Chunk, Result, !IO) :-
	(if
		ChunkSize =< 0
	then
		Result = ok
	else
		io.read_byte(Stream, IByte, !IO),
		(
			IByte = ok(Byte),
			readChunk(Stream, ChunkSize - 1, list.cons(Byte, !.Chunk), !:Chunk, Result, !IO)
			;
			IByte = eof,
		  %(io.format("\nread %d at EOF\n", [i(list.length(!.Chunk))], !IO)),
			Result = eof
			;
			IByte = error(Error),
			Result = error(Error)
		)
	).

:- end_module parseable.iou.

%%% Local Variables: 
%%% mode: mercury
%%% mode: flyspell-prog
%%% ispell-local-dictionary: "british"
%%% End:
