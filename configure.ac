AC_INIT(
	[Mercury Utils] ,
	[1.0] ,
	[mariano.pedro@gmail.com] ,
	[mercury-utils-1.0] ,
	[https://github.com/plsm/mercury-utils]
)
AC_CONFIG_SRCDIR( foldable.m )
AC_CONFIG_SRCDIR( fraction.m )
AC_CONFIG_SRCDIR( printable.m )
AC_CONFIG_SRCDIR( probability.m )
AC_CONFIG_SRCDIR( rng.m )
AC_CONFIG_SRCDIR( rng.distribution.m )
AC_CONFIG_SRCDIR( mersenneTwister-int.m )
AC_CONFIG_SRCDIR( mersenneTwister-integer.m)
AC_CONFIG_FILES(Makefile)
AC_ARG_VAR(mersenne_twister, [mersenne twister pseudo-random number generator to use])
#while true ; do
	echo "Which mersenne twister pseudo-random number generator to use?"
	echo " 1 - primitive type int (32 or 64 bits)"
	echo " 2 - arbitrary precision integers"
	read ANS <&AS_ORIGINAL_STDIN_FD
	if test $ANS = 1 ; then
		AC_SUBST(mersenne_twister,[int])
#		break
	elif test $ANS = 2 ; then
		AC_SUBST(mersenne_twister,[integer])
#		break
	fi
#done
AC_OUTPUT
