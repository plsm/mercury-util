AC_INIT(
	[Mercury Utils] ,
	[1.0] ,
	[mariano.pedro@gmail.com] ,
	[mercury-utils-1.0] ,
	[https://github.com/plsm/mercury-utils] )

dnl AC_CONFIG_SRCDIR( foldable.m )
dnl AC_CONFIG_SRCDIR( fraction.m )
dnl AC_CONFIG_SRCDIR( printable.m )
dnl AC_CONFIG_SRCDIR( probability.m )
dnl AC_CONFIG_SRCDIR( rng.m )
dnl AC_CONFIG_SRCDIR( rng.distribution.m )
dnl AC_CONFIG_SRCDIR( mersenneTwister-int.m )
dnl AC_CONFIG_SRCDIR( mersenneTwister-integer.m)

AC_CONFIG_FILES(Makefile)

############################################################
# check for mercury
AC_PATH_PROG(MMC,mmc,notFound)
if test "$MMC" = notFound ; then
	AC_MSG_ERROR(["Mercury compiler is required!"])
else
	AC_ARG_VAR(lib_mc4ap, [path where mc4ap components (ui_swing or libui_console) were installed])
	# find where mc4ap components are installed
	if test -z "$lib_mc4ap" ; then
		lib_mc4ap=$(AS_DIRNAME($MMC))
		lib_mc4ap=$(AS_DIRNAME($lib_mc4ap))
	fi
	if test -n "$lib_mc4ap" -a -d "$lib_mc4ap" ; then
		AS_ECHO_N("Searching mc4ap in $lib_mc4ap...")
		if test -d $lib_mc4ap/lib/mercury/lib && test -d $lib_mc4ap/lib/mercury/ints ; then
			PLACES1=$(find $lib_mc4ap/lib/mercury/lib -maxdepth 2 -name 'libui_console.so' -o -name 'ui_swing.jar')
			PLACES2=$(find $lib_mc4ap/lib/mercury/ints -maxdepth 1 -name 'userInterface.int')
			if test -n "$PLACES1" && test -n "$PLACES2" ; then
				AS_ECHO(" found")
			else
				AS_ECHO("")
				AC_MSG_ERROR([Could not find any mc4ap libraries])
			fi
		else
			AS_ECHO("")
			AC_MSG_ERROR([Directories $lib_mc4ap/lib/mercury/lib and $lib_mc4ap/lib/mercury/ints do not exist])
		fi
	else
		AC_MSG_ERROR([$lib_mc4ap is not a valid directory])
	fi
fi

# check which version of mersenne twister to use
AC_ARG_VAR(mersenne_twister, [mersenne twister pseudo-random number generator to use])
if test "$mersenne_twister" != "int" && test "$mersenne_twister" != "integer" ; then
	AS_ECHO("Which mersenne twister pseudo-random number generator to use?")
	AS_ECHO(" 1 - primitive type int (32 or 64 bits)")
	AS_ECHO(" 2 - arbitrary precision integers")
	AS_ECHO_N("? ")
	read ANS <&AS_ORIGINAL_STDIN_FD
	if test $ANS = 1 ; then
		AC_SUBST(mersenne_twister,[int])
	elif test $ANS = 2 ; then
		AC_SUBST(mersenne_twister,[integer])
	else
		AC_MSG_ERROR([Invalid option])
	fi
fi

AC_OUTPUT
