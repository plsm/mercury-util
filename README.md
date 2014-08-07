mercury-util
============

Common utilities

Contains modules used by several applications.

Implementation of the mersenne twister pseudo-random number generator.

Type-classes foldable, printable.

Type fraction, similar to rational but restricted to numbers in the interval [0,1].

Type probability and predicates and functions to handle random events.

Requirements
------------

You need the following tools:

* autoconf
* java compiler

You need the package

* MC4AP - Mercury Components for All Platforms obtained in  https://github.com/plsm/mc4ap.git

Installation
-----------

Run the following commands to install

	autoconf
	./configure lib_mc4ap=LIB_MC4AP
	make
	su -c make install

LIB_MC4AP should be replaced by the root directory where the MC4AP was installed.
