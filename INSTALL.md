<!--- OASIS_START --->
<!--- DO NOT EDIT (digest: 3cdf190e3231e55171908a6a9d2ef4f4) --->

This is the INSTALL file for the electrumAnalyzer distribution.

This package uses OASIS to generate its build system. See section OASIS for
full information.

Dependencies
============

In order to compile this package, you will need:

* ocaml (>= 4.00)
* findlib
* pprint
* menhirLib (>= 20150720)
* batteries
* cmdliner (>= 0.9.5)

Installing
==========

1. Uncompress the source archive and go to the root of the package
2. Run 'ocaml setup.ml -configure'
3. Run 'ocaml setup.ml -build'
4. Run 'ocaml setup.ml -install'

Uninstalling
============

1. Go to the root of the package
2. Run 'ocaml setup.ml -uninstall'

OASIS
=====

OASIS is a program that generates a setup.ml file using a simple '_oasis'
configuration file. The generated setup only depends on the standard OCaml
installation: no additional library is required.

<!--- OASIS_STOP --->
