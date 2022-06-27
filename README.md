# Unsatisfiability of Comparison-Based Definition of Non-Malleability for Commitments


Setup
-----

* For this project we used the developement version of EasyCrypt (1.0)
theorem prover with GIT hash: r2022.04-23-gb44893a5

* EasyCrypt was configured with support from the following SMT solvers:
Why3@1.5.0, Z3@4.8.7, CVC4@1.6, Alt-Ergo@2.4.1

* to check the development run:
  
  $> cd DEVELOPMENT_FOLDER
  $> bash checkall


Contents
--------

* checkall - script for running the EasyCrypt proof-checker on the
  entire development.
  
* CNM_unsat.ec - definition of comparison-based non-malleability and
  the proof of its unsatisfiability.

  lemma cnm_unsat formalizes Thm. 1 from Sec. 2.1.

* D1D2.ec, WholeMsg.ec - auxiliary games
