# About the project
The main content of this repository is an Isabelle framework for typing ghost code for program verification. The project is associated with my Master's Thesis "Mechanized Ghost Code and
Weakest Precondition Reasoning".

# Overview of the different files
- *WPG*: This folder contains a Haskell project for typing and verifying PL0 programs.
- *ghost-code.vpr*: Examples of programs with ghost code in the MicroViper language.
- *pexp.thy*: Definitions and lemmas related to arithmetic expressions and logical formulas.
- *regular_interpretations.thy*: Definitions and lemmas related to projections of interpretations by ghost labelling functions.
- *pl0.thy*: Definition of the PL0 programming language.
- *wp0.thy*: Definition of the weakest precondition semantics for PL0, as well as definitions and lemmas for typing ghost code.
- *wp0_soundness.thy*: Proof of the correspondence between big-step semantics and weakest precondition semantics for PL0.
- *pl1.thy*: Definition of the PL1 programming language.
- *fixed_points.thy*: A theory for deriving fixed points by transfinite recursion.
- *wp1.thy*: Definition of the weakest precondition semantics for PL1, as well as definitions and lemmas for typing ghost code.
- *wp1_flipped.thy*: Using the weakest precondition for the "captured properties" analysis, and typing ghost code in this context.
- *wp1_incorrectness.thy*: Ghost code in incorrectness logic.
  
