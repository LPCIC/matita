sig refiner.

kind term type.

/** PTS */
type app  term -> term -> term.
/* lam sty body */
type lam  term -> (term -> term) -> term.
type prod term -> (term -> term) -> term.
type set  term.

/** Arithmetics */
type nat term.
type zero term.
type succ term.
/* rec rty n base step:(n -> res_n -> rty) */
type rec  term -> term -> term -> (term -> term -> term) -> term.

/** Dependent type */
type vnil term.
type vcons term.
type vect term.

/** Constants with a body ??? */
type plus term.

/** untyped */
type hole term.

/* hack */
kind bool type.
type tt bool.
type ff bool.

kind seq type.
type decl term -> (term -> seq) -> seq.
type goal term -> term -> seq.

type mem term -> list seq -> term -> o.
type find term -> list seq -> term -> o.
type append list seq -> list seq -> list seq.

/** Program */
/* of sigma term type term' extra_sigma : sigma@extra_simga is sigma' */
type of   list seq -> term -> term -> term -> list seq -> o.
type unif bool -> list seq -> term -> term -> o.
type unify list seq -> term -> term -> o.
type rof list seq -> term -> term -> o.
type test_unify list seq -> term -> term -> term -> term -> list seq -> o.

type dummy1__, dummy2__ term.
type is_flex term -> o.
type is_same_flex term -> term -> o.

type sigma_appl list seq -> list seq -> term -> term -> o.
type same_goal term -> seq -> term -> o.
