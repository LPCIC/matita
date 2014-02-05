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
type f term.
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

type append list A -> list A -> list A.

/** Program */
/* of term type term' */
type of   term -> term -> term -> list (list term) -> o -> o.
type unif bool -> term -> term -> o.
type unify term -> term -> o.
