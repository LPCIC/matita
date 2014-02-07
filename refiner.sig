sig refiner.

kind term type.

/** PTS */
type app  term -> term -> term.
/* lam sty body */
type lam  term -> (term -> term) -> term.
type prod term -> (term -> term) -> term.
type set  term.

type ginst term -> term -> term.

type atom id -> term.

/* rec rty n base step:(n -> res_n -> rty) */
type rec  term -> term -> term -> term -> term.

type hole term.

/** Ids */
type nat id.
type zero id.
type succ id.
type vnil  id.
type vcons id.
type vect  id.
type plus id.

type var int -> term.

/** Lookup in the library */
kind id type.
type env id -> term -> o.
type body id -> term -> o.

/** Sequents */

kind seq type.
type decl term -> (term -> seq) -> seq.
type goal term -> term -> seq.

/* hack */
kind bool type.
type tt bool.
type ff bool.

type append list seq -> list seq -> list seq.

type dummy1__, dummy2__ term.
type is_flex term -> o.
type is_same_flex term -> term -> o.

type sigma_appl list seq -> list seq -> term -> term -> o.

/** Program */
type exp int -> term -> o.
type clean term -> term -> o.
type clean_sigma list seq -> list seq -> o.
type clean_seq seq -> seq -> o.
type ho   term -> term -> term -> term -> o.
type copy term -> term -> o.
/* subst where what out */
type subst (term -> term) -> term -> term -> o.
type unif bool -> term -> term -> o.
type rof term -> term -> o.

type test_unify term -> term -> term -> term -> term -> list seq -> o.

/* of term type term' extra_sigma : sigma@extra_simga is sigma' */
type of   term -> term -> term -> list seq -> o.
type unify term -> term -> o.

type claim term -> term -> o.


type step list seq -> o.
type step_in int -> seq -> list seq -> o.
