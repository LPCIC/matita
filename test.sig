sig test.

kind term type.
kind ref type.

type app list term -> term.
type lam term -> (term -> term) -> term.
type let-in term -> term -> (term -> term) -> term.
type prod term -> (term -> term) -> term.
type atom ref -> term.
type succ ref.
type zero ref.
type nat ref.
type set term.

type ten term -> term -> o.
type hundred term -> term -> o.

type if o -> o -> o -> o.
type body ref -> term -> o.
type rev list term -> list term -> o.
type rev-aux list term -> list term -> list term -> o.
type whd term -> term -> o.
type whd-w-delta term -> term -> o.
type of term -> term -> term -> o.
type def term -> term -> term -> o.
type eat-prod term -> list term -> list term -> term -> list term -> term -> term -> o.
type env ref -> term -> o.
type test term -> o.
