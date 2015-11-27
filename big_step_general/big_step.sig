sig big_step.

kind formula type.

type aand formula -> formula -> formula.
type oor formula -> formula -> formula.
type ttrue formula.
type ssigma (formula -> formula) -> formula.
type iimp formula -> formula -> formula.
type ppi (formula -> formula) -> formula.

type to_fla formula -> o.



