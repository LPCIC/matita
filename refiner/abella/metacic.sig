sig metacic.

accum_sig cic.

kind    seq     type.

type    vdash     tm -> seq.
type    decl      tm -> (tm -> seq) -> seq.

type    of-seq    seq -> listtm -> tm -> o.
