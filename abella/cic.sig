sig cic.

kind    bool       type.

type    tt         bool.
type    ff         bool.

kind    tm         type.
kind    listtm     type.

type    neq, eq    tm -> tm -> o.
type    and        o -> o -> o.

type    xcons       tm -> listtm -> listtm.
type    xnil        listtm.

type    hole       tm.
type    set        tm.
type    lam        tm -> (tm -> tm) -> tm.
type    prod       tm -> (tm -> tm) -> tm.
type    app        listtm -> tm.

type    copy       tm -> tm -> o.
type    of         tm -> tm -> tm -> o.

type    coerce     tm -> tm -> tm -> tm -> o.
type    eat-prod   tm -> listtm -> listtm -> tm -> listtm -> tm -> tm -> o.
type    whd-w-delta tm -> tm -> o.
type    whd        tm -> tm -> o.
type    whd-progress tm -> tm -> o.
type    subst      (tm -> tm) -> tm -> listtm -> tm -> o.
type    unify      tm -> tm -> o.
type    unif       bool -> tm -> tm -> o.

/* <auxiliary> */
type    is_term    tm -> o.
/* </auxiliary> */

type    list2      (tm -> tm -> o) -> listtm -> listtm -> o.
type    list1      (tm -> o) -> listtm -> o.
type    rev        listtm -> listtm -> o.
type    rev-aux        listtm -> listtm -> listtm -> o.
type    if         tm -> tm -> o -> o -> o.
