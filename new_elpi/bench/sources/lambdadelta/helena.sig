sig helena.

kind k type. % sort
kind l type. % layer
kind c type. % auxiliary information
kind t type. % term
kind g type. % global environment
kind s type. % RTM stack
kind m type. % RTM mode
kind e type. % environment side

type constant c.

type l+0 l.
type l+1 l.
type l+2 l.
type l+y l.

type m+0 m.
type m+1 m.
type m+y m.

type e+sn e.
type e+dx e.

type sort k -> t.
type abbr t -> (t -> t) -> t.
type abst l -> t -> (t -> t) -> t.
type prod l -> t -> (t -> t) -> t.
type appr t -> t -> t.
type appx t -> t -> t.
type cast t -> t -> t.

type gtop g.
type gdef c -> t -> (t -> g) -> g.
type gdec c -> t -> (t -> g) -> g.

type satom s.
type scons s -> t -> s.

type $print c -> c -> o.
type $lt t -> t -> o.

type k+succ k -> k -> o.
type l+zero l -> o.
type l+pred l -> l -> o.

type r+exp  t -> m -> e -> m -> t -> o.
type rtm+0  t -> s -> m -> m -> s -> t -> o.
type stack+ s -> s -> o.
type conv+  t -> s -> m -> m -> s -> t -> o.
type conv+l t -> s -> m -> m -> s -> t -> o.
type conv+r t -> s -> m -> m -> s -> t -> o.
type conv+0 t -> s -> m -> m -> s -> t -> o.
type ok+l   t -> m -> t -> o.
type appl+  t -> s -> m -> t -> o.
type tv+    t -> o.
type gv+    g -> o.
