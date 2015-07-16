sig phases.

type memb         A -> list A -> o.

kind atm, i       type.
kind fm           type.

type tt           fm.
type imp, and     fm -> fm -> fm.
type all          (A -> fm) -> fm.
type atm          atm -> fm.

kind premises     type.
type none         premises.
type one          list fm -> atm -> premises.
type pand         premises -> premises -> premises.
type eigen        (i -> premises) -> premises.

type boundry      list fm -> atm -> premises -> o.
type sync         list fm -> atm -> fm -> premises -> o.
type async        list fm -> fm -> premises -> o.

type pr           list fm -> atm -> o.
type continue     premises -> o.

% Exmamples are accounted for below.

type app  i -> i -> i.
type abs  (i -> i) -> i.

type a,b  i.
type arr  i -> i -> i.

type of   i -> i -> atm.

type prog       fm -> o.
type program    string -> fm -> o.
