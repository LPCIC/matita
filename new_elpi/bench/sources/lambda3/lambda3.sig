sig lambda3.

kind t type.
kind ty type.
kind a type.

type append (list a) -> (list a) -> (list a) -> o.
type of t -> ty -> o.
type termify (list a) -> t -> o.
type impl ty -> ty -> ty.
type appl t -> t -> t.
type lam (t -> t) -> t.
type test t -> ty -> o .
type x0 a.
type x1 a.
type x2 a.
type x3 a.
type x4 a.
type x5 a.
type x6 a.
type x7 a.
type x8 a.
type x9 a.
type x10 a.

kind i type.
type zero i.
type s    i -> i.
type plus i -> i -> i -> o.
type mult i -> i -> i -> o.
type exp i -> i -> i -> o.
type iter i -> o -> o.
type once o.
type main o. 
