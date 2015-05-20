module lambda3.

of (appl T1 T2) B :- of T1 (impl A B), of T2 A.
of (lam F) (impl A B) :- pi x\ of x A => of (F x) B.

append (X::XS) L (X::L1)  :- append XS L L1 .
append nil L L .

termify nil (lam x\x).
termify (X::XS) (lam F) :- pi c\ termify XS (F c).

test L Z :- 
  X1 = (x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::nil), 
  append X1 X1 X2 ,
  append X2 X2 X3 ,
  append X3 X3 X4 ,
  append X4 X4 X5 ,
  append X5 X5 X6 ,
  % append X6 X6 X7 ,
  % append X7 X7 X8 ,
  % append X8 X8 X9 ,
  % append X9 X9 X10 ,
  % append X10 X10 X11 ,
  % append X11 X11 X12 ,
  % append X12 X12 X13 ,
  % append X13 X13 X14 ,
   % append X14 X14 X15 ,
   % append X15 X15 X16 ,
   % append X16 X16 X17 ,
   % append X17 X17 X18 ,
   X = X6 ,
   termify X L , 
   of L Z . 
