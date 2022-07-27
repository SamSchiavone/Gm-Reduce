AttachSpec("spec");
R<z>:=PolynomialRing(Rationals());
K<nu> := NumberField(z^2-2);
R<t,x> := PolynomialRing(K,2);
ZK := Integers(K);
UK,mUK:=UnitGroup(K);
epsilon:= [ K!(mUK(eps)) : eps in Generators(UK) | not(IsFinite(eps)) ][1];
f := 5*x^3 - 2*epsilon^7*t*x;
coefs:=Coefficients(f);
fred, abc := reducemodel_units(f);
inf_places:=InfinitePlaces(K);
prec:=100;
k:=RealField(prec);
phi:=function(x);
  return [ Log(k!Abs(Evaluate(x,v : Precision:=prec))) : v in inf_places ];
  //assert first r places are real.
end function;


f;
fred;
abc;



avg1:=ClosestElementInUnitHyperplane(coefs[1]);
avg2:=ClosestElementInUnitHyperplane(coefs[2]);

best_eps:=(avg1+avg2)/2;
phi(epsilon);
[ (close1[i] +close2[i])/2 : i in [1..2] ];

places := InfinitePlaces(K);
a := abc[1];
v := places[1];
[Log(AbsoluteValue(Evaluate(el,v)))/Log(AbsoluteValue(Evaluate(epsilon,v))) : el in abc];
f;
f_red;
f_naive := reducemodel_units_naive(f);
#Sprint(f);
#Sprint(f_red);
#Sprint(f_naive);
