AttachSpec("spec");
R<u0,u1,u2,u3>:=PolynomialRing(Rationals(),4);

q1 := u1^2 - 81920000/15165891*u2^2 - 327680000/107811*u3^2;
q2 := u0^2 - 117406179/6525845768*u2^2 + 1033857/4394*u3^2;
q0 := -u0^2 + 864536409/110755840000*u1^2 - 26136/28561*u0*u2 - 170772624/815730721*u2^2 - 264627/135200*u1*u3 + 20736/169*u3^2;

c1,m1:=CoefficientsAndMonomials(q1);
c2,m2:=CoefficientsAndMonomials(q2);
c0,m0:=CoefficientsAndMonomials(q0);

allmon:=Setseq(Set(m1 cat m2 cat m0));

f:=R!0;

for m in allmon do



f:=q1*q2*q0;

CoefficientSupport(f);
put:=[ pp : pp in CoefficientSupport(f) | Norm(pp) lt 100 ];
fp,abc:=reducemodel_padic(f : PrimesForReduction:=CoefficientSupport(f), FixedVariables:=[5]);
//fp:=reducemodel_padic(f : PrimesForReduction:=CoefficientSupport(f));
q1gm:=Evaluate(q1, [R.i*BaseRing(R)!abc[i] : i in [1..#abc-1]]);
q2gm:=Evaluate(q2, [R.i*BaseRing(R)!abc[i] : i in [1..#abc-1]]);
q0gm:=Evaluate(q0, [R.i*BaseRing(R)!abc[i] : i in [1..#abc-1]]);

ZK:=Integers(BaseRing(Parent(q1gm)));
jj1num := (ideal<ZK | [ZK!Numerator(a) : a in Coefficients(q1gm)] >);
jprinbl, j1num := IsPrincipal(jj1num);
jj1den := (ideal<ZK | [ZK!Denominator(a) : a in Coefficients(q1gm)] >);
jprinbl, j1den := IsPrincipal(jj1den);
q1gm*(j1den/j1num);

reducemodel_padic_old(f : Integral:=false);



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
