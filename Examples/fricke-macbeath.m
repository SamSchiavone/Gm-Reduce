AttachSpec("spec");
AttachSpec("~/github/Belyi/Code/spec");
K<rho> := CyclotomicField(7);
R<x,y1,y2,y3> := PolynomialRing(K,4);
f1 := y1^2 - &*[x-rho^i : i in [1,3,5,6]];
f2 := y2^2 - &*[x-rho^i : i in [2,4,5,6]];
f3 := y3^2 - &*[x-rho^i : i in [1,3,4,5]];
X := Curve(Spec(R), [f1,f2,f3]);
G := PSL(2,8);

R<x,y> := PolynomialRing(QQ,2);
f := 1 + 7*x*y + 21*x^2*y^2 + 35*x^3*y^3 + 28*x^4*y^4 + 2*x^7 + 2*y^7;
C := Curve(Spec(R),f);
