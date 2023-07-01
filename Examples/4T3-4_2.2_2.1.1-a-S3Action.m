// Belyi maps downloaded from the LMFDB on 30 June 2023.
// Magma code for Belyi map with label 4T3-4_2.2_2.1.1-a

AttachSpec("~/github/Gm-Reduce/spec");

// Group theoretic data

d := 4;
i := 3;
G := TransitiveGroup(d,i);
sigmas := [[Sym(4) | [2, 3, 4, 1], [2, 1, 4, 3], [3, 2, 1, 4]]];
embeddings := [ComplexField(15)![1.0, 0.0]];

// Geometric data

// Define the base field
K<nu> := RationalsAsNumberField();
// Define the curve
X := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
// Define the map
KX<x> := FunctionField(X);
phi := -1/4/(x^4-x^2);
// Plane model
R<t,u> := PolynomialRing(K,2);
f := t + u^4 - u^2;
X_plane := Curve(Spec(R), f);
KX_plane<tt,xx> := FunctionField(X_plane);
a := 1/4;
phi_plane := (1/a)*tt;

// test S3Action
// (0, a, oo)
f1 := S3ActionPlane(Sym(3)!(1,2,3), f, a);
assert f1 eq t*u^2*(u-1)*(u+1) + t*a - a^2;
X1 := Curve(Spec(R), f1);
KX1<tt1,xx1> := FunctionField(X1);
phi1 := (1/a)*tt1;
Support(Divisor(phi1));
Support(Divisor(phi1-1));
Evaluate(S3ActionPlane(Sym(3)!(1,2,3), f, a), [S3Action(Sym(3)!(1,2,3), phi_plane), xx]);
