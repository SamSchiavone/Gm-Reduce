
// Belyi maps downloaded from the LMFDB on 13 June 2023.
// Magma code for Belyi map with label 6T16-6_6_3.1.1.1-a


// Group theoretic data

d := 6;
i := 1;
G := TransitiveGroup(d,i);
sigmas := [[Sym(6) | [2, 3, 4, 5, 6, 1], [5, 1, 2, 6, 4, 3], [4, 2, 3, 6, 5, 1]], [Sym(6) | [2, 3, 4, 5, 6, 1], [5, 1, 6, 3, 4, 2], [3, 2, 6, 4, 5, 1]], [Sym(6) | [2, 3, 4, 5, 6, 1], [6, 1, 4, 2, 3, 5], [1, 2, 4, 5, 3, 6]]];
embeddings := [ComplexField(15)![-0.6299605249474366, -1.091123635971721], ComplexField(15)![-0.6299605249474366, 1.091123635971721], ComplexField(15)![1.259921049894873, 0.0]];

// Geometric data

// Define the base field
R<T> := PolynomialRing(Rationals());
K<nu> := NumberField(R![-2, 0, 0, 1]);

// Define the curve
S<x> := PolynomialRing(K);
X := EllipticCurve(S!x^3 + (-7/972*nu^2 - 5/972*nu + 71/3888)*x + 31/26244*nu^2 - 317/104976*nu + 407/209952,S!0);
// Define the map
KX<x,y> := FunctionField(X);
phi := (1/2916*(-51*nu^2+30*nu+44)*x+1/314928*(-173*nu^2+1726*nu-1896))/(x^6+1/18*(-4*nu^2+8*nu-9)*x^5+1/3888*(680*nu^2-560*nu-235)*x^4+1/104976*(452*nu^2-2920*nu+2657)*x^3+1/15116544*(113360*nu^2-217440*nu+92215)*x^2+1/816293376*(877204*nu^2-426088*nu-856739)*x+1/176319369216*(2065272*nu^2+4034416*nu-8362327))*y+(1/2916*(51*nu^2-30*nu-44)*x^3+1/104976*(395*nu^2-1030*nu+660)*x^2+1/11337408*(4663*nu^2-886*nu-6284)*x+1/1224440064*(-246035*nu^2+576982*nu-336356))/(x^6+1/18*(-4*nu^2+8*nu-9)*x^5+1/3888*(680*nu^2-560*nu-235)*x^4+1/104976*(452*nu^2-2920*nu+2657)*x^3+1/15116544*(113360*nu^2-217440*nu+92215)*x^2+1/816293376*(877204*nu^2-426088*nu-856739)*x+1/176319369216*(2065272*nu^2+4034416*nu-8362327));
// Plane model
R<t,u> := PolynomialRing(K,2);
X_plane := Curve(Spec(R), -t^2 + 2*t*u^3 + (3*nu^2 + 6)*t*u^2 + 6*nu^2*t*u + (3*nu^2 - 2)*t - u^6);
KX_plane<t,u> := FunctionField(X_plane);
a := 1/9*(-23*nu^2 + 28*nu - 2);
phi_plane := (1/a)*t;


f_plane:=DefiningEquations(X_plane)[1];

assert f_plane eq reducemodel_padic(f_plane);

fu:=reducemodel_units(f_plane)