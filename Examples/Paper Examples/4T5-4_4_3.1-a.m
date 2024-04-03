
// Belyi maps downloaded from the LMFDB on 25 January 2024.
// Magma code for Belyi map with label 4T5-4_4_3.1-a


// Group theoretic data

d := 4;
i := 5;
G := TransitiveGroup(d,i);
sigmas := [[Sym(4) | [2, 3, 4, 1], [3, 1, 4, 2], [3, 2, 4, 1]]];
embeddings := [ComplexField(15)![1.0, 0.0]];

// Geometric data

// Define the base field
K<nu> := RationalsAsNumberField();
// Define the curve
S<x> := PolynomialRing(K);
//X := EllipticCurve(S!x^3 + 47/768*x + 2359/55296,S!0);
// Define the map
//KX<x,y> := FunctionField(X);
//phi := 27/64/(x^4-13/12*x^3-155/384*x^2-1225/27648*x-8375/5308416)*y+(-27/64*x^2+9/512*x+1401/16384)/(x^4-13/12*x^3-155/384*x^2-1225/27648*x-8375/5308416);

// Above are the map and curve stored in the LMFDB, but the ones in KMSV are slightly different
X := EllipticCurve(S!x^3 + 47/48*x + 2359/864,S!0);
// Define the map
KX<x,y> := FunctionField(X);
phi := (139968*x^2 - 23328*x + 490860 + 279936*y)/(12*x-13)^4;

// Plane model
R<t,u> := PolynomialRing(K,2);
X_plane := Curve(Spec(R), t^2 + (2*u^2 - 4*u + 9)*t + u^4);
KX_plane<t,u> := FunctionField(X_plane);
a := 27/4;
phi_plane := (1/a)*t;

// steps of computation
AttachSpec("spec");

// points above 0, 1, oo
RsandPs := Support(Divisor(phi));
RsandQs := Support(Divisor(phi-1));
R := SetToSequence(SequenceToSet(RsandPs cat RsandQs));
printf "fibers above 0, 1, oo: %o\n", R;

effort := 10;
degree := 2;
xs, xsDs := SmallFunctions(R, degree);
ts_xs_Fs_sorted := SortSmallFunctions(phi, xs : effort := effort);
reduced_models := []; 
for tup in ts_xs_Fs_sorted do
  t, x, F := Explode(tup); 
  f_pl:=model(t,x);
  fred, scalars := ReducedModel(t, x);
  //vprintf GmReduce: "t = %o,\nx = %o,\nreduced model = %o\n\n", t, x, fred;
  Append(~reduced_models, <#Sprint(fred), t, x, fred, scalars, f_pl>);
end for;
reduced_models_sorted := Sort(reduced_models);


// Compare with minimal model
X_min, mp := MinimalModel(X);
KX_min<v,w> := FunctionField(X_min);
phi_min := Pushforward(mp, phi);

