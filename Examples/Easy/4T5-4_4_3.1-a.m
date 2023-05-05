AttachSpec("spec");
// Belyi maps downloaded from the LMFDB on 28 January 2022.
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
X := EllipticCurve(S!x^3 + 47/768*x + 2359/55296,S!0);
// Define the map
KX<x,y> := FunctionField(X);
phi := 27/64/(x^4-13/12*x^3-155/384*x^2-1225/27648*x-8375/5308416)*y+(-27/64*x^2+9/512*x+1401/16384)/(x^4-13/12*x^3-155/384*x^2-1225/27648*x-8375/5308416);


RsandPs := Support(Divisor(phi));
RsandQs := Support(Divisor(phi-1));
PsQsRs := SetToSequence(SequenceToSet(RsandPs cat RsandQs));

SetProfile(true);
xs:=SmallFunctions(PsQsRs, Floor((Genus(X)+3)/2)+1);
ts_xs_Fs_sorted:=SortSmallFunctions(phi, xs : effort:=30);
f1:=ReducedModel(ts_xs_Fs_sorted[1,1],ts_xs_Fs_sorted[1,2]);
models:= [ Parent(f1)!PlaneModel(tx[1],tx[2]) : tx in ts_xs_Fs_sorted ];
reduced_models:= [ Parent(f1)!ReducedModel(tx[1],tx[2]) : tx in ts_xs_Fs_sorted ];
#models; //30
#Set(models); //25
#reduced_models; //30
#Set(reduced_models); //24
duplicates := [ f : f in models | f in Exclude(models,f) ];
fns_duplicates:= [ ts_xs_Fs_sorted[i] : i in [1..#models] | models[i] in Exclude(models,models[i]) ];
duplicates[1] eq duplicates[5];
fns_duplicates[1]; fns_duplicates[5];

g1:=duplicates[1];
g2:=duplicates[5];
Evaluate(g1,[fns_duplicates[1,1], fns_duplicates[1,2]]);
Evaluate(g1,[fns_duplicates[5,1], fns_duplicates[5,2]]);
fns_duplicates[5,1] in S3Orbit(fns_duplicates[1,1]);

t1_test:=fns_duplicates[1,1];
t2_test:=fns_duplicates[5,1];
t2_test in S3Orbit(t1_test);

-t1_test/(1-t1_test) eq t2_test;

phi:=t2_test;
x_op:=fns_duplicates[1,2];
//using the resultant to create a model we see that
 //Parent(fuv1)!fuv1 eq Parent(fuv1)!fuv2;
 //false
// but Factorization(fuv1)[1,1] eq Factorization(fuv2)[1,1]; is true

// copy-pasta
/*
AttachSpec("spec");
// Belyi maps downloaded from the LMFDB on 28 January 2022.
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
X := EllipticCurve(S!x^3 + 47/768*x + 2359/55296,S!0);
// Define the map
KX<x,y> := FunctionField(X);
phi := 27/64/(x^4-13/12*x^3-155/384*x^2-1225/27648*x-8375/5308416)*y+(-27/64*x^2+9/512*x+1401/16384)/(x^4-13/12*x^3-155/384*x^2-1225/27648*x-8375/5308416);
RsandPs := Support(Divisor(phi));
RsandQs := Support(Divisor(phi-1));
PsQsRs := SetToSequence(SequenceToSet(RsandPs cat RsandQs));
SetVerbose("GmReduce",true);
AllReducedModels(phi);
Genus(X);
small2 := SmallFunctions(PsQsRs,2);
#small2;
KX;
sub< KX | small2[1..2]>;
Type(KX);
Subfield;
Subfields;
Subfields(KX);
small2[1..2];
MinimalPolynomial(small2[1]);
BaseRing(KX);
AlgorithmicFunctionField(KX);
KXalg := $1;
KXalg, mp := AlgorithmicFunctionField(KX);
sub< KXalg | [mp(el) : el in small2[1..2] >;
sub< KXalg | [mp(el) : el in small2[1..2]] >;
KXsmall := $1;
KXsmall eq KXalg;
KXsmall;
KX;
DefiningEquation(KXsmall);
DefiningEquations(KXsmall);
AbsoluteField(KXsmall);
KXsmall.1;
KXsmall.2;
Generators(KXsmall);
small2[1];
Model;
model;
model(small2[1], small2[2]);
p := $1;
X;
Curve(Spec(Parent(p)),p);
C := $1;
Curve(X);
Genus(C);
IsIsomorphic(E,C);
IsIsomorphic(X,C);
DefiningEquation(X);
DefiningEquation(AffinePatch(X,1));
f := $1;
C2 := Curve(Spec(Parent(f)), f);
C2;
IsIsomorphic(C,C2);
EllipticCurve(C);
C;
PointSearch(C,10);
ChangeRing(C,QQ);
CQQ := $1;
PointSearch(C,10);
PointSearch(CQQ,10);
E;
X;
EllipticCurve(C,C![1,-1/2]);
Cbar := ProjectiveClosure(C);
EllipticCurve(Cbar,Cbar![1,-1/2,1]);
E2 := $1;
jInvariant(E2);
jInvariant(E);
jInvariant(X);
IsIsomorphic(X,E2);
KXsmall;
KXsmall eq KXalg;
*/ 
