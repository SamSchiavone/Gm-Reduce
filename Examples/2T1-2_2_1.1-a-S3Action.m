// 2T1-2_2_1.1-a S3Action test
AttachSpec("~/github/Gm-Reduce/spec");

R<t,x> := PolynomialRing(QQ,2);
f := t + x^2;
X := Curve(Spec(R), f);
KX<tt,xx> := FunctionField(X);
phi := tt;
a := 1;
Support(Divisor(phi));
Support(Divisor(phi-1));

// (0, 1)
f1 := 1 - t + x^2;
X1 := Curve(Spec(R), f1);
KX1<tt1,xx1> := FunctionField(X1);
phi1 := tt1;
Support(Divisor(phi1));
Support(Divisor(phi1-1));
Evaluate(f1, [S3Action(Sym(3)!(1,2), phi), xx]);
Evaluate(S3ActionPlane(Sym(3)!(1,2), f, a), [S3Action(Sym(3)!(1,2), phi), xx]);

// (0, oo)
f2 := Numerator(Evaluate(f, [1/t,x]));
f2;
X2 := Curve(Spec(R), f2);
KX2<tt2,xx2> := FunctionField(X2);
phi2 := tt2;
Support(Divisor(phi2));
Support(Divisor(phi2-1));
Evaluate(f2, [S3Action(Sym(3)!(1,3), phi), xx]);
Evaluate(S3ActionPlane(Sym(3)!(1,3), f, a), [S3Action(Sym(3)!(1,3), phi), xx]);

// (0, 1, oo)
// phi gets mapped to 1/(1-phi), but the polynomial f undergoes the inverse transformation, which is 1 - 1/phi
f3 := Numerator(Evaluate(f, [1-1/t,x]));
f3;
X3 := Curve(Spec(R), f3);
KX3<tt3,xx3> := FunctionField(X3);
phi3 := tt3;
Support(Divisor(phi3));
Support(Divisor(phi3-1));
Evaluate(f3, [S3Action(Sym(3)!(1,2,3), phi), xx]);
Evaluate(S3ActionPlane(Sym(3)!(1,2,3), f, a), [S3Action(Sym(3)!(1,2,3), phi), xx]);
