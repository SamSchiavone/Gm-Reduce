// Guo--Yang, Equations of hyperelliptic Shimura curves
// Appendix A, Table A.1
//y2 = −(x6 −7x4 +43x2 +27)(243x6 +523x4 +369x2 +81)

AttachSpec("../spec");
SetVerbose("GmReduce",true);

QQ := Rationals();
R<t> := PolynomialRing(QQ);
h := (t^6 - 7*t^4 + 43*t^2 + 27)*(243*t^6 + 523*t^4 + 369*t^2 + 81);
X := HyperellipticCurve(h);
KX<x,y> := FunctionField(X);
phi := x;
models := AllReducedModels(phi);
