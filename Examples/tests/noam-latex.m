//AttachSpec("code/spec_database");
//load "../gm-Reduce/reducecurve.m";
AttachSpec("spec");

F<g> := NumberField(Polynomial([8,-10,9,1,1]));
X := Curve(ProjectiveSpace(PolynomialRing(F, 2)));
KX1<x> := FunctionField(X);

tau := 2^383^17/23^3(47323g^3-1084897g^2+7751g-711002);
//_<x> := PolynomialRing(F);

P2 := (8g^3+16g^2-20g+20)x^2-(7g^3+17g^2-7g+76)x -
13g^3+25g^2-107g+596;
P3 := 8(31g^3+405g^2-459g+333)x^3+(941g^3+1303g^2-1853g+1772)x+85g^3-
385g^2+395g-220;
P4 := 32(4g^3-69g^2+74g-49)x^4+32(21g^3+53g^2-68g+58)x^3-8(97g^3+95
g^2-145g+148)x^2+8(41g^3-89g^2-g+140)x-123g^3+391g^2-93g+3228;
P := P2^2P3P4^4/tau;

phi:=P;
f:=BestModel(phi : effort:=3);
fd:=DisplayPolynomial(f);


(1/49152(-19g^3 + 1201g^2 - 1298g + 872))(x)^1(1/6(g^3 + 5g^2 + 5g + 10)x^2 + 1/3(-4g^3 - 5g^2 - 35g - 43)x + 1/6(49g^3 + 101g^2 + 557g - 14))^1(1/6(g^3 + 5g^2 + 5g + 10)x^2 + 1/6(-7g^3 - 29g^2 - 89g - 220)x - 4g^3 + 13g^2 + 3g + 227)^2(1/6(g^3 + 5g^2 + 5g + 10)x^4 + (-g^3 - g^2 - 5g - 26)x^3 + (-7g^3 - 7g^2 - 27g + 142)x^2 + 1/3(139g^3 + 119g^2 + 1067g - 1622)x - 78g^3 - 103g^2 - 701g + 617)^4 + (-1)t


Support(Divisor(phi));

RsandPs := Support(Divisor(phi));
RsandQs := Support(Divisor(phi-1));
PsQsRs := SetToSequence(SequenceToSet(RsandPs cat RsandQs));
//xs := SmallFunctions(PsQsRs, 2genus(X)+1);
//"The number of small functions is"; #xs;
small_functions:=SmallFunctions(PsQsRs, 1);

SetProfile(true);
ffs:=[];
multiplicities:=[];
support:=[];
for xx in small_functions do
  // this is too brutal, surely we want x to have zeros/poles at oo as well;
  // is there any pattern in what works best here?
  //try 1/phi etc
  S3orbit:=[ phi, 1/phi, 1-phi, phi/(phi-1), 1-1/phi, 1/(1-phi)  ];
  for belyimap in S3orbit do
    f := model(belyimap, xx);

    Append(~ffs,<#Sprint(f),f, Index(S3orbit, belyimap), Degree(xx) >);
    sup,mult:=Support(Divisor(xx));
    Append(~support, mult);
    //insert reduction into model
  end for;
end for;
ParallelSort(~ffs,~support);

shortest_ffs:=[ ffs[i] : i in [1..Min(#ffs,10)] ];
for fuv_es in shortest_ffs do
  fuv := fuv_es[2];

  padic_redfuv:= reducemodel_padic(fuv);
  unit_redfuv := reducemodel_units(padic_redfuv);
  fuv_display := PolynomialToFactoredString(MultivariateToUnivariate(unit_redfuv));
  print fuv_display;
  print "";
end for;

ProfilePrintByTotalTime(:Max:=40);





fuv:=shortest_ffs[1,2];
fp1:=reducemodel_padic(fuv : Integral:=false, ClearDenominators:=false); //fairly quick
fp2:=reducemodel_padic(fuv : Integral:=true, ClearDenominators:=true);  //slow due to polyhedra, in particular meet, reduct, MinimalRgenerators(), Polyhedron(), Inequalities took a long time.
fp3:=reducemodel_padic(fuv : Integral:=true, ClearDenominators:=false); //~2 mins, same as fp2 but even longer because its 3-dimensional

CoefficientValuations(fp1);
CoefficientValuations(fp2);
CoefficientValuations(fp3);

fu1:=reducemodel_units(fp1);
fu2:=reducemodel_units(fp2);
fu3:=reducemodel_units(fp3);

K<g>:=F;
_<t,x>:=PolynomialRing(K,2);

//why is it not clearing denominators??
g:=(-352330873874g^3 - 140724214886g^2 - 2459611303550g +
6316249625192)(x)^23 + (1/324(-176407g^3 - 117699g^2 - 1330647g +
2664154))((17g^3 + 39g^2 + 187g + 32)x^2 + 1/6(-11g^3 - 13g^2
- 145g + 28)x + 1/6(g^3 - g^2 + 5g - 2))^2(1/3(26g^3 + 58g^2
+ 238g - 196)x^2 + 1/6(-g^3 + g^2 - 83g + 32)x + 1/6(g^3 - g^2
+ 5g - 2))^1(1/3(254g^3 + 682g^2 + 3154g + 4616)x^4 + (-108g^3
- 220g^2 - 636g - 272)x^3 + 1/3(14g^3 + 310g^2 + 154g + 56)x^2
+ (4g^3 + 2g^2 - 22g + 16)x + 1/6(g^3 - 7g^2 + 11g - 8))^4t;


fp1:=reducemodel_padic(g);
lc:=Coefficients(fp1)[24];
assert IsUnit(lc);
fu1:=reducemodel_units(fp1);
assert Coefficients(fu1)[24]^2 eq 1;
