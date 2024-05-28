// Example 8.1.7 (p. 32) from ON EXPLICIT MODULI PROBLEMS FOR SHIMURA CURVES
//y2=x3+27x+ 189
/*
E := EllipticCurve([27,189]);
KE<x,y> := FunctionField(E);
c:=(11^3)/(2*3^6);
num:=(x - 3/11)^4*(x^2 + (3/11)*x + 45/242)^4;
den:=(x + 3/22)^3*(x^2 - (3/22)*x + 63/484)^3;
phi := c*num/den;

BelyiMapNum:=(803437664440576*z^12 + 358558957684224*z^10 - 162981344401920*z^9 + 60006767711616*z^8 - 54551607010560*z^7 + 16861405803264*z^6 - 6086336319360*z^5 + 2891009751696*z^4 - 645520518720*z^3 + 154330466400*z^2 - 46766808000*z + 5314410000);
BelyiMapDen:=(880099259770368*z^9 + 294578677857024*z^7 + 46864789659072*z^6 + 32866216124544*z^5 + 10457432403264*z^4 + 2054138507784*z^3 + 583369162992*z^2 + 92808730476*z + 4921675101);
phi2 := BelyiMapNum/BelyiMapDen;
sigma := [ Sym(24) |
  (1, 2, 5, 12, 20, 11)(3, 4, 10, 17, 21, 16)(6, 7, 15, 23, 24, 14)(8, 9, 13, 22, 18, 19),
  (1, 3, 8, 7)(2, 6, 14, 13)(4, 11, 18, 10)(5, 9, 16, 21)(12, 17, 22, 24)(15, 19, 20, 23),
  (1, 4)(2, 7)(3, 9)(5, 13)(8, 15)(11, 19)(12, 21)(14, 22)(17, 18)(20, 24)
];
*/

AttachSpec("spec");
SetVerbose("GmReduce",true);
SetSeed(1);
S<x>:=PolynomialRing(RationalsAsNumberField());
X:=EllipticCurve(S!x^3 + 27/242*x + 189/10648,S!0);
KX<x,y> := FunctionField(X);
//phi:= (864/1331*x^9 + 34992/161051*x^7 + 61236/1771561*x^6 + 472392/19487171*x^5 + 1653372/214358881*x^4 + 59049/38974342*x^3 + 11160261/25937424601*x^2 + 78121827/1141246682444*x + 182284263/50214854027536)/(x^12 + 54/121*x^10 + 54/121*x^9 + 2187/29282*x^8 + 2187/14641*x^7 + 98415/1771561*x^6 + 59049/3543122*x^5 + 38795193/3429742096*x^4 + 610173/857435524*x^3 + 129140163/207499396808*x^2 + 531441/51874849202*x + 531441/51874849202);
phi := ((2^5*3^3)/11^3)*((x + 3/22)^3*(x^2 - 3/22*x + 63/484)^3)/((x + 6/11)^2*(x^2 + 9/242)^2*(x^2 + 18/121)*(x^2 - 6/11*x + 9/22)^2);
printf "ramification values of original map %o\n", ComputeRamificationValues(phi);

// reduce model
models := AllReducedModels(phi);
//models := AllReducedModels(phi : effort := 60);
f, abc := Explode(models[1]);
C := Curve(Spec(Parent(f)), f);
print C;
printf "abc: %o\n", abc;
a, b, c := Explode(abc);
KC<tt,xx> := FunctionField(C);
printf "ramification values of a*t:\n%o\n", ComputeRamificationValues(a*tt);

// compare with minimal model
X_min, mp := MinimalModel(X);
KX_min<v,w> := FunctionField(X_min);
phi_min := Pushforward(mp, phi);
phi_v := Coefficients(phi_min);
num := Numerator(phi_v[1]);
den := Denominator(phi_v[1]);
Factorization(num);
Factorization(den);

_<z> := Parent(num);
strings := [];
for poly in [num, den] do
  s := "";
  for fact in Factorization(poly) do
    b, e := Explode(fact);
    if e eq 1 then
      s *:= Sprintf("(%o)*", b);
    else
      s *:= Sprintf("(%o)^%o*", b, e);
    end if;
  end for;
  ReplaceString(~s, "z", "x");
  s := s[1..#s-1];
  Append(~strings, s);
end for;



/*
lc
2725888/27

num
<x + 7, 3>,
<x^2 - 8*x + 379, 3>

den
<x + 29, 2>,
<x^2 - 30*x + 1193, 2>,
<x^2 - 2/3*x + 323/3, 2>,
<x^2 - 2/3*x + 1291/3, 1>
*/

/*
-512 x^6 t^3 - (-192 x^12 + 15488 x^8 + 63888 x^6 + 1288408 x^2 - 1771561) t^2 + 2 x^4 (-12 x^14 - 968 x^10 + 41261 x^8 + 58564 x^6 - 322102 x^4 - 19487171) t + x^8 (x^4 + 121)^4
*/
