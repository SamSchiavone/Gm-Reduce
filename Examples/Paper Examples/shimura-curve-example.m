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
*/

AttachSpec("spec");
SetVerbose("GmReduce",true);
SetSeed(1);
S<x>:=PolynomialRing(RationalsAsNumberField());
X:=EllipticCurve(S!x^3 + 27/242*x + 189/10648,S!0);
KX<x,y> := FunctionField(X);
phi:= (864/1331*x^9 + 34992/161051*x^7 + 61236/1771561*x^6 + 472392/19487171*x^5 + 1653372/214358881*x^4 + 59049/38974342*x^3 + 11160261/25937424601*x^2 + 78121827/1141246682444*x + 182284263/50214854027536)/(x^12 + 54/121*x^10 + 54/121*x^9 + 2187/29282*x^8 + 2187/14641*x^7 + 98415/1771561*x^6 + 59049/3543122*x^5 + 38795193/3429742096*x^4 + 610173/857435524*x^3 + 129140163/207499396808*x^2 + 531441/51874849202*x + 531441/51874849202);
printf "ramification values of original map %o\n", ComputeRamificationValues(phi);
// reduce model
models := AllReducedModels(phi);
f, abc := Explode(models[1]);
C := Curve(Spec(Parent(f)), f);
print C;
printf "abc: %o\n", abc;
a, b, c := Explode(abc);
KC<tt,xx> := FunctionField(C);
printf "ramification values of a*t:\n%o\n", ComputeRamificationValues(a*tt);
