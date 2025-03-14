// Ariel Pacetti example; see email from 27 Jan 2024

AttachSpec("~/github/Gm-Reduce/spec");
SetVerbose("GmReduce",true);
SetSeed(1);
K := RationalsAsNumberField();
R<u,v> := PolynomialRing(K,2);
f := (256*u^10 - 2560*u^9 + 11520*u^8 - 30720*u^7 + 53760*u^6 - 64512*u^5 + 53760*u^4 - 30720*u^3 + 11520*u^2 - 2560*u + 256)*v^24 + (-11520*u^9 + 67680*u^8 - 164160*u^7 + 208800*u^6 - 144000*u^5 + 47520*u^4 - 2880*u^3 - 1440*u^2)*v^16 + (17280*u^9 - 25920*u^8 - 71280*u^7 + 198720*u^6 - 168480*u^5 + 51840*u^4 - 2160*u^3)*v^12 + (-77760*u^8 + 136080*u^7 - 40095*u^6 - 17010*u^5 - 1215*u^4)*v^8 + (15552*u^8 + 40824*u^7 + 2916*u^6 - 243*u^5)*v^4 + (-432*u^8 + 432*u^7);
//f := (256*t^10 - 2560*t^9 + 11520*t^8 - 30720*t^7 + 53760*t^6 - 64512*t^5 + 53760*t^4 - 30720*t^3 + 11520*t^2 - 2560*t + 256)*y^24 + (-11520*t^9 + 67680*t^8 - 164160*t^7 + 208800*t^6 - 144000*t^5 + 47520*t^4 - 2880*t^3 - 1440*t^2)*y^16 + (17280*t^9 - 25920*t^8 - 71280*t^7 + 198720*t^6 - 168480*t^5 + 51840*t^4 - 2160*t^3)*y^12 + (-77760*t^8 + 136080*t^7 - 40095*t^6 - 17010*t^5 - 1215*t^4)*y^8 + (15552*t^8 + 40824*t^7 + 2916*t^6 - 243*t^5)*y^4 + (-432*t^8 + 432*t^7);
// replace v^4 -> v
fp := (256*u^10 - 2560*u^9 + 11520*u^8 - 30720*u^7 + 53760*u^6 - 64512*u^5 + 53760*u^4 - 30720*u^3 + 11520*u^2 - 2560*u + 256)*v^6 + (-11520*u^9 + 67680*u^8 - 164160*u^7 + 208800*u^6 - 144000*u^5 + 47520*u^4 - 2880*u^3 - 1440*u^2)*v^4 + (17280*u^9 - 25920*u^8 - 71280*u^7 + 198720*u^6 - 168480*u^5 + 51840*u^4 - 2160*u^3)*v^3 + (-77760*u^8 + 136080*u^7 - 40095*u^6 - 17010*u^5 - 1215*u^4)*v^2 + (15552*u^8 + 40824*u^7 + 2916*u^6 - 243*u^5)*v + (-432*u^8 + 432*u^7);

C := Curve(Spec(R), f);
Cp := Curve(Spec(R), fp);

KCp<uu,vv> := FunctionField(Cp);
t0 := Cputime();
models := AllReducedModels(uu);
t1 := Cputime();
printf "Gm-reduction took %o seconds\n", t1-t0;
fred, abc := Explode(models[1]);
X_plane := Curve(Spec(Parent(fred)), fred);
print X_plane;
printf "abc: %o\n", abc;
a, b, c := Explode(abc);
KX_plane<tt,xx> := FunctionField(X_plane);
printf "ramification values of a*t:\n%o\n", ComputeRamificationValues(a*tt);

// can we get the genus 5 curve back?
/*
  JV sez:

  This didn't finish in a reasonable amount of time; but if you replace
  y^4 by y in the above equation, it finds:

  > BestModel(t);
  9*t*x^2 - t + x^6 - x^4
  1/27

  I think that's too small to be a coincidence.  So apparently the
  quotient by y |-> i*y in the above realizes the curve as a degree 4
  cyclic cover of PP^1?

  The next step is probably to rewrite this cyclic cover in these
  coordinates, using the ramification points?  Maybe indeed there's
  something nicer here.
*/
