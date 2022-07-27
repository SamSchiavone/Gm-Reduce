// TODO: just import from Belyi; Gm-Reduce should output f and scalar a
intrinsic BelyiMapSanityCheck(sigma::SeqEnum[GrpPermElt], f::RngMPolElt : lax := false) -> Any
  {Does a basic check to see if the candidate is plausible. If lax is set to true, then work in the category of lax Belyi maps.}
  // make curve and function field to compute divisors
  X := Curve(AffineSpace(Parent(f)), f);
  KX<t,x> := FunctionField(X);
  // compute third ramification value (not nec 1)
  rambool, a := ComputeThirdRamificationValue(f);
  if rambool then
    L := Parent(a);
    assert L eq BaseRing(Parent(f));
  else
    a := 1;
  end if;

  supp, ramdeg := Support(Divisor(t));
  supp1, ramdeg1 := Support(Divisor(t-a));
  // print ramdeg;
  // print ramdeg1;
  cyc := [];
  for i := 1 to 3 do
    if i eq 1 then
      cyci := Sort([<ramdeg[i], Degree(supp[i])> : i in [1..#supp] | ramdeg[i] gt 0]);
    elif i eq 2 then
      cyci := Sort([<ramdeg1[i], Degree(supp1[i])> : i in [1..#supp1] | ramdeg1[i] gt 0]);
    else
      cyci := Sort([<Abs(ramdeg[i]), Degree(supp[i])> : i in [1..#supp] | ramdeg[i] lt 0]);
    end if;
    // Clean up in case points split
    j := 1;
    while j lt #cyci do
      if cyci[j][1] eq cyci[j+1][1] then
        cyci := cyci[1..j-1] cat [<cyci[j][1], cyci[j][2]+cyci[j+1][2]>] cat cyci[j+2..#cyci];
      else
        j +:= 1;
      end if;
    end while;
    Append(~cyc, cyci);
  end for;
  map_structure := cyc;
  sigma_structure := [Sort(CycleStructure(s)) : s in sigma];
  if lax eq false then
    return (map_structure eq sigma_structure);
  else
    if map_structure eq sigma_structure then
      return true, Sym(3)!1;
    else
      lax_equivalent := false;
      lax_permutation := Sym(3)!1;
      for s in Sym(3) do
        lax_sigma := S3Action(s, sigma);
        lax_sigma_structure := [Sort(CycleStructure(t)) : t in lax_sigma];
        if map_structure eq lax_sigma_structure then
          lax_equivalent := true;
          lax_permutation := Sym(3)!s;
        end if;
      end for;
      return lax_equivalent, lax_permutation;
    end if;
  end if;
end intrinsic;

intrinsic ReplaceAll(string::MonStgElt, char1::MonStgElt, char2::MonStgElt) -> MonStgElt
  {Replace all instances of the string char1 with char2 in string}
  return Pipe(Sprintf("sed \"s/%o/%o/g\"", char1, char2), string);
end intrinsic;

intrinsic ComputeThirdRamificationValue(f::RngMPolElt) -> Any
  {Given a polynomial f(t,x) defining a plane curve where t is a 3-point branched cover ramified over 0, oo, and s, return s}
  C := Curve(AffineSpace(Parent(f)), f);
  KC<t,x> := FunctionField(C);
  k := BaseRing(BaseRing(KC));
  ram_up := Support(Divisor(Differential(t)));
  ram_down := [*Evaluate(t, el) : el in ram_up*];
  ram_other := [k!el : el in ram_down | el ne 0 and el cmpne Infinity()];
  ram_other := Setseq(Set(ram_other));
  assert #ram_other in [0,1];
  if #ram_other eq 1 then
    a1:=BaseField(C)!ram_other[1];
    return true, a1;
  else
    return false, _;
  end if;
end intrinsic;

intrinsic S3Action(tau::GrpPermElt, f::RngMPolElt) -> RngMPolElt
  {}
  S := Sym(3);
  assert Parent(tau) eq S;

  R<t,x> := Parent(f);
  bool, a := ComputeThirdRamificationValue(f);
  if bool then
    L := Parent(a);
    assert L eq BaseRing(Parent(f));
  else
    a := 1;
  end if;
  //RL<t,x> := ChangeRing(R,L);
  // TODO: fix this when only ramified above 0, oo
  if tau eq S!(1,2) then
    //return 1-phi;
    t_ev := a-t;
  elif tau eq S!(1,3) then
    //return 1/phi;
    t_ev := a^2/t;
  elif tau eq S!(2,3) then
    //return phi/(phi-1);
    t_ev := a - a^2/(a-t);
  elif tau eq S!(1,2,3) then // are these two backwards?
    //return 1-1/phi;
    t_ev := a - a^2/t;
  elif tau eq S!(1,3,2) then // are these two backwards? or right- vs left action?
    //return 1/(1-phi);
    t_ev := a^2/(a-t);
  else
    t_ev := t;
  end if;
  return Numerator(Evaluate(f, [t_ev,x])); // need to re-integralize at the end?
end intrinsic;

intrinsic S3Orbit(f::RngMPolElt) -> SeqEnum
  {}
  return [ Parent(f)!S3Action(el, f) : el in Sym(3) ];
end intrinsic;

intrinsic MultivariateToUnivariate(f::RngMPolElt) -> RngUPolElt
  {turns an element f in K[x,t] into an element K[x][t]}

  fstring:=Sprint(f);
  K<nu1> := BaseRing(Parent(f));
  Kx<x>:=PolynomialRing(K);
  Kxt<t>:=PolynomialRing(Kx);
  return eval(fstring);
end intrinsic;

intrinsic MonicToIntegral(f::RngUPolElt : Minkowski := true) -> Any
  {scale the monic univariate polynomial to be integral}
  assert IsMonic(f);
  K:=BaseRing(Parent(f));
  ZK:=Integers(K);
  coefs:=[ a : a in Coefficients(f) | a ne 0 ];

  aa := ideal<ZK | coefs>^-1;
  aprin, a := IsPrincipal(aa);
  if aprin eq false then
    a:=IdealShortVectorsProcess(aa, 0, 2: Minkowski:=Minkowski)[1];
  end if;
  f_new:=f*a;

  return f_new, a;
end intrinsic;

intrinsic PolynomialToFactoredString(f::RngUPolElt) -> MonStgElt
  {factorise the polynomial f and return it as a string. Needs to be a multivariate polynomial in K[x][t]}

  coefs:=Coefficients(f);
  mon:=Monomials(f);
  str:="";
  for j in [1..#coefs] do
    if j ne 1 then
      str:=str cat " + ";
    end if;
    a:=LeadingCoefficient(coefs[j]);
    fac:=Factorization(coefs[j]);
    list:=[];
    for item in fac do
      int,co:= MonicToIntegral(item[1]);
      Append(~list,<co,int,item[2]>);
    a /:= co^item[2];
    end for;

    str:= str cat Sprintf("(%o)",a);
    for i in [1..#list] do
      str:= str cat Sprintf("*(%o)^%o", list[i,2],list[i,3]);
    end for;
    if j ne 1 then
      str:=str cat Sprintf("*%o",mon[j]);
    end if;
  end for;

  K<nu1>:=BaseRing(BaseRing(f));
  Kx<x>:=PolynomialRing(K);
  Kxt<t>:=PolynomialRing(Kx);

  assert f eq eval(str);
  return str;
end intrinsic;


intrinsic DisplayPolynomial(f::RngMPolElt) -> MonStgElt
  {factor the polynomial}
  return PolynomialToFactoredString(MultivariateToUnivariate(f));
end intrinsic;
