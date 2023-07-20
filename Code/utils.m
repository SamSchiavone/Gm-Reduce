// TODO: just import from Belyi; Gm-Reduce should output f and scalar a
// Take scalar as input, too!
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

intrinsic ReplaceString(s::MonStgElt, fs::MonStgElt, ts::MonStgElt) -> MonStgElt
    {Return a string obtained from the string s by replacing all occurences of the SINGLE character fs with ts.}
    //assert #fs eq 1;
    L := Split(s,fs);
    if Index(s,fs) eq 1 then
      L := [""] cat L;
    end if;
    fs_rev := Reverse(fs);
    s_rev := Reverse(s);
    if Index(s_rev, fs_rev) eq 1 then
      L := L cat [""];
    end if;
    // Split doesn't deal with fs at the beginning or end of the string correctly.
    //if s[1] eq fs then Insert(~L, 1, ""); end if;
    //if s[#s] eq fs then Append(~L, ""); end if;
    return Join(L, ts);
end intrinsic;

intrinsic ReplaceString(s::MonStgElt, fs::[MonStgElt], ts::[MonStgElt]) -> MonStgElt
  {Return a string obtained from the string s by replacing all occurences of strings in fs with strings in ts.}
  // assert not (true in [ts[i] in s : i in [1..#ts]]);
  for i:=1 to #fs do
    s:=ReplaceString(s,fs[i],ts[i]);
  end for;
  return s;
end intrinsic;

// procedure versions
intrinsic ReplaceString(~s::MonStgElt, fs::MonStgElt, ts::MonStgElt)
  {In the string s, replace all occurences of fs with ts.}
  s := ReplaceString(s,fs,ts);
end intrinsic;

intrinsic ReplaceString(~s::MonStgElt, fs::[MonStgElt], ts::[MonStgElt])
  {In the string s, replace all occurences of strings in fs with strings in ts.}
  for i:=1 to #fs do
    ReplaceString(~s,fs[i],ts[i]);
  end for;
end intrinsic;

intrinsic PySplit(s::MonStgElt, sep::MonStgElt : limit:=-1) -> SeqEnum[MonStgElt]
{Splits using Python semantics (different when #sep > 1, and different when sep at beginning or end)}
    if #sep eq 0 then
        error "Empty separator";
    end if;
    i := 1;
    j := 0;
    ans := [];
    while limit gt 0 or limit eq -1 do
        if limit ne -1 then limit -:= 1; end if;
        pos := Index(s, sep, i);
        if pos eq 0 then break; end if;
        j := pos - 1;
        Append(~ans, s[i..j]);
        i := j + #sep + 1;
    end while;
    Append(~ans, s[i..#s]);
    return ans;
end intrinsic;

intrinsic PyReplaceString(s::MonStgElt, sep::MonStgElt, rep::MonStgElt : limit:=-1) -> MonStgElt
  {In the string s, replace all occurences of strings in fs with strings in ts. Uses PySplit to split}
  spl := PySplit(s, sep : limit := limit);
  return Join(spl, rep);
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

intrinsic S3ActionPlane(tau::GrpPermElt, f::RngMPolElt, a::RngElt) -> RngMPolElt
  {}

  S := Sym(3);
  assert Parent(tau) eq S;
  R<t,x> := Parent(f);
  // WARNING: the variable t in the polynomial ring undergoes the INVERSE transformation. This is because we're basically setting, e.g., u = 1/(1-t), and then solving for t. This is only noticeable for the 3-cycles since transpositions are self-inverse
  if tau eq S!(1,2) then
    //return 1-phi;
    t_ev := a-t;
  elif tau eq S!(1,3) then
    //return 1/phi;
    t_ev := a^2/t;
  elif tau eq S!(2,3) then
    //return 1 - 1/(1-phi);
    t_ev := a - a^2/(a-t);
  elif tau eq S!(1,2,3) then // these are the tricky ones that are inverse
    //return 1/(1-phi);
    t_ev := a - a^2/t;
  elif tau eq S!(1,3,2) then
    //return 1-1/phi;
    t_ev := a^2/(a-t);
  else
    t_ev := t;
  end if;
  return Numerator(Evaluate(f, [t_ev,x])); // need to re-integralize at the end?
end intrinsic;

intrinsic S3Orbit(f::RngMPolElt, a::RngElt) -> RngMPolElt
  {}
  return [S3ActionPlane(tau, f, a) : tau in Sym(3)];
end intrinsic;

// copied from Belyi (belyi_main.m)
intrinsic S3Action(tau::GrpPermElt, phi::FldFunFracSchElt) -> FldFunFracSchElt
  {}
  S := Sym(3);
  assert Parent(tau) eq S;
  if tau eq S!(1,2) then
    return 1-phi;
  elif tau eq S!(1,3) then
    return 1/phi;
  elif tau eq S!(2,3) then
    return 1 - 1/(1-phi);
  elif tau eq S!(1,2,3) then // swapped these compared to belyi_main because they seemed to be backwards
    return 1/(1-phi);
  elif tau eq S!(1,3,2) then
    return 1-1/phi;
  else
    return phi;
  end if;
end intrinsic;

// TODO: change this
/*
intrinsic S3Orbit(f::RngMPolElt) -> SeqEnum
  {}
  return [ Parent(f)!S3ActionPlane(el, f, phi) : el in Sym(3) ];
end intrinsic;
*/

// copied from Belyi (belyi_main.m)
intrinsic S3Orbit(phi::FldFunFracSchElt) -> SeqEnum 
  {Produce the orbit of phi under the action of S3 permuting 0, 1, and oo.}
  return [S3Action(el, phi) : el in Sym(3)];
end intrinsic;

intrinsic MultivariateToUnivariate(f::RngMPolElt) -> RngUPolElt
  {turns an element f in K[x,t] into an element K[x][t]}

  fstring:=Sprint(f);
  K<nu> := BaseRing(Parent(f));
  Kx<x>:=PolynomialRing(K);
  Kxt<t>:=PolynomialRing(Kx);
  return eval(fstring);
end intrinsic;

// Another possibility
/*
  R<x,y> := PolynomialRing(K,2);
  S0<X> := PolynomialRing(K);
  S<Y> := PolynomialRing(S0);
  mp_x := hom< S0 -> R | x >;
  mp_y := hom< S -> R | mp_x, [y]>;
  mp_xy := hom< R -> S | [X, Y] >;
*/

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
  {factorise the polynomial f and return it as a string. Needs to be a polynomial in K[x][t]}

  coefs:=Coefficients(f); // coefficients are polys in x
  mons:=Monomials(f); // monomials 1, t, t^2, ...
  Reverse(~coefs);
  Reverse(~mons);
  //printf "coefs = %o\n", coefs;
  //printf "mons = %o\n", mons;
  if #coefs eq 0 and #mons eq 0 then // f = 0
    return Sprint(0);
  end if;
  str := "";
  for j in [1..#coefs] do
    str_j := "";
    if coefs[j] ne 0 then
      a := LeadingCoefficient(coefs[j]);
      fac := Factorization(coefs[j]);
      list := [];
      for item in fac do
        poly,const := MonicToIntegral(item[1]);
        a /:= const^item[2];
        Append(~list,<const,poly,item[2]>);
      end for;
      if j ne 1 then
        if Sprint(a)[1] eq "-" then
          str *:= " - ";
          a := -a;
        else
          str *:= " + ";
        end if;
      end if;

      if "+" in Sprint(a) or "-" in Sprint(a) then
        str_j *:= Sprintf("(%o)",a);
      elif (a eq 1) and (not coefs[j] in [1,-1]) then
        str_j *:= "";
      elif (a eq 1) and (coefs[j] in [1,-1]) then
        str_j *:= Sprintf("%o", a);
      else
        str_j *:= Sprintf("%o", a);
      end if;
      if (#list ne 0) and (a ne 1) then
        str_j *:= "*";
      end if;
      for i in [1..#list] do
        if "+" in Sprint(list[i][2]) or "-" in Sprint(list[i][2]) then
          str_j *:= Sprintf("(%o)", list[i][2]);
        else
          str_j *:= Sprintf("%o", list[i][2]);
        end if;
        if list[i][3] ne 1 then
          str_j *:= Sprintf("^{%o}", list[i][3]);
        end if;
        if i ne #list then
          str_j *:= "*";
        end if;
      end for;
      //printf "j = %o, str_j = %o\n", j, str_j;
      //if (str_j eq "1") and (j ne 1) then // reverse
      if (str_j eq "1") and (j ne #coefs) then
        str *:= "";
      else
        str *:= str_j;
      end if;
      //if j ne 1 then // reverse
      if j ne #coefs then
        if #str eq 0 then
          str *:= Sprintf("%o",mons[j]); // multiply by monomial in t
        elif (str[#str] in ["+","-"," "]) then
          str *:= Sprintf("%o",mons[j]); // multiply by monomial in t
          //printf "mons[j] = %o\n", mons[j];
        else
          str *:= Sprintf("*%o",mons[j]); // multiply by monomial in t
          //printf "mons[j] = %o\n", mons[j];
        end if;
      end if;
    end if;
  end for;

  K<nu>:=BaseRing(BaseRing(f));
  Kx<x>:=PolynomialRing(K);
  Kxt<t>:=PolynomialRing(Kx);

  //printf "before LaTeXing: %o\n", str;
  test_str := str;
  test_str := PyReplaceString(test_str, "{", "");
  test_str := PyReplaceString(test_str, "}", "");
  assert f eq eval(test_str);
  // format for LaTeX
  //str := ReplaceString(str, "*", " \\cdot ");
  str := PyReplaceString(str, "*", " ");
  str := PyReplaceString(str, "(", "\\\\left(");
  str := PyReplaceString(str, ")", "\\\\right)");
  str := PyReplaceString(str, "nu", "\\\\nu");
  // TODO: deal with 2-digit powers
  return str;
end intrinsic;

intrinsic DisplayPolynomial(f::RngMPolElt) -> MonStgElt
  {factor the polynomial}
  return PolynomialToFactoredString(MultivariateToUnivariate(f));
end intrinsic;

intrinsic ReadDataRow(line::MonStgElt) -> Any
  {}

  lab1, lab2, f, a, cs := Explode(Split(line, "|"));
  cs := eval cs;
  if cs eq [-1,1] then
    K<nu> := RationalsAsNumberField();
  else
    K<nu> := NumberField(Polynomial(cs));
  end if;
  R<t,x> := PolynomialRing(K,2);
  f := eval f;
  a := eval a;
  /*
    C := Curve(Spec(R),f);
    KC<t,x> := FunctionField(C);
    phi := (1/a)*t;
    return lab1, lab2, C, phi, cs;
  */
  return lab1, lab2, f, a, cs;
end intrinsic;

intrinsic ComputeRamificationValues(phi::FldFunFracSchElt)-> Any
  {}

  dpts, dmults := Support(Divisor(Differential(phi)));
  return [* Evaluate(phi, el) : el in dpts *];
end intrinsic;
