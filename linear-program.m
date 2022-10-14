//AttachSpec("../Belyi/Code/spec"); // have to change if Belyi repo is elsewhere
SetClassGroupBounds("GRH");

intrinsic TrialReduction(phi::FldFunFracSchElt) -> FldFunFracSchElt
  {Try to reduce an element of the function field naively over just the integers
  first we treat the number field element as just a variable and then fix it in reducemodel_padic}

  X:=Curve(Parent(phi));
  K:=BaseRing(X);
  Kw<w>:=PolynomialRing(K);

  S1:=&cat[ Eltseq(c) : c in Coefficients(Numerator(phi)) ]
  cat &cat[ Eltseq(c) : c in Coefficients(Denominator(phi)) ];

  S2:=&cat[ TrialDivision(Integers()!Numerator(a)) : a in S1 | a ne 0 ]
  cat &cat[ TrialDivision(Integers()!Denominator(a)) : a in S1  ];

  S3:= Setseq(Set([a[1] : a in S2]));

  E1:=X;
  for p in S3 do
    fw:=Kw!HyperellipticPolynomials(E1);
    u0:=p;
    E2:=EllipticCurve(Evaluate(fw,(w*u0^2))/u0^6);
    m:=Isomorphism(E1,E2,[0,0,0,1/u0]);
    phi_init:=Pushforward(m,phi);

    sprint_phi:=Sprint(phi);
    if #Sprint(phi_init) gt #sprint_phi then
      u0:=1/u0;
    end if;


    phi1:=phi;
    phi2:=phi;
    sprint_phi1:=Sprint(phi1);
    sprint_phi2:=Sprint(phi2);
    while #sprint_phi2 le #sprint_phi1 do
      phi1:=phi2;
      E1:=Curve(Parent(phi1));
      fw:=Kw!HyperellipticPolynomials(E1);
      E2:=EllipticCurve(Evaluate(fw,u0^2*w)/u0^6);
      m:=Isomorphism(E1,E2,[0,0,0,1/u0]);
      phi2:=Pushforward(m,phi1);
      sprint_phi1:=Sprint(phi1);
      sprint_phi2:=Sprint(phi2); #sprint_phi2;
      //u:=u*u0;
    end while;

    phi:=phi1;
  end for;

  return phi;
end intrinsic;

intrinsic BelyiObjectiveFunction(fuv::RngMPolElt) -> RngMPolElt
  {Given a polynomial or rational function fuv in 2 variables, return...?} // TODO: finish doc string
  K := BaseRing(Parent(fuv));
  u := Parent(fuv).1;
  v := Parent(fuv).2;
  Rx3<x1,x2,x3>:=PolynomialRing(Rationals(),3);
  mexps := [ Exponents(m) : m in Monomials(fuv) ];
  coefs:=Coefficients(fuv);
  assert &+[ coefs[i]*(u^mexps[i,1])*v^mexps[i,2] : i in [1..#mexps] ] eq fuv;
  return (&+[ m[1] : m in mexps])*x1 + (&+[ m[2] : m in mexps])*x2 + #mexps*x3;
end intrinsic;

intrinsic MinimiseL1ToLinearProgram(coefficients::ModMatRngElt, constants::ModMatRngElt : prec:=100) -> LP
  {}/*we turn minimising the function \sum_{i=1..m} | a_{i,1}x_1 + ... + a_{i,n}x_n + b_i |
   into a linear program. The input is coefficients which is an mxn matrix of coefficients a_{i,j}
   and and mx1 matrix of the {b_i}. The output is an equivalent linear program */

  k:=BaseRing(coefficients);
  rows:=Rows(coefficients);
  row_no:=NumberOfRows(coefficients);
  column_no:=NumberOfColumns(coefficients);
  var_no:=row_no+column_no;
 	L := LPProcess(k, var_no);
 	obj:=Matrix(k,1,var_no,[0 : i in [1..column_no]] cat [1 : i in [1..row_no]]);
 	SetObjectiveFunction(L, obj);
  SetIntegerSolutionVariables(L,[ i : i in [1..var_no]], true);


 	for m in [1..row_no] do

    extra_var:=[ 0 : k in [1..row_no-1] ];
    Insert(~extra_var, m, -1);
		lhs1:= Matrix(k,1,var_no, Eltseq(rows[m]) cat extra_var);
		lhs2:= Matrix(k,1,var_no, Eltseq(-rows[m]) cat extra_var);

		rhs1:= Matrix(k,-constants[m]);
		rhs2:= Matrix(k,constants[m]);

		AddConstraints(L, lhs1, rhs1 : Rel := "le");
		AddConstraints(L, lhs2, rhs2 : Rel := "le");

		AddConstraints(L, Matrix(k,1,var_no, [0 : i in [1..column_no]] cat extra_var), Matrix(k,[[0]]) : Rel :="le");
  end for;
  for i in [1..column_no] do  SetLowerBound(L, i, k!-10000); end for;
  for j in [column_no+1..var_no] do  SetLowerBound(L, j, k!0); end for;
  return L;
end intrinsic;

intrinsic RemoveInfinitesimal(a::FldReElt,N::FldRatElt,prec::RngIntElt) -> FldReElt
  {If |a| < N then return 0, else return a}
  if Abs(a) lt RealField(prec)!N then
    return Parent(a)!0;
  else
    return a;
  end if;
end intrinsic;

intrinsic CoefficientSupport(f::RngMPolElt : rationals:=true) -> SeqEnum
  {returns all of the primes ideals with nonzero valuation in the coefficients}
  if BaseRing(Parent(f)) eq Rationals() then
    if rationals ne true then
      K:=RationalsAsNumberField();
    else
      K := Rationals();
    end if;
  else
    K := BaseRing(Parent(f));
  end if;
  S := &cat[TrialDivision(Integers()!Norm(Numerator(s))) : s in Coefficients(f) | s ne 0 ]
     cat &cat[TrialDivision(Integers()!Norm(Denominator(s))) : s in Coefficients(f) | s ne 0 ];
  S := SequenceToSet([s[1] : s in S]);
  SS:=&cat[ [pp[1] : pp in Factorization(p*Integers(K))] : p in S ];
  return SS;
end intrinsic;

intrinsic CoefficientValuations(f::RngMPolElt : primes:=CoefficientSupport(f)) -> SeqEnum
  {the valuations of each coefficient at every prime in CoefficientSupport(f)}
  if BaseRing(Parent(f)) eq Rationals() then
    K:=RationalsAsNumberField();
  else
    K := BaseRing(Parent(f));
  end if;

  return [ [ Valuation(cc,pp) : cc in Coefficients(ChangeRing(f,K)) ] : pp in primes ];
end intrinsic;

intrinsic IgnorePrime(f::RngMPolElt,pp::RngOrdIdl) -> Any
  {}
  //check if the linear program is already optimal at (0,..,0) for the prime pp.
  if BaseRing(Parent(f)) eq Rationals() then
    K:=RationalsAsNumberField();
  else
    K := BaseRing(Parent(f));
  end if;
  variables:=[ Parent(f).i : i in [1..#Names(Parent(f))] ];
  n:=#variables;
  ZK := Integers(K);
  k:=Integers();
  coefs_and_monomials:= [ [Coefficients(f)[i],Monomials(f)[i]] : i in [1..#Coefficients(f)] ];
  mexps := [ Exponents(m[2]) : m in coefs_and_monomials ];
  m:=#mexps;
  coefs:=[ K!a[1] : a  in coefs_and_monomials ];
  //assert &+[ coefs[i]*(u^mexps[i,1])*v^mexps[i,2] : i in [1..#mexps] ] eq fuv;
  obj_coefs:= [ &+[ m[i] : m in mexps] : i in [1..n] ];

  obj := Matrix(k,1,n+1, obj_coefs cat [m]);
  lhs_coefs:= [ A cat [1] : A in mexps ];
  lhs := Matrix(k, lhs_coefs);     //constraints
  rel := Matrix(k,[[1] : ef in mexps]);
  lp_size:=n+1;

  cvals := [ Valuation(c,pp) : c in coefs  ];
  rhs := Matrix(k, [[-cf] : cf in cvals]);          //valuations

  if not(Set([ vv ge 0 : vv in cvals ]) eq Set([true])) then
    ignore_prime:=false;
  else

    zero_constraints:=[];
    nonzero_constraints:=[];
    pp_rhs:=[ Eltseq(r)[1] : r in Rows(rhs) ];

    for i in [1..#lhs_coefs] do
      if pp_rhs[i] eq 0 then
        Append(~zero_constraints, lhs_coefs[i]);
      else
        Append(~nonzero_constraints, lhs_coefs[i]);
      end if;
    end for;

    if zero_constraints eq [] then
      ignore_prime:=false;
    elif nonzero_constraints eq [] then
      ignore_prime:=true;
    else
      zero_angles := [ Arccos(A[lp_size]/Sqrt(&+[ x^2 : x in A ])) : A in zero_constraints ];
      nonzero_angles := [ Arccos(A[lp_size]/Sqrt(&+[ x^2 : x in A ])) : A in nonzero_constraints ];;
      obj_angle:=Arccos((Eltseq(obj)[lp_size])/Sqrt(&+[ x^2 : x in Eltseq(obj) ]));
      zero_angle_range := [ Min(zero_angles), Max(zero_angles) ];
      nonzero_angle_range := [ Min(nonzero_angles), Max(nonzero_angles) ];
      //assert #Set(zero_angle_range) eq 2;

      if (obj_angle gt zero_angle_range[2]) and (obj_angle le nonzero_angle_range[2])
        or (obj_angle lt zero_angle_range[1]) and (obj_angle ge nonzero_angle_range[1]) then
        ignore_prime:=false;
      else
        ignore_prime:=true;
      end if;

      if (obj_angle gt Max(zero_angles cat nonzero_angles))
          or (obj_angle lt Min(zero_angles cat nonzero_angles)) then
            ignore_prime:=true;
      end if;
      //pp; cvals; zero_optimal;
    end if;
  end if;
  return ignore_prime;
end intrinsic;




intrinsic reducemodel_padic(f::RngMPolElt : FixedVariables:=[], PrimesForReduction:=[]) -> RngMPolElt, SeqEnum
  {Input: a multivariate polynomial f \in K[z_1,..,z_n]; Output: minimal and integral c*f(a_1z_1,...,a_nz_n) and [a_1,...,a_n,c]
  FixedVariable is the set of variables to fix, include n+1 if no scaling is allowed}
  if BaseRing(Parent(f)) eq Rationals() then
    K:=RationalsAsNumberField();
  else
    K := BaseRing(Parent(f));
  end if;
  variables:=[ Parent(f).i : i in [1..#Names(Parent(f))] ];
  var_size:=#variables;
  ZK := Integers(K);
  k:=RealField(20);
  h:=ClassNumber(K);
  Cl,mp:=ClassGroup(K);
  pm:=Inverse(mp);

  coefs_and_monomials:= [ [Coefficients(f)[i],Monomials(f)[i]] : i in [1..#Coefficients(f)] ];
  mexps := [ Exponents(m[2]) : m in coefs_and_monomials ];
  m:=#mexps;
  coefs:=[ K!a[1] : a  in coefs_and_monomials ];
  //assert &+[ coefs[i]*(u^mexps[i,1])*v^mexps[i,2] : i in [1..#mexps] ] eq fuv;

  //SS:= [ pp : pp in SS | Set([Valuation(cc,pp) : cc in coefs]) notin [{0,1},{0}] ];
  if PrimesForReduction eq [] then
    support_init:=PrimesUpTo(3,K);
  else
    support_init:=[ ZK!!p : p in PrimesForReduction];
  end if;
  SS:=[];
  for pp in support_init do
    cvals := [ Valuation(c,pp) : c in coefs  ];
    if not((Set(cvals) in [{0,1},{0}]) and (#[ a : a in cvals | a eq 1 ] in [0,1])) then
      Append(~SS,pp);
    end if;
  end for;
  if SS eq [] then
    return f, [K!1 : i in [1..var_size+1] ];
  end if;
  //ignore prime not working properly SS:=[ pp : pp in support_init | IgnorePrime(f,pp) eq false ];
  //S is the prime divisors of all norms of numerators and denominators of coeffients

  if h eq 1 then
    lp_size:=(var_size+1)*#SS;
    obj:= Matrix(k,1,lp_size,&cat[ [ Log(Norm(SS[j]))*(&+[ m[i] : m in mexps]) : i in [1..var_size] ] cat [Log(Norm(SS[j]))*m] : j in [1..#SS] ] );
  else
    lp_size:=(var_size+1)*(#SS+#Generators(Cl));
    obj:= Matrix(k,1,lp_size,&cat[ [ Log(Norm(SS[j]))*(&+[ m[i] : m in mexps]) : i in [1..var_size] ] cat [Log(Norm(SS[j]))*m] : j in [1..#SS] ] cat [0 : w in [1..#Generators(Cl)*(var_size+1)]]);
  end if;

  L := LPProcess(k, lp_size);
  SetObjectiveFunction(L, obj);
  SetIntegerSolutionVariables(L,[ i : i in [1..lp_size]], true);
  //SetIntegerSolutionVariables(L,[ i : i in [1+lp_size-#Generators(Cl)*(var_size+1)..lp_size]], true);

  if h eq 1 then
    extra_zeroes:=[ 0 : t in [1..(var_size+1)*(#SS-1)]];
  else
    extra_zeroes:=[ 0 : t in [1..(var_size+1)*(#SS-1)]] cat [ 0 : w in [1..#Generators(Cl)*(var_size+1)] ];
  end if;

  for i in [1..#SS] do
    for j in [1..m] do
      lhs:=Insert(extra_zeroes, (var_size+1)*i-var_size,(var_size+1)*i-var_size-1,mexps[j] cat [1]);
      lhs:=Matrix(k,1,lp_size,lhs);
  		rhs:= Matrix(k,1,1,[-Valuation(coefs[j],SS[i])]);
  		AddConstraints(L, lhs, rhs : Rel := "ge");
    end for;
  end for;

  if h ne 1 then
    for w in [1..var_size+1] do
      //add in the constraints to be principal one variable at a time
      zeroes:= [ 0 : t in [1..var_size] ];
      for m in [1..#Generators(Cl)] do

        Clcon:=[];
        for v in [1..#Generators(Cl)] do
          if v eq m then
            Append(~Clcon,Order(Cl.m));
          else
            Append(~Clcon,0);
          end if;
        end for;
        Clzeroes:=[];
        for s in [1..var_size+1] do
          if s eq w then
            Append(~Clzeroes,Clcon);
          else
            Append(~Clzeroes,[ 0 : n in [1..#Generators(Cl)] ]);
          end if;
        end for;
        Clzeroes:=&cat(Clzeroes);

        principal_constraint:=&cat[ Insert(zeroes, w,w-1, [ Eltseq(pm(SS[j]))[m] ]) : j in [1..#SS] ];
        principal_constraint_lhs:=Matrix(k,1,(var_size+1)*(#SS+#Generators(Cl)),principal_constraint cat Clzeroes);
        principal_constraint_rhs:=Matrix(k,1,1,[0]);
        AddConstraints(L, principal_constraint_lhs, principal_constraint_rhs : Rel := "eq");
      end for;
    end for;
  end if;

  //add in the fixed variable constraints
  if FixedVariables ne [] then
    for i in FixedVariables do
      for j in [0..#SS-1] do
        zeroes :=[  0 : t in [1..(var_size+1)*#SS-1] ];
        lhs_fix:= Insert(zeroes, (var_size+1)*j+i,1);
        lhs_fix:=Matrix(k,1,lp_size,lhs_fix);
        AddConstraints(L,lhs_fix,Matrix(k,1,1,[0]) : Rel := "eq" );
      end for;
    end for;
  end if;



  for i in [1..lp_size] do  SetLowerBound(L, i, k!-1000); end for;

  soln,state:=Solution(L);
  assert state eq 0;
  soln:=Eltseq(soln);
  soln:= [ Integers()!Round(s) : s in soln ];

  soln_ideals:=<>;
  soln_exponents:=[];
  for r in [1..var_size+1] do
    Append(~soln_exponents, [ soln[(var_size+1)*(j-1)+r] : j in [1..#SS] ] );
    Append(~soln_ideals,&*[ SS[j]^soln[(var_size+1)*(j-1)+r] : j in [1..#SS] ]);
  end for;

  scaling_factors:=<>;
  for aa in soln_ideals do
    tr,a:=IsPrincipal(aa);
    Append(~scaling_factors,a);
  end for;

  guv:=Evaluate(f,[(BaseRing(Parent(f))!scaling_factors[i])*variables[i] : i in [1..var_size]])*BaseRing(Parent(f))!scaling_factors[var_size+1];

  return guv, [K!el : el in scaling_factors];
end intrinsic;


intrinsic reducemodel_padic_old(f::RngMPolElt : Integral:=true, ClearDenominators:=false, Minkowski:=true, Speedy:=false) -> RngMPolElt, SeqEnum
  {Input: a multivariate polynomial f \in K[z_1,..,z_n]; Output: minimal and integral c*f(a_1z_1,...,a_nz_n) and [a_1,...,a_n,c]}
  /*Options: Integral, ClearDenominator, Minkowski, Speedy */
  if BaseRing(Parent(f)) eq Rationals() then
    K:=RationalsAsNumberField();
  else
    K := BaseRing(Parent(f));
  end if;
  variables:=[ Parent(f).i : i in [1..#Names(Parent(f))] ];
  n:=#variables;
  ZK := Integers(K);
  k:=RealField(30);


  if ClearDenominators eq true then
    coefs_and_monomials:= [ [Coefficients(f)[i],Monomials(f)[i]] : i in [1..#Coefficients(f)] | Coefficients(f)[i] ne 0 and Exponents(Monomials(f)[i]) ne [0 : k in [1..n]] ];
    mexps := [ Exponents(m[2]) : m in coefs_and_monomials ];
    m:=#mexps;
    coefs:=[ K!a[1] : a  in coefs_and_monomials ];
    //assert &+[ coefs[i]*(u^mexps[i,1])*v^mexps[i,2] : i in [1..#mexps] ] eq fuv;
    obj_coefs:= [ &+[ m[i] : m in mexps] : i in [1..n] ];

    //clear denominators after the fact
    obj := Matrix(k,1,n, obj_coefs);
    lhs_coefs:= mexps;
    lhs := Matrix(k, lhs_coefs);     //constraints
    rel := Matrix(k,[[1] : ef in mexps]);  //lhs greater than rhs
    rescaling_ideals:=[[ 1 : i in [1..n] ]];
    lp_size:=n;
  else
    coefs_and_monomials:= [ [Coefficients(f)[i],Monomials(f)[i]] : i in [1..#Coefficients(f)] | Coefficients(f)[i] ne 0 ];
    mexps := [ Exponents(m[2]) : m in coefs_and_monomials ];
    m:=#mexps;
    coefs:=[ K!a[1] : a  in coefs_and_monomials ];
    //assert &+[ coefs[i]*(u^mexps[i,1])*v^mexps[i,2] : i in [1..#mexps] ] eq fuv;
    obj_coefs:= [ &+[ m[i] : m in mexps] : i in [1..n] ];

    //scaling the whole function is baked into the linear program
    obj := Matrix(k,1,n+1, obj_coefs cat [m]);
    lhs_coefs:= [ A cat [1] : A in mexps ];
    lhs := Matrix(k, lhs_coefs);     //constraints
    rel := Matrix(k,[[1] : ef in mexps]);
    rescaling_ideals:=[[ 1 : i in [1..n+1] ]];
    lp_size:=n+1;
  end if;

  new_c := 1;
  new_f:=f;

  SS:=CoefficientSupport(f);
  //S is the prime divisors of all norms of numerators and denominators of coeffients

  minimal_solutions:=[];
  for pp in SS do
    cvals := [ Valuation(c,pp) : c in coefs  ];
    rhs := Matrix(k, [[-cf] : cf in cvals]);          //valuations
    if Integral eq false then
      L:=MinimiseL1ToLinearProgram(lhs, -rhs);
      soln,state:=Solution(L);
      assert state eq 0;
      soln:= [ Eltseq(soln)[i] : i in [1..NumberOfColumns(lhs)] ];
      points_loop:=[soln];

    else

      /*V2:=VectorSpace(Rationals(),2);
      if lp_size eq 2 and Set([ IsIndependent([V2!obj[1],V2!row]) : row in Rows(lhs) ]) eq {true} then

        L := LPProcess(k, lp_size);
        SetObjectiveFunction(L, obj);
        AddConstraints(L, lhs, rhs : Rel := "ge");
        for i in [1..lp_size] do  SetLowerBound(L, i, k!-10000); end for;
        soln,state:=Solution(L);
        assert state eq 0;
        points_loop:=[soln];*/

      //else

      if Speedy eq true then

        L := LPProcess(k, lp_size);
        SetObjectiveFunction(L, obj);
        AddConstraints(L, lhs, rhs : Rel := "ge");
        //UnsetBounds(L) doesn't work
        //These are lower bounds on the solution
        for i in [1..lp_size] do  SetLowerBound(L, i, k!-10000); end for;
        soln,state:=Solution(L);
        points_loop:=[soln];

      else

        //Need to remove the spurious ones that are all zero already
        halfspaces:=[ HalfspaceToPolyhedron(Eltseq(Rows(lhs)[i]),Eltseq(rhs)[i]) : i in [1..#Rows(lhs)] ];
        poly:= &meet[ POL : POL in halfspaces ];
        //find the minimum of the objective function in the region, either using integral vertices or the linear program

        L := LPProcess(k, lp_size);
        SetObjectiveFunction(L, obj);
        AddConstraints(L, lhs, rhs : Rel := "ge");
        //AddConstraints(L, Matrix(k,1,3,[0,1,0]),  Matrix(k,1,1,[0]) : Rel := "eq"); //fix one variables.
        //UnsetBounds(L) doesn't work
        //These are lower bounds on the solution
        for i in [1..lp_size] do SetLowerBound(L, i, k!-10000); end for;
        soln,state:=Solution(L);
        //ProfilePrintByTotalTime(:Max:=40);
        assert state eq 0;
        min:=EvaluateAt(L,soln);

        //Now we intersect our polyhedron with the 'plane of minimal solutions'
        minimal_hyperplane := HyperplaneToPolyhedron(Eltseq(obj),min);
        poly := poly meet minimal_hyperplane;
        //poly := poly meet HyperplaneToPolyhedron([0,1,0],0);
        int_poly := IntegralPart(poly);
        assert IsEmpty(poly) eq false;
        assert IsPolytope(poly);
        min_points:=Setseq(Points(int_poly));
        points_loop:=min_points;
        //all of the points at which the objective function is minimal.
      end if;
      //end if;
    end if;

    points_loop := [ [ Integers()!Round(a) : a in Eltseq(PP) ] : PP in points_loop ];

    Append(~minimal_solutions,points_loop);
    //all triples of ideals to try rescaling by
    rescaling_ideals:=&cat[ [ [ (ideals[i])*(pp^Eltseq(pt)[i]) : i in [1..#Eltseq(pt)] ] : pt in points_loop ] : ideals in rescaling_ideals ];
  end for;
  //for each variable create all possible elements to scale by.

  all_rescalings:=[];
  for vv in rescaling_ideals do
    scaling_factors:= [ ];
    for w in vv do
      aprin, a := IsPrincipal(w);
      if aprin eq false then
        a:=IdealShortVectorsProcess(w, 0, 2: Minkowski:=Minkowski);
      else
        a:=[a];
      end if;
      Append(~scaling_factors,a);
    end for;

    all_lists:=[ [a] : a in scaling_factors[1] ];
    i:=1;
    while i lt lp_size do
      for list in all_lists do
        for elt in scaling_factors[i+1] do
          Append(~all_lists,list cat [elt]);
        end for;
        Exclude(~all_lists,list);
      end for;
      i:=i+1;
    end while;
    assert #all_lists eq &*[ #A : A in scaling_factors ];
    Append(~all_rescalings,all_lists);
  end for;
  all_rescalings:=&cat(all_rescalings);

  new_fuvs:=[];
  for ab in all_rescalings do
    if ClearDenominators eq true then
      guv:=Evaluate(f,[(BaseRing(Parent(f))!ab[i])*variables[i] : i in [1..n]]);
      jj := (ideal<ZK | Coefficients(guv)>)^-1;
      jprinbl, j := IsPrincipal(jj);
      j:=BaseRing(Parent(f))!j;
      if not jprinbl then
        js := IdealShortVectorsProcess(jj, 0, 2: Minkowski:=Minkowski);
      else
        js:=[j];
      end if;
      for j in js do
        guv *:= j;
        Append(~new_fuvs, <#Sprint(guv),guv,ab cat [j]>);
      end for;
    else
      guv:=Evaluate(f,[(BaseRing(Parent(f))!ab[i])*variables[i] : i in [1..n]])*BaseRing(Parent(f))!ab[n+1];
      Append(~new_fuvs, <#Sprint(guv),guv,ab>);
    end if;
    // JV: possibly redundantly, clear denominators one last time
  end for;

  Sort(~new_fuvs);
  new_fuv:=new_fuvs[1,2];
  new_scaling:= new_fuvs[1,3];

  return new_fuv, new_scaling;
end intrinsic;




intrinsic reducemodel_units(f::RngMPolElt : prec:=0) -> RngMPolElt, SeqEnum
  {}
  K := BaseRing(Parent(f));
  if prec eq 0 then
    //wild guess imprecise
    prec:=Floor(Sqrt(Degree(K)))*100;
  end if;

  //u := Parent(fuv).1;
  //v := Parent(fuv).2;
  ZK := Integers(K);
  r,s:=Signature(K);
  k:=RealField(prec);
  //Rx3<x1,x2,x3>:=PolynomialRing(Rationals(),3);

  variables:=[ Parent(f).i : i in [1..#Names(Parent(f))] ];
  var_size:=#variables;
  ZK := Integers(K);

  inf_places:=InfinitePlaces(K);
  assert #inf_places eq r+s;
  phi:=function(x);
    return [ Log(k!Abs(Evaluate(x,v : Precision:=prec))) : v in inf_places ];
  end function;

  mexps := [ Exponents(m) : m in Monomials(f) ];
  coefs:=Coefficients(f);
  //assert &+[ coefs[i]*(u^mexps[i,1])*v^mexps[i,2] : i in [1..#mexps] ] eq fuv;

  UK,mUK:=UnitGroup(K);
  k := RealField(prec);
  //UU:= [ K!(mUK(eps)) : eps in Generators(UK) | not(IsFinite(eps)) ];
  UU:= [ K!(mUK(eps)) : eps in Generators(UK) | not(IsFinite(eps)) and k!0 notin phi(K!(mUK(eps)))  ];

  if UU eq [] then
    return f, [K!1: i in [1..var_size+1] ];
  else

    constants := [];
    abs_coef := [];
  	for n in [1..#mexps] do

      alpha_norm := Log(k!Abs(Norm(coefs[n])))/(r+s);
      log_coef:= phi(coefs[n]);

  		for m in [1..r+s] do

        if m le r then
          const:= Log(k!Abs(Evaluate(coefs[n], inf_places[m]))) - Log(k!Abs(Norm(coefs[n])))/(r+s);
        else
          const:= Log(k!Abs(Evaluate(coefs[n], inf_places[m]))) - Log(k!Abs(Norm(coefs[n])))/(2*(r+s));
        end if;
        Append(~constants, [const]);

        etas:= [ phi(eps)[m] : eps in UU ];
        lhs:=&cat[ [ eta*a : a in mexps[n] ] cat [eta] : eta in etas ];
        Append(~abs_coef, lhs);

      end for;
    end for;

    constants:=Matrix(k,constants);
    abs_coef:=Matrix(k,abs_coef);

    L:=MinimiseL1ToLinearProgram(abs_coef, constants);
    //fix_var:=[0,1] cat [0: i in [1..NumberOfVariables(L)-2]]; fix a variable
    //AddConstraints(L, Matrix(k,1,NumberOfVariables(L),fix_var),  Matrix(k,1,1,[0]) : Rel := "eq");

    soln,state:=Solution(L);
    if state ne 0 then
      return reducemodel_units_naive(f);
    end if;
    assert state eq 0;
    soln:= [ Eltseq(soln)[i] : i in [1..(var_size+1)*#UU] ];
    soln_rounded:=[ Round(a) : a in soln ];

    eps_soln:= [K! &*[ UU[i]^soln_rounded[k*#UU+i] : i in [1..#UU] ] : k in [0..var_size] ];
    assert #eps_soln eq var_size + 1;
    guv:=Evaluate(f,[eps_soln[i]*variables[i] : i in [1..var_size]])*eps_soln[var_size+1];
  	return guv, eps_soln;
  end if;
end intrinsic;



intrinsic reducemodel_units_naive(f::RngMPolElt: effort:=0) -> RngMPolElt, SeqEnum
  {Try substituting increasing powers of fundamental units until it stops improving}
  print "attempting naive reduction of the units";
  f_init:=f;
  if effort eq 0 then
    exp:=5;
  else
    exp:=effort;
  end if;
  variables:=[ Parent(f).i : i in [1..#Names(Parent(f))] ];

  K:=BaseRing(Parent(f));
  UK, mUK := UnitGroup(Integers(K));

  UU := [ K!(mUK(eps)) : eps in Generators(UK) | not(IsFinite(eps)) ];
  us:= Setseq(Set(&cat[ [ u^e : e in [-exp..exp] ] : u in UU ]));

  yepdone := false;
  oldlen := #Sprint(f);
  //oldlen; Sprint(f);

  repeat
    printf "trying units of exponent %o\n", exp;
    S := [<#Sprint(f), [K!1,K!1,K!1]>];
    for u,v,w in us do
      tuple:=[u,v,w];
      Append(~S, <#Sprint(Evaluate(f,[tuple[i]*variables[i] : i in [1..#variables]])*tuple[3]), tuple>);
    end for;
    Sort(~S);
    if S[1][1] lt oldlen then
      //print oldlen, S[1], exp;
      oldlen := S[1][1];
      exp := exp+1;
      old_us:=us;
      us:=Setseq(Set(&cat[ [ u^e : e in [-exp..exp] ] : u in UU ]));
      us:= Setseq(Set(us) diff Set(old_us));
    else
      yepdone := true;
    end if;
  until yepdone;

  tuple:=S[1,2];
  f:=Evaluate(f,[tuple[i]*variables[i] : i in [1..#variables]])*tuple[3];


  yepdone := false;
  oldlen := #Sprint(f);

  no_tuples:=100;
  max_exp:=10;

  repeat
    printf "trying %o tuples of units with random exponents up to %o\n", no_tuples, max_exp;
    B:=[<#Sprint(f), [K!1,K!1,K!1]>];
    ran :=[ [ [ Random(Integers(),max_exp) : i in [1..#UU] ] : j in [1..3] ] : k in [1..no_tuples] ];
    unit_tuples:= [ [ &*[ UU[i]^elt[i] : i in [1..#UU] ] : elt in list ] : list in ran ];
    //uus:= [ [ &*[ UU[i]^elt[i] : i in [1..#UU]] : elt in list ]: list in ran ];

    for tup in unit_tuples do
      Append(~B,<#Sprint(Evaluate(f,[tup[i]*variables[i] : i in [1..#variables]])*tup[3]), tup>);
    end for;
    Sort(~B);
    if B[1][1] lt oldlen then
      oldlen:=B[1,1];
      tuple := [ tuple[i]*B[1,2][i] : i in [1..3] ];
      f:=Evaluate(f,[B[1,2][i]*variables[i] : i in [1..#variables]])*B[1,2][3];
    else
      yepdone:=true;
    end if;
  until yepdone;

  assert #Sprint(f) le #Sprint(f_init);
  return f, tuple;

end intrinsic;


intrinsic padic_LPsolutions(f::RngMPolElt, pp::RngOrdIdl) -> Any
  {return all of the points at which the objective function is minimal.}
  if BaseRing(Parent(f)) eq Rationals() then
    K:=RationalsAsNumberField();
  else
    K := BaseRing(Parent(f));
  end if;
  variables:=[ Parent(f).i : i in [1..#Names(Parent(f))] ];
  n:=#variables;
  ZK := Integers(K);
  k:=Integers();

  coefs_and_monomials:= [ [Coefficients(f)[i],Monomials(f)[i]] : i in [1..#Coefficients(f)] | Coefficients(f)[i] ne 0 ];
  mexps := [ Exponents(m[2]) : m in coefs_and_monomials ];
  m:=#mexps;
  coefs:=[ K!a[1] : a  in coefs_and_monomials ];
  //assert &+[ coefs[i]*(u^mexps[i,1])*v^mexps[i,2] : i in [1..#mexps] ] eq fuv;
  obj_coefs:= [ &+[ m[i] : m in mexps] : i in [1..n] ];

  //scaling the whole function is baked into the linear program
  obj := Matrix(k,1,n+1, obj_coefs cat [m]);
  lhs_coefs:= [ A cat [1] : A in mexps ];
  lhs := Matrix(k, lhs_coefs);     //constraints
  rel := Matrix(k,[[1] : ef in mexps]);
  rescaling_ideals:=[[ 1 : i in [1..n+1] ]];
  lp_size:=n+1;


  cvals := [ Valuation(c,pp) : c in coefs  ];
  rhs := Matrix(k, [[-cf] : cf in cvals]);          //valuations

  //Need to remove the spurious ones that are all zero already
  halfspaces:=[ HalfspaceToPolyhedron(Eltseq(Rows(lhs)[i]),Eltseq(rhs)[i]) : i in [1..#Rows(lhs)] ];
  poly:= &meet[ POL : POL in halfspaces ];
  //find the minimum of the objective function in the region, either using integral vertices or the linear program

  L := LPProcess(k, lp_size);
  SetObjectiveFunction(L, obj);
  AddConstraints(L, lhs, rhs : Rel := "ge");
  //AddConstraints(L, Matrix(k,1,3,[0,1,0]),  Matrix(k,1,1,[0]) : Rel := "eq"); //fix one variables.
  //UnsetBounds(L) doesn't work
  //These are lower bounds on the solution
  for i in [1..lp_size] do SetLowerBound(L, i, k!-10000); end for;
  soln,state:=Solution(L);
  //ProfilePrintByTotalTime(:Max:=40);
  assert state eq 0;
  min:=EvaluateAt(L,soln);

  //Now we intersect our polyhedron with the 'plane of minimal solutions'
  minimal_hyperplane := HyperplaneToPolyhedron(Eltseq(obj),min);
  poly := poly meet minimal_hyperplane;
  //poly := poly meet HyperplaneToPolyhedron([0,1,0],0);
  int_poly := IntegralPart(poly);
  assert IsEmpty(poly) eq false;
  assert IsPolytope(poly);
  min_points:=Setseq(Points(int_poly));

  solns:= [ Eltseq(A) : A in min_points ];
  return solns;
  //all of the points at which the objective function is minimal.
end intrinsic;

intrinsic reducemodel_unitsL2(f::RngMPolElt : prec:=0) -> RngMPolElt, SeqEnum
  {return the quadratic form and average vector using the coefficients}
  K := BaseRing(Parent(f));
  if prec eq 0 then
    //wild guess imprecise
    prec:=Floor(Sqrt(Degree(K)))*100;
  end if;

  //u := Parent(fuv).1;
  //v := Parent(fuv).2;
  ZK := Integers(K);
  r,s:=Signature(K);
  k:=RealField(prec);
  //Rx3<x1,x2,x3>:=PolynomialRing(Rationals(),3);

  variables:=[ Parent(f).i : i in [1..#Names(Parent(f))] ];
  var_size:=#variables;
  ZK := Integers(K);

  inf_places:=InfinitePlaces(K);
  assert #inf_places eq r+s;
  phi:=function(x);
    return [ Log(k!Abs(Evaluate(x,v : Precision:=prec))) : v in inf_places ];
    //assert first r places are real.
  end function;

  mexps := [ Exponents(m) : m in Monomials(f) ];
  coefs:=Coefficients(f);
  //assert &+[ coefs[i]*(u^mexps[i,1])*v^mexps[i,2] : i in [1..#mexps] ] eq fuv;

  UK,mUK:=UnitGroup(K);
  k := RealField(prec);
  //UU:= [ K!(mUK(eps)) : eps in Generators(UK) | not(IsFinite(eps)) ];
  UU:= [ K!(mUK(eps)) : eps in Generators(UK) | not(IsFinite(eps)) and k!0 notin phi(K!(mUK(eps)))  ];

  if UU eq [] then
    return f, [K!1: i in [1..var_size+1] ];
  else
    constants := [];
    abs_coef := [];

    for n in [1..#mexps] do

      alpha_norm := Log(k!Abs(Norm(coefs[n])))/(r+s);
      log_coef:= phi(coefs[n]);
      tuple:=[];

      for m in [1..r+s] do

        if m le r then
          const:= Log(Abs(Evaluate(coefs[n], inf_places[m] : Precision:=prec))) - Log(k!Abs(Norm(coefs[n])))/(r+s);
        else
          const:= Log(Abs(Evaluate(coefs[n], inf_places[m] : Precision:=prec))) - Log(k!Abs(Norm(coefs[n])))/(2*(r+s));
        end if;
        Append(~tuple, const);

        etas:= [ phi(eps)[m] : eps in UU ];
        lhs:=&cat[ [ eta*a : a in mexps[n] ] cat [eta] : eta in etas ];
        Append(~abs_coef, lhs);

      end for;
      Append(~constants,tuple);
    end for;

    average:= [ &+[ (A[i])/#mexps : A in constants ] : i in [1..r+s] ];

    L2coef:= [ &+[I[i] : I in mexps] : i in [1..var_size] ] cat [#mexps];
    L2pols<[X]> := PolynomialRing(k,3*(r+s));
    quadform_pol:= &+[ (L2coef[1]*X[i] + L2coef[1]*X[r+s+i] + L2coef[1]*X[2*(r+s)+i])^2 : i in [1..r+s] ];
    L2mat:=SymmetricMatrix(quadform_pol);
    return L2mat, L2coef, average;
  end if;
end intrinsic;



intrinsic ReducedEquations(pols::SeqEnum) -> SeqEnum
  {For multiple multivariate polynomials defined over the rationals,
  do simultanous p-adic reduction}

  assert BaseRing(Parent(pols[1])) eq Rationals();
  /*if BaseRing(Parent(pols[1])) eq Rationals() then
    K:=RationalsAsNumberField();
    pols:=[ ChangeRing(f,K) : f in pols];
  else*/
    K := BaseRing(Parent(pols[1]));
  //end if;
  variables:=[ Parent(pols[1]).i : i in [1..#Names(Parent(pols[1]))] ];
  var_size:=#variables;
  ZK := Integers(K);
  k:=RealField(20);
  lp_size:=var_size+#pols;

  lp_size:=#variables+#pols;
  Ob<[Y]>:=PolynomialRing(Integers(),lp_size);
  obj_fun:=Ob!0;
  zeroes :=[  0 : t in [1..#pols-1] ];
  lhs_coefs:=[];

  for j in [1..#pols] do
    co,mo:=CoefficientsAndMonomials(pols[j]);
    assert 0 notin co;
    mexps := [ Exponents(m) : m in mo ];
    obj_j:= [ (&+[ m[i] : m in mexps])*Y[i] : i in [1..#variables] ];
    obj_j := obj_j cat [#mo*Y[#variables+j]];
    obj_j := &+(obj_j);
    obj_fun:=obj_fun+obj_j;


    scaling1:=Insert(zeroes, j,1);
    for exps in mexps do
      Append(~lhs_coefs,exps cat scaling1);
    end for;
  end for;

  SS:=[];
  for pol in pols do
    for pp in CoefficientSupport(pol) do
      Append(~SS,pp);
    end for;
  end for;
  SS:=Setseq(Set(SS));
  scaling_factors:= [K!1 : i in [1..lp_size]];

  for pp in SS do

    _,p:=IsPrincipal(pp);
    rhs_coefs:=[];
    for j in [1..#pols] do
      co,mo:=CoefficientsAndMonomials(pols[j]);
      for c in co do
        Append(~rhs_coefs, [-Valuation(c,pp)]);
      end for;
    end for;

    obj:=Matrix(k,1,lp_size,Coefficients(obj_fun));
    lhs := Matrix(k, lhs_coefs);     //constraints
    //rel := Matrix(k,[[1] : i in [1..#rhs] ]);
    rhs := Matrix(k,rhs_coefs);
    L := LPProcess(k, lp_size);
    SetObjectiveFunction(L, obj);
    SetIntegerSolutionVariables(L,[ i : i in [1..lp_size]], true);
    AddConstraints(L, lhs, rhs : Rel := "ge");
    for i in [1..lp_size] do  SetLowerBound(L, i, k!-10); end for;

    soln,state:=Solution(L);
    assert state eq 0;
    soln:=Eltseq(soln);
    soln:= [ Integers()!Round(s) : s in soln ];

    scaling_factors:= [ scaling_factors[i]*(p^soln[i]) : i in [1..#soln] ];
  end for;

  guvs:=[ Evaluate(pols[j],[(BaseRing(Parent(pols[j]))!scaling_factors[i])*variables[i] : i in [1..var_size]])*BaseRing(Parent(pols[j]))!scaling_factors[var_size+j] : j in [1..#pols] ];

  return guvs, [K!el : el in scaling_factors];

end intrinsic;



intrinsic SmallHyperplaneRepresentative(alpha::FldNumElt: prec:=0) -> ModMatRngElt
  {Input: alpha an element of a number field and psi the minkowski Embedding
  Output: An element in the hyperplane in minkowski space which is small in all coordinates}
  K:=Parent(alpha);
  inf_places:=InfinitePlaces(K);
  if prec eq 0 then
    prec:=10;
  end if;
  k:=RealField(prec);
  VR:=VectorSpace(k,#inf_places);
  return VR![ Log(Abs(Norm(alpha)))/#inf_places : i in [1..#inf_places] ];

end intrinsic;


intrinsic ClosestElementInUnitHyperplane(alpha::FldNumElt : prec:=0) -> ModMatRngElt
  {Find the element in the hyperplane spanned by the units which is closest to
   SmallHyperplaneRepresentative(alpha) - psi(alpha) }
   K:=Parent(alpha);
   inf_places:=InfinitePlaces(K);
   if prec eq 0 then
     prec:=10;
   end if;
   k:=RealField(prec);
   VR:=VectorSpace(k,#inf_places);
   psi:=function(x);
     return [ Log(k!Abs(Evaluate(x,v : Precision:=prec))) : v in inf_places ];
     //assert first r places are real.
   end function;
   return SmallHyperplaneRepresentative(alpha) - VR!psi(alpha);
end intrinsic;


intrinsic IdealShortVectorsProcess(I::RngOrdFracIdl, l::RngIntElt, u::RngIntElt : Minkowski:=true, timeout:=2) -> SeqEnum
  {Given an ideal I, thought of as a lattice, and integers l and u, return vectors in the lattice bounded by l and u scaled by a medium sized vector in parallelepiped.}
  //l,u are size in which to search over lattice, scaled by a medium sized vector in parallelepiped.
  if Degree(NumberField(Order(I))) gt 1 then
    if Minkowski eq true then
      Ibasis:=Basis(I);
      IxDen := Order(I)!!(I*Denominator(I));
      IxDen_gens,mxDen:=MinkowskiLattice(IxDen);
      Igens:=IxDen_gens/Denominator(I);
      BI:=Basis(Igens);
      dimL:=#BI;
      prec:=100+6*dimL;
      Rprec:=RealField(prec);
      VS:=VectorSpace(Rprec,dimL);
      BI_gens:=[ [ Rprec!v : v in Eltseq(gen) ] : gen in BI ];

      while Dimension(sub< VS | BI_gens >) lt dimL do
        prec:=prec+20;
        Rprec:=RealField(prec);
        VS:=VectorSpace(Rprec,dimL);
        BI_gens:=[ [ Rprec!v : v in Eltseq(gen) ] : gen in BI ];
      end while;

      LWB:=LatticeWithBasis(RMatrixSpace(Rprec,dimL,dimL)!&cat(BI_gens)); //lower the precision for efficiency
      OLWB:=LWB; // save original lattice in case wanted
      LWB:=CoordinateLattice(LWB);
      min_vec:=Min(LWB);
      avg_vec:=Determinant(LWB)^(1/(dimL));
      //EC:=EnumerationCost(LWB20, 10*Sqrt(avg_vec));
      if l eq 0 then l +:= Rprec!10^(-prec); end if;
      SVP:=ShortVectorsProcess(LWB, avg_vec*l, avg_vec*u);

      SV:=[];
      while not(IsEmpty(SVP)) do
        Append(~SV, NextVector(SVP));
      end while;

      t:=Realtime(); //set a timeout
      SVcoord :=[];
      for w in SV do
        Append(~SVcoord, [ Round(c) : c in Eltseq(w) ]);
        if Realtime(t) gt timeout then
          break;
        end if;
      end for;

      SIelts := [ &+[w[i]*Ibasis[i] : i in [1..#Ibasis]] : w in SVcoord ];
      //assert something to make sure there was no precision error
      return SIelts;

    else
      Igens := LLLBasis(I);
      // assert [ A/Denominator(I) : A in LLLBasis(I*Denominator(I)) ] eq Igens;
      Zn :=StandardLattice(#Igens);
      if l eq 0 then l := 1; end if;  // integral lattice, so
      SVP:=ShortVectorsProcess(Zn, Ceiling(l),Ceiling(u));
      SV:=[];
      while not(IsEmpty(SVP)) do
        Append(~SV, NextVector(SVP));
      end while;
      MM := [ Eltseq(w) : w in SV ];
      SIelts:=[ (&+[ M[i]*Igens[i] : i in [1..#Igens] ]) : M in MM ] cat [1];
      return SIelts;
    end if;

  else
    tr, I_pr:=IsPrincipal(I);
    return [I_pr];
  end if;
end intrinsic;
