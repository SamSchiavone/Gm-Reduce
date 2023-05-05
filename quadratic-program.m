


intrinsic UnitsQuadraticObjectiveFunction(f::RngMPolElt : prec:=0) -> RngMPolElt, SeqEnum
  {Given a multivariate polynomial f over number field K, we wish to scale by units to the reduce the 
  size of the equation. To find which units to scale by this intrinsic creates the obective function,
  which is a quadratic function of the form 1/2x^TQx + C^Tx + b. The function returns Q and C. Note Q 
  not necessarily positive definite, but it will be positive semi definite because it is symmetric.}
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
  assert var_size eq 2;
  ZK := Integers(K);

  inf_places:=InfinitePlaces(K);
  assert #inf_places eq r+s;
  phi:=function(x);
    return [ Log(k!Abs(Evaluate(x,v : Precision:=prec))) : v in inf_places ];
  end function;

  mexps := [ Exponents(m) : m in Monomials(f) ];
  coefs:=Coefficients(f);
  //assert &+[ coefs[i]*(u^mexps[i,1])*v^mexps[i,2] : i in [1..#mexps] ] eq fuv;

  vprintf GmReduce: "About to compute the unit group...\n";
  UK,mUK:=IndependentUnits(K);
    vprintf GmReduce: "Done with computing the unit group...\n";
  k := RealField(prec);
  //UU:= [ K!(mUK(eps)) : eps in Generators(UK) | not(IsFinite(eps)) ];
  UU:= [ K!(mUK(eps)) : eps in Generators(UK) | not(IsFinite(eps)) and k!0 notin phi(K!(mUK(eps)))  ];

  if UU eq [] then
    return IdentityMatrix(k,var_size+1), Matrix(k,var_size+1,1,[K!-11: i in [1..var_size+1] ]), [Rationals()!1];
  else

    kPol:=PolynomialRing(k,3*#UU);
    names:= [ Sprintf("a%o",i) : i in [1..#UU] ]
        cat [ Sprintf("b%o",i) : i in [1..#UU] ] 
        cat [ Sprintf("c%o",i) : i in [1..#UU] ];
    AssignNames(~kPol,names);
 
    Vees:=[];
    constants := [];
    abs_coef := [];
    pol:=kPol!0;
    for n in [1..#mexps] do
      i,j:=Explode(mexps[n]);
      Vn:=Matrix(kPol,r+s,1,[0 : i in [1..r+s]]);
      for v in [1..#UU] do
        av:=kPol.v;
        bv:=kPol.(#UU+v);
        cv:=kPol.(2*#UU+v);
        gn:=(i*av + j*bv + cv)*Matrix(kPol,r+s,1,phi(UU[v]));
        Vn:=Vn+gn;
      end for;

      //alpha_norm := Log(k!Abs(Norm(coefs[n])))/(r+s);
      //log_coef:= phi(coefs[n]);

      constants := [];
      for m in [1..r+s] do
        if m le r then
          const:= - ( Log(k!Abs(Evaluate(coefs[n], inf_places[m]))) - Log(k!Abs(Norm(coefs[n])))/(r+s) );
        else
          const:= - ( Log(k!Abs(Evaluate(coefs[n], inf_places[m]))) - Log(k!Abs(Norm(coefs[n])))/(2*(r+s)) );
        end if;
        Append(~constants, [const]);
      end for;
      beta_n:=Matrix(kPol,r+s,1,&cat(constants));

      Vn:=Vn - beta_n;
      Append(~Vees,Vn);

      pol:=pol + (&+[ Ve^2 : Ve in Eltseq(Vn) ]);
      
    end for;

    coefs,mons:=CoefficientsAndMonomials(pol);
    assert pol eq &+[ coefs[i]*mons[i] : i in [1..#coefs] ];
    quadratic_pol := &+[ Parent(mons[1]) | coefs[i]*mons[i] : i in [1..#coefs] | Degree(mons[i]) eq 2 ];
    linear_pol := &+[ Parent(mons[1]) | coefs[i]*mons[i] : i in [1..#coefs] | Degree(mons[i]) eq 1 ];
    
    Q:=2*SymmetricMatrix(quadratic_pol);
    assert Universe(NumericalEigenvalues(Q)) eq k;

    linear_coefs:= [ Coefficient(linear_pol, kPol.i,1) : i in [1..#names] ];
    C:=Matrix(k,#names,1,linear_coefs);
    //assert IsPositiveDefinite(Q);

    variable_matrix:=Matrix(kPol,#names,1,[ kPol.i : i in [1..#names] ]);
    
    obj:=1/2*Transpose(variable_matrix)*ChangeRing(Q,kPol)*variable_matrix + ChangeRing(Transpose(C),kPol)*variable_matrix; 
    obj:=obj[1,1];
    assert obj eq pol - ConstantTerm(pol);

    return Q,C,UU;
  end if;

end intrinsic;


intrinsic SolveQuadraticProgramUnconstrained(H::AlgMatElt,B::ModMatFldElt) -> ModMatFldElt
  {Given a symmetix matrix Q and a vector B, find a numerical solution to Hx = B where
   H and B are over the reals. The second return value is the nullspace}

  V,N:=NumericalSolution(H,Transpose(B));
  return V,N;
end intrinsic;




intrinsic reducemodel_units_L2(f::RngMPolElt : prec:=0) -> RngMPolElt, SeqEnum
  {Given a multivariate polynomial f over a number field, find optimal units to scale by in order to 
reduce the size of the coefficients of f.}

 
  K := BaseRing(Parent(f));
  var_size:=#Names(Parent(f));

  if K eq Rationals() or K eq RationalsAsNumberField() then 
    return f, [K!1 : i in [1..var_size+1]];
  end if;

  if prec eq 0 then
    //wild guess imprecise
    prec:=Floor(Sqrt(Degree(K)))*100;
  end if;

  K:=BaseRing(Parent(f));
  Q,C,UU:=UnitsQuadraticObjectiveFunction(f : prec:=prec);
  soln,N:=SolveQuadraticProgramUnconstrained(Q,-C);

  soln_rounded:=[ Round(a) : a in Eltseq(soln) ];

  eps_soln:= [ K!&*[ UU[i]^soln_rounded[k*#UU+i] : i in [1..#UU] ] : k in [0..var_size] ];
  assert #eps_soln eq var_size + 1;
  guv:=Evaluate(f,[eps_soln[i]*Parent(f).i : i in [1..var_size]])*eps_soln[var_size+1];
  return guv, eps_soln;

end intrinsic;
 

intrinsic reducemodel_units(f::RngMPolElt : prec:=0, norm:= "L2") -> RngMPolElt, SeqEnum
  {reduce mode units, use L2 by default}
  
  if norm eq "L1" then 
    return reducemodel_units_L1(f : prec:=prec);
  elif norm eq "L2" then
    return reducemodel_units_L2(f : prec:=prec);
  else 
    return "norm must be L1 or L2";
  end if;

end intrinsic;





