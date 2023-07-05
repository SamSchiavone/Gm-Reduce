


intrinsic UnitsQuadraticObjectiveFunction(f::RngMPolElt : prec:=0) -> RngMPolElt, SeqEnum
  {Given a multivariate polynomial f over number field K, we wish to scale by units to the reduce the 
  size of the equation. To find which units to scale by, this intrinsic creates the obective function,
  which is a quadratic function of the form 1/2x^TQx + C^Tx + b. The intrinsic returns the quadratic function. Note Q 
  not necessarily positive definite, but it will be positive semi definite because it is symmetric.}
  K := BaseRing(Parent(f));
  if prec eq 0 then
    //wild guess imprecise
    prec:=Floor(Sqrt(Degree(K)))*20;
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
    //return IdentityMatrix(k,var_size+1), Matrix(k,var_size+1,1,[k!-1: i in [1..var_size+1] ]), [Rationals()!1];
    return PolynomialRing(k)!0, [];  
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

    return pol - ConstantTerm(pol), UU;
  end if;
end intrinsic;


intrinsic ObjectiveFunctionToMatrices(obj::RngMPolElt) -> AlgMatElt,AlgMatElt
    {}

  k:=BaseRing(Parent(obj));
  kPol:=Parent(obj);
  names:=Names(kPol);



  pol:=obj;
  coefs,mons:=CoefficientsAndMonomials(pol);
  assert pol eq &+[ coefs[i]*mons[i] : i in [1..#coefs] ];

  quadratic_pol := &+[ Parent(mons[1]) | coefs[i]*mons[i] : i in [1..#coefs] | Degree(mons[i]) eq 2 ];
  linear_pol := &+[ Parent(mons[1]) | coefs[i]*mons[i] : i in [1..#coefs] | Degree(mons[i]) eq 1 ];
  

  Q:=2*SymmetricMatrix(quadratic_pol);
  //assert Universe(NumericalEigenvalues(Q)) eq k;

  linear_coefs:= [ Coefficient(linear_pol, kPol.i,1) : i in [1..#names] ];
  C:=Matrix(k,#names,1,linear_coefs);

  //assert IsPositiveDefinite(Q);

  variable_matrix:=Matrix(kPol,#names,1,[ kPol.i : i in [1..#names] ]);
  
  newobj:=1/2*Transpose(variable_matrix)*ChangeRing(Q,kPol)*variable_matrix + ChangeRing(Transpose(C),kPol)*variable_matrix; 
  newobj:=newobj[1,1];
  assert newobj eq pol - ConstantTerm(pol);

  return Q,C;


end intrinsic;



intrinsic UnitsQuadraticObjectiveMatrices(f::RngMPolElt : prec:=0) -> RngMPolElt, SeqEnum
  {Given a multivariate polynomial f over number field K, we wish to scale by units to the reduce the 
  size of the equation. To find which units to scale by, this intrinsic creates the obective function,
  which is a quadratic function of the form 1/2x^TQx + C^Tx + b. The intrinsic returns Q and C. Note Q 
  not necessarily positive definite, but it will be positive semi definite because it is symmetric.}
  obj,UU:=UnitsQuadraticObjectiveFunction(f : prec:=prec);
  if UU eq [] then 
    return "No fundamental units";
  else 
    Q,C:=ObjectiveFunctionToMatrices(obj);
    return Q,C;
  end if;
end intrinsic;


intrinsic SolveQuadraticProgramReals(Q::AlgMatElt,C::ModMatFldElt : prec:=0) -> ModMatFldElt
  {Given a symmetix matrix Q and a vector C, find a minimum of 1/2x^TQx + C^Tx, 
   which is given by Qx=-C}
 
  if IsExact(BaseRing(Parent(Q))) then 
    if prec eq 0 then 
      prec:=20;
    end if;
    k:=RealField(prec);
  else 
    k:=BaseRing(Parent(Q));
  end if;

  V,N:=NumericalSolution(ChangeRing(Q,k),ChangeRing(Transpose(-C),k));
  return V,N;

end intrinsic;

intrinsic SolveQuadraticProgramReals(obj::RngMPolElt : prec:=0) -> ModMatFldElt
  {Given a symmetix matrix Q and a vector C, find a minimum of 1/2x^TQx + C^Tx, 
   which is given by Qx=-C}
  Q,C:=ObjectiveFunctionToMatrices(obj);
  return SolveQuadraticProgramReals(Q,C : prec:=prec);
end intrinsic; 

/*intrinsic SolveQuadraticProgramReals(Q::AlgMatElt,C::AlgMatElt : prec:=0) -> ModMatFldElt
  {Given a symmetix matrix Q and a vector C, find a minimum of 1/2x^TQx + C^Tx, 
   which is given by Qx=-C}
  
  return SolveQuadraticProgramReals(Q,C : prec:=prec);
end intrinsic; */


intrinsic Norm(A::ModMatRngElt) -> FldReElt 
  {}
  return Sqrt(RealField(5)!(&+[ a^2 : a in Eltseq(A) ]));
end intrinsic;

intrinsic Norm(A::AlgMatElt) -> FldReElt 
  {}
  return Sqrt(RealField(5)!(&+[ a^2 : a in Eltseq(A) ]));
end intrinsic;


intrinsic mu(tt::ModMatRngElt, z::ModMatRngElt) -> FldReElt
  {}
  
  tt:=ChangeRing(tt,RealField(5));
  z:=ChangeRing(z,RealField(5));
  return Abs(Round(Eltseq(Transpose(tt)*z)[1]) - Eltseq(Transpose(tt)*z)[1]);
end intrinsic;

intrinsic IsPivotColumn(j::RngIntElt, A::ModMatFldElt) -> BoolElt 
  {Given the j-th column C_j of the matrix A in  reduced row echelon form,
  return whether C_j is a pivot column.}

  rows:=Rows(Transpose(ChangeRing(A,RealField(3))));
  Cj:=rows[j];
  standardbasis:=Basis(VectorSpace(RealField(3),#Rows(A)));
  if Cj in standardbasis then 
    if j eq 1 or forall(e){ i : i in [1..j-1] | rows[i] ne Cj } then 
      return true;
    else 
      return false;
    end if;
  else 
    return false;
  end if;
end intrinsic;


intrinsic SubspaceToLinearDefiningEquations(N::ModMatFldElt,V::ModMatFldElt) -> SeqEnum,SeqEnum
  {xN+V is a linear subset of R^n: return it as a list of defining equations and linear terms}
  k:=BaseRing(N);

  echN:=EchelonForm(N);
  echNcolumns:=Rows(Transpose(echN));
  //echNspan:=sub< Parent(echNcolumns[1]) | echNcolumns >;
  //standardbasis:=Basis(VectorSpace(RealField(2),Dimension(echNspan)));

  basiscolumns := [ echNcolumns[j] : j in [1..#echNcolumns] | IsPivotColumn(j,echN) ];
  nonbasiscolumns:= [ echNcolumns[j] : j in [1..#echNcolumns] | not(IsPivotColumn(j,echN)) ];
  minus1:=-IdentityMatrix(BaseRing(echNcolumns[1]),#nonbasiscolumns);
  minus1rows:=Rows(minus1);
  definingequations:= [ Eltseq(nonbasiscolumns[i]) cat Eltseq(minus1rows[i]) : i in [1..#nonbasiscolumns]  ];
  constants := [ &+[ b[j]*Eltseq(V)[j] : j in [1..#Eltseq(V)] ] : b in definingequations ];
  return definingequations,constants;
end intrinsic;



intrinsic BoundingBoxOfLinearSubset(N::ModMatFldElt,V::ModMatFldElt,eps::FldReElt : bound:=100) -> LP
  {Given a set of defining equations of a linear subset of R^n, 
  create a small box of width 2*eps around the subset given as a linear program}
  
  definingequations,constants:=SubspaceToLinearDefiningEquations(N,V);

  k:=BaseRing(N);
  var_size:=#definingequations[1];
  L := LPProcess(k, var_size);
  obj:=Matrix(k,1,var_size,[0 : i in [1..var_size]]);
  SetObjectiveFunction(L, obj);

  for i in [1..#definingequations] do 
    AddConstraints(L,Matrix(k,[definingequations[i]]), Matrix(k,[[constants[i]+eps]]) : Rel:="le");
    AddConstraints(L,Matrix(k,[definingequations[i]]), Matrix(k,[[constants[i]-eps]]) : Rel:="ge");
  end for;

  idd:=IdentityMatrix(k,var_size);
  idd_rows:=[ Eltseq(row) : row in Rows(idd) ];
  for j in [1..var_size] do 
    AddConstraints(L,Matrix(k,[idd_rows[j]]), Matrix(k,[[Eltseq(V)[j]+bound]]) : Rel:="le");
    AddConstraints(L,Matrix(k,[idd_rows[j]]), Matrix(k,[[Eltseq(V)[j]-bound]]) : Rel:="ge");
  end for;

  for j in [1..var_size] do
    SetLowerBound(L, j, k!(Eltseq(V)[j]-bound));
  end for;

  SetIntegerSolutionVariables(L,[j : j in [1..var_size]], true);

  return L;
end intrinsic;



intrinsic SolveQuadraticProgramIntegers(Q::AlgMatElt,C::ModMatFldElt : prec:=0) -> SeqEnum 
  {}

  if IsExact(BaseRing(Parent(Q))) then 
    if prec eq 0 then 
      prec:=20;
    end if;
    k:=RealField(prec);
  else 
    k:=BaseRing(Parent(Q));
  end if;

  Q:=ChangeRing(Q,k);
  C:=ChangeRing(C,k);
 
  V,N:=SolveQuadraticProgramReals(Q,C : prec:=prec);

  if NumericalRank(Q) eq NumberOfRows(Q) then 
    B:=Transpose(Cholesky(Q));
  /*else 
    diag,F:=OrthogonalizeGram(Q);
    assert forall(e){ a ge 0 : a in Diagonal(diag) };
    sqrt:= DiagonalMatrix(k,[ Sqrt(a) : a in Diagonal(diag) ]);
    B:=Transpose(Inverse(F)*sqrt);
  end if;*/

    assert ChangeRing(Q,RealField(3)) eq  ChangeRing(Transpose(B)*B,RealField(3));
    Binv:=Inverse(B);
    L:=LatticeWithBasis(Binv);
    //basis of L is rows of Binv.
    Lop,TT:=BasisReduction(L);
    Binvop:=BasisMatrix(Lop);
    //Basis(Lop) eq T*Basis(L), or if Binvop is matrix with rows equal to basis of Lop, then Binvop:=TT*Binv
    assert ChangeRing(Binvop,RealField(3)) eq ChangeRing(TT*Binv,RealField(3));
    T:=Transpose(TT);

    zz:=Transpose(Matrix([V]));
    op_init:=ChangeRing(Transpose(T),BaseRing(zz))*zz;
    op_init:= Transpose(Matrix([[ Round(a) : a in Eltseq(op_init) ]]));
    op:=Transpose(T)^-1*op_init;

    return Eltseq(op);

  else 

    state:=2;
    eps:=0.1;
    newbound:=10;
    while state ne 0 and eps lt 1 do
      L:=BoundingBoxOfLinearSubset(N,V,eps : bound:=newbound);
      soln,state:=Solution(L);
      eps:=eps+0.1;
      newbound:=newbound+10;
    end while;

    soln_rounded:=[ Round(a) : a in Eltseq(soln) ];
    return soln_rounded;

  end if;

  //else 

    /*Vrat:=[ BestApproximation(v,1000) : v in Eltseq(V) ];
    N1:=[ n/Eltseq(N)[1] : n in Eltseq(N) ];
    Nrat:=[ BestApproximation(n,1000) : n in Eltseq(N1) ];*/

    /*Nlattice:=Lattice(N);
    Nbasis:=Rows(BasisMatrix(Nlattice));
    vinit:=Rows(V)[1];

    eps:=0.1;
    bd:=10;

    all_vectors:=[vinit];
    for V in Nbasis do
      //for all s in [ m*eps : m in [-bd/eps..bd/eps] ];
      head:=[ w+s*V : w in all_vectors, s in [-bd/eps..bd/eps] ];
      all_vectors:=all_vectors cat head;
    end for;
    all_vectors_rounded:=[ [ Round(a) : a in Eltseq(VV) ] : VV in all_vectors ];

    obj:=QuadraticForm(Q);
    obj:= obj + &+[ Parent(obj).i*Eltseq(C)[i] : i in [1..#Eltseq(C)] ];
    
    eval_obj:= [ <Evaluate(obj,P), P> : P in all_vectors_rounded ];
    integersoln_sorted:=Sort(eval_obj);

    return integersoln_sorted[1,2];

  end if;*/



  /*ColumnsT:=[ ColumnSubmatrix(T,i,1) : i in [1..#Rows(Transpose(T)) ] ];
  Qs:=[ t*Transpose(t) : t in ColumnsT ];
  LambdaQs:=[ 2*Norm(ChangeRing(Transpose(t),BaseRing(Parent(Binv)))*Binv) : t in ColumnsT ];
  Q0:=&+[ LambdaQs[i]^2*Qs[i] : i in [1..#Qs] ];
  muQ0:= Sqrt( &+[ LambdaQs[i]^2*(mu(ColumnsT[i],zz)) : i in [1..#ColumnsT] ]);*/
  

end intrinsic;





/*intrinsic SolveQuadraticProgramUnconstrained(obj::RngMPolElt) -> ModMatFldElt
  {Given a symmetix matrix Q and a vector B, find a numerical solution to Hx = B where
   H and B are over the reals. The second return value is the nullspace}

  Q,C:=ObjectiveFunctionToMatrices(obj);
  return SolveQuadraticProgramUnconstrained(Q,C);
end intrinsic;*/




intrinsic reducemodel_units_L2(f::RngMPolElt : prec:=0) -> RngMPolElt, SeqEnum
  {Given a multivariate polynomial f over a number field, find optimal units to scale by in order to 
reduce the size of the coefficients of f.}

 
  K := BaseRing(Parent(f));
  var_size:=#Names(Parent(f));

  if K eq Rationals() or K eq RationalsAsNumberField() then 
    return f, [K!1 : i in [1..var_size+1]];
  end if;

  K:=BaseRing(Parent(f));
  obj,UU:=UnitsQuadraticObjectiveFunction(f : prec:=prec);

  if UU eq [] then 
    return f, [K!1 : i in [1..var_size+1]];
  else 

    if prec eq 0 then
      //wild guess imprecise
      prec:=Floor(Sqrt(Degree(K)))*20;
    end if;

    Q,C:=ObjectiveFunctionToMatrices(obj : prec:=prec);
    //soln,N:=SolveQuadraticProgramUnconstrained(Q,-C);
    soln:=SolveQuadraticProgramIntegers(Q,C : prec:=prec);

    eps_soln:= [ K!&*[ UU[i]^soln[k*#UU+i] : i in [1..#UU] ] : k in [0..var_size] ];
    assert #eps_soln eq var_size + 1;
    guv:=Evaluate(f,[eps_soln[i]*Parent(f).i : i in [1..var_size]])*eps_soln[var_size+1];
    return guv, eps_soln;
  end if;

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





