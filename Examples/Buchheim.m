Q:=Matrix([[1,-2],[-2,8]]);

S:=Matrix([[-1,0],[0,10]]);
U:=Matrix([[0,1],[1,0]]);
V:=Matrix([[3/5,4/5],[-4/5,3/5]]);

Q:=V*S*Transpose(V);
R<x,y>:=PolynomialRing(Rationals(),2);
q:=(x-1/2)^2 + 50*(y-1/2)^2 + 10*(x-1/2)*(y-1/2);
qquad:=x^2+10*x*y+50*y^2;
Q:=2*SymmetricMatrix(qquad);


 B:=Transpose(Cholesky(Q));
  assert ChangeRing(Q,RealField(5)) eq  ChangeRing(Transpose(B)*B,RealField(5));
  Binv:=Inverse(B);
  L:=LatticeWithBasis(Binv);
  //basis of L is rows of Binv.
  Lop,TT:=BasisReduction(L);
  Binvop:=BasisMatrix(Lop);
  //Basis(Lop) eq T*Basis(L), or if Binvop is matrix with rows equal to basis of Lop, then Binvop:=TT*Binv
  assert ChangeRing(Binvop,RealField(5)) eq ChangeRing(TT*Binv,RealField(5));
  T:=Transpose(TT);

  zz:=Matrix([[1/2],[1/2]]);

  op_init:=ChangeRing(Transpose(T),BaseRing(zz))*zz;
  op_init:= Matrix([[ Round(a) : a in Eltseq(op_init) ]]);
  Transpose(T)^-1*Transpose(op_init);
  //[-2,1]


  Sort([ <RealField(3)!Evaluate(q,[i,j]),[i,j]> : i in [-3..3], j in [-3..3] ]);
  //Min is at [-2,1]!!

  ColumnsT:=[ ColumnSubmatrix(T,i,1) : i in [1..#Rows(Transpose(T)) ] ];
  Qs:=[ t*Transpose(t) : t in ColumnsT ];

  LambdaQs:=[ 2*Norm(ChangeRing(Transpose(t),BaseRing(Parent(Binv)))*Binv) : t in ColumnsT ];

  Q0:=&+[ LambdaQs[i]^2*Qs[i] : i in [1..#Qs] ];

  muQ0:= Sqrt( &+[ LambdaQs[i]^2*(mu(ColumnsT[i],zz)) : i in [1..#ColumnsT] ]);



// semidefinite example
  f:=4*x^2 - 4*x*y - 2*x + y^2 + y +1/4;
  Q,U:=ObjectiveFunctionToMatrices(f);
  diag,F:=OrthogonalizeGram(Q);
  assert forall(e){ a ge 0 : a in Diagonal(diag) }
  assert ChangeRing(Q,RealField(5)) eq ChangeRing(Transpose(F)*diag*F,RealField(5));
  sqrt:= DiagonalMatrix(RealField(5),[ Sqrt(a) : a in Diagonal(diag) ]);
  R:=Inverse(F)*sqrt;
  assert ChangeRing(Q,RealField(2)) eq ChangeRing(R*Transpose(R),RealField(2));

//Let's try and use L1 program to solve when it's semidefinite:

k:=RealField(5);
L := LPProcess(k, 2);
obj:=Matrix(k,1,2,[0,0]);
SetObjectiveFunction(L, obj);


//y=x-1.2
const:=-1.2;
eps:=0.2;
bound:=100;
AddConstraints(L,Matrix(k,[[-1,1]]), Matrix(k,[[const+eps]]) : Rel:="le");
AddConstraints(L,Matrix(k,[[-1,1]]), Matrix(k,[[const-eps]]) : Rel:="ge");
AddConstraints(L,Matrix(k,[[1,0]]), Matrix(k,[[bound]]) : Rel:="le");
AddConstraints(L,Matrix(k,[[-1,0]]), Matrix(k,[[bound]]) : Rel:="le");
AddConstraints(L,Matrix(k,[[0,1]]), Matrix(k,[[bound]]) : Rel:="le");
AddConstraints(L,Matrix(k,[[0,-1]]), Matrix(k,[[bound]]) : Rel:="le");


SetIntegerSolutionVariables(L,[1,2], true);

Solution(L);

SetLowerBound(L, 1, k!-100);
SetLowerBound(L, 2, k!-100);

Solution(L);


R<t1,x1,x2>:=PolynomialRing(Rationals(),3);
b1:=[2,-1];
vars:=Transpose(Matrix(R,[[x1,x2]]));
c1:=Transpose(t1*Matrix(R,[b1]));

pols:=vars-c1;
eqns:=Eltseq(pols);
idl:=ideal< R | eqns >;



  