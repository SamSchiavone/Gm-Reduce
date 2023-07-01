
R<z>:=PolynomialRing(Rationals());
K<nu> := NumberField(z^2-2);
R<x,y> := PolynomialRing(K,2);
ZK := Integers(K);
UK,mUK:=UnitGroup(K);
epsilon:= [ K!(mUK(eps)) : eps in Generators(UK) | not(IsFinite(eps)) ][1];
f := epsilon^2*x^2 + epsilon^4*y^2;


Q,C:=UnitsQuadraticObjectiveMatrices(f);
V,N:=SolveQuadraticProgramReals(Q,C);


Q:=Matrix([[1,0,0],[1,0,0],[1,0,0]]);
Q:=ChangeRing(Q,RealField(10));
C:=Matrix([[2,0,0]]);
C:=ChangeRing(C,RealField(10));

V,N:=NumericalSolution(Q,C);


echN:=EchelonForm(N);
echNcolumns:=Rows(Transpose(echN));
echNspan:=sub< Parent(echNcolumns[1]) | echNcolumns >;
standardbasis:=Basis(VectorSpace(BaseRing(echNspan),Dimension(echNspan)));

nonbasiscolumns:= [ A : A in echNcolumns | A notin standardbasis ];
minus1:=-IdentityMatrix(BaseRing(echNcolumns[1]),#nonbasiscolumns);
minus1rows:=Rows(minus1);
definingequations:= [ Eltseq(nonbasiscolumns[i]) cat Eltseq(minus1rows[i]) : i in [1..#nonbasiscolumns]  ];
linearterms := [ &+[ b[j]*Eltseq(V)[j] : j in [1..#Eltseq(V)] ] : b in definingequations ];
//note echN is reduced row echelon so some of the columns will be standard basis vectors. 




k:=RealField(10);
var_size:=#definingequations[1];
L := LPProcess(k, var_size);
obj:=Matrix(k,1,var_size,[0 : i in [1..var_size]]);
SetObjectiveFunction(L, obj);


//y=x-1.2
const:=-1.2;
eps:=0.2;
bound:=100;

for i in [1..#definingequations] do 
  AddConstraints(L,Matrix(k,[definingequations[i]]), Matrix(k,[[linearterms[i]+eps]]) : Rel:="le");
  AddConstraints(L,Matrix(k,[definingequations[i]]), Matrix(k,[[linearterms[i]-eps]]) : Rel:="ge");
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

Solution(L);


A:=BasisMatrix(Nspace);
exs:=[ Eltseq(NumericalSolution(A,echNcolumns[2])), Eltseq(NumericalSolution(A,echNcolumns[3])) ];
x1 = x2 
x1 = -2*x3 

x3 = - x1 - x2
x1 + x2 + x3 = 0
x1 + x2 + x3 < 0.2 
x1 + x2 + x3 > -0.2
-100 < x1 < 100

rowsN:=Rows(N);


/*
names:= [ Sprintf("t%o",i) : i in [1..#rowsN] ]
  cat [ Sprintf("x%o",j) : j in [1..#Eltseq(rowsN[1])] ];
S:=PolynomialRing(BaseRing(Q),#names);
AssignNames(~S,names);

span:=&+[ S.i*ChangeRing(rowsN[i],S) : i in [1..#rowsN] ];
newvars:=Parent(span)![ S.j : j in [#rowsN+1..#names] ];
vinit:=Parent(span)!V;

//newvars = vinit + span
Zspan:= newvars - vinit -span;
eqns:=Eltseq(Zspan);

idl:=ideal< S | eqns >;
Neqns:=EliminationIdeal(idl,#rowsN);*/
