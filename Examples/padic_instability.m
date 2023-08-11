K<nu>:=ext<K0|Polynomial(K0, [20, 0, 40, 0, -13, 0, 1])> where K0 is RationalField();
P<t,x>:=PolynomialRing(K, 2);
//f:=1/4704884352*(1821390765000*nu^5 + 2656703300973*nu^4 - 24471476525000*nu^3 - 35693783559305*nu^2 + 83520124400000*nu + 121816950278930)*t*x^3 + 1/1185630856704*(-916110286260920*nu^5 - 1048515338751287*nu^4 + 12309762456013450*nu^3 + 14090045703660770*nu^2 - 42017943233167700*nu - 48098746918137045)*t*x^2 + 1/33197663987712*(16847701882494805*nu^5 + 16892568757438789*nu^4 - 226386036740650550*nu^3 - 227016730958997190*nu^2 + 772761730103146300*nu + 775021993515310740)*t*x + 1/13013484283183104*(-1363055619047196520*nu^5 - 1377861278343661579*nu^4 + 18315497375810409200*nu^3 + 18516391528941006340*nu^2 - 62519014396129583200*nu - 63212684645652545265)*t + x^8 + 1/1764*(-73*nu^5 + 926*nu^4 + 544*nu^3 - 16164*nu^2 - 180*nu + 69280)*x^7 + 1/127008*(136435*nu^5 + 1597651*nu^4 - 1825060*nu^3 - 21500580*nu^2 + 6134820*nu + 73277900)*x^6 + 1/4572288*(73438975*nu^5 + 312670327*nu^4 - 982527620*nu^3 - 4189846180*nu^2 + 3339087700*nu + 14261843220)*x^5;

f:=t*x^8 + 1/14893335*(-383413*nu^5 + 2443942*nu^4 + 4222044*nu^3 - 19954296*nu^2 + 1509860*nu - 80920760)*t*x^7 + 1/29574856989630*(30451129087603*nu^5 - 91042293414331*nu^4 - 191419666591860*nu^3 + 568187500505940*nu^2 - 109262175418172*nu + 503488835965724)*t*x^6 + 1/146822750907883705350*(-761760392417709351373*nu^5 + 2049657836055145270549*nu^4 + 4588173624883375295244*nu^3 - 12355444335138130502892*nu^2 + 2312302794863402005700*nu - 6489037634316749463140)*t*x^5 + 1/1085565465231182207860407731380125*(35658444985798320108278934400000000*nu^5 - 96317683323370695565375314011476048*nu^4 - 208720500561837047517995891266560000*nu^3 + 571224871988619492626660244440228544*nu^2 - 97438802719553542429935427512320000*nu + 266899570551044264273227526543336000)*x^3 + 1/3233538027623769813540937116006842793375*(-429721467563163497289527885902118703145648*nu^5 + 1169231675813056791323874636951861987532144*nu^4 + 2434375482799145922561253980221782678294848*nu^3 - 6715032113799093063548382093499533696341568*nu^2 + 1143637460182292678795057456114362815908288*nu - 3151173978511546966921206721416579917619392)*x^2 + 1/48158165080640057795952712682623772014069655625*(-18881893365009591829079462280244863729321938772856*nu^5 + 46299279716653167644458600022324068887211449207352*nu^4 + 132894982645379792809411002238647490269124157863968*nu^3 - 330611821569650255205684659426281143909666409172256*nu^2 + 61548740714658520401425431263326778259869003663200*nu - 152990282114054878369116063832852858642130779119200)*x + 1/47815712368751626344965692942737634371277606303850625*(4427823691758944229205798173373289990516550362045400032*nu^5 - 14297569935883411789262941033545164786079020413792974560*nu^4 - 13331834009354352225703716710131434763774278560963725440*nu^3 + 52812644472167602825594561931952951343685299760313171072*nu^2 - 6656329532472951003727526652990818352659700732563805568*nu + 25751600308264258482897285833354706715756198650499748224);

//reducemodel_padic(f);

PrimesForReduction:=[];

 if BaseRing(Parent(f)) eq Rationals() then
    K:=RationalsAsNumberField();
  else
    K := BaseRing(Parent(f));
  end if;
  variables:=[ Parent(f).i : i in [1..#Names(Parent(f))] ];
  var_size:=#variables;
  ZK := Integers(K);
  k:=RealField(5);
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
    support_init:=PrimesUpTo(10000,K);
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
  for i in [1..lp_size] do  SetLowerBound(L, i, k!-100); end for;
  for i in [1..lp_size] do  SetUpperBound(L, i, k!100); end for;

  soln_real,state:=Solution(L);
  assert state eq 0;
  //soln_real is the best possible solution, but we might not be able to principalize the ideals, 
  //hence we must project onto the subspace defined by forcing the solution to be principal.
  
  if h ne 1 then
    principal_constraints:=[];
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
        Append(~principal_constraints,principal_constraint_lhs);
        //principal_constraint_rhs:=Matrix(k,1,1,[0]);
        //AddConstraints(L, principal_constraint_lhs, principal_constraint_rhs : Rel := "eq");
      end for;
    end for;
  end if;


for i in [1..lp_size] do SetLowerBound(Lprinc, i, k!-100); end for;
for i in [1..lp_size] do SetUpperBound(Lprinc, i, k!-1); end for;

//soln,state:=Solution(Lprinc);

con1:=[ Round(a) : a in Eltseq(Constraint(Lprinc,1)) ];
con2:=[ Round(a) : a in Eltseq(Constraint(Lprinc,2)) ];
con3:=[ Round(a) : a in Eltseq(Constraint(Lprinc,3)) ];

H1:=HyperplaneToPolyhedron(con1,0);
H2:=HyperplaneToPolyhedron(con2,0);
H3:=HyperplaneToPolyhedron(con3,0);

H:=H1 meet H2 meet H3;

M:=Transpose(Matrix(Integers(),3,#con1,[con1,con2,con3]));
W:=Matrix(Integers(),1,3,[[0],[0],[0]]);
X,N:=Solution(M,W);

Lat:=LatticeWithBasis(N);
w:= RSpace(BaseRing(soln_real), lp_size)!soln_real;
op:=ClosestVector(L,w);

opelt:=Eltseq(op);  
assert &+[ opelt[i]*con1[i] : i in [1..33] ] eq 0;
assert &+[ opelt[i]*con2[i] : i in [1..33] ] eq 0;
assert &+[ opelt[i]*con3[i] : i in [1..33] ] eq 0;



////////////////////

con1:=[ Round(a) : a in Eltseq(Constraint(Lprinc,1)) ];
con2:=[ Round(a) : a in Eltseq(Constraint(Lprinc,2)) ];
con3:=[ Round(a) : a in Eltseq(Constraint(Lprinc,3)) ];


realsoln:=[ Eltseq(soln_real)[i] : i in [1..#Eltseq(soln_real)-3] ];


c1:=-(&+[ realsoln[j]*con1[j] : j in [1..#realsoln] ])/con1[#con1-2];
c2:=-(&+[ realsoln[j]*con2[j] : j in [1..#realsoln] ])/con2[#con2-1];
c3:=-(&+[ realsoln[j]*con3[j] : j in [1..#realsoln] ])/con3[#con3];
newreal:=realsoln cat [c1,c2,c3];
assert &+[ newreal[i]*con1[i] : i in [1..33] ] eq 0;
assert &+[ newreal[i]*con2[i] : i in [1..33] ] eq 0;
assert &+[ newreal[i]*con3[i] : i in [1..33] ] eq 0;

M:=Transpose(Matrix(Integers(),3,#con1,[con1,con2,con3]));
W:=Matrix(Integers(),1,3,[[0],[0],[0]]);
X,N:=Solution(M,W);


Lat:=Lattice(N);
w:= RSpace(Universe(newreal), lp_size)!newreal;
op:=ClosestVector(Lat,w);




