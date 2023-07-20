

euclidean:=TextFileToLines("Gm-Reduce/Examples/EucBelyiMapDataForLMFDB.m");

RT<T>:=PolynomialRing(Rationals());
for line in euclidean do 

  split:=Split(line,",");
  label:=Reverse(Prune(Reverse(split[1])));
  nofld_eqn:=Prune(Prune(Prune(split[5])));

  Index(euclidean,line); 
  label;

  try 
    if nofld_eqn eq "T" then 
      K<v>:=RationalsAsNumberField();
    else 
      pol:=RT!(eval(nofld_eqn));
      K<v>:=NumberField(pol);
    end if;

    if split[3] eq "P" then
      X := Curve(ProjectiveSpace(PolynomialRing(K, 2)));
      KX<t> := FunctionField(X);
      phi := KX!eval(split[4]);
    else 
      fX:=Split(split[3],"=")[2];
      fx:=ReplaceAll(fX,"X","x");
      S<x> := PolynomialRing(K);
      X := EllipticCurve(S!eval(fx),S!0);
      KX<t,x> := FunctionField(X);
      phi := KX!eval(split[4]);
    end if;

    f_plane:=BestModel(phi);

    phi;
    print "";
    f_plane;
  catch e 
    print "error in evaluating string";
  end try;

  new_line:=Sprintf("%o || %o || %o || %o",label, phi, f_plane, DefiningPolynomial(K));
  Write("Gm-Reduce/Examples/euclidean-maps-reduced.m",new_line);
  print "=======================================";

end for;

