intrinsic SmallFunctions(Qs::SeqEnum[PlcCrvElt], d::RngIntElt) -> SeqEnum
  {Given a sequence of points Qs, return functions supported on Qs of degree <= d}
  // Qs, points which are "small"
  // d, a degree bound;
  // Output: functions supported on {Qs} of degree <= d

  //The "small" points are the support of phi, phi-1.
  //sort "small" points by degree
  Qs := Sort(Qs, func<Q,R | Degree(Q)-Degree(R)>);
  Ds := [];
  QDs := [Divisor(Q) : Q in Qs]; //Make the points into divisors
  newDs := [Universe(QDs) | 0];

  //add divisors so that degree is <= d and collect in Ds
  while #newDs ne 0 do
    frontierDs := [];
    for newD in newDs do
      dnewD := Degree(newD);
      for RD in QDs do
        if Degree(RD) + dnewD le d then
          Append(~Ds, RD + newD);
          Append(~frontierDs, RD + newD);
        end if;
      end for;
    end for;
    newDs := frontierDs;
  end while;
  Ds:=Setseq(Set(Ds));
  if #Ds eq 0 then return []; end if;

  xs := [];
  divisorsSeen := [Universe(Ds) | 0];
  for Dden in Ds do
    for Dnum in Ds do
      D := Dden-Dnum;
      // if Degree(D) ne 0 then continue; end if;
      if D eq Parent(D)!0 then continue; end if;
      RR, mRR := RiemannRochSpace(D);
      if Dimension(RR) eq 1 then
        x := mRR(RR.1);
        divx := Divisor(x);
        // yeah yeah, we know a lot about the divisor of x, but
        // it may have an extra zero (or zeros!)
        if divx notin divisorsSeen then
          Append(~xs, x);
          Append(~divisorsSeen, divx);
        end if;
      end if;
    end for;
  end for;
  //looks like every x appears twice
  return Setseq(Set(xs));
  //functions supported on the points of small degree as
  //generated by the Riemann Roch space
end intrinsic;

intrinsic SmallFunctionsExactDegree(Qs::SeqEnum[PlcCrvElt], d::RngIntElt) -> SeqEnum
  {Given a sequence of points Qs, return functions supported on Qs of exact degree d}
  if d eq 1 then
    return SmallFunctions(Qs,d);
  else
    sfd:=SmallFunctions(Qs,d);
    sfd1 := SmallFunctions(Qs,d-1);
    return [ s : s in sfd | s notin sfd1 ];
  end if;
end intrinsic;