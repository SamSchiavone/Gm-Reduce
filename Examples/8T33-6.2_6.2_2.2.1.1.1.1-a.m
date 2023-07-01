function ComputeRamificationValuesPoly(g)
  R<t,x> := Parent(g);
  C := Curve(Spec(R),g);
  KC<t,x> := FunctionField(C);
  dpts, dmults := Support(Divisor(Differential(t)));
  return [* Evaluate(t, RepresentativePoint(el)) : el in dpts *];
end function;

function ComputeRamificationValues(t)
  dpts, dmults := Support(Divisor(Differential(t)));
  return [* Evaluate(t, RepresentativePoint(el)) : el in dpts *];
end function;


AttachSpec("~/github/Gm-Reduce/spec");
SetVerbose("GmReduce",true);
lab := LMFDBLabelToBelyiDBLabel("8T33-6.2_6.2_2.2.1.1.1.1-a" : dot_m := true);
s := BelyiDBRead(lab);
phi := s`BelyiDBBelyiMaps[1];

// copy-pasta of AllReducedModels

effort := 0;
degree := 0;
NaiveUnits := false;

Kinit:=BaseRing(BaseRing(Parent(phi)));
if effort eq 0 then
  //wild effort hack
  effort:=Max(Floor(-2*(Degree(Kinit))/3+11),1);
end if;
vprintf GmReduce: "now taking effort = %o\n", effort;
if degree eq 0 then
  degree:=Floor((Genus(Curve(Parent(phi)))+3)/2);
end if;
vprintf GmReduce: "now taking degree = %o\n", degree;
RsandPs := Support(Divisor(phi));
RsandQs := Support(Divisor(phi-1));
PsQsRs := SetToSequence(SequenceToSet(RsandPs cat RsandQs));

t0:=Cputime();
vprint GmReduce: "Starting to compute SmallFunctions()";
xs := SmallFunctions(PsQsRs, degree);
t1:=Cputime();
vprintf GmReduce: "Done with SmallFunctions(), it took %o seconds\n", t1-t0;

t0:=Cputime();
vprint GmReduce: "Starting to compute SortSmallFunctions()";
ts_xs_Fs_sorted := SortSmallFunctions(phi, xs : effort := effort);

while #ts_xs_Fs_sorted eq 0 do
  degree +:= 1;
  vprintf GmReduce: "degree is now %o", degree;
  xs := SmallFunctions(PsQsRs, degree);
  ts_xs_Fs_sorted := SortSmallFunctions(phi, xs : effort := effort);
end while;
t1:=Cputime();
vprintf GmReduce: "Done with SortSmallFunctions(), it took %o seconds\n", t1-t0;

vprintf GmReduce: "Computing reduced models...";
t0 := Cputime();
reduced_models := [];
for tup in ts_xs_Fs_sorted do
  t, x, F := Explode(tup);
  fred, scalars := ReducedModel(t, x : NaiveUnits := NaiveUnits);
  //vprintf GmReduce: "t = %o,\nx = %o,\nreduced model = %o\n\n", t, x, fred;
  Append(~reduced_models, <#Sprint(fred), t, x, fred, scalars>);
end for;
t1 := Cputime();
vprintf GmReduce: "done. That took %o seconds\n", t1 - t0;
Sort(~reduced_models);

ComputeRamificationValues(reduced_models[1][4]); // this is bad
reduced_models[1][5]; // this is bad
//t, x, F := ts_xs_Fs_sorted[1];
t, x, F := Explode(ts_xs_Fs_sorted[2]);
ComputeRamificationValues(F); // this is okay
f_plane := model(t,x);
ComputeRamificationValues(f_plane); // this is bad!
f_padic, scalars1 := reducemodel_padic(f_plane);
ComputeRamificationValues(f_padic);
f_unit, scalars2 := reducemodel_units(f_padic);
ComputeRamificationValues(f_unit);

// now from ReducedEquation


// start computing polys
/*
  print "Unreduced plane model";
  f_unred := UnreducedModel(phi);
  ComputeRamificationValues(f_unred);
  print "p-adic reduced model";
  f_padic, scalars1  := reducemodel_padic(f_unred);
  ComputeRamificationValues(f_padic);
  f_unit, scalars2 := reducemodel_units(f_padic);
  print "fully reduced model";
  f_red := f_unit;
  scalars_red := [ scalars1[i]*scalars2[i] : i in [1..#scalars1] ];
  ComputeRamificationValues(f_red);

  orb := S3Orbit(f_red);
  for g in orb do
      ComputeRamificationValues(g);
  end for;
*/
