intrinsic ComputeBadMaps(path::MonStgElt) -> Any
  {}

  file := Open(path, "r");
  bad_maps := [* *];
  eof := false;
  while not eof do
    line := Gets(file);
    if IsEof(line) then
      eof := true;
      break;
    end if;
    //lab1, lab2, C, phi, cs := ReadDataRow(line);
    lab1, lab2, f, a, cs := ReadDataRow(line);
    print lab1;
    R<t,x> := Parent(f);
    C := Curve(Spec(R),f);
    KC<t,x> := FunctionField(C);
    phi := (1/a)*t;
    rams := ComputeRamificationValues(phi);
    bad := [];
    for el in rams do
      if (el cmpne 0) and (el cmpne 1) and (el cmpne Infinity()) then
        Append(~bad, el);
      end if;
    end for;
    bad := Setseq(Seqset(bad));
    print bad;
    if #bad gt 0 then
      Append(~bad_maps, <lab1, bad>);
    end if;
  end while;
  return bad_maps;
end intrinsic;

intrinsic FixBadMaps(path_in::MonStgElt, path_out::MonStgElt) -> Any
  {}

  file := Open(path_in, "r");
  bad_ := 0;
  eof := false;
  while not eof do
    line := Gets(file);
    if IsEof(line) then
      eof := true;
      break;
    end if;
    lab1, lab2, f, a, cs := ReadDataRow(line);
    print lab1;
    R<t,x> := Parent(f);
    C := Curve(Spec(R),f);
    KC<t,x> := FunctionField(C);
    phi := (1/a)*t;
    rams := ComputeRamificationValues(phi);
    bad := [];
    for el in rams do
      if (el cmpne 0) and (el cmpne 1) and (el cmpne Infinity()) then
        Append(~bad, el);
      end if;
    end for;
    bad := Setseq(Seqset(bad));
    print bad;
    if #bad gt 0 then
      printf "bad ramification, %o\n", bad;
      if bad eq [-1] then
        print "-1 bug";
        a := -a; // fix -1 bug
      end if;
    end if;
    Write(path_out, Join([Sprint(el) : el in [* lab1, lab2, f, a, cs *]], "|"));
  end while;
  return Sprintf("Data written to %o", path_out);
end intrinsic;

intrinsic RedoUnitReduction(path_in::MonStgElt, path_out::MonStgElt) -> Any
  {}

  file_out := Open(path_out, "r");
  eof_out := false;
  size_out := 0;
  while not eof_out do
    line := Gets(file_out);
    size_out +:= 1;
    if IsEof(line) then
      eof_out := true;
      break;
    end if;
  end while;
  file := Open(path_in, "r");
  eof := false;
  // skip over the first size_out many lines
  printf "skipping %o lines\n", size_out-1;
  for i := 1 to size_out-1 do
    line := Gets(file);
  end for;
  while not eof do
    line := Gets(file);
    if IsEof(line) then
      eof := true;
      break;
    end if;
    lab1, lab2, f, a, cs := ReadDataRow(line);
    print lab1, lab2, f, a, cs;
    printf "Doing unit reduction on %o...", lab1;
    try
      f_unit, scalars := reducemodel_units(f);
    catch e;
    end try;
    print "done";
    a := a/scalars[1];
    Write(path_out, Join([Sprint(el) : el in [* lab1, lab2, f_unit, a, cs *]], "|"));
    //Write(path_out, Join([Sprint(el) : el in [* lab1, lab2, f, a, cs *]], "|"));
    delete f; delete a; delete cs;
  end while;
  return Sprintf("Data written to %o", path_out);
end intrinsic;

intrinsic WriteDisplayPolynomials(path_in::MonStgElt, path_out::MonStgElt) -> Any
  {}
  col_names:= "label|BelyiDB_label|plane_model|plane_constant|plane_model_latex";
  data_types := "text|text|text|text|text";
  Write(path_out, col_names);
  Write(path_out, data_types);
  Write(path_out, "");

  file := Open(path_in, "r");
  eof := false;
  while not eof do
    line := Gets(file);
    if IsEof(line) then
      eof := true;
      break;
    end if;
    lab1, lab2, f, a, cs := ReadDataRow(line);
    print lab1;
    Write(path_out, Join([Sprint(el) : el in [* lab1, lab2, f, a, DisplayPolynomial(f) *]], "|"));
  end while;
  return Sprintf("Data written to %o", path_out);
end intrinsic;
