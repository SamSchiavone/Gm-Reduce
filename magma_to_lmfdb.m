intrinsic BelyiDBToRows(s::BelyiDB : NaiveUnits := false) -> MonStgElt
  {}
  row := "";
  // galmaps dictionaries
  require BelyiMapIsComputed(s): "maps must be computed";
  gal_orbits_before_sorting := GaloisOrbits(s); // we will sort by size (increasing)
  gal_orbits := gal_orbits_before_sorting;
  gal_orbits_sizes := [#orbit : orbit in gal_orbits_before_sorting];
  ParallelSort(~gal_orbits_sizes, ~gal_orbits);
  pass := PointedPassport(s);
  for i := 1 to #gal_orbits do
    if i lt #gal_orbits then assert #gal_orbits[i] le #gal_orbits[i+1]; end if;
    gal_orbit := gal_orbits[i];
    inds := [Index(pass, triple) : triple in gal_orbit];
    belyi_label := BelyiDB_label(s, inds, i);
    lmfdb_label := GalmapLabel(s, inds, i);
    X := BelyiCurves(s)[inds[1]];
    //phi := BelyiMap(s, inds, i);
    phi := BelyiMaps(s)[inds[1]];
    KX := Parent(phi);
    K<nu> := BaseRing(BaseRing(KX));
    f, a := BestModel(phi : NaiveUnits := NaiveUnits);
    row *:= Sprintf("%o|%o|%o|%o", lmfdb_label, belyi_label, f, K!a);
    if i lt #gal_orbits then
      row *:= "\n";
    end if;
  end for;
  return row;
end intrinsic;

intrinsic LoadDataRow(s::MonStgElt) -> Any
  {Take a row of data of the form
id|geomtype|map|abc|base_field|triples_cyc|g|curve|orbit_size|label|a_s|pass_size|c_s|aut_group|deg|group_num|embeddings|group|triples|b_s|plabel|lambdas|friends|curve_label|specializations|models|moduli_field|moduli_field_label|base_field_label|primitivization|is_primitive|BelyiDB_label|BelyiDB_plabel|plane_model|plane_constant
    and return a boolean indicating whether the plane model is null or not, the label, plane equation, and plane constant}
  spl := Split(s, "|");
  label := spl[10];
  printf "loading row for %o\n", label;
  fld := spl[5];
  fld := PyReplaceString(fld, "{", "[");
  fld := PyReplaceString(fld, "}", "]");
  fld := eval fld;
  if #fld ne 2 then
    K<nu> := NumberField(Polynomial(fld));
  else
    K := RationalsAsNumberField();
  end if;
  R<t,x> := PolynomialRing(K,2);
  f := spl[34];
  if f eq "\\N" then
    return false, label, _, _;
  end if;
  f := eval f;
  a := eval spl[35];
  return true, label, f, a; // returns label, plane model, plane constant
end intrinsic;

intrinsic WriteFactoredPolynomials(read_file::MonStgElt, write_file::MonStgElt) -> Any
  {}

  my_file := Open(read_file, "r");
  header := Gets(my_file);
  header *:= "|plane_model_latex";
  Write(write_file, header);
  data_types := Gets(my_file);
  data_types *:= "|text";
  Write(write_file, data_types);
  line := Gets(my_file); // blank line
  Write(write_file, line);
  // append factored form to each line
  eof_bool := false;
  while not eof_bool do
    line := Gets(my_file);
    if IsEof(line) then
      eof_bool := true;
      break;
    end if;
    if not ("|" in line) then
      break;
    end if;
    //print line;
    bool, label, f, a := LoadDataRow(line);
    if not bool then
      Write(write_file, line*"|"*"\\N");
    else
      f_factored := DisplayPolynomial(f);
      Write(write_file, line*"|"*f_factored);
    end if;
  end while;
  return Sprintf("Data with factored polys written to %o\n", write_file);
end intrinsic;
