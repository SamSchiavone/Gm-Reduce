/*
  Usage: run the following command in ~/github/BelyiDB, or wherever filenames.txt is located

  parallel -j 16 --joblog joblog --eta -a filenames.txt magma -b filename:={} ~/github/Gm-Reduce/script.m  > output.txt
 */

AttachSpec("code/spec_database");
AttachSpec("code/spec_triangle");
AttachSpec("../Gm-Reduce/spec");
//AttachSpec("../Belyi/Code/spec");
//SetProfile(true);

s := BelyiDBRead(filename);
if BelyiMapIsComputed(s) then
  Ks := [el[1] : el in s`BelyiDBBaseFieldData];
  d := Max([Degree(el) : el in Ks]);
  //if d le 20 then
    try
      print BelyiDBToRows(s);
    catch e
      print "================================";
      printf "%o failed\n", s`BelyiDBFilename;
      print e`Object;
      print "================================";
    end try;
  //end if;
end if;
//G := ProfileGraph();
//ProfilePrintByTotalTime(G : Max := 15);
quit;
