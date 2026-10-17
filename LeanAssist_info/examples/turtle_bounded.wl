(* ::Package:: *)
(* turtle_bounded.wl -- Lean-verified computational part of the boundedness proof of turtle programs on Penrose rhomb tilings
   (proof_sketch.md; reference implementations prove2.py / subst_fast.py and notebook_src/lib.wl / check_atlas.wl / verify_all.wl).

   Step 1, atlas closure.  Mathematica computes the 30 marked triangle coronas of sigma^8(sun) (centre triangle t and all triangles
   sharing a vertex with t, up to translation and rotation by multiples of 36 deg, written in the frame of the centre) and Lean checks
   that every entry is the corona of its centre and that, for every child t' of sigma(t_C), the corona of t' inside sigma(C) is
   complete (angle sum 360 deg at its three vertices, integer units of 36 deg) and equivalent to an entry.
   Step 2, V(P, n).  For every corona C, Mathematica runs P* from every state of every rhomb of sigma^n(C) that contains a triangle of
   sigma^n(t_C) and writes a certificate: the rhombs used (addresses of their two triangles in sigma^n(C)), one representative per orbit
   with its period, the navigation table and the orbit states in key order.  Lean recomputes the rhombs by substitution, runs every
   orbit (closed with the stated minimal period, no escape from the rhombs of the certificate), matches the claimed states one to one,
   enumerates sigma^n(t_C) itself and checks that every start state is a claimed state, and that the periods form the stated set.
   The checker is LeanAssist_info/lean/turtle/TurtleBounded_template.lean (standalone Lean, appended to the O2 and O1 templates).

   Usage (front end or headless, LeanAssist loaded):
     Get[FileNameJoin[{$LeanAssistDirectory, "examples", "turtle_bounded.wl"}]];
     LeanTurtleAtlasClosure[]                     (* checkAtlas atlas = true, decide +kernel *)
     LeanTurtleBoundedRun["SSR", 7]               (* checkBounded prog 7 atlas certs periods = true, native_decide *)
     LeanTurtleBoundedRun["SSR", 7, "Method" -> "decide"]           (* kernel: one theorem per corona, about 30 min *)
     LeanTurtleBoundedRun["SSR", 7, "Method" -> "decide", "Coronas" -> {1, 12}]   (* kernel on some coronas only *)
   Options: "Method", "Name", "SaveSource" (writes the .lean into LeanAssist_info/lean/turtle), "Timeout", "Perturb" (negative controls,
   Lean must reject; see the comments at the definitions).  tbAtlas[] and tbBoundedData[prog, n] are the Mathematica side. *)

If[!MemberQ[$Packages, "LeanAssist`"],
  Block[{$CharacterEncoding = "UTF-8"}, Get[FileNameJoin[{$packageDirectory, "LeanAssist.wl"}]]]];

(* ---- exact arithmetic in Z[zeta] on 4-vectors {a, b, c, d} = a + b zeta + c zeta^2 + d zeta^3 (Lean: <a, b, c, d, 0>) ---- *)
tbZ = {{0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}, {-1, -1, -1, -1}};      (* v . tbZ = zeta v *)
tbPhiM = -(tbZ . tbZ) - (tbZ . tbZ . tbZ);                             (* phi = 1 + zeta + zeta^4 = -zeta^2 - zeta^3 *)
tbRhoM = -(tbZ . tbZ . tbZ);                                           (* rho = -zeta^3 = rotation by 36 deg *)
tbRhoPow = Table[MatrixPower[tbRhoM, k], {k, 0, 9}];
tbUnits = Table[{1, 0, 0, 0} . tbRhoPow[[k + 1]], {k, 0, 9}];
tbE4 = N[Table[{Cos[2 Pi j/5], Sin[2 Pi j/5]}, {j, 0, 3}]];
(* point keys of the Lean checker: 16-bit digits of the coordinates + 32768 *)
tbPointKeys[v_] := With[{w = v + 32768}, ((w[[All, 1]]*65536 + w[[All, 2]])*65536 + w[[All, 3]])*65536 + w[[All, 4]]];
tbAngUnits = {{1, 2, 2}, {3, 1, 1}};    (* units of 36 deg at A, B, C of an acute / obtuse triangle *)

(* ---- marked triangles <|"col", "A", "B", "C", "code"|>; code = address root 3^n + sum slot_i 3^(n-i) ---- *)
tbTri[list_] := <|"col" -> list[[All, 1]], "A" -> list[[All, 2]], "B" -> list[[All, 3]], "C" -> list[[All, 4]],
  "code" -> Range[0, Length[list] - 1]|>;
tbWheel[] := tbTri[Table[With[{b = tbUnits[[Mod[i, 10] + 1]], c = tbUnits[[Mod[i + 1, 10] + 1]]},
  If[EvenQ[i], {0, {0, 0, 0, 0}, c, b}, {0, {0, 0, 0, 0}, b, c}]], {i, 0, 9}]];
(* one substitution step, children in the slot order of the Lean `subdivide` *)
tbSubdivide[t_] := Module[{col = t["col"], code = t["code"], ia, io, A, B, C, A2, B2, C2, P, Q, R, parts = {}},
  ia = Flatten[Position[col, 0]]; io = Flatten[Position[col, 1]];
  If[ia =!= {},
    A = t["A"][[ia]]; B = t["B"][[ia]]; C = t["C"][[ia]]; A2 = A . tbPhiM; B2 = B . tbPhiM; C2 = C . tbPhiM; P = A2 + B - A;
    AppendTo[parts, {ConstantArray[0, Length[ia]], C2, P, B2, 3 code[[ia]]}];
    AppendTo[parts, {ConstantArray[1, Length[ia]], P, C2, A2, 3 code[[ia]] + 1}]];
  If[io =!= {},
    A = t["A"][[io]]; B = t["B"][[io]]; C = t["C"][[io]]; A2 = A . tbPhiM; B2 = B . tbPhiM; C2 = C . tbPhiM; Q = B2 + A - B; R = B2 + C - B;
    AppendTo[parts, {ConstantArray[1, Length[io]], R, C2, A2, 3 code[[io]]}];
    AppendTo[parts, {ConstantArray[1, Length[io]], Q, R, B2, 3 code[[io]] + 1}];
    AppendTo[parts, {ConstantArray[0, Length[io]], R, Q, A2, 3 code[[io]] + 2}]];
  AssociationThread[{"col", "A", "B", "C", "code"} -> Table[Developer`ToPackedArray[Join @@ parts[[All, k]]], {k, 5}]]];
tbSign[t_] := Module[{a = t["A"] . tbE4, b = t["B"] . tbE4, c = t["C"] . tbE4},
  Sign[(b[[All, 1]] - a[[All, 1]]) (c[[All, 2]] - a[[All, 2]]) - (b[[All, 2]] - a[[All, 2]]) (c[[All, 1]] - a[[All, 1]])]];

(* ---- coronas and the atlas ---- *)
tbIncidence[t_] := Module[{n = Length[t["col"]], k, u, vid, ang, inc},
  k = Join[tbPointKeys[t["A"]], tbPointKeys[t["B"]], tbPointKeys[t["C"]]];
  u = Union[k]; vid = Lookup[AssociationThread[u -> Range[Length[u]]], k];
  ang = Join @@ Table[tbAngUnits[[t["col"] + 1, r]], {r, 3}];
  inc = GroupBy[Transpose[{vid, Join[Range[n], Range[n], Range[n]], ang}], First -> Rest];
  <|"vid" -> Transpose[Partition[vid, n]], "inc" -> inc, "full" -> Map[Total[#[[All, 2]]] == 10 &, inc]|>];
(* indices of the triangles sharing a vertex with triangle i; None when an angle sum around a vertex of i is not 360 deg *)
tbCorona[inc_, i_] := With[{vs = inc["vid"][[i]]},
  If[And @@ (inc["full"] /@ vs), Union @@ (inc["inc"][#][[All, 1]] & /@ vs), None]];
(* canonical form in the frame of the centre c: apex -> 0, leg AB -> direction 0; rows {col, flag, A, B, C} *)
tbCoronaCanon[t_, idx_, c_] := Module[{A0 = t["A"][[c]], k, M},
  k = First[FirstPosition[tbUnits, t["B"][[c]] - A0]] - 1; M = tbRhoPow[[Mod[-k, 10] + 1]];
  Sort[Table[Join[{t["col"][[j]], Boole[j == c]}, (t["A"][[j]] - A0) . M, (t["B"][[j]] - A0) . M, (t["C"][[j]] - A0) . M], {j, idx}]]];
(* atlas entry <|"tris" -> {{col, A, B, C}, ...}, "centre" -> 0-based index|> of a canonical form *)
tbEntry[canon_] := <|"tris" -> ({#[[1]], #[[3 ;; 6]], #[[7 ;; 10]], #[[11 ;; 14]]} & /@ canon),
  "centre" -> First[FirstPosition[canon[[All, 2]], 1]] - 1|>;
(* the marked triangle coronas of sigma^8(sun), up to translation and rotation by 36 deg (sorted canonical forms) *)
tbAtlas[] := tbAtlas[] = Module[{t = Nest[tbSubdivide, tbWheel[], 8], inc, keys = <||>, cor},
  inc = tbIncidence[t];
  Do[cor = tbCorona[inc, i]; If[cor =!= None, keys[tbCoronaCanon[t, cor, i]] = True], {i, Length[t["col"]]}];
  tbEntry /@ Sort[Keys[keys]]];
(* Mathematica-side closure check (same statement as checkAtlas): number of child coronas outside the atlas or incomplete *)
tbAtlasClosureWL[atlas_] := Module[{keys = Association[(tbCoronaCanon[tbTri[#tris], Range[Length[#tris]], #centre + 1] -> True) & /@ atlas], bad = 0, n = 0},
  Do[Module[{st = tbSubdivide[tbTri[e["tris"]]], inc, cor},
    inc = tbIncidence[st];
    Do[If[Quotient[st["code"][[i]], 3] == e["centre"], n++; cor = tbCorona[inc, i];
      If[cor === None || !KeyExistsQ[keys, tbCoronaCanon[st, cor, i]], bad++]], {i, Length[st["col"]]}]], {e, atlas}];
  <|"Children" -> n, "Outside" -> bad|>];

(* ---- V(P, n): the certificate of one corona ---- *)
tbCycle[nav_, pk_, prog_, {r0_, e0_}] := Module[{r = r0, e = e0, k},
  Catch[Do[Switch[cmd,
      "S", k = Lookup[nav, pk[[r, Mod[e + 1, 4] + 1]]*2^64 + pk[[r, e + 1]], Missing[]];
        If[MissingQ[k], Throw[$Failed]];
        r = Quotient[k, 4] + 1; e = Mod[Mod[k, 4] + 2, 4]; Sow[r],
      "R", e = Mod[e + 3, 4],
      "L", e = Mod[e + 1, 4]], {cmd, Characters[prog]}];
    {r, e}]];

tbCoronaCert[entry_, prog_String, n_Integer, maxCycles_ : 100000] := Module[
  {st, sg, nT, triIdx, pos, partner, keep, quads, posCode, negCode, nR, pk, nav, startR, starts, claim = <||>, orbits = {}, seqs = {},
   visited, seq, cur, res, R, ridx, fine, fidx, skey, navCodes, states, periods, esc = 0},
  st = Nest[tbSubdivide, tbTri[entry["tris"]], n];
  sg = tbSign[st]; nT = Length[st["col"]];
  triIdx = AssociationThread[Transpose[{st["col"], st["A"], st["B"], st["C"]}] -> Range[nT]];
  pos = Flatten[Position[sg, 1]];
  (* mirror image of the positive triangle (col, A, B, C): (col, B + C - A, B, C) *)
  partner = Lookup[triIdx, Key /@ Transpose[{st["col"][[pos]], st["B"][[pos]] + st["C"][[pos]] - st["A"][[pos]], st["B"][[pos]], st["C"][[pos]]}], 0];
  keep = Flatten[Position[partner, _?Positive]];
  quads = Transpose[{st["A"][[pos[[keep]]]], st["B"][[pos[[keep]]]], st["A"][[partner[[keep]]]], st["C"][[pos[[keep]]]]}];
  posCode = st["code"][[pos[[keep]]]]; negCode = st["code"][[partner[[keep]]]];
  nR = Length[quads];
  pk = Partition[tbPointKeys[Flatten[quads, 1]], 4];
  nav = AssociationThread[Flatten[Table[pk[[r, e + 1]]*2^64 + pk[[r, Mod[e + 1, 4] + 1]], {r, nR}, {e, 0, 3}]] -> Range[0, 4 nR - 1]];
  If[Length[nav] != 4 nR, Return[Failure["Overlap", <|"Message" -> "duplicated directed edge"|>]]];
  (* start rhombs: a triangle descends from the centre *)
  startR = Flatten[Position[Transpose[{Quotient[posCode, 3^n], Quotient[negCode, 3^n]}], {___, entry["centre"], ___}, {1}, Heads -> False]];
  starts = Flatten[Table[{r, e}, {r, startR}, {e, 0, 3}], 1];
  visited = Reap[Do[If[!KeyExistsQ[claim, s],
      cur = s; seq = {s}; Sow[First[s]];
      While[True,
        cur = tbCycle[nav, pk, prog, cur];
        If[cur === $Failed, esc++; Break[]];
        If[cur === s, Break[]];
        AppendTo[seq, cur];
        If[Length[seq] > maxCycles, esc++; Break[]]];
      If[cur =!= s, Continue[]];
      Do[claim[seq[[j]]] = {Length[orbits], j - 1}, {j, Length[seq]}];
      AppendTo[orbits, {s, Length[seq]}]], {s, starts}]][[2]];
  If[esc > 0, Return[Failure["Escape", <|"Message" -> "orbits leave the patch or do not close", "Count" -> esc|>]]];
  R = SortBy[Union[Flatten[visited]], posCode[[#]] &];
  ridx = AssociationThread[R -> Range[0, Length[R] - 1]];
  fine = Union[posCode[[R]], negCode[[R]]];
  fidx = AssociationThread[fine -> Range[0, Length[fine] - 1]];
  skey[{r_, e_}] := pk[[r, e + 1]]*2^64 + pk[[r, Mod[e + 1, 4] + 1]];
  navCodes = SortBy[Flatten[Table[{r, e}, {r, R}, {e, 0, 3}], 1], skey];
  states = SortBy[Normal[claim], skey[First[#]] &];
  periods = Union[orbits[[# + 1, 2]] & /@ (First /@ Lookup[claim, Key /@ starts])];
  <|"fine" -> fine, "rhombs" -> Flatten[Transpose[{fidx /@ posCode[[R]], fidx /@ negCode[[R]]}]],
    "orbits" -> Flatten[{4 ridx[#[[1, 1]]] + #[[1, 2]], #[[2]]} & /@ orbits],
    "nav" -> (4 ridx[#[[1]]] + #[[2]] & /@ navCodes),
    "states" -> Flatten[{4 ridx[#[[1, 1]]] + #[[1, 2]], #[[2, 1]], #[[2, 2]]} & /@ states],
    "periods" -> periods,
    "Starts" -> Length[starts], "StartPeriods" -> Counts[orbits[[# + 1, 2]] & /@ (First /@ Lookup[claim, Key /@ starts])],
    "PatchRhombs" -> nR, "Rhombs" -> Length[R], "Orbits" -> Length[orbits], "OrbitStates" -> Length[claim]|>];

(* certificates of all coronas of the atlas; memoised *)
tbBoundedData[prog_String, n_Integer] := tbBoundedData[prog, n] = Module[{atlas = tbAtlas[], certs},
  certs = tbCoronaCert[#, prog, n] & /@ atlas;
  If[!FreeQ[certs, _Failure], Return[SelectFirst[certs, FailureQ]]];
  <|"Program" -> prog, "n" -> n, "Atlas" -> atlas, "Certificates" -> certs,
    "Periods" -> Union @@ (#periods & /@ certs), "Starts" -> Total[#Starts & /@ certs],
    "Spectrum" -> KeySort[Merge[#StartPeriods & /@ certs, Total]], "Orbits" -> Total[#Orbits & /@ certs]|>];

(* ---- Lean data ---- *)
tbInt[x_Integer] := If[x < 0, "-" <> IntegerString[-x], IntegerString[x]];
tbZ5[v_] := "\:27e8" <> StringRiffle[tbInt /@ v, ", "] <> ", 0\:27e9";
tbLeanTri[{col_, A_, B_, C_}] := "(" <> tbInt[col] <> ", " <> tbZ5[A] <> ", " <> tbZ5[B] <> ", " <> tbZ5[C] <> ")";
(* packed list (TurtleBounded.unpack): chunks of at most 256 numbers, h + 2^32 sum d_i 2^(w (i - 1)) with header h = 64 count + w,
   w = bit length of the largest number of the chunk; hexadecimal literals *)
tbPackChunk[ch_List] := With[{w = Max[1, BitLength[Max[ch]]]}, FromDigits[Reverse[ch], 2^w]*2^32 + 64 Length[ch] + w];
tbPack[xs_List] := "[" <> StringRiffle["0x" <> IntegerString[tbPackChunk[#], 16] & /@ Partition[xs, UpTo[256]], ", "] <> "]";
tbNatList[xs_List] := "[" <> StringRiffle[IntegerString /@ xs, ", "] <> "]";

tbLeanAtlas[atlas_] := StringJoin[
  "open TurtleO2 TurtleO1 TurtleBounded\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n",
  Table["def cor" <> IntegerString[i - 1] <> " : Corona := { tris := [" <> StringRiffle[tbLeanTri /@ atlas[[i]]["tris"], ", "] <>
    "], centre := " <> IntegerString[atlas[[i]]["centre"]] <> " }\n", {i, Length[atlas]}],
  "\ndef atlas : List Corona := [" <> StringRiffle["cor" <> IntegerString[# - 1] & /@ Range[Length[atlas]], ", "] <> "]\n"];

tbLeanCerts[data_] := StringJoin[
  "\ndef prog : List Cmd := [" <> StringRiffle["Cmd." <> # & /@ Characters[data["Program"]], ", "] <> "]\n\n",
  Table[With[{d = data["Certificates"][[i]]},
    "def cert" <> IntegerString[i - 1] <> " : CoronaCert := { fine := " <> tbPack[d["fine"]] <> ", rhombs := " <> tbPack[d["rhombs"]] <>
      ", orbits := " <> tbPack[d["orbits"]] <> ", nav := " <> tbPack[d["nav"]] <> ", states := " <> tbPack[d["states"]] <>
      ", periods := " <> tbNatList[d["periods"]] <> " }\n"], {i, Length[data["Certificates"]]}],
  "\ndef certs : List CoronaCert := [" <> StringRiffle["cert" <> IntegerString[# - 1] & /@ Range[Length[data["Certificates"]]], ", "] <> "]\n",
  "def periods : List Nat := " <> tbNatList[data["Periods"]] <> "\n"];

tbTemplate[] := StringRiffle[Import[FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", #}], "Text", CharacterEncoding -> "UTF-8"] & /@
  {"TurtleO2_template.lean", "TurtleO1_template.lean", "TurtleBounded_template.lean"}, "\n"];

(* ---- Step 1: atlas closure ---- *)
Options[LeanTurtleAtlasClosure] = {"Method" -> "decide", "Name" -> "turtle_atlas_closed", "SaveSource" -> True, "Timeout" -> 1200, "Perturb" -> None};
(* "Perturb" -> {"Drop", i} removes entry i (1-based) of the atlas (its class is needed by the closure), {"Shift", i, j} moves
   triangle j of entry i by a unit vector (the entry is no longer a corona): negative controls, Lean must reject. *)
LeanTurtleAtlasClosure[OptionsPattern[]] := Module[{atlas = tbAtlas[], pert = OptionValue["Perturb"], wl, thm, res, src, name = OptionValue["Name"]},
  Switch[pert,
    {"Drop", _Integer}, atlas = Delete[atlas, pert[[2]]],
    {"Shift", _Integer, _Integer}, atlas = MapAt[MapAt[# + tbUnits[[1]] &, #, {{2}, {3}, {4}}] &, atlas, {pert[[2]], Key["tris"], pert[[3]]}]];
  wl = tbAtlasClosureWL[atlas];
  thm = LeanTheorem[name, {}, {}, "checkAtlas atlas = true",
    "Proof" -> If[OptionValue["Method"] === "native_decide", "native_decide", "decide +kernel"],
    "Preamble" -> tbTemplate[] <> "\n" <> tbLeanAtlas[atlas],
    "DocString" -> "Step 1 of the boundedness proof: the " <> IntegerString[Length[atlas]] <>
      " marked triangle coronas of sigma^8(sun) form a closed atlas (every entry is the corona of its centre; the coronas of the children of every centre are complete inside sigma(C) and equivalent to entries)",
    "Imports" -> {}, "Data" -> <|"Entries" -> Length[atlas], "Sizes" -> Sort[Length[#tris] & /@ atlas], "WLClosure" -> wl|>];
  res = LeanProve[thm, "Mathlib" -> False, "Timeout" -> OptionValue["Timeout"]];
  If[TrueQ[OptionValue["SaveSource"]] && pert === None && Head[res] === LeanCheckResult,
    LeanSaveSource[res["Theorem"], FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", name <> ".lean"}]]];
  res];

(* ---- Step 2: V(P, n) ---- *)
(* negative controls on the certificate data (indices 1-based): {"Period", c, o, d} adds d to the period of orbit o of corona c;
   {"DropOrbit", c, o} removes orbit o of corona c and its states (its start states are no longer covered); {"Address", c, k, d}
   adds d to the k-th fine-triangle address of corona c; {"Periods", p} removes p from the stated period set *)
tbPerturb[data_, pert_] := Module[{d = data, cert},
  Switch[pert,
    {"Period", _Integer, _Integer, _Integer},
      d[["Certificates", pert[[2]], "orbits", 2 pert[[3]]]] += pert[[4]],
    {"DropOrbit", _Integer, _Integer},
      cert = d["Certificates"][[pert[[2]]]];
      cert["orbits"] = Flatten[Delete[Partition[cert["orbits"], 2], pert[[3]]]];
      cert["states"] = Flatten[If[#[[2]] > pert[[3]] - 1, {#[[1]], #[[2]] - 1, #[[3]]}, #] & /@
        DeleteCases[Partition[cert["states"], 3], {_, pert[[3]] - 1, _}]];
      d[["Certificates", pert[[2]]]] = cert,
    {"Address", _Integer, _Integer, _Integer},
      d[["Certificates", pert[[2]], "fine", pert[[3]]]] += pert[[4]],
    {"Periods", _Integer},
      d["Periods"] = DeleteCases[d["Periods"], pert[[2]]]];
  d];

Options[LeanTurtleBoundedRun] = {"Method" -> "native_decide", "Name" -> Automatic, "SaveSource" -> True, "Timeout" -> Automatic,
  "Perturb" -> None, "Coronas" -> All};
(* "Method" -> "native_decide": one theorem checkBounded prog n atlas certs periods = true (compiled code; the axiom
   <name>._native.native_decide.ax_1_1 records the trust in the compiler).  "decide": kernel only: the atlas closure and one theorem
   per corona (checked one after another, Elab.async false), combined into the same statement.  "Coronas" -> {i, ...} (1-based)
   restricts Step 2 to some coronas: the statement is then allCoronas prog n [cor_i, ...] [cert_i, ...] = true.
   tbBoundedTheorem[prog, n, opts] returns the LeanTheorem without running Lean (LeanSaveSource writes it; the full kernel run takes
   about 30 min and 6 GB, better started with lean.exe directly under a memory watchdog). *)
tbBoundedTheorem[prog_String, n_Integer, opts : OptionsPattern[LeanTurtleBoundedRun]] := Module[
  {data, sel = OptionValue[LeanTurtleBoundedRun, {opts}, "Coronas"], pert = OptionValue[LeanTurtleBoundedRun, {opts}, "Perturb"],
   method = OptionValue[LeanTurtleBoundedRun, {opts}, "Method"], name = OptionValue[LeanTurtleBoundedRun, {opts}, "Name"],
   tag, idx, ns = IntegerString[n], concl, sub, perC, proof, pre},
  data = tbBoundedData[prog, n];
  If[FailureQ[data], Return[data]];
  data = tbPerturb[data, pert];
  idx = If[sel === All, Range[Length[data["Atlas"]]], sel];
  tag = StringReplace[prog, Except[WordCharacter] -> "_"] <> "_n" <> ns;
  If[!StringQ[name], name = "bounded_" <> tag <> If[sel === All, "", "_partial"] <> If[method === "decide", "_kernel", "_verified"]];
  sub = "[" <> StringRiffle["cor" <> IntegerString[# - 1] & /@ idx, ", "] <> "] [" <> StringRiffle["cert" <> IntegerString[# - 1] & /@ idx, ", "] <> "]";
  concl = If[sel === All, "checkBounded prog " <> ns <> " atlas certs periods = true", "allCoronas prog " <> ns <> " " <> sub <> " = true"];
  pre = tbTemplate[] <> "\n" <> tbLeanAtlas[data["Atlas"]] <> tbLeanCerts[data];
  If[method === "decide",
    perC = Table["theorem " <> name <> "_c" <> IntegerString[i - 1] <> " : checkCorona prog " <> ns <> " cor" <> IntegerString[i - 1] <>
      " cert" <> IntegerString[i - 1] <> " = true := by decide +kernel", {i, idx}];
    pre = pre <> "\nset_option Elab.async false\n\n" <> StringRiffle[perC, "\n\n"] <> "\n";
    proof = If[sel === All,
      "have h1 : checkAtlas atlas = true := by decide +kernel\n" <>
      "have h2 : allCoronas prog " <> ns <> " atlas certs = true := by\n  simp only [atlas, certs, allCoronas, " <>
        StringRiffle[name <> "_c" <> IntegerString[# - 1] & /@ idx, ", "] <> ", Bool.and_true]\n" <>
      "have h3 : samePeriods (unionPeriods certs) periods = true := by decide +kernel\n" <>
      "simp only [checkBounded, h1, h2, h3, Bool.and_self]",
      "simp only [allCoronas, " <> StringRiffle[name <> "_c" <> IntegerString[# - 1] & /@ idx, ", "] <> ", Bool.and_true]"],
    proof = "native_decide"];
  LeanTheorem[name, {}, {}, concl, "Proof" -> proof, "Preamble" -> pre,
    "DocString" -> "V(P, n) for P = (" <> prog <> ")*, n = " <> ns <> If[sel === All, " and the atlas closure: ", " on " <> IntegerString[Length[idx]] <> " coronas: "] <>
      IntegerString[Total[#Starts & /@ data["Certificates"][[idx]]]] <> " start states, " <> IntegerString[Total[#Orbits & /@ data["Certificates"][[idx]]]] <>
      " orbits, all closed inside sigma^n(C), periods " <> ToString[data["Periods"]],
    "Imports" -> {}, "Data" -> KeyDrop[data, {"Atlas", "Certificates"}]]];

LeanTurtleBoundedRun[prog_String, n_Integer, opts : OptionsPattern[]] := Module[{thm, res, timeout = OptionValue["Timeout"]},
  thm = tbBoundedTheorem[prog, n, opts];
  If[FailureQ[thm], Return[thm]];
  If[!NumericQ[timeout], timeout = If[OptionValue["Method"] === "decide",
    600 + 90 If[OptionValue["Coronas"] === All, Length[tbAtlas[]], Length[OptionValue["Coronas"]]], 1200]];
  res = LeanProve[thm, "Mathlib" -> False, "Timeout" -> timeout];
  If[TrueQ[OptionValue["SaveSource"]] && OptionValue["Perturb"] === None && OptionValue["Coronas"] === All && Head[res] === LeanCheckResult,
    LeanSaveSource[res["Theorem"], FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", thm["Name"] <> ".lean"}]]];
  res];

Print[Style["turtle_bounded.wl: LeanTurtleAtlasClosure[] and LeanTurtleBoundedRun[prog, n] defined.", Bold]];
