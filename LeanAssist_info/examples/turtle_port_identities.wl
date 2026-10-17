(* ::Package:: *)
(* turtle_port_identities.wl -- Lean-verified obligations O2 / O3 of a pass-substitution certificate
   (unboundedness of turtle programs on Penrose rhomb tilings, proof_unbounded.md).

   Mathematica reads the certificate JSON (results/unbounded_certs/cert*.json), derives the child
   frames of the four standard Robinson triangles, writes everything as Lean data and asks Lean to
   check, by `decide` (kernel evaluation) or `native_decide` (compiled code), that
     * the frames agree with the substitution sigma,
     * the delta of every port family is consistent with a unit leg,
     * O3 (closure / consistency of the pass table) holds,
     * O2 (port identities at the two lowest levels of each parity class) holds.
   The checker itself is LeanAssist_info/lean/turtle/TurtleO2_template.lean (standalone Lean, no Mathlib).

   Usage (front end or headless, LeanAssist loaded):
     Get[FileNameJoin[{$LeanAssistDirectory, "examples", "turtle_port_identities.wl"}]];
     res = LeanTurtlePortIdentities[certFile];           (* LeanCheckResult *)
     res["Status"], res["Axioms"], res["Time"]
   Options: "Method" -> "decide" | "native_decide" | Automatic (kernel decide first, then native_decide),
            "Name" -> theorem name, "SaveSource" -> True writes the .lean into LeanAssist_info/lean/turtle.
   O1 (base-level simulation, TurtleO1_template.lean) is checked by LeanTurtleBaseSimulation[certFile] (same options,
   "Perturb" -> {"N", passId, d} also available); tpBaseSimulation[cert] is the Mathematica side of it.
   O4 (growth) and O6 (exact recurrence N(m+2) = a N(m) + b of the roots, TurtleO46_template.lean) are checked by
   LeanTurtleRecurrence[certFile] ("Perturb" -> {"a" | "b" | "N0", rootId, d} or {"N", passId, d}); tpRecurrenceData[cert, sim, roots]
   is the Mathematica side.  The logical part of O6 (Cayley-Hamilton) is lean/turtle/CayleyHamiltonRecurrence.lean and the
   induction H(m) is lean/turtle/PassInduction.lean (both Mathlib, LeanCheckFile). *)

If[!MemberQ[$Packages, "LeanAssist`"],
  Block[{$CharacterEncoding = "UTF-8"}, Get[FileNameJoin[{$packageDirectory, "LeanAssist.wl"}]]]];

(* ---- exact arithmetic in Z[zeta] on 5-vectors (same conventions as verify_cert.py) ---- *)
tpCanon[k_List] := k - Last[k];                                   (* last coordinate 0 *)
tpAdd[k_, l_] := tpCanon[k + l];
tpSub[k_, l_] := tpCanon[k - l];
tpMulPhi[k_] := tpCanon[Table[k[[j]] + k[[Mod[j - 2, 5] + 1]] + k[[Mod[j, 5] + 1]], {j, 5}]];   (* phi = 1 + zeta + zeta^4 *)
tpRot36[k_] := tpCanon[Table[-k[[Mod[j - 4, 5] + 1]], {j, 5}]];                                  (* times -zeta^3 *)
tpRotN[n_, k_] := Nest[tpRot36, k, n];
tpUnit[n_] := tpRotN[n, {1, 0, 0, 0, 0}];
tpEmbed[k_] := N[k . Table[{Cos[2 Pi j/5], Sin[2 Pi j/5]}, {j, 0, 4}], 30];
tpOrientation[A_, B_, C_] := Sign[Det[{tpEmbed[B] - tpEmbed[A], tpEmbed[C] - tpEmbed[A]}]];

tpStdTriangle[col_, sign_] := With[{b = tpUnit[0], c = If[col == 0, tpUnit[1], tpUnit[3]]},
  If[sign > 0, {col, {0, 0, 0, 0, 0}, b, c}, {col, {0, 0, 0, 0, 0}, c, b}]];
tpSubdivide[{col_, A_, B_, C_}] := Module[{A2 = tpMulPhi[A], B2 = tpMulPhi[B], C2 = tpMulPhi[C], P, Q, R},
  If[col == 0,
    P = tpAdd[A2, tpSub[B, A]]; {{0, C2, P, B2}, {1, P, C2, A2}},
    Q = tpAdd[B2, tpSub[A, B]]; R = tpAdd[B2, tpSub[C, B]]; {{1, R, C2, A2}, {1, Q, R, B2}, {0, R, Q, A2}}]];

(* child frames of the standard triangle (col, sign): {childCol, childSign, k, t} per slot *)
tpChildFrames[{col_, sign_}] := Module[{children = tpSubdivide[tpStdTriangle[col, sign]]},
  Table[Module[{ccol = ch[[1]], A = ch[[2]], B = ch[[3]], C = ch[[4]], s, std, k},
    s = tpOrientation[A, B, C]; std = tpStdTriangle[ccol, s];
    k = SelectFirst[Range[0, 9], tpRotN[#, std[[3]]] === tpSub[B, A] &];
    If[!IntegerQ[k] || tpRotN[k, std[[4]]] =!= tpSub[C, A], Print["frame mismatch for ", {col, sign}]; Abort[]];
    {ccol, s, k, A}], {ch, children}]];
$tpTypes = {{0, 1}, {0, -1}, {1, 1}, {1, -1}};

(* ---- Lean data: one small definition per port / pass (deeply nested tuples make the elaborator time out) ---- *)
tpZ5[k_List] := "\:27e8" <> StringRiffle[ToString /@ tpCanon[k], ", "] <> "\:27e9";
tpCross[{tail_, head_, i_}] := "\:27e8" <> tpZ5[tail] <> ", " <> tpZ5[head] <> ", " <> ToString[i] <> "\:27e9";

tpLeanData[cert_Association] := Module[{portIds, passIds, portDefs, passDefs, frameDefs},
  portIds = Sort[ToExpression /@ Keys[cert["ports"]]];
  passIds = Sort[ToExpression /@ Keys[cert["passes"]]];
  portDefs = Table[With[{f = cert["ports"][ToString[id]]},
    "def port" <> ToString[id] <> " : Port := { id := " <> ToString[id] <> ", col := " <> ToString[f["typ"][[1]]] <>
      ", sign := " <> ToString[f["typ"][[2]]] <> ", parity := " <> ToString[f["parity"]] <>
      ", ref := " <> tpCross[f["ref"]] <> ", dtail := " <> tpZ5[f["delta"][[1]]] <> ", dhead := " <> tpZ5[f["delta"][[2]]] <> " }"],
    {id, portIds}];
  passDefs = Table[With[{p = cert["passes"][ToString[id]]},
    "def pass" <> ToString[id] <> " : Pass := { id := " <> ToString[id] <> ", out := " <> ToString[p["out"]] <>
      ", children := [" <> StringRiffle["\:27e8" <> StringRiffle[ToString /@ #, ", "] <> "\:27e9" & /@ p["children"], ", "] <> "] }"],
    {id, passIds}];
  frameDefs = Table["(" <> ToString[t[[1]]] <> ", " <> ToString[t[[2]]] <> ", [" <>
      StringRiffle["\:27e8" <> ToString[#[[1]]] <> ", " <> ToString[#[[2]]] <> ", " <> ToString[#[[3]]] <> ", " <> tpZ5[#[[4]]] <> "\:27e9" & /@ tpChildFrames[t], ", "] <> "])",
    {t, $tpTypes}];
  StringJoin[
    "open TurtleO2\n\nset_option maxHeartbeats 4000000\n\n",
    StringRiffle[portDefs, "\n"], "\n\n",
    "def portData : List Port := [" <> StringRiffle["port" <> ToString[#] & /@ portIds, ", "] <> "]\n\n",
    StringRiffle[passDefs, "\n"], "\n\n",
    "def passData : List Pass := [" <> StringRiffle["pass" <> ToString[#] & /@ passIds, ", "] <> "]\n\n",
    "def frameData : List (Nat \:00d7 Int \:00d7 List Frame) := [" <> StringRiffle[frameDefs, ",\n  "] <> "]\n\n",
    "def cert : Cert := { B := " <> ToString[cert["B"]] <> ", ports := portData, passes := passData, frames := frameData }\n"]];

Options[LeanTurtlePortIdentities] = {"Method" -> Automatic, "Name" -> Automatic, "SaveSource" -> True, "Timeout" -> 1200, "Perturb" -> None};
(* "Perturb" -> {portId, "delta" | "ref", coordinate} adds 1 to one integer of the certificate: negative control (Lean must reject) *)
LeanTurtlePortIdentities[certFile_String?FileExistsQ, OptionsPattern[]] := Module[
  {cert, template, data, name, thm, method = OptionValue["Method"], res, src, out, pert = OptionValue["Perturb"]},
  cert = Import[certFile, "RawJSON"];
  If[MatchQ[pert, {_Integer, "delta" | "ref", _Integer}],
    cert = MapAt[# + 1 &, cert, {Key["ports"], Key[ToString[pert[[1]]]], Key[pert[[2]]], 1, pert[[3]]}]];
  template = Import[FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", "TurtleO2_template.lean"}], "Text", CharacterEncoding -> "UTF-8"];
  data = tpLeanData[cert];
  name = OptionValue["Name"];
  If[!StringQ[name], name = "o2_" <> StringReplace[cert["prog"], Except[WordCharacter] -> "_"] <> "_verified"];
  thm[m_] := LeanTheorem[name, {}, {}, "checkCertificate cert = true", "Proof" -> m,
    "Preamble" -> template <> "\n" <> data,
    "DocString" -> "frames, port deltas, O3 and O2 of the certificate " <> FileNameTake[certFile] <> " (program " <> cert["prog"] <> ", base level " <> ToString[cert["B"]] <> ", " <>
      ToString[Length[cert["passes"]]] <> " pass families, " <> ToString[Length[cert["ports"]]] <> " port families)",
    "Imports" -> {}, "Data" -> <|"Certificate" -> certFile, "Program" -> cert["prog"], "Passes" -> Length[cert["passes"]], "Ports" -> Length[cert["ports"]]|>];
  res = Switch[method,
    "native_decide", LeanProve[thm["native_decide"], "Mathlib" -> False, "Timeout" -> OptionValue["Timeout"]],
    "decide", LeanProve[thm["decide +kernel"], "Mathlib" -> False, "Timeout" -> OptionValue["Timeout"]],
    _, (* kernel first, native code as fallback *)
    out = LeanProve[thm["decide +kernel"], "Mathlib" -> False, "Timeout" -> OptionValue["Timeout"]];
    If[Head[out] === LeanCheckResult && out["Status"] === "Proved", out,
      Print["decide failed or timed out (", If[Head[out] === LeanCheckResult, out["Status"], out], "); trying native_decide"];
      LeanProve[thm["native_decide"], "Mathlib" -> False, "Timeout" -> OptionValue["Timeout"]]]];
  If[TrueQ[OptionValue["SaveSource"]] && pert === None && Head[res] === LeanCheckResult,
    src = FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", name <> ".lean"}];
    LeanSaveSource[res["Theorem"], src]];
  res];

Print[Style["turtle_port_identities.wl: LeanTurtlePortIdentities[certFile] defined.", Bold]];

(* ---- O1: base-level simulation (same specification as verify_cert.py `Supertile` and lib.wl ptRhombs "Ghost"->True / ptNav).
   Mathematica computes N(pi, B) for the pass families of parity B mod 2 and writes them as Lean data; Lean recomputes the
   supertile, the owned rhombs, the navigation and the turtle run (LeanAssist_info/lean/turtle/TurtleO1_template.lean). ---- *)

(* orientation of a marked Robinson triangle, exact: C - A = rho^(+-theta) (B - A), theta = 1 (acute) / 3 (obtuse); 0 = malformed *)
tpOrient[{col_, A_, B_, C_}] := With[{th = If[col == 0, 1, 3], u = tpSub[B, A], v = tpSub[C, A]},
  Which[tpRotN[th, u] === v, 1, tpRotN[10 - th, u] === v, -1, True, 0]];
tpSupertile[{col_, sign_}, B_] := Nest[Join @@ (tpSubdivide /@ #) &, {tpStdTriangle[col, sign]}, B];
(* rhombs {A, B, B + C - A, C} (counter-clockwise) of the positively oriented fine triangles (ownership) *)
tpOwnedRhombs[tris_] := Module[{o = tpOrient /@ tris},
  If[MemberQ[o, 0], Print["tpOwnedRhombs: malformed fine triangle"]; Abort[]];
  {#[[2]], #[[3]], tpSub[tpAdd[#[[3]], #[[4]]], #[[2]]], #[[4]]} & /@ Pick[tris, o, 1]];
(* directed edge {tail, head} -> {rhomb index (1-based), e (0..3)} *)
tpEdgeTable[rhombs_] := Module[{assoc = <||>, key},
  Do[Do[key = {rhombs[[r, e + 1]], rhombs[[r, Mod[e + 1, 4] + 1]]};
     If[KeyExistsQ[assoc, key], Print["tpEdgeTable: duplicated directed edge"]; Abort[]];
     assoc[key] = {r, e}, {e, 0, 3}], {r, Length[rhombs]}];
  assoc];
(* state {rhomb, edge, command index} after the entry crossing; None if the far side is not owned or the near side is owned *)
tpEntryState[tbl_, {tail_, head_, i_}] := Which[
  !KeyExistsQ[tbl, {head, tail}], None,
  KeyExistsQ[tbl, {tail, head}], None,
  True, With[{re = tbl[{head, tail}]}, {re[[1]], Mod[re[[2]] + 2, 4], i + 1}]];
(* turtle run: {exit crossing (CCW order of the rhomb left), N} or {None, N} *)
tpRun[rhombs_, tbl_, prog_String, {r0_, e0_, ci0_}, maxN_ : 10^6] :=
  Module[{r = r0, e = e0, ci = ci0, n = StringLength[prog], cnt = 0, c, a, b, re},
   While[cnt < maxN,
    c = StringTake[prog, {Mod[ci, n] + 1}];
    Switch[c,
     "S", a = rhombs[[r, e + 1]]; b = rhombs[[r, Mod[e + 1, 4] + 1]]; cnt++;
       If[!KeyExistsQ[tbl, {b, a}], Return[{{a, b, Mod[ci, n]}, cnt}]];
       re = tbl[{b, a}]; r = re[[1]]; e = Mod[re[[2]] + 2, 4],
     "R", e = Mod[e + 3, 4],
     _, e = Mod[e + 1, 4]];
    ci++];
   {None, cnt}];
tpRq[B_, q_] := If[Mod[B, 2] == q, B, B + 1];
(* port of family pid at level m (m >= R(q), m == q mod 2): x -> phi^2 x + delta, (m - R(q))/2 times *)
tpPortAt[cert_, pid_, m_] := Module[{f = cert["ports"][ToString[pid]], s},
  s = (m - tpRq[cert["B"], f["parity"]])/2;
  {Nest[tpAdd[tpMulPhi[tpMulPhi[#]], f["delta"][[1]]] &, tpCanon[f["ref"][[1]]], s],
   Nest[tpAdd[tpMulPhi[tpMulPhi[#]], f["delta"][[2]]] &, tpCanon[f["ref"][[2]]], s], f["ref"][[3]]}];

(* O1 in Mathematica: list of <|"id", "N", "Exit", "ExitOK"|> for the pass families of parity B mod 2 *)
tpBaseSimulation[cert_Association] := Module[{B = cert["B"], prog = cert["prog"], passIds, tbls = <||>, res = {}},
  passIds = Select[Sort[ToExpression /@ Keys[cert["passes"]]], cert["ports"][ToString[#]]["parity"] == Mod[B, 2] &];
  Do[Module[{p = cert["passes"][ToString[id]], typ = cert["ports"][ToString[id]]["typ"], st, s, ex, n},
    If[!KeyExistsQ[tbls, typ], With[{rh = tpOwnedRhombs[tpSupertile[typ, B]]}, tbls[typ] = {rh, tpEdgeTable[rh]}]];
    st = tbls[typ];
    s = tpEntryState[st[[2]], tpPortAt[cert, id, B]];
    If[s === None,
     Print["O1 pass ", id, ": the entry port is not an entry crossing at level ", B];
     AppendTo[res, <|"id" -> id, "N" -> 0, "Exit" -> None, "ExitOK" -> False|>],
     {ex, n} = tpRun[st[[1]], st[[2]], prog, s];
     AppendTo[res, <|"id" -> id, "N" -> n, "Exit" -> ex, "ExitOK" -> ex === tpPortAt[cert, p["out"], B]|>]]],
   {id, passIds}];
  res];

tpO1LeanData[cert_Association, sim_List] := StringJoin[
  "open TurtleO1\n\n",
  "def prog : List Cmd := [" <> StringRiffle["Cmd." <> # & /@ Characters[cert["prog"]], ", "] <> "]\n\n",
  "def o1Data : List O1Pass := [" <> StringRiffle["\:27e8" <> ToString[#id] <> ", " <> ToString[#N] <> "\:27e9" & /@ sim, ", "] <> "]\n"];

tpO1Template[] := Import[FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", "TurtleO2_template.lean"}], "Text", CharacterEncoding -> "UTF-8"] <> "\n" <>
  Import[FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", "TurtleO1_template.lean"}], "Text", CharacterEncoding -> "UTF-8"];

tpPerturbCert[cert_, pert_] := If[MatchQ[pert, {_Integer, "delta" | "ref", _Integer}],
  MapAt[# + 1 &, cert, {Key["ports"], Key[ToString[pert[[1]]]], Key[pert[[2]]], 1, pert[[3]]}], cert];

tpRunMethod[thm_, method_, timeout_] := Module[{out},
  Switch[method,
    "native_decide", LeanProve[thm["native_decide"], "Mathlib" -> False, "Timeout" -> timeout],
    "decide", LeanProve[thm["decide +kernel"], "Mathlib" -> False, "Timeout" -> timeout],
    _, out = LeanProve[thm["decide +kernel"], "Mathlib" -> False, "Timeout" -> timeout];
    If[Head[out] === LeanCheckResult && out["Status"] === "Proved", out,
      Print["decide failed or timed out (", If[Head[out] === LeanCheckResult, out["Status"], out], "); trying native_decide"];
      LeanProve[thm["native_decide"], "Mathlib" -> False, "Timeout" -> timeout]]]];

Options[LeanTurtleBaseSimulation] = {"Method" -> Automatic, "Name" -> Automatic, "SaveSource" -> True, "Timeout" -> 1200, "Perturb" -> None};
(* "Perturb" -> {portId, "delta" | "ref", coordinate} (adds 1 to one integer of a port family) or {"N", passId, d} (adds d to the
   exported length N(pass, B)): negative controls, Lean must reject.  Result: LeanCheckResult; res["Theorem"]["Simulation"] holds the
   Mathematica simulation (id, N, Exit, ExitOK). *)
LeanTurtleBaseSimulation[certFile_String?FileExistsQ, OptionsPattern[]] := Module[
  {cert, sim, data, name, thm, res, src, pert = OptionValue["Perturb"]},
  cert = tpPerturbCert[Import[certFile, "RawJSON"], pert];
  sim = tpBaseSimulation[cert];
  If[MatchQ[pert, {"N", _Integer, _Integer}],
    sim = Map[If[#id == pert[[2]], Append[#, "N" -> #N + pert[[3]]], #] &, sim]];
  If[!AllTrue[sim, #ExitOK &], Print["LeanTurtleBaseSimulation: the Mathematica simulation disagrees with the certificate for passes ",
    Select[sim, !#ExitOK &][[All, "id"]], " (Lean will reject)"]];
  data = tpLeanData[cert] <> "\n" <> tpO1LeanData[cert, sim];
  name = OptionValue["Name"];
  If[!StringQ[name], name = "o1_" <> StringReplace[cert["prog"], Except[WordCharacter] -> "_"] <> "_verified"];
  thm[m_] := LeanTheorem[name, {}, {}, "checkO1 cert prog o1Data = true", "Proof" -> m,
    "Preamble" -> tpO1Template[] <> "\n" <> data,
    "DocString" -> "O1 (base simulation at level " <> ToString[cert["B"]] <> ") of the certificate " <> FileNameTake[certFile] <>
      " (program " <> cert["prog"] <> ", " <> ToString[Length[sim]] <> " pass families of parity " <> ToString[Mod[cert["B"], 2]] <>
      ", " <> ToString[Total[sim[[All, "N"]]]] <> " S-moves in all)",
    "Imports" -> {}, "Data" -> <|"Certificate" -> certFile, "Program" -> cert["prog"], "Simulation" -> sim|>];
  res = tpRunMethod[thm, OptionValue["Method"], OptionValue["Timeout"]];
  If[TrueQ[OptionValue["SaveSource"]] && pert === None && Head[res] === LeanCheckResult,
    src = FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", name <> ".lean"}];
    LeanSaveSource[res["Theorem"], src]];
  res];

Print[Style["turtle_port_identities.wl: LeanTurtleBaseSimulation[certFile] defined (O1).", Bold]];

(* ---- O4 / O6: growth and exact recurrence of the root lengths (same specification as verify_cert.py `Nrec`, `expand2`,
   `recurrence`).  N(pi, B) from the O1 simulation, N(pi, m+1) = Sum over the children of N(child entry, m); along one parity
   class N(m+2) = M N(m) with the two-level expansion matrix M.  For every root r: O4 (r occurs mu >= 1 times in its own
   two-level expansion, which has more than mu members) and the closed recurrence N(r, m+2) = a N(r, m) + b for dim M + 3
   steps from m0 = R(q).  By Cayley-Hamilton (CayleyHamiltonRecurrence.lean, Mathlib) the recurrence then holds at every
   level of the class.  Lean recomputes every length from the pass table (TurtleO46_template.lean). ---- *)

tpPassTable[cert_Association] := Association[ToExpression[#] -> cert["passes"][#] & /@ Keys[cert["passes"]]];
tpParity[cert_Association, id_Integer] := cert["ports"][ToString[id]]["parity"];

(* lengths at the levels B .. mMax: <|m -> <|id -> N(id, m)|>|>, the families of parity m mod 2 at level m *)
tpLengths[cert_Association, sim_List, mMax_Integer] := Module[{B = cert["B"], passes = tpPassTable[cert], lv = <||>, ids},
  lv[B] = Association[#id -> #N & /@ sim];
  Do[With[{prev = lv[m - 1]},
     ids = Select[Keys[passes], tpParity[cert, #] == Mod[m, 2] &];
     lv[m] = Association[Table[id -> Total[Lookup[prev, passes[id]["children"][[All, 2]]]], {id, ids}]]],
   {m, B + 1, mMax}];
  lv];

(* the two-level expansion of a family: multiplicities of the grandchildren (entry ids) *)
tpExpand2[passes_Association, id_Integer] := Counts[Flatten[passes[#]["children"][[All, 2]] & /@ passes[id]["children"][[All, 2]]]];

(* O4 / O6 in Mathematica for the given roots: list of <|"id", "Type", "Parity", "m0", "Dimension", "Steps", "N", "a", "b",
   "Multiplicity", "ExpansionSize", "Growth", "TwoLevelOK", "RecurrenceOK"|> ("N" = N(r, m0 + 2 s), s = 0 .. Steps) *)
tpRecurrenceData[cert_Association, sim_List, roots_List] := Module[{B = cert["B"], passes = tpPassTable[cert]},
  Table[Module[{q = tpParity[cert, r], m0, fam, dim, K, lv, seq, d0, d1, a = None, b = None, ok = False, ex, mult, total, two},
    m0 = tpRq[B, q];
    fam = Select[Keys[passes], tpParity[cert, #] == q &];
    dim = Length[fam]; K = dim + 3;
    lv = tpLengths[cert, sim, m0 + 2 K];
    seq = Table[lv[m0 + 2 s][r], {s, 0, K}];
    {d0, d1} = {seq[[2]] - seq[[1]], seq[[3]] - seq[[2]]};
    If[d0 != 0 && Divisible[d1, d0],
      a = d1/d0; b = seq[[2]] - a seq[[1]];
      ok = AllTrue[Range[K], seq[[# + 1]] == a seq[[#]] + b &]];
    ex = tpExpand2[passes, r]; mult = Lookup[ex, r, 0]; total = Total[ex];
    two = AllTrue[Range[0, K - 1], Function[s, With[{m = m0 + 2 s},
      AllTrue[fam, lv[m + 2][#] == Total[KeyValueMap[Function[{g, c}, c lv[m][g]], tpExpand2[passes, #]]] &]]]];
    <|"id" -> r, "Type" -> cert["ports"][ToString[r]]["typ"], "Parity" -> q, "m0" -> m0, "Dimension" -> dim, "Steps" -> K,
      "N" -> seq, "a" -> a, "b" -> b, "Multiplicity" -> mult, "ExpansionSize" -> total,
      "Growth" -> (mult >= 1 && total > mult), "TwoLevelOK" -> two, "RecurrenceOK" -> ok|>],
   {r, roots}]];

tpO6LeanData[recs_List] := StringJoin[
  "open TurtleO46\n\n",
  "def o6Data : List O6Root := [" <> StringRiffle["\:27e8" <> ToString[#id] <> ", " <> ToString[#a] <> ", " <> ToString[#b] <> ", " <>
    ToString[#N[[1]]] <> "\:27e9" & /@ recs, ", "] <> "]\n"];

tpO46Template[] := tpO1Template[] <> "\n" <>
  Import[FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", "TurtleO46_template.lean"}], "Text", CharacterEncoding -> "UTF-8"];

Options[LeanTurtleRecurrence] = {"Method" -> Automatic, "Name" -> Automatic, "SaveSource" -> True, "Timeout" -> 1200,
  "Perturb" -> None, "Roots" -> Automatic};
(* "Perturb" -> {"a" | "b" | "N0", rootId, d} adds d to the stated recurrence / initial length of a root, {"N", passId, d} adds d
   to the exported base length N(pass, B): negative controls, Lean must reject.  "Roots" -> Automatic uses cert["roots"].
   Result: LeanCheckResult; res["Theorem"]["Recurrence"] holds tpRecurrenceData. *)
LeanTurtleRecurrence[certFile_String?FileExistsQ, OptionsPattern[]] := Module[
  {cert, sim, roots, recs, data, name, thm, res, src, pert = OptionValue["Perturb"]},
  cert = Import[certFile, "RawJSON"];
  sim = tpBaseSimulation[cert];
  roots = Replace[OptionValue["Roots"], Automatic :> cert["roots"]];
  recs = tpRecurrenceData[cert, sim, roots];
  If[!AllTrue[recs, #Growth && #TwoLevelOK && #RecurrenceOK &],
    Print["LeanTurtleRecurrence: no growth / two-level identity / closed recurrence for roots ",
      Select[recs, !(#Growth && #TwoLevelOK && #RecurrenceOK) &][[All, "id"]]]];
  recs = Select[recs, IntegerQ[#a] && IntegerQ[#b] &];
  If[recs === {}, Print["LeanTurtleRecurrence: no root with a closed recurrence"]; Return[$Failed]];
  Which[
    MatchQ[pert, {"a" | "b", _Integer, _Integer}],
      recs = Map[If[#id == pert[[2]], Append[#, pert[[1]] -> #[pert[[1]]] + pert[[3]]], #] &, recs],
    MatchQ[pert, {"N0", _Integer, _Integer}],
      recs = Map[If[#id == pert[[2]], Append[#, "N" -> ReplacePart[#N, 1 -> #N[[1]] + pert[[3]]]], #] &, recs],
    MatchQ[pert, {"N", _Integer, _Integer}],
      sim = Map[If[#id == pert[[2]], Append[#, "N" -> #N + pert[[3]]], #] &, sim]];
  data = tpLeanData[cert] <> "\n" <> tpO1LeanData[cert, sim] <> "\n" <> tpO6LeanData[recs];
  name = OptionValue["Name"];
  If[!StringQ[name], name = "o46_" <> StringReplace[cert["prog"], Except[WordCharacter] -> "_"] <> "_verified"];
  thm[m_] := LeanTheorem[name, {}, {}, "checkO46 cert o1Data o6Data = true", "Proof" -> m,
    "Preamble" -> tpO46Template[] <> "\n" <> data,
    "DocString" -> "O4 (growth) and O6 (N(m+2) = a N(m) + b for dim M + 3 steps) of the certificate " <> FileNameTake[certFile] <>
      " (program " <> cert["prog"] <> "; " <> StringRiffle[("root " <> ToString[#id] <> ": N(" <> ToString[#m0] <> ") = " <> ToString[#N[[1]]] <>
      ", N(m+2) = " <> ToString[#a] <> " N(m) + " <> ToString[#b] <> ", " <> ToString[#Steps] <> " steps") & /@ recs, "; "] <> ")",
    "Imports" -> {}, "Data" -> <|"Certificate" -> certFile, "Program" -> cert["prog"], "Recurrence" -> recs, "Simulation" -> sim|>];
  res = tpRunMethod[thm, OptionValue["Method"], OptionValue["Timeout"]];
  If[TrueQ[OptionValue["SaveSource"]] && pert === None && Head[res] === LeanCheckResult,
    src = FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", name <> ".lean"}];
    LeanSaveSource[res["Theorem"], src]];
  res];

Print[Style["turtle_port_identities.wl: LeanTurtleRecurrence[certFile] defined (O4 / O6).", Bold]];

(* ---- O5: exit property (obligation O5 / condition (V3) of the paper), exact (same specification as verify_cert.py O5 and
   verify_cert_exact.py).  For every pass family: the affine form of the exit port of its last child, and a child edge UW
   with (i) y on the open segment phi^n0 U - phi^n0 W, (ii) the placed edge on a side of the parent, (iii)
   min(|y - phi^n0 U|, |y - phi^n0 W|) >= (1.903 + |c|)/sin 36 deg + 0.05.  Square roots are not taken in Lean:
   Mathematica supplies a rational lower bound of sin 36 deg and, for every pass family, a rational upper bound of |c|;
   Lean decides every inequality in Z[Sqrt[5]] (TurtleO5_template.lean). ---- *)

(* product in Z[zeta] (not canonicalised), complex conjugate, 4 Re(u Conjugate[v]) = A + B Sqrt[5] *)
tpZMul[k_, l_] := Table[Sum[If[Mod[i + j, 5] == m, k[[i + 1]] l[[j + 1]], 0], {i, 0, 4}, {j, 0, 4}], {m, 0, 4}];
tpConj[k_] := {k[[1]], k[[5]], k[[4]], k[[3]], k[[2]]};
tpDot4[u_, v_] := With[{w = tpZMul[u, tpConj[v]]}, {4 w[[1]] - w[[2]] - w[[3]] - w[[4]] - w[[5]], w[[2]] + w[[5]] - w[[3]] - w[[4]]}];
tpAbs[u_] := With[{d = tpDot4[u, u]}, Sqrt[(d[[1]] + d[[2]] Sqrt[5])/4]];
tpRationalUp[x_, digits_ : 6] := Ceiling[N[x, 40] 10^digits]/10^digits;
tpRationalDown[x_, digits_ : 6] := Floor[N[x, 40] 10^digits]/10^digits;
$tpSinLower = tpRationalDown[Sin[Pi/5]];

(* per pass family (sorted by id, the order of passData): c = delta_tail(b) - phi delta_tail(b) for the exit port b of the
   last child, |c| and its rational upper bound *)
tpExitData[cert_Association] := Module[{passIds = Sort[ToExpression /@ Keys[cert["passes"]]]},
  Table[Module[{p = cert["passes"][ToString[id]], b, dt, c, nc},
    b = Last[p["children"]][[3]];
    dt = cert["ports"][ToString[b]]["delta"][[1]];
    c = tpSub[dt, tpMulPhi[dt]];
    nc = tpAbs[c];
    <|"id" -> id, "Exit" -> b, "c" -> c, "Norm" -> N[nc, 20], "Upper" -> If[PossibleZeroQ[nc], 0, tpRationalUp[nc]]|>], {id, passIds}]];

(* numeric margin surplus of every pass family (best child edge on which y lies; the side condition (ii) is left to Lean) *)
tpExitSurplus[cert_Association, wit_List] := Module[{B = cert["B"], sin36 = N[Sin[Pi/5], 30]},
  Association @ Table[Module[{p = cert["passes"][ToString[w["id"]]], pin, ch, fr, n0, y, child, nd, best = -Infinity},
    pin = cert["ports"][ToString[w["id"]]];
    ch = Last[p["children"]];
    fr = tpChildFrames[pin["typ"]][[ch[[1]] + 1]];
    n0 = If[Mod[B + 1, 2] == pin["parity"], B + 1, B + 2] - 1;
    y = tpSub[tpPortAt[cert, ch[[3]], n0][[1]], w["c"]];
    child = Rest[tpStdTriangle[fr[[1]], fr[[2]]]];
    nd = (1903/1000 + w["Norm"])/sin36 + 1/20;
    Do[Module[{un = Nest[tpMulPhi, child[[i]], n0], wn = Nest[tpMulPhi, child[[Mod[i, 3] + 1]], n0], a, v, s},
       a = tpEmbed[tpSub[y, un]]; v = tpEmbed[tpSub[wn, un]];
       s = (a . v)/(v . v);
       If[Abs[a[[1]] v[[2]] - a[[2]] v[[1]]] < 10^-15 && 0 < s < 1,
         best = Max[best, Min[Norm[a], Norm[tpEmbed[tpSub[y, wn]]]] - nd]]], {i, 3}];
    w["id"] -> best], {w, wit}]];

tpO5LeanData[wit_List, sin_] := StringJoin[
  "open TurtleO5\n\n",
  "def o5SinNum : Int := ", ToString[Numerator[sin]], "\n",
  "def o5SinDen : Int := ", ToString[Denominator[sin]], "\n\n",
  "def o5Data : List Wit := [", StringRiffle["\:27e8" <> ToString[#id] <> ", " <> ToString[Numerator[#Upper]] <> ", " <>
    ToString[Denominator[#Upper]] <> "\:27e9" & /@ wit, ", "], "]\n"];

tpO5Template[] := Import[FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", "TurtleO2_template.lean"}], "Text", CharacterEncoding -> "UTF-8"] <> "\n" <>
  Import[FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", "TurtleO5_template.lean"}], "Text", CharacterEncoding -> "UTF-8"];

Options[LeanTurtleExitProperty] = {"Method" -> Automatic, "Name" -> Automatic, "SaveSource" -> True, "Timeout" -> 1200, "Perturb" -> None};
(* "Perturb" -> {"c", passId} halves the upper bound of |c| of that pass family, {"sin"} replaces the lower bound of sin 36 deg by
   3/5 (too large), {portId, "delta" | "ref", coordinate} adds 1 to one integer of a port family: negative controls, Lean must reject.
   Result: LeanCheckResult; res["Theorem"]["Witnesses"] holds tpExitData, res["Theorem"]["Surplus"] the numeric margin surpluses. *)
LeanTurtleExitProperty[certFile_String?FileExistsQ, OptionsPattern[]] := Module[
  {cert, wit, sin = $tpSinLower, surplus, data, name, thm, res, src, pert = OptionValue["Perturb"]},
  cert = tpPerturbCert[Import[certFile, "RawJSON"], pert];
  wit = tpExitData[cert];
  Which[
    MatchQ[pert, {"c", _Integer}], wit = Map[If[#id == pert[[2]], Append[#, "Upper" -> tpRationalDown[#Norm/2]], #] &, wit],
    MatchQ[pert, {"sin"}], sin = 3/5];
  surplus = tpExitSurplus[cert, wit];
  If[Min[Values[surplus]] < 0, Print["LeanTurtleExitProperty: no child edge with a positive margin for passes ",
    Keys[Select[surplus, # < 0 &]], " (Lean will reject)"]];
  data = tpLeanData[cert] <> "\n" <> tpO5LeanData[wit, sin];
  name = OptionValue["Name"];
  If[!StringQ[name], name = "o5_" <> StringReplace[cert["prog"], Except[WordCharacter] -> "_"] <> "_verified"];
  thm[m_] := LeanTheorem[name, {}, {}, "checkO5 cert o5SinNum o5SinDen o5Data = true", "Proof" -> m,
    "Preamble" -> tpO5Template[] <> "\n" <> data,
    "DocString" -> "O5 (exit property, exact in Z[sqrt 5]) of the certificate " <> FileNameTake[certFile] <> " (program " <> cert["prog"] <>
      ", " <> ToString[Length[wit]] <> " pass families; smallest numeric margin surplus " <> ToString[NumberForm[Min[Values[surplus]], 4]] <> ")",
    "Imports" -> {}, "Data" -> <|"Certificate" -> certFile, "Program" -> cert["prog"], "Witnesses" -> wit, "Surplus" -> surplus, "SinLower" -> sin|>];
  res = tpRunMethod[thm, OptionValue["Method"], OptionValue["Timeout"]];
  If[TrueQ[OptionValue["SaveSource"]] && pert === None && Head[res] === LeanCheckResult,
    src = FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", name <> ".lean"}];
    LeanSaveSource[res["Theorem"], src]];
  res];

Print[Style["turtle_port_identities.wl: LeanTurtleExitProperty[certFile] defined (O5).", Bold]];

(* ---- Theorem U(1) as one Lean theorem (lean/turtle/CheckerSoundness.lean, Mathlib).  The decided Bool checks (frames/O2/O3,
   O1, O4/O6, side conditions) are joined by soundness lemmas to the induction H(m) on the concrete pass system of the
   certificate (PassInduction.lean) and to Cayley-Hamilton (CayleyHamiltonRecurrence.lean).  The source is: every `import`
   first, then TurtleO2 + TurtleO1 + TurtleO46 templates, PassInduction, CayleyHamiltonRecurrence, CheckerSoundness, the
   certificate data and the final theorem of each root.  Axioms of the final theorem: TurtleGeom.edgeUnique (non-overlap of
   the owned rhombs of a supertile) and TurtleGeom.exitProperty_<certificate> (Lemma 2), besides propext, Classical.choice,
   Quot.sound. ---- *)

tpLeanFile[f_String] := Import[FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", f}], "Text", CharacterEncoding -> "UTF-8"];

(* concatenate Lean parts: every `import` line first (deduplicated, in order), then the bodies *)
tpAssembleLean[parts_List] := Module[{lines, imps, bodies},
  lines = StringSplit[StringReplace[#, "\r\n" -> "\n"], "\n", All] & /@ parts;
  imps = DeleteDuplicates[StringTrim /@ Select[Flatten[lines], StringStartsQ[#, "import "] &]];
  bodies = StringTrim[StringRiffle[Select[#, !StringStartsQ[#, "import "] &], "\n"], "\n" ..] & /@ lines;
  StringRiffle[imps, "\n"] <> "\n\n" <> StringRiffle[bodies, "\n\n"] <> "\n"];

(* the generic part (checkers, logic, soundness; no certificate data) *)
LeanTurtleSoundnessSource[] := tpAssembleLean[{tpLeanFile["TurtleO2_template.lean"], tpLeanFile["TurtleO1_template.lean"],
  tpLeanFile["TurtleO46_template.lean"], "section\n\n" <> tpLeanFile["PassInduction.lean"] <> "\n\nend",
  "section\n\n" <> tpLeanFile["CayleyHamiltonRecurrence.lean"] <> "\n\nend", tpLeanFile["CheckerSoundness.lean"]}];

tpLeanInt[n_Integer] := If[n < 0, "(" <> ToString[n] <> ")", ToString[n]];

(* the checks, the Lemma 2 axiom and the final theorem of each root *)
tpUnboundedFinal[certName_String, B_Integer, recs_List] := Module[{one = Length[recs] == 1, thm},
  thm[rec_] := Module[{id = ToString[rec["id"]], m0 = ToString[rec["m0"]], q = ToString[rec["Parity"]],
      name = "TurtleUnbounded." <> certName <> If[one, "", "_root" <> ToString[rec["id"]]],
      S = "(turtleSystem cert prog o1Data)"},
    StringJoin[
      "/-- **Theorem U(1), certificate ", certName, ", root ", id, "** (parity ", q, ", first level ", m0, ").  In the model `turtleSystem cert prog o1Data`\n",
      "(points of Z[\:03b6], supertiles \:03c3^m of the standard triangles, owned rhombs, the turtle step): the root's pass has N(", m0, ") = ",
      ToString[First[rec["N"]]], " S-moves and N(m+2) = ", ToString[rec["a"]], " N(m) + ", ToString[rec["b"]], " at every level m \:2265 ", m0,
      " of its parity\nclass (checked for dim M + 3 = ", ToString[rec["Steps"]], " steps, extended by Cayley\:2013Hamilton); for every M there is a level m at which the pass, in the\n",
      "standard supertile X and in every isometric copy g X, has more than M S-moves inside the owned rhombs and ends with an exit; for every\n",
      "injective crossing map F that agrees with the turtle step of g X on crossings into its owned rhombs, the orbit of the entry crossing\n",
      "has no repetition within M crossings (the orbit is infinite or its period exceeds M S-moves). -/\n",
      "theorem ", name, " :\n",
      "    \:2203 \:03c1 : ", S, ".Fam, \:03c1.1 = ", id, " \:2227\n",
      "      ", S, ".N \:03c1 ", m0, " = ", ToString[First[rec["N"]]], " \:2227\n",
      "      (\:2200 s, ((", S, ".N \:03c1 (", m0, " + 2 * s + 2) : \:2115) : \:2124) = ", tpLeanInt[rec["a"]], " * ((", S, ".N \:03c1 (", m0, " + 2 * s) : \:2115) : \:2124) + ", tpLeanInt[rec["b"]], ") \:2227\n",
      "      \:2200 M : \:2115, \:2203 m, ", ToString[B], " \:2264 m \:2227 M < ", S, ".N \:03c1 m \:2227\n",
      "        ", S, ".Seg (", S, ".std (", S, ".typ \:03c1) m) (", S, ".portIn \:03c1 m) (", S, ".N \:03c1 m) (", S, ".portOut \:03c1 m) \:2227\n",
      "        \:00ac ", S, ".owned (", S, ".std (", S, ".typ \:03c1) m) (", S, ".enters (", S, ".portOut \:03c1 m)) \:2227\n",
      "        \:2200 (g : ", S, ".Iso) (F : Crs \:2192 Crs), Function.Injective F \:2192\n",
      "          (\:2200 x, ", S, ".owned (", S, ".actT g (", S, ".std (", S, ".typ \:03c1) m)) (", S, ".enters x) \:2192\n",
      "            F x = ", S, ".next (", S, ".actT g (", S, ".std (", S, ".typ \:03c1) m)) x) \:2192\n",
      "          \:2200 i j, i < j \:2192 F^[i] (", S, ".actC g (", S, ".portIn \:03c1 m)) = F^[j] (", S, ".actC g (", S, ".portIn \:03c1 m)) \:2192 M < j - i := by\n",
      "  have hr : (\:27e8", id, ", ", tpLeanInt[rec["a"]], ", ", tpLeanInt[rec["b"]], ", ", ToString[First[rec["N"]]], "\:27e9 : O6Root) \:2208 o6Data := by simp [o6Data]\n",
      "  obtain \:27e8\:03c1, h\:03c1, hU\:27e9 := unbounded cert prog o1Data o6Data TurtleUnbounded.checkCertificate_ok\n",
      "    TurtleUnbounded.checkO1_ok TurtleUnbounded.checkO46_ok TurtleUnbounded.checkSide_ok\n",
      "    TurtleGeom.exitProperty_", certName, " _ hr\n",
      "  obtain \:27e8hN0, -\:27e9 := root_recurrence cert o1Data o6Data TurtleUnbounded.checkCertificate_ok\n",
      "    TurtleUnbounded.checkO46_ok _ hr\n",
      "  have hrec := root_recurrence_all cert o1Data o6Data TurtleUnbounded.checkCertificate_ok\n",
      "    TurtleUnbounded.checkO46_ok TurtleUnbounded.checkSide_ok _ hr\n",
      "  obtain \:27e8hpar, hB, hR\:27e9 := TurtleUnbounded.root_data_", id, "\n",
      "  simp only at h\:03c1 hN0 hrec\n",
      "  rw [hpar, hB, hR] at hN0 hrec\n",
      "  refine \:27e8\:03c1, h\:03c1, ?_, ?_, fun M => ?_\:27e9\n",
      "  \:00b7 rw [\:2190 NId_fam cert prog o1Data \:03c1, h\:03c1]\n",
      "    exact hN0\n",
      "  \:00b7 intro s\n",
      "    rw [\:2190 NId_fam cert prog o1Data \:03c1, \:2190 NId_fam cert prog o1Data \:03c1, h\:03c1]\n",
      "    exact hrec s\n",
      "  \:00b7 obtain \:27e8m, hm, h\:27e9 := hU M\n",
      "    exact \:27e8m, by rw [\:2190 hB]; exact hm, h\:27e9\n"]];
  StringJoin[
    "\n/-! ## ", certName, ": the checks, Lemma 2, and Theorem U(1) -/\n\n",
    "section\nopen TurtleO2 TurtleO1 TurtleO46 TurtleSound\n\n",
    "/-- frames, port deltas, O3 and O2 -/\ntheorem TurtleUnbounded.checkCertificate_ok : checkCertificate cert = true := by decide +kernel\n\n",
    "/-- O1: the base simulation at level ", ToString[B], " -/\ntheorem TurtleUnbounded.checkO1_ok : checkO1 cert prog o1Data = true := by decide +kernel\n\n",
    "/-- O4 and O6 of the roots -/\ntheorem TurtleUnbounded.checkO46_ok : checkO46 cert o1Data o6Data = true := by decide +kernel\n\n",
    "/-- the side conditions (standard frames, parities 0/1, entry ports in the key range of the O1 table) -/\n",
    "theorem TurtleUnbounded.checkSide_ok : checkSide cert o1Data = true := by decide +kernel\n\n",
    StringRiffle[Table["/-- root " <> ToString[rec["id"]] <> ": parity, base level, first level of its class -/\ntheorem TurtleUnbounded.root_data_" <>
      ToString[rec["id"]] <> " : portParity cert " <> ToString[rec["id"]] <> " = " <> ToString[rec["Parity"]] <> " \:2227 cert.B = " <> ToString[B] <>
      " \:2227 Rq " <> ToString[B] <> " " <> ToString[rec["Parity"]] <> " = " <> ToString[rec["m0"]] <> " := by\n  decide +kernel\n", {rec, recs}], "\n"],
    "\nend\n\n",
    "/-- **Axiom (Lemma 2 for ", certName, ", the exit property).**  For every level m \:2265 ", ToString[B], ", given H(m), the exit crossing of the\n",
    "last child of every pass family of parity m + 1, placed in the parent's standard supertile of level m + 1, leads to a rhomb\n",
    "not owned by the parent.  `proof_unbounded.md` proves it from O5 (conditions (i)\:2013(iii), checked in Lean by\n",
    "`TurtleO5_template.lean`, `LeanTurtleExitProperty`) and plane geometry (a ball around the exit point meets the parent\n",
    "triangle only inside the child). -/\n",
    "axiom TurtleGeom.exitProperty_", certName, " : TurtleSound.ExitProperty cert prog o1Data\n\n",
    "section\nopen TurtleO2 TurtleO1 TurtleO46 TurtleSound\n\n",
    StringRiffle[thm /@ recs, "\n"],
    "\nend\n"]];

Options[LeanTurtleUnbounded] = {"Name" -> Automatic, "SaveSource" -> True, "Timeout" -> 1800, "Perturb" -> None, "Roots" -> Automatic};
(* Theorem U(1) for the roots of a certificate as one Lean theorem (`decide +kernel` for the checks; Mathlib).  "Perturb" -> {"a" | "b" |
   "N0", rootId, d} or {"N", passId, d} as in LeanTurtleRecurrence: negative controls, Lean must reject.  Result: LeanCheckResult with
   "Recurrence" (tpRecurrenceData), "Theorems" (the final theorem names) and, when saved, "SourceFile". *)
LeanTurtleUnbounded[certFile_String?FileExistsQ, OptionsPattern[]] := Module[
  {cert, sim, roots, recs, certName, data, src, name, res, file, pert = OptionValue["Perturb"], finals},
  cert = Import[certFile, "RawJSON"];
  sim = tpBaseSimulation[cert];
  roots = Replace[OptionValue["Roots"], Automatic :> cert["roots"]];
  recs = Select[tpRecurrenceData[cert, sim, roots], IntegerQ[#a] && IntegerQ[#b] &];
  If[recs === {}, Print["LeanTurtleUnbounded: no root with a closed recurrence"]; Return[$Failed]];
  Which[
    MatchQ[pert, {"a" | "b", _Integer, _Integer}],
      recs = Map[If[#id == pert[[2]], Append[#, pert[[1]] -> #[pert[[1]]] + pert[[3]]], #] &, recs],
    MatchQ[pert, {"N0", _Integer, _Integer}],
      recs = Map[If[#id == pert[[2]], Append[#, "N" -> ReplacePart[#N, 1 -> #N[[1]] + pert[[3]]]], #] &, recs],
    MatchQ[pert, {"N", _Integer, _Integer}],
      sim = Map[If[#id == pert[[2]], Append[#, "N" -> #N + pert[[3]]], #] &, sim]];
  certName = StringReplace[FileBaseName[certFile], Except[WordCharacter] -> "_"];
  data = tpLeanData[cert] <> "\n" <> tpO1LeanData[cert, sim] <> "\n" <> tpO6LeanData[recs];
  src = tpAssembleLean[{LeanTurtleSoundnessSource[], data, tpUnboundedFinal[certName, cert["B"], recs]}];
  name = OptionValue["Name"];
  If[!StringQ[name], name = "unbounded_" <> StringReplace[cert["prog"], Except[WordCharacter] -> "_"] <> "_verified"];
  finals = Table["TurtleUnbounded." <> certName <> If[Length[recs] == 1, "", "_root" <> ToString[r["id"]]], {r, recs}];
  res = LeanCheck[src, "Mathlib" -> True, "FileName" -> name, "Timeout" -> OptionValue["Timeout"]];
  If[Head[res] =!= LeanCheckResult, Return[res]];
  res = LeanCheckResult[Join[First[res], <|"Recurrence" -> recs, "FinalTheorems" -> finals, "Certificate" -> certFile|>]];
  If[TrueQ[OptionValue["SaveSource"]] && pert === None,
    file = FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", name <> ".lean"}];
    If[FileExistsQ[file], DeleteFile[file]];
    BinaryWrite[file, StringToByteArray[src, "UTF-8"]]; Close[file];
    res = LeanCheckResult[Append[First[res], "SourceFile" -> file]]];
  res];

Print[Style["turtle_port_identities.wl: LeanTurtleUnbounded[certFile] defined (Theorem U(1), CheckerSoundness.lean).", Bold]];
