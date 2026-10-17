(* ::Package:: *)
(* ============================================================ *)
(*  LeanAssist.wl                                                *)
(*  Lean 4 assisted proofs from the Wolfram Language.            *)
(*                                                              *)
(*  Layers:                                                     *)
(*   1. toolchain  -- run `lean` / `lake env lean` (Mathlib),    *)
(*      parse the diagnostics, detect `sorry`, print the axioms  *)
(*      every theorem depends on  (LeanCheck)                    *)
(*   2. theorems   -- WL expressions -> Lean source (LeanForm,   *)
(*      LeanTheorem, LeanSource, LeanProve)                      *)
(*   3. certificates -- polynomial identities: Mathematica      *)
(*      computes the cofactors (Groebner basis, tag variables),  *)
(*      Lean verifies them with `linear_combination` / `ring`    *)
(*   4. geometry   -- GeometricScene hypotheses / conclusions    *)
(*      -> coordinate polynomials -> certificate -> Lean theorem *)
(*   5. data       -- WL data as Lean definitions for `decide`   *)
(*      style checks of finite certificates (CA / turtle proofs) *)
(*                                                              *)
(*  Requires: Lean 4 toolchain installed by elan.  Mathlib is   *)
(*  used through an existing Lake project ($LeanAssistMathlib-  *)
(*  Directory, default ~/src/mathlib4).  Wolfram/LeanLink is     *)
(*  optional (LeanLinkImport).                                   *)
(*  2026-10-16  K. Imai (with Claude)                             *)
(* ============================================================ *)

BeginPackage["LeanAssist`"];

(* --- configuration --- *)
$LeanAssistDirectory::usage = "$LeanAssistDirectory: LeanAssist_info folder (lean/ templates, docs, examples).";
$LeanAssistWorkDirectory::usage = "$LeanAssistWorkDirectory: folder for generated .lean files, command files and compiler output (default $TemporaryDirectory/LeanAssist).";
$LeanAssistToolchain::usage = "$LeanAssistToolchain: elan toolchain name used for Mathlib-free compiles (default: the toolchain of the Wolfram/LeanLink paclet, leanprover/lean4:v4.30.0).";
$LeanAssistMathlibDirectory::usage = "$LeanAssistMathlibDirectory: Lake project that has Mathlib built (default ~/src/mathlib4). Sources importing Mathlib are compiled with `lake env lean` in this project.";
$LeanAssistTimeout::usage = "$LeanAssistTimeout: default time limit (seconds) of one Lean compile (600).";
LeanAssistStatus::usage = "LeanAssistStatus[] returns a Dataset describing the Lean toolchain, the Mathlib project and LeanLink as seen by LeanAssist.";
LeanToolchainBinary::usage = "LeanToolchainBinary[\"lean\"] / LeanToolchainBinary[\"lake\"] returns the path of the executable used by LeanAssist.";

(* --- checking --- *)
LeanCheck::usage = "LeanCheck[src] compiles the Lean 4 source string src and returns a LeanCheckResult with the parsed diagnostics, the axioms of every theorem (#print axioms) and the `sorry` status. LeanCheck[thm] / LeanCheck[{thm1, thm2, ...}] checks LeanTheorem objects. Options: \"Mathlib\" -> Automatic (use the Mathlib project when the source imports Mathlib), \"Timeout\", \"Axioms\" -> True, \"KeepFiles\" -> False, \"FileName\", \"Directory\".";
LeanCheckFile::usage = "LeanCheckFile[file] compiles an existing .lean file (same options and result as LeanCheck).";
LeanCheckResult::usage = "LeanCheckResult[assoc] is the result of LeanCheck. Properties: \"Status\" (\"Proved\" | \"OK\" | \"Sorry\" | \"Failed\" | \"Timeout\" | \"Error\"), \"Success\", \"Theorems\", \"TheoremStatus\", \"Axioms\", \"Sorries\", \"Errors\", \"Warnings\", \"Messages\", \"Output\", \"Time\", \"Source\", \"File\", \"Dataset\".";
LeanDiagnostics::usage = "LeanDiagnostics[result] returns the compiler messages of a LeanCheckResult as a Dataset (Line, Column, Severity, Message).";
LeanProve::usage = "LeanProve[thm] generates the source of a LeanTheorem (or a list of theorems), compiles it and returns the LeanCheckResult (result[\"Theorem\"] / result[\"TheoremStatus\"]). Same options as LeanCheck.";

(* --- source generation --- *)
LeanForm::usage = "LeanForm[expr] renders a Wolfram Language expression (polynomials, rational expressions, Equal, Unequal, inequalities, And/Or/Not/Implies, ForAll/Exists, Abs, Min/Max, If/Boole, Sqrt) as Lean 4 source text. Strings are passed through unchanged.";
LeanIdentifier::usage = "LeanIdentifier[sym] returns the Lean identifier used for a symbol (Subscript[x, 1] -> x_1, $ -> _).";
LeanLiteral::usage = "LeanLiteral[data] renders integers, rationals, booleans, strings, lists ([...]) and LeanTuple[...] ((...)) as Lean literals.";
LeanTuple::usage = "LeanTuple[a, b, ...] marks a tuple for LeanLiteral / LeanDataDefinitions (rendered as (a, b, ...), type A \[Times] B \[Times] ...).";
LeanDataDefinitions::usage = "LeanDataDefinitions[<|\"name\" -> data, ...|>] returns Lean `def` declarations for WL data (Int, Bool, String, List, tuples) with inferred types, for `decide`-style checks of finite certificates. Option \"Types\" -> <|\"name\" -> \"type\"|> overrides the inferred type.";
LeanTheorem::usage = "LeanTheorem[name, vars, hyps, concl, opts] builds a theorem object. vars: symbols (type \"\[DoubleStruckCapitalR]\" by default), sym -> \"Int\", {x, y} -> \"Nat\" or raw strings \"x : \[DoubleStruckCapitalR]\"; hyps: WL propositions, \"h\" -> prop, or raw Lean strings; concl: proposition or raw string. Options: \"Proof\" -> tactic text (\"sorry\"), \"Type\" -> default variable type, \"Imports\" -> Automatic | list, \"Preamble\" -> Lean text placed before the theorem, \"DocString\", \"Namespace\". LeanTheorem[thm, opts] returns a modified copy. thm[\"Source\"], thm[\"Name\"], thm[\"Proof\"], ... access the fields.";
LeanSource::usage = "LeanSource[thm] / LeanSource[{thm1, ...}] returns the Lean 4 source (imports, preamble, theorems) of LeanTheorem objects.";
LeanSaveSource::usage = "LeanSaveSource[thm, file] writes LeanSource[thm] to file (UTF-8) and returns the path. LeanSaveSource[thm] uses $LeanAssistDirectory/lean/<name>.lean.";

(* --- polynomial certificates --- *)
LeanPolynomialCertificate::usage = "LeanPolynomialCertificate[goal, {h1, h2, ...}, vars] searches polynomials c_i (and a factor d built from the \"NonDegenerate\" polynomials) with d goal == Sum c_i h_i, using a Groebner basis with tag variables. goal and h_i may be given as polynomials or equations lhs == rhs. Returns an Association (\"Found\", \"Coefficients\", \"Factor\", \"FactorExponents\", \"Verified\", \"Inconsistent\"). Options: \"NonDegenerate\" -> {d1, ...} (polynomials assumed nonzero), \"MaxExponent\" -> 3.";
LeanLinearCombination::usage = "LeanLinearCombination[cert, {\"h1\", \"h2\", ...}] returns the `linear_combination` tactic text of a certificate (\"ring\" when no hypothesis is needed).";
LeanPolynomialProof::usage = "LeanPolynomialProof[cert, hypNames, ndNames] returns the complete tactic script of a certificate: linear_combination, or `have` + mul_eq_zero when a nondegeneracy factor is involved. ndNames are the Lean names of the hypotheses d_j \[NotEqual] 0 in the order of cert[\"NonDegenerate\"].";
LeanPolynomialTheorem::usage = "LeanPolynomialTheorem[name, vars, {h1 == 0, ...}, goal, opts] builds a LeanTheorem over \[DoubleStruckCapitalR] whose proof is the certificate found by LeanPolynomialCertificate (goal may be a list: conjunction). Options: \"NonDegenerate\" -> {d1, ...} (become hypotheses d_j \[NotEqual] 0), \"MaxExponent\", \"Type\", and the options of LeanTheorem. thm[\"Certificates\"] holds the certificates.";

(* --- geometry --- *)
LeanGeometryCoordinates::usage = "LeanGeometryCoordinates[points] assigns symbolic coordinates {xP, yP} to point symbols. Option \"Normalize\" -> True puts the first point at the origin and the second on the x axis (an isometry: valid for every Euclidean-invariant statement).";
LeanGeometryPolynomials::usage = "LeanGeometryPolynomials[scene] translates the hypotheses of a GeometricScene into polynomial equations in the coordinates. Returns an Association with \"Coordinates\", \"Variables\", \"Parameters\", \"Hypotheses\" (one record per hypothesis), \"Polynomials\", \"NonDegenerate\", \"Unsupported\", \"Caveats\". Options: \"Normalize\" -> True, \"Parametric\" -> True (points defined by Midpoint / Centroid / Element[p, Line[...]] are substituted: p = a + t (b - a)), \"Coordinates\" -> <|p -> {x, y}|> fixed coordinates.";
LeanGeometryStatement::usage = "LeanGeometryStatement[concl, geo] translates a geometric conclusion (the vocabulary of GeometricScene plus SignedRatio) into polynomials in the coordinates of geo = LeanGeometryPolynomials[scene]. Rational conclusions give a numerator polynomial and nondegeneracy conditions (denominators).";
LeanGeometryTheorem::usage = "LeanGeometryTheorem[scene, concl, opts] builds a LeanTheorem for a GeometricScene and a conclusion: coordinates, hypothesis polynomials, nondegeneracy conditions, certificate (Mathematica) and the Lean proof. The translation is checked numerically on a RandomInstance. Options: \"Name\", \"NonDegenerate\" -> extra conditions, \"MaxExponent\", \"Normalize\", \"Parametric\", \"InstanceCheck\" -> True. thm[\"Geometry\"], thm[\"Statement\"], thm[\"Certificates\"], thm[\"InstanceCheck\"] give the details.";
LeanGeometryReport::usage = "LeanGeometryReport[scene, concl, opts] shows a RandomInstance of the scene, the generated Lean theorem and the result of the Lean check (options of LeanGeometryTheorem and LeanCheck).";
LeanGeometryConjectures::usage = "LeanGeometryConjectures[scene] runs FindGeometricConjectures and tries to prove every conjecture in Lean. Returns a Dataset (Conjecture, Status, Caveats, Theorem). Option \"Prove\" -> False only searches the certificates.";
SignedRatio::usage = "SignedRatio[a, p, b] denotes the signed ratio ap/pb of the point p on the line ab (t/(1 - t) for p = a + t (b - a)), for use in conclusions of LeanGeometryTheorem (Menelaus, Ceva, Euler line).";

(* --- LeanLink bridge --- *)
LeanLinkImport::usage = "LeanLinkImport[thm | src] compiles a Mathlib-free source with Wolfram`LeanLink`LeanImportString and returns the LeanEnvironment (expression graphs, tactic states of LeanLink).";

Begin["`Private`"];

(* ------------------------------------------------------------ *)
(*  configuration                                                *)
(* ------------------------------------------------------------ *)

$laPackageDir = DirectoryName[$InputFileName];
If[$laPackageDir === "" || $laPackageDir === None,
  $laPackageDir = Quiet @ Check[Global`$packageDirectory, Directory[]]];
$LeanAssistDirectory = FileNameJoin[{$laPackageDir, "LeanAssist_info"}];
$LeanAssistWorkDirectory = FileNameJoin[{$TemporaryDirectory, "LeanAssist"}];
$LeanAssistTimeout = 600;
$LeanAssistMathlibDirectory = With[{d = FileNameJoin[{$HomeDirectory, "src", "mathlib4"}]},
  If[DirectoryQ[d], d, None]];
$LeanAssistToolchain = Automatic;
$laExe = If[$OperatingSystem === "Windows", ".exe", ""];

laElanHome[] := With[{e = Environment["ELAN_HOME"]},
  If[StringQ[e] && DirectoryQ[e], e, FileNameJoin[{$HomeDirectory, ".elan"}]]];

(* toolchain name: $LeanAssistToolchain, else the LeanLink paclet's lean-toolchain, else the Mathlib project's, else v4.30.0 *)
laToolchainName[] := Module[{tc = $LeanAssistToolchain, f, pac},
  If[StringQ[tc], Return[tc]];
  pac = Quiet @ Check[PacletObject["Wolfram/LeanLink"]["Location"], $Failed];
  If[StringQ[pac],
    f = FileNameJoin[{pac, "lean-toolchain"}];
    If[FileExistsQ[f], Return[StringTrim[Import[f, "Text"]]]]];
  If[StringQ[$LeanAssistMathlibDirectory],
    f = FileNameJoin[{$LeanAssistMathlibDirectory, "lean-toolchain"}];
    If[FileExistsQ[f], Return[StringTrim[Import[f, "Text"]]]]];
  "leanprover/lean4:v4.30.0"];

laToolchainDir[] := FileNameJoin[{laElanHome[], "toolchains",
  StringReplace[laToolchainName[], {"/" -> "--", ":" -> "---"}]}];

LeanToolchainBinary["lean"] := With[{b = FileNameJoin[{laToolchainDir[], "bin", "lean" <> $laExe}]},
  If[FileExistsQ[b], b, FileNameJoin[{laElanHome[], "bin", "lean" <> $laExe}]]];
LeanToolchainBinary["lake"] := FileNameJoin[{laElanHome[], "bin", "lake" <> $laExe}];

laMathlibReadyQ[] := StringQ[$LeanAssistMathlibDirectory] && DirectoryQ[$LeanAssistMathlibDirectory] &&
  DirectoryQ[FileNameJoin[{$LeanAssistMathlibDirectory, ".lake", "packages", "mathlib", ".lake", "build"}]];

LeanAssistStatus[] := Module[{lean = LeanToolchainBinary["lean"], lake = LeanToolchainBinary["lake"], ver, ll},
  ver = If[FileExistsQ[lean], Quiet @ Check[StringTrim[RunProcess[{lean, "--version"}, "StandardOutput"]], "?"], Missing["NotFound"]];
  ll = Quiet @ Check[PacletObject["Wolfram/LeanLink"]["Version"], Missing["NotInstalled"]];
  Dataset[<|
    "Toolchain" -> laToolchainName[],
    "LeanBinary" -> lean,
    "LeanVersion" -> ver,
    "LakeBinary" -> If[FileExistsQ[lake], lake, Missing["NotFound"]],
    "MathlibDirectory" -> $LeanAssistMathlibDirectory,
    "MathlibReady" -> laMathlibReadyQ[],
    "LeanLinkPaclet" -> ll,
    "LeanLinkLoaded" -> MemberQ[$Packages, "Wolfram`LeanLink`"],
    "WorkDirectory" -> $LeanAssistWorkDirectory,
    "Timeout" -> $LeanAssistTimeout|>]];

(* ------------------------------------------------------------ *)
(*  running lean                                                 *)
(* ------------------------------------------------------------ *)

LeanCheck::nolean = "Lean executable not found: `1`. Install the toolchain `2` with elan (elan toolchain install `2`).";
LeanCheck::nomathlib = "The source imports Mathlib but no Mathlib project is available ($LeanAssistMathlibDirectory = `1`).";
LeanCheck::timeout = "Lean did not finish within `1` seconds; the process was killed.";

Options[LeanCheck] = {"Mathlib" -> Automatic, "Timeout" -> Automatic, "Axioms" -> True,
  "KeepFiles" -> False, "FileName" -> Automatic, "Directory" -> Automatic};
Options[LeanCheckFile] = Options[LeanCheck];
Options[LeanProve] = Options[LeanCheck];

laWriteUTF8[file_, s_String] := (
  If[!DirectoryQ[DirectoryName[file]], CreateDirectory[DirectoryName[file]]];
  BinaryWrite[file, StringToByteArray[s, "UTF-8"]]; Close[file]; file);
laReadUTF8[file_] := If[FileExistsQ[file], ByteArrayToString[ReadByteArray[file], "UTF-8"], ""];
laWinPath[p_String] := If[$OperatingSystem === "Windows", StringReplace[p, "/" -> "\\"], p];
laQ[s_String] := "\"" <> s <> "\"";

(* declared theorem names (theorem / lemma; `example` is anonymous) *)
laTheoremNames[src_String] := StringCases[src,
  RegularExpression["(?m)^(?:@\\[[^\\]]*\\]\\s*)?(?:protected\\s+|private\\s+|noncomputable\\s+)*(?:theorem|lemma)\\s+([^\\s:({\\[]+)"] :> "$1"];

laImportsMathlibQ[src_String] := StringContainsQ[src, RegularExpression["(?m)^import\\s+Mathlib"]];

(* run a command line (list of strings) with cwd, output to a file, time limit; returns <|"ExitCode", "Output", "Time", "TimedOut"|> *)
laRunToFile[cmd_List, cwd_, outFile_, timeout_] := Module[{cmdFile, proc, t0, status, exit, timedOut = False, pid},
  cmdFile = FileNameJoin[{DirectoryName[outFile], FileBaseName[outFile] <> If[$OperatingSystem === "Windows", ".cmd", ".sh"]}];
  If[$OperatingSystem === "Windows",
    laWriteUTF8[cmdFile, "@echo off\r\n" <> StringRiffle[laQ[laWinPath[#]] & /@ cmd, " "] <>
      " > " <> laQ[laWinPath[outFile]] <> " 2>&1\r\nexit /b %ERRORLEVEL%\r\n"];
    proc = StartProcess[{"cmd.exe", "/c", laWinPath[cmdFile]}, ProcessDirectory -> cwd],
    laWriteUTF8[cmdFile, "#!/bin/sh\n" <> StringRiffle[laQ /@ cmd, " "] <> " > " <> laQ[outFile] <> " 2>&1\n"];
    proc = StartProcess[{"/bin/sh", cmdFile}, ProcessDirectory -> cwd]];
  t0 = AbsoluteTime[];
  While[ProcessStatus[proc] === "Running" && AbsoluteTime[] - t0 < timeout, Pause[0.1]];
  If[ProcessStatus[proc] === "Running",
    timedOut = True;
    pid = Quiet @ Check[ProcessInformation[proc]["PID"], None];
    If[$OperatingSystem === "Windows" && IntegerQ[pid],
      Quiet @ RunProcess[{"taskkill", "/PID", ToString[pid], "/T", "/F"}]];
    Quiet @ KillProcess[proc]];
  exit = Quiet @ Check[ProcessInformation[proc]["ExitCode"], None];
  status = <|"ExitCode" -> exit, "Output" -> laReadUTF8[outFile], "Time" -> AbsoluteTime[] - t0,
    "TimedOut" -> timedOut, "CommandFile" -> cmdFile|>;
  status];

(* parse lean output: message blocks + axioms lines *)
laParseOutput[out_String] := Module[{lines, blocks = {}, cur = None, axioms = <||>, hdr, m, rest = {}},
  (* Lean wraps a long axiom list over several lines ("depends on axioms: [propext,\n Classical.choice, ...]"): join them
     first, otherwise the axioms of that theorem (sorryAx included) would be missed *)
  lines = StringSplit[FixedPoint[
    StringReplace[#, RegularExpression["(depends on axioms: \\[[^\\]\\n]*)\\r?\\n\\s*"] :> "$1 "] &, out], "\n"];
  Do[
    hdr = StringCases[ln, RegularExpression["^(.*?\\.lean):(\\d+):(\\d+): (error|warning|info)(?:\\([^)]*\\))?: ?(.*)$"] :>
      {"$1", "$2", "$3", "$4", "$5"}];
    Which[
      hdr =!= {},
      If[cur =!= None, AppendTo[blocks, cur]];
      m = First[hdr];
      cur = <|"Line" -> ToExpression[m[[2]]], "Column" -> ToExpression[m[[3]]], "Severity" -> m[[4]], "Message" -> m[[5]]|>,
      (* names may end with primes (foo'), so the name is \S+ rather than [^']+ *)
      StringMatchQ[ln, RegularExpression["^'\\S+' depends on axioms: .*$"]],
      If[cur =!= None, AppendTo[blocks, cur]; cur = None];
      With[{p = StringCases[ln, RegularExpression["^'(\\S+)' depends on axioms: \\[(.*)\\]"] :> {"$1", "$2"}]},
        If[p =!= {}, axioms[p[[1, 1]]] = StringTrim /@ StringSplit[p[[1, 2]], ","]]],
      StringMatchQ[ln, RegularExpression["^'\\S+' does not depend on any axioms$"]],
      If[cur =!= None, AppendTo[blocks, cur]; cur = None];
      axioms[First @ StringCases[ln, RegularExpression["^'(\\S+)' does not depend"] :> "$1"]] = {},
      cur =!= None,
      cur["Message"] = StringTrim[cur["Message"] <> "\n" <> ln, "\n"],
      True, AppendTo[rest, ln]],
    {ln, lines}];
  If[cur =!= None, AppendTo[blocks, cur]];
  <|"Messages" -> blocks, "Axioms" -> axioms, "Other" -> StringRiffle[rest, "\n"]|>];

LeanCheck[src_String, OptionsPattern[]] := Module[
  {mathlib, timeout, axioms, keep, dir, name, file, outFile, names, src2, lean, lake, cmd, cwd, run, parsed,
   msgs, errors, warnings, sorries, status, ranges, thmStatus, res},
  mathlib = OptionValue["Mathlib"]; If[mathlib === Automatic, mathlib = laImportsMathlibQ[src]];
  timeout = OptionValue["Timeout"]; If[!NumericQ[timeout], timeout = $LeanAssistTimeout];
  axioms = TrueQ[OptionValue["Axioms"]]; keep = TrueQ[OptionValue["KeepFiles"]];
  dir = OptionValue["Directory"]; If[!StringQ[dir], dir = $LeanAssistWorkDirectory];
  If[!DirectoryQ[dir], CreateDirectory[dir]];
  name = OptionValue["FileName"];
  If[!StringQ[name], name = "LeanAssist_" <> IntegerString[Hash[src, "SHA256"], 36, 12]];
  name = StringReplace[FileBaseName[name], Except[WordCharacter | "_"] -> "_"];
  file = FileNameJoin[{dir, name <> ".lean"}]; outFile = FileNameJoin[{dir, name <> ".out.txt"}];
  names = laTheoremNames[src];
  src2 = src;
  If[axioms && names =!= {},
    src2 = StringTrim[src, "\n"] <> "\n\n" <> StringRiffle["#print axioms " <> # & /@ names, "\n"] <> "\n"];
  laWriteUTF8[file, src2];
  lean = LeanToolchainBinary["lean"]; lake = LeanToolchainBinary["lake"];
  If[mathlib,
    If[!laMathlibReadyQ[], Message[LeanCheck::nomathlib, $LeanAssistMathlibDirectory]; Return[$Failed]];
    cmd = {lake, "env", "lean", file}; cwd = $LeanAssistMathlibDirectory,
    If[!FileExistsQ[lean], Message[LeanCheck::nolean, lean, laToolchainName[]]; Return[$Failed]];
    cmd = {lean, file}; cwd = dir];
  run = laRunToFile[cmd, cwd, outFile, timeout];
  If[run["TimedOut"], Message[LeanCheck::timeout, timeout]];
  parsed = laParseOutput[run["Output"]];
  msgs = parsed["Messages"];
  errors = Select[msgs, #Severity === "error" &];
  warnings = Select[msgs, #Severity === "warning" &];
  sorries = Union[Keys[Select[parsed["Axioms"], MemberQ[#, "sorryAx"] &]],
    If[axioms, {}, If[AnyTrue[warnings, StringContainsQ[#Message, "sorry"] &], {"(declaration uses sorry)"}, {}]]];
  status = Which[
    run["TimedOut"], "Timeout",
    errors =!= {}, "Failed",
    run["ExitCode"] =!= 0, "Error",
    sorries =!= {}, "Sorry",
    names =!= {}, "Proved",
    True, "OK"];
  (* per-theorem status from the line ranges of the declarations *)
  ranges = laTheoremRanges[src, names];
  thmStatus = Association @ Table[
    n -> Which[
      run["TimedOut"], "Timeout",
      AnyTrue[errors, ranges[n][[1]] <= #Line <= ranges[n][[2]] &], "Failed",
      MemberQ[parsed["Axioms"][n] /. _Missing -> {}, "sorryAx"], "Sorry",
      errors =!= {} && !KeyExistsQ[parsed["Axioms"], n], "Failed",
      True, "Proved"], {n, names}];
  res = <|"Status" -> status, "Success" -> MemberQ[{"Proved", "OK"}, status],
    "Theorems" -> names, "TheoremStatus" -> thmStatus, "Axioms" -> parsed["Axioms"], "Sorries" -> sorries,
    "Errors" -> errors, "Warnings" -> warnings, "Messages" -> msgs, "Other" -> parsed["Other"],
    "Output" -> run["Output"], "ExitCode" -> run["ExitCode"], "Time" -> Round[run["Time"], 0.01],
    "Source" -> src, "File" -> file, "Command" -> cmd, "Mathlib" -> mathlib|>;
  If[!keep, Quiet[DeleteFile /@ Select[{file, outFile, run["CommandFile"]}, FileExistsQ]]];
  LeanCheckResult[res]];

(* compiled as a copy in the work directory: the original file is never rewritten (LeanCheck appends the #print axioms lines
   to the file it compiles).  The result records the original path as "SourceFile". *)
LeanCheckFile[file_String?FileExistsQ, opts : OptionsPattern[]] := Module[{res},
  res = LeanCheck[laReadUTF8[file], "FileName" -> FileBaseName[file], opts];
  If[Head[res] === LeanCheckResult, LeanCheckResult[Append[First[res], "SourceFile" -> ExpandFileName[file]]], res]];

(* line ranges of the theorem declarations: from the `theorem name` line to the line before the next declaration *)
laTheoremRanges[src_String, names_List] := Module[{lines = StringSplit[src, "\n", All], starts, n = Length[names], ends, decl},
  decl = RegularExpression["^(?:@\\[[^\\]]*\\]\\s*)?(?:protected\\s+|private\\s+|noncomputable\\s+)*(?:theorem|lemma|def|example|instance|structure|inductive|abbrev|end|namespace|section|#).*"];
  starts = Table[With[{nm = names[[i]]},
    FirstPosition[lines, _String?(StringMatchQ[#, RegularExpression["^(?:@\\[[^\\]]*\\]\\s*)?(?:protected\\s+|private\\s+|noncomputable\\s+)*(?:theorem|lemma)\\s+" <> StringReplace[nm, {"." -> "\\.", "_" -> "_"}] <> "(?:\\s|:|\\(|\\{|\\[|$).*"]] &),
      {1}][[1]]], {i, n}];
  ends = Table[Module[{s = starts[[i]], e = Length[lines]},
    Do[If[StringMatchQ[lines[[j]], decl], e = j - 1; Break[]], {j, s + 1, Length[lines]}]; e], {i, n}];
  Association @ Table[names[[i]] -> {starts[[i]], ends[[i]]}, {i, n}]];

(* --- result object --- *)
LeanCheckResult[a_Association][prop_String] := Switch[prop,
  "Dataset", Dataset[a["Messages"]],
  "Properties", Append[Keys[a], "Dataset"],
  _, Lookup[a, prop, Missing["KeyAbsent", prop]]];
LeanDiagnostics[LeanCheckResult[a_Association]] := Dataset[a["Messages"]];
LeanDiagnostics[_] := $Failed;

laStatusColor["Proved" | "OK"] = Darker[Green, 0.3];
laStatusColor["Sorry"] = Darker[Orange, 0.1];
laStatusColor[_] = Red;

LeanCheckResult /: MakeBoxes[r : LeanCheckResult[a_Association], fmt : (StandardForm | TraditionalForm)] := Module[
  {status = a["Status"], icon, above, below},
  icon = Graphics[{laStatusColor[status], Disk[], White, Thickness[0.15],
    Switch[status, "Proved" | "OK", Line[{{-0.45, 0.05}, {-0.1, -0.35}, {0.5, 0.4}}],
      "Sorry", Text[Style["?", Bold, 14, White], {0, 0}],
      _, Line[{{{-0.4, -0.4}, {0.4, 0.4}}, {{-0.4, 0.4}, {0.4, -0.4}}}]]},
    ImageSize -> 28, PlotRange -> 1];
  above = {
    {BoxForm`SummaryItem[{"Status: ", Style[status, Bold, laStatusColor[status]]}],
     BoxForm`SummaryItem[{"Time: ", ToString[a["Time"]] <> " s"}]},
    {BoxForm`SummaryItem[{"Theorems: ", If[a["Theorems"] === {}, "none", StringRiffle[a["Theorems"], ", "]]}], SpanFromLeft}};
  below = {
    {BoxForm`SummaryItem[{"Errors: ", Length[a["Errors"]]}], BoxForm`SummaryItem[{"Warnings: ", Length[a["Warnings"]]}]},
    {BoxForm`SummaryItem[{"Axioms: ", Column[KeyValueMap[Row[{#1, ": ", StringRiffle[#2, ", "]}] &, a["Axioms"]]]}], SpanFromLeft},
    {BoxForm`SummaryItem[{"Messages: ", Column[Style[StringTake[#Severity <> " (" <> ToString[#Line] <> ":" <> ToString[#Column] <> ") " <> #Message, UpTo[400]], 10] & /@ a["Messages"]]}], SpanFromLeft},
    {BoxForm`SummaryItem[{"File: ", a["File"]}], SpanFromLeft}};
  BoxForm`ArrangeSummaryBox[LeanCheckResult, r, icon, above, below, fmt, "Interpretable" -> Automatic]];

(* ------------------------------------------------------------ *)
(*  LeanForm: WL expressions -> Lean text                        *)
(* ------------------------------------------------------------ *)

LeanForm::unsup = "No Lean rendering for `1`; its InputForm is inserted.";

LeanIdentifier[s_Symbol] := laIdent[SymbolName[s]];
LeanIdentifier[s_String] := laIdent[s];
LeanIdentifier[Subscript[s_, i_]] := LeanIdentifier[s] <> "_" <> StringReplace[ToString[i, InputForm], Except[WordCharacter] -> "_"];
LeanIdentifier[e_] := laIdent[ToString[e, InputForm]];
laIdent[s_String] := Module[{t = StringReplace[s, {"$" -> "_", "`" -> "_"}]},
  t = StringReplace[t, Except[WordCharacter | "_" | "'"] -> "_"];
  If[StringMatchQ[t, DigitCharacter ~~ ___], "v" <> t, t]];

(* precedence: 0 logic, 5 relation, 10 sum, 20 product, 30 unary minus, 40 power, 50 atom *)
LeanForm[e_] := laForm[e, 0];
laParen[s_String, need_] := If[TrueQ[need], "(" <> s <> ")", s];

laForm[s_String, _] := s;
laForm[True, _] := "True"; laForm[False, _] := "False";
laForm[n_Integer, p_] := If[n >= 0, IntegerString[n], laParen["-" <> IntegerString[-n], p > 30]];
laForm[Rational[a_, b_], p_] := laParen[If[a < 0, "-" <> IntegerString[-a], IntegerString[a]] <> "/" <> IntegerString[b], p > 10];
laForm[x_Real, p_] := laForm[Rationalize[x, 0], p];
laForm[Pi, _] := "Real.pi";
laForm[E, _] := "Real.exp 1";
laForm[s_Symbol, _] := LeanIdentifier[s];
laForm[Subscript[s_, i_], _] := LeanIdentifier[Subscript[s, i]];
laForm[Inactive[h_][args___], p_] := laForm[h[args], p];

(* sums *)
laForm[e_Plus, p_] := Module[{terms = List @@ e, first, rest, s},
  first = laForm[First[terms], 10];
  rest = laSignedTerm /@ Rest[terms];
  s = first <> StringJoin[rest];
  laParen[s, p > 10]];
laSignedTerm[t_] := Module[{neg = laNegativeQ[t]},
  If[neg, " - " <> laForm[laNegate[t], 20], " + " <> laForm[t, 20]]];
laNegativeQ[n_?NumberQ] := n < 0;
laNegativeQ[Times[n_?NumberQ, ___]] := n < 0;
laNegativeQ[_] := False;
laNegate[n_?NumberQ] := -n;
laNegate[Times[n_?NumberQ, rest___]] := If[n == -1, Times[rest], Times[-n, rest]];
laNegate[t_] := -t;

(* products and quotients *)
laForm[e_Times, p_] := Module[{factors = List @@ e, num, den, coef, s, sign = ""},
  coef = Select[factors, NumberQ];
  factors = Select[factors, !NumberQ[#] &];
  coef = Times @@ coef;
  If[coef < 0, sign = "-"; coef = -coef];
  num = Select[factors, !MatchQ[#, Power[_, _?Negative]] &];
  den = Cases[factors, Power[b_, k_?Negative] :> If[k == -1, b, Power[b, -k]]];
  If[coef =!= 1 || num === {}, PrependTo[num, coef]];
  s = StringRiffle[laForm[#, 20] & /@ num, "*"];
  If[den =!= {},
    s = s <> " / " <> If[Length[den] == 1, laForm[First[den], 30], "(" <> StringRiffle[laForm[#, 20] & /@ den, "*"] <> ")"]];
  If[sign === "-", laParen["-" <> If[Length[num] + Length[den] > 1, "(" <> s <> ")", s], p > 10], laParen[s, p > 20]]];
laForm[Power[b_, -1], p_] := laParen["1 / " <> laForm[b, 30], p > 20];
laForm[Power[b_, n_Integer?Negative], p_] := laParen["1 / " <> laForm[b, 50] <> "^" <> IntegerString[-n], p > 20];
laForm[Power[b_, n_Integer?Positive], p_] := laParen[laForm[b, 50] <> "^" <> IntegerString[n], p > 40];
laForm[Power[b_, Rational[1, 2]], p_] := laParen["Real.sqrt " <> laForm[b, 50], p > 40];
laForm[Power[b_, x_], p_] := laParen[laForm[b, 50] <> "^" <> laForm[x, 50], p > 40];
laForm[Sqrt[b_], p_] := laParen["Real.sqrt " <> laForm[b, 50], p > 40];
laForm[Abs[x_], _] := "|" <> laForm[x, 0] <> "|";
laForm[e_Max, p_] /; Length[e] == 2 := laParen["max " <> laForm[e[[1]], 50] <> " " <> laForm[e[[2]], 50], p > 40];
laForm[e_Min, p_] /; Length[e] == 2 := laParen["min " <> laForm[e[[1]], 50] <> " " <> laForm[e[[2]], 50], p > 40];
laForm[Mod[a_, b_], p_] := laParen[laForm[a, 20] <> " % " <> laForm[b, 30], p > 20];
laForm[Quotient[a_, b_], p_] := laParen[laForm[a, 20] <> " / " <> laForm[b, 30], p > 20];
laForm[Boole[c_], p_] := laParen["if " <> laForm[c, 0] <> " then 1 else 0", p > 0];
laForm[If[c_, a_, b_], p_] := laParen["if " <> laForm[c, 0] <> " then " <> laForm[a, 0] <> " else " <> laForm[b, 0], p > 0];
laForm[HoldPattern[Piecewise[{{a_, c_}}, b_]], p_] := laForm[If[c, a, b], p];
laForm[HoldPattern[Piecewise[{{a_, c_}, rest__}, b_]], p_] := laForm[If[c, a, Piecewise[{rest}, b]], p];
laForm[HoldPattern[Piecewise[{{a_, c_}}]], p_] := laForm[If[c, a, 0], p];
laForm[UnitStep[x_], p_] := laParen["if 0 \:2264 " <> laForm[x, 0] <> " then 1 else 0", p > 0];
laForm[Floor[x_], _] := "\:230a" <> laForm[x, 0] <> "\:230b";
laForm[Ceiling[x_], _] := "\:2308" <> laForm[x, 0] <> "\:2309";
laForm[Sign[x_], p_] := laParen["SignType.sign " <> laForm[x, 50], p > 40];
laForm[Exp[x_], p_] := laParen["Real.exp " <> laForm[x, 50], p > 40];
laForm[Log[x_], p_] := laParen["Real.log " <> laForm[x, 50], p > 40];
laForm[Sin[x_], p_] := laParen["Real.sin " <> laForm[x, 50], p > 40];
laForm[Cos[x_], p_] := laParen["Real.cos " <> laForm[x, 50], p > 40];
laForm[Factorial[n_], p_] := laParen["Nat.factorial " <> laForm[n, 50], p > 40];
laForm[Binomial[n_, k_], p_] := laParen["Nat.choose " <> laForm[n, 50] <> " " <> laForm[k, 50], p > 40];

(* relations *)
laForm[Equal[a_, b_], p_] := laParen[laForm[a, 10] <> " = " <> laForm[b, 10], p > 5];
laForm[Equal[a_, b_, c__], p_] := laForm[And @@ Thread[{a, b, c}[[;; -2]] == {b, c}], p];
laForm[Unequal[a_, b_], p_] := laParen[laForm[a, 10] <> " \:2260 " <> laForm[b, 10], p > 5];
laForm[Less[a_, b_], p_] := laParen[laForm[a, 10] <> " < " <> laForm[b, 10], p > 5];
laForm[Greater[a_, b_], p_] := laParen[laForm[a, 10] <> " > " <> laForm[b, 10], p > 5];
laForm[LessEqual[a_, b_], p_] := laParen[laForm[a, 10] <> " \:2264 " <> laForm[b, 10], p > 5];
laForm[GreaterEqual[a_, b_], p_] := laParen[laForm[a, 10] <> " \:2265 " <> laForm[b, 10], p > 5];
laForm[(h : Less | LessEqual | Greater | GreaterEqual)[a_, b_, c__], p_] := laForm[And @@ MapThread[h, {{a, b, c}[[;; -2]], {b, c}}], p];
laForm[Divisible[a_, b_], p_] := laParen[laForm[b, 10] <> " \:2223 " <> laForm[a, 10], p > 5];
laForm[Element[x_, Reals], _] := "True";
laForm[Element[x_, s_], p_] := laParen[laForm[x, 10] <> " \:2208 " <> laForm[s, 10], p > 5];

(* logic *)
(* And / Or / Max / Min are Flat + OneIdentity: a pattern And[args__] would match any expression *)
laForm[e_And, p_] := laParen[StringRiffle[laForm[#, 1] & /@ (List @@ e), " \:2227 "], p > 0];
laForm[e_Or, p_] := laParen[StringRiffle[laForm[#, 1] & /@ (List @@ e), " \:2228 "], p > 0];
laForm[Not[a_], p_] := laParen["\:00ac" <> laForm[a, 50], p > 40];
laForm[Implies[a_, b_], p_] := laParen[laForm[a, 1] <> " \:2192 " <> laForm[b, 0], p > 0];
laForm[Equivalent[a_, b_], p_] := laParen[laForm[a, 1] <> " \:2194 " <> laForm[b, 1], p > 0];
(* definitions with a bare ForAll / Exists head are silently dropped by the kernel: use Verbatim heads *)
laForm[Verbatim[ForAll][x_Symbol, body_], p_] := laParen["\:2200 " <> LeanIdentifier[x] <> ", " <> laForm[body, 0], p > 0];
laForm[Verbatim[ForAll][xs_List, body_], p_] := laParen["\:2200 " <> StringRiffle[LeanIdentifier /@ xs, " "] <> ", " <> laForm[body, 0], p > 0];
laForm[Verbatim[ForAll][x_, cond_, body_], p_] := laForm[ForAll[x, Implies[cond, body]], p];
laForm[Verbatim[Exists][x_Symbol, body_], p_] := laParen["\:2203 " <> LeanIdentifier[x] <> ", " <> laForm[body, 0], p > 0];
laForm[Verbatim[Exists][xs_List, body_], p_] := laParen["\:2203 " <> StringRiffle[LeanIdentifier /@ xs, " "] <> ", " <> laForm[body, 0], p > 0];
laForm[Verbatim[Exists][x_, cond_, body_], p_] := laForm[Exists[x, And[cond, body]], p];

(* function application of unknown heads, lists *)
laForm[l_List, _] := "[" <> StringRiffle[laForm[#, 0] & /@ l, ", "] <> "]";
laForm[e_, p_] := laFormGeneric[e, p];
laFormGeneric[e_, p_] := Module[{h = Head[e]},
  If[Length[e] > 0 && (Head[h] === Symbol),
    laParen[LeanIdentifier[h] <> " " <> StringRiffle[laForm[#, 50] & /@ (List @@ e), " "], p > 40],
    Message[LeanForm::unsup, e]; "(" <> ToString[e, InputForm] <> ")"]];

(* ------------------------------------------------------------ *)
(*  LeanLiteral / LeanDataDefinitions                            *)
(* ------------------------------------------------------------ *)

LeanLiteral[n_Integer] := If[n >= 0, IntegerString[n], "(-" <> IntegerString[-n] <> ")"];
LeanLiteral[Rational[a_, b_]] := "(" <> LeanLiteral[a] <> " / " <> LeanLiteral[b] <> ")";
LeanLiteral[True] := "true"; LeanLiteral[False] := "false";
LeanLiteral[s_String] := "\"" <> StringReplace[s, {"\\" -> "\\\\", "\"" -> "\\\""}] <> "\"";
LeanLiteral[l_List] := "[" <> StringRiffle[LeanLiteral /@ l, ", "] <> "]";
LeanLiteral[LeanTuple[args__]] := "(" <> StringRiffle[LeanLiteral /@ {args}, ", "] <> ")";
LeanLiteral[x_Real] := LeanLiteral[Rationalize[x, 0]];
LeanLiteral[e_] := laForm[e, 50];

laLeanType[_Integer] := "Int";
laLeanType[_Rational] := "Rat";
laLeanType[True | False] := "Bool";
laLeanType[_String] := "String";
laLeanType[{}] := "List Int";
laLeanType[l_List] := "List " <> laTypeParen[laLeanType[First[l]]];
laLeanType[LeanTuple[args__]] := StringRiffle[laTypeParen /@ (laLeanType /@ {args}), " \:00d7 "];
laLeanType[_] := "Int";
laTypeParen[t_String] := If[StringContainsQ[t, " "], "(" <> t <> ")", t];

Options[LeanDataDefinitions] = {"Types" -> <||>};
LeanDataDefinitions[a_Association, OptionsPattern[]] := Module[{types = OptionValue["Types"]},
  StringRiffle[KeyValueMap[
    "def " <> laIdent[#1] <> " : " <> Lookup[types, #1, laLeanType[#2]] <> " := " <> LeanLiteral[#2] &, a], "\n\n"]];
LeanDataDefinitions[rules : {__Rule}, opts : OptionsPattern[]] := LeanDataDefinitions[Association[rules], opts];

(* ------------------------------------------------------------ *)
(*  LeanTheorem                                                  *)
(* ------------------------------------------------------------ *)

Options[LeanTheorem] = {"Proof" -> "sorry", "Type" -> "\:211d", "Imports" -> Automatic, "Preamble" -> "",
  "DocString" -> None, "Namespace" -> None, "Data" -> <||>, "MaxHeartbeats" -> Automatic};

laVarSpecs[vars_List, type_String] := Flatten[Replace[vars, {
  (s_Symbol | s_Subscript) :> {{LeanIdentifier[s], type}},
  Rule[s_Symbol | s_Subscript, t_String] :> {{LeanIdentifier[s], t}},
  Rule[l_List, t_String] :> ({LeanIdentifier[#], t} & /@ l),
  s_String :> With[{parts = StringSplit[s, ":", 2]},
    If[Length[parts] == 2, {{StringTrim[parts[[1]]], StringTrim[parts[[2]]]}}, {{StringTrim[s], type}}]],
  other_ :> {{LeanIdentifier[other], type}}}, {1}], 1];

laHypSpecs[hyps_List] := Module[{k = 0},
  Replace[hyps, {
    Rule[n_String, e_] :> {n, laForm[e, 0]},
    e_ :> (k++; {"h" <> ToString[k], laForm[e, 0]})}, {1}]];

LeanTheorem[name_String, vars_List, hyps_List, concl_, opts : OptionsPattern[]] := LeanTheorem[<|
  "Name" -> laIdent[name],
  "Variables" -> laVarSpecs[vars, OptionValue["Type"]],
  "Hypotheses" -> laHypSpecs[hyps],
  "Conclusion" -> laForm[concl, 0],
  "Proof" -> OptionValue["Proof"],
  "Imports" -> OptionValue["Imports"],
  "Preamble" -> OptionValue["Preamble"],
  "DocString" -> OptionValue["DocString"],
  "Namespace" -> OptionValue["Namespace"],
  "MaxHeartbeats" -> OptionValue["MaxHeartbeats"],
  "Data" -> OptionValue["Data"]|>];

LeanTheorem[LeanTheorem[a_Association], opts : OptionsPattern[]] := LeanTheorem[Join[a,
  Association @ Cases[{opts}, Rule[k_String, v_] /; KeyExistsQ[a, k] :> (k -> v)]]];

LeanTheorem[a_Association][prop_String] := Switch[prop,
  "Source", LeanSource[LeanTheorem[a]],
  "Properties", Join[Keys[a], {"Source"}, Keys[a["Data"]]],
  _, If[KeyExistsQ[a, prop], a[prop], Lookup[a["Data"], prop, Missing["KeyAbsent", prop]]]];

LeanTheorem /: MakeBoxes[t : LeanTheorem[a_Association], fmt : (StandardForm | TraditionalForm)] := Module[{above, below, icon},
  icon = Graphics[{Darker[Blue, 0.2], Text[Style["\:2200", Bold, 18, Darker[Blue, 0.2]], {0, 0}]}, ImageSize -> 28, PlotRange -> 1];
  above = {
    {BoxForm`SummaryItem[{"Name: ", a["Name"]}], BoxForm`SummaryItem[{"Variables: ", Length[a["Variables"]]}]},
    {BoxForm`SummaryItem[{"Conclusion: ", Style[StringTake[a["Conclusion"], UpTo[120]], "Input", 10]}], SpanFromLeft}};
  below = {
    {BoxForm`SummaryItem[{"Hypotheses: ", Column[Style[#[[1]] <> " : " <> StringTake[#[[2]], UpTo[150]], "Input", 10] & /@ a["Hypotheses"]]}], SpanFromLeft},
    {BoxForm`SummaryItem[{"Proof: ", Style[StringTake[ToString[a["Proof"]], UpTo[300]], "Input", 10]}], SpanFromLeft},
    {BoxForm`SummaryItem[{"Data: ", StringRiffle[Keys[a["Data"]], ", "]}], SpanFromLeft}};
  BoxForm`ArrangeSummaryBox[LeanTheorem, t, icon, above, below, fmt, "Interpretable" -> Automatic]];

(* imports inferred from the variable types and the tactics used in the proof *)
$laTypeImports = {
  "\:211d" -> "Mathlib.Data.Real.Basic", "Real" -> "Mathlib.Data.Real.Basic",
  "\:211a" -> "Mathlib.Data.Rat.Defs", "Rat" -> "Mathlib.Data.Rat.Defs",
  "\:2102" -> "Mathlib.Data.Complex.Basic", "Complex" -> "Mathlib.Data.Complex.Basic",
  "\:2124" -> "Mathlib.Data.Int.Defs", "\:2115" -> "Mathlib.Data.Nat.Defs"};
$laTacticImports = {
  "linear_combination" -> "Mathlib.Tactic.LinearCombination", "ring" -> "Mathlib.Tactic.Ring",
  "ring_nf" -> "Mathlib.Tactic.Ring", "nlinarith" -> "Mathlib.Tactic.Linarith", "linarith" -> "Mathlib.Tactic.Linarith",
  "positivity" -> "Mathlib.Tactic.Positivity", "field_simp" -> "Mathlib.Tactic.FieldSimp", "norm_num" -> "Mathlib.Tactic.NormNum",
  "polyrith" -> "Mathlib.Tactic.Polyrith", "split_ifs" -> "Mathlib.Tactic.SplitIfs", "push_cast" -> "Mathlib.Tactic.NormNum",
  "nlinarith!" -> "Mathlib.Tactic.Linarith", "abel" -> "Mathlib.Tactic.Abel", "Real.sqrt" -> "Mathlib.Analysis.SpecialFunctions.Sqrt",
  "Real.sin" -> "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic", "Real.cos" -> "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic",
  "Real.exp" -> "Mathlib.Analysis.SpecialFunctions.Exp", "Real.log" -> "Mathlib.Analysis.SpecialFunctions.Log.Basic",
  "Real.pi" -> "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic", "mul_eq_zero" -> "Mathlib.Algebra.GroupWithZero.Basic",
  "omega" -> None, "decide" -> None, "simp" -> None, "rfl" -> None};

laInferImports[a_Association] := Module[{types, text, imps = {}},
  types = If[a["Variables"] === {}, {}, Union[a["Variables"][[All, 2]]]];
  imps = Join[imps, Cases[$laTypeImports, Rule[t_, m_] /; MemberQ[types, t] :> m]];
  text = StringJoin[ToString[a["Proof"]], " ", a["Conclusion"], " ", StringRiffle[a["Hypotheses"][[All, 2]], " "], " ", a["Preamble"], " ",
    StringRiffle[a["Variables"][[All, 2]], " "]];
  imps = Join[imps, Cases[$laTacticImports, Rule[t_String, m_String] /; StringContainsQ[text, t] :> m]];
  DeleteDuplicates[imps]];

laTheoremImports[a_Association] := Module[{imp = a["Imports"]},
  Which[
    imp === Automatic, laInferImports[a],
    ListQ[imp] && MemberQ[imp, Automatic], DeleteDuplicates[Join[laInferImports[a], Cases[imp, _String]]],
    ListQ[imp], Cases[imp, _String],
    StringQ[imp], {imp},
    True, {}]];

laIndent[s_String, n_Integer] := Module[{lines = StringSplit[StringTrim[s, "\n"], "\n", All], common},
  lines = StringReplace[lines, StartOfString ~~ Whitespace ~~ EndOfString -> ""];
  common = Min[StringLength[First[StringCases[#, StartOfString ~~ (" " ...)], ""]] & /@ Select[lines, # =!= "" &]];
  If[!IntegerQ[common], common = 0];
  StringRiffle[If[# === "", "", StringJoin[ConstantArray[" ", n]] <> StringDrop[#, UpTo[common]]] & /@ lines, "\n"]];

laDeclText[a_Association] := Module[{vars = a["Variables"], hyps = a["Hypotheses"], binders, doc, proof, body, hb},
  binders = Join[
    (* group consecutive variables of the same type *)
    With[{g = Split[vars, #1[[2]] === #2[[2]] &]}, "(" <> StringRiffle[#[[All, 1]], " "] <> " : " <> #[[1, 2]] <> ")" & /@ g],
    "(" <> #[[1]] <> " : " <> #[[2]] <> ")" & /@ hyps];
  doc = If[StringQ[a["DocString"]] && a["DocString"] =!= "", "/-- " <> a["DocString"] <> " -/\n", ""];
  proof = ToString[a["Proof"]];
  body = If[StringTrim[proof] === "" || StringMatchQ[StringTrim[proof], "sorry"], "  sorry", laIndent[proof, 2]];
  (* long certificates (linear_combination over big polynomials) need more than the default 200000 heartbeats *)
  hb = Lookup[a, "MaxHeartbeats", Automatic];
  hb = Which[IntegerQ[hb] && hb > 0, hb, hb === Automatic && StringLength[proof] > 2000, 4000000, True, None];
  If[IntegerQ[hb], "set_option maxHeartbeats " <> IntegerString[hb] <> " in\nset_option maxRecDepth 16384 in\n", ""] <>
  doc <> "theorem " <> a["Name"] <> If[binders === {}, "", " " <> StringRiffle[binders, "\n    "]] <> " :\n    " <> a["Conclusion"] <> " := by\n" <> body <> "\n"];

LeanSource[LeanTheorem[a_Association]] := LeanSource[{LeanTheorem[a]}];
LeanSource[thms : {__LeanTheorem}] := Module[{as = First /@ thms, imports, preambles, decls, ns},
  imports = DeleteDuplicates[Flatten[laTheoremImports /@ as]];
  preambles = DeleteDuplicates[Select[StringTrim /@ Select[#["Preamble"] & /@ as, StringQ], # =!= "" &]];
  decls = laDeclText /@ as;
  ns = DeleteDuplicates[Cases[as, KeyValuePattern["Namespace" -> n_String] :> n]];
  StringJoin[
    If[imports === {}, "", StringRiffle["import " <> # & /@ imports, "\n"] <> "\n\n"],
    If[preambles === {}, "", StringRiffle[preambles, "\n\n"] <> "\n\n"],
    If[ns =!= {}, "namespace " <> First[ns] <> "\n\n", ""],
    StringRiffle[decls, "\n"],
    If[ns =!= {}, "\nend " <> First[ns] <> "\n", ""]]];

LeanSaveSource[t : (_LeanTheorem | {__LeanTheorem}), file_String] := laWriteUTF8[file, LeanSource[t]];
LeanSaveSource[t_LeanTheorem] := LeanSaveSource[t, FileNameJoin[{$LeanAssistDirectory, "lean", t["Name"] <> ".lean"}]];

LeanCheck[t_LeanTheorem, opts : OptionsPattern[]] := LeanProve[t, opts];
LeanCheck[ts : {__LeanTheorem}, opts : OptionsPattern[]] := LeanProve[ts, opts];
LeanProve[t_LeanTheorem, opts : OptionsPattern[]] := Module[{r = LeanCheck[LeanSource[t], "FileName" -> t["Name"], opts]},
  If[Head[r] === LeanCheckResult, LeanCheckResult[Append[First[r], "Theorem" -> t]], r]];
LeanProve[ts : {__LeanTheorem}, opts : OptionsPattern[]] := Module[{r = LeanCheck[LeanSource[ts], opts]},
  If[Head[r] === LeanCheckResult, LeanCheckResult[Append[First[r], "Theorem" -> ts]], r]];

(* ------------------------------------------------------------ *)
(*  polynomial certificates                                      *)
(* ------------------------------------------------------------ *)

Options[LeanPolynomialCertificate] = {"NonDegenerate" -> {}, "MaxExponent" -> 3, "Method" -> Automatic, "TimeLimit" -> 30};

laToPoly[Equal[a_, b_]] := Together[a - b] // Numerator // Expand;
laToPoly[Unequal[a_, b_]] := Together[a - b] // Numerator // Expand;
laToPoly[e_] := Expand[Numerator[Together[e]]];

(* exponent vectors of total degree d over n slots *)
laExponentVectors[n_, d_] := Select[Tuples[Range[0, d], n], Total[#] == d &];

LeanPolynomialCertificate[goal_, hyps_List, vars_List, OptionsPattern[]] := Module[
  {g, hs, nds, maxe, gb, order, n, inconsistent, inIdeal, res, tl = OptionValue["TimeLimit"]},
  g = laToPoly[goal]; hs = laToPoly /@ hyps; nds = DeleteCases[laToPoly /@ OptionValue["NonDegenerate"], _?NumericQ];
  maxe = OptionValue["MaxExponent"];
  n = Length[hs];
  If[hs === {},
    Return[<|"Found" -> g === 0, "Coefficients" -> {}, "Factor" -> 1, "FactorExponents" -> {}, "Verified" -> g === 0,
      "Inconsistent" -> False, "Goal" -> g, "Hypotheses" -> hs, "NonDegenerate" -> nds, "Variables" -> vars, "Method" -> "Groebner"|>]];
  order = DegreeReverseLexicographic;
  gb = GroebnerBasis[hs, vars, MonomialOrder -> order];
  inconsistent = gb === {1};
  inIdeal[t_] := TimeConstrained[PolynomialReduce[Expand[t], gb, vars, MonomialOrder -> order][[2]] === 0, tl, False];
  (* 1. ideal membership of goal * (small powers of the declared nondegeneracy polynomials) *)
  res = laCertificateSearch[g, hs, vars, nds, maxe, inIdeal, tl];
  (* 2. triangular elimination of the variables that occur linearly in a hypothesis (constructed points):
        the leading coefficients become the nondegeneracy factor, with the exact exponents *)
  If[!TrueQ[res["Found"]] && OptionValue["Method"] =!= "Groebner",
    res = laCertificateByElimination[g, hs, vars, nds, maxe, inIdeal, tl]];
  Join[res, <|"Inconsistent" -> inconsistent, "Goal" -> g, "Hypotheses" -> hs, "Variables" -> vars|>]];

(* block monomial order: degree reverse lexicographic on the first nx variables, then on the remaining ny
   (an elimination order for the first block, much cheaper than Lexicographic) *)
laBlockOrder[nx_, ny_] := Module[{drl},
  drl[n_] := Join[{ConstantArray[1, n]}, Table[-UnitVector[n, n - i + 1], {i, 1, n - 1}]];
  Join[Join[#, ConstantArray[0, ny]] & /@ drl[nx], Join[ConstantArray[0, nx], #] & /@ drl[ny]]];

(* cofactors of target in terms of hs: first a plain division by the hypotheses (enough for triangular
   systems), then through tag variables: target == r(x, y) mod <h_i - y_i> with r in the ideal <y>; returns {coeffs, ok} *)
laCofactors[target_, hs_, vars_] := Module[{n = Length[hs], tags, allvars, gb2, q, r, coeffs, rem, direct, ord},
  direct = PolynomialReduce[target, hs, vars];
  If[direct[[2]] === 0 && Expand[target - direct[[1]] . hs] === 0, Return[{Expand /@ direct[[1]], True}]];
  tags = Table[Symbol["LeanAssist`Private`tag" <> ToString[i]], {i, n}];
  allvars = Join[vars, tags];
  ord = laBlockOrder[Length[vars], n];
  gb2 = GroebnerBasis[hs - tags, allvars, MonomialOrder -> ord];
  {q, r} = PolynomialReduce[target, gb2, allvars, MonomialOrder -> ord];
  coeffs = ConstantArray[0, n]; rem = r;
  Do[
    With[{qq = PolynomialReduce[rem, {tags[[i]]}, allvars]},
      coeffs[[i]] = Expand[qq[[1, 1]] /. Thread[tags -> hs]];
      rem = qq[[2]]],
    {i, n}];
  {coeffs, (rem === 0) && (Expand[target - coeffs . hs] === 0)}];

(* exponent vectors of the declared factors by increasing total degree *)
laCertificateSearch[g_, hs_, vars_, nds_, maxe_, inIdeal_, tl_ : 30] := Module[{found = False, exps = {}, factor, target, coeffs, ok},
  Do[
    Do[
      If[inIdeal[g Times @@ MapThread[Power, {nds, e}]], found = True; exps = e; Break[]],
      {e, If[nds === {}, If[d == 0, {{}}, {}], laExponentVectors[Length[nds], d]]}];
    If[found, Break[]],
    {d, 0, maxe}];
  If[!found,
    Return[<|"Found" -> False, "Coefficients" -> {}, "Factor" -> 1, "FactorExponents" -> {}, "Verified" -> False, "NonDegenerate" -> nds, "Method" -> "Groebner"|>]];
  factor = Times @@ MapThread[Power, {nds, exps}];
  target = Expand[factor g];
  {coeffs, ok} = Replace[TimeConstrained[laCofactors[target, hs, vars], 4 tl, $Failed], $Failed -> {{}, False}];
  <|"Found" -> ok, "Coefficients" -> coeffs, "Factor" -> factor, "FactorExponents" -> exps, "Verified" -> ok, "NonDegenerate" -> nds, "Method" -> "Groebner"|>];

(* pseudo-division of the goal by hypotheses h = c t + r that are linear in one of their variables t:
   c^m G = h Q + R with R free of t (m = degree of G in t).  Repeating this for the constructed parameters
   (feet of perpendiculars, intersection points, centres) leaves a remainder that is checked by ideal
   membership; the leading coefficients c are exactly the nondegeneracy conditions of the construction. *)
laCertificateByElimination[g_, hs_, vars_, nds_, maxe_, inIdeal_, tl_] := Module[
  {G = g, usedH = {}, steps = {}, cand, pick, h, t, c, m, Q, R, k = 0, rest, coeffs, ok, factorPoly, fl, facs = {}, exps = {}, const, pruned},
  While[k < 60,
    k++;
    cand = Flatten[Table[If[!MemberQ[usedH, j] && Exponent[hs[[j]], v] == 1 && Exponent[G, v] >= 1, {j, v}, Nothing], {j, Length[hs]}, {v, vars}], 1];
    If[cand === {}, Break[]];
    (* later variables first: vars lists the free coordinates before the constructed parameters, so the
       parameters of feet / intersections are eliminated first and the free coordinates stay (Wu's ordering) *)
    pick = First[SortBy[cand, {-First[FirstPosition[vars, #[[2]], {0}]], Exponent[G, #[[2]]], LeafCount[Coefficient[hs[[#[[1]]]], #[[2]]]]} &]];
    {h, t} = {hs[[pick[[1]]]], pick[[2]]};
    c = Coefficient[h, t]; m = Exponent[G, t];
    {Q, R} = Expand[Together[#]] & /@ PolynomialQuotientRemainder[Expand[c^m G], h, t];
    AppendTo[usedH, pick[[1]]];
    If[!(PolynomialQ[Q, vars] && PolynomialQ[R, vars]), Continue[]];
    AppendTo[steps, <|"Index" -> pick[[1]], "Q" -> Q, "c" -> c, "m" -> m|>];
    G = R];
  rest = If[G === 0,
    <|"Found" -> True, "Coefficients" -> ConstantArray[0, Length[hs]], "Factor" -> 1, "FactorExponents" -> ConstantArray[0, Length[nds]]|>,
    laCertificateSearch[G, hs, vars, nds, maxe, inIdeal, tl]];
  If[!TrueQ[rest["Found"]],
    Return[<|"Found" -> False, "Coefficients" -> {}, "Factor" -> 1, "FactorExponents" -> {}, "Verified" -> False, "NonDegenerate" -> nds, "Method" -> "Elimination"|>]];
  (* compose: d * prod_i c_i^{m_i} * g = sum_i h_i (d Q_i prod_{j>i} c_j^{m_j}) + sum_j a_j h_j *)
  coeffs = rest["Coefficients"];
  Do[With[{s = steps[[i]], tail = Times @@ Table[steps[[j]]["c"]^steps[[j]]["m"], {j, i + 1, Length[steps]}]},
    coeffs[[s["Index"]]] += Expand[rest["Factor"] s["Q"] tail]], {i, Length[steps]}];
  factorPoly = Expand[rest["Factor"] Times @@ (#["c"]^#["m"] & /@ steps)];
  (* distinct irreducible factors with exponents; the numeric content goes into the coefficients *)
  fl = FactorList[factorPoly];
  const = fl[[1, 1]]^fl[[1, 2]];
  If[Length[fl] > 1, {facs, exps} = Transpose[Rest[fl]]];
  coeffs = Expand[coeffs/const];
  factorPoly = Times @@ MapThread[Power, {facs, exps}];
  ok = Expand[factorPoly g - coeffs . hs] === 0;
  (* prune: lower the exponents while membership survives; cofactors are recomputed for the smaller factor *)
  pruned = exps;
  Do[While[pruned[[i]] > 0 && inIdeal[g Times @@ MapThread[Power, {facs, ReplacePart[pruned, i -> pruned[[i]] - 1]}]], pruned[[i]]--], {i, Length[facs]}];
  If[pruned =!= exps,
    With[{alt = TimeConstrained[laCofactors[Expand[g Times @@ MapThread[Power, {facs, pruned}]], hs, vars], tl, $Failed]},
      If[ListQ[alt] && TrueQ[alt[[2]]], exps = pruned; coeffs = alt[[1]]; factorPoly = Times @@ MapThread[Power, {facs, exps}]; ok = True]]];
  <|"Found" -> ok, "Coefficients" -> coeffs, "Factor" -> factorPoly, "FactorExponents" -> exps, "Verified" -> ok, "NonDegenerate" -> facs, "Method" -> "Elimination"|>];

LeanLinearCombination[cert_Association, hypNames_List] := Module[{terms},
  If[!TrueQ[cert["Found"]], Return["sorry"]];
  terms = MapThread[If[#1 === 0, Nothing, "(" <> laForm[#1, 0] <> ") * " <> #2] &, {cert["Coefficients"], hypNames}];
  If[terms === {}, "ring", "linear_combination " <> StringRiffle[terms, " + "]]];

(* d^e != 0 proof term from the names of the hypotheses d_j != 0 *)
laNonzeroTerm[exps_List, ndNames_List] := Module[{parts},
  parts = MapThread[Which[#1 == 0, Nothing, #1 == 1, #2, True, "(pow_ne_zero " <> IntegerString[#1] <> " " <> #2 <> ")"] &, {exps, ndNames}];
  Fold["(mul_ne_zero " <> #1 <> " " <> #2 <> ")" &, First[parts], Rest[parts]]];
laFactorText[nds_List, exps_List] := StringRiffle[MapThread[Which[#2 == 0, Nothing, #2 == 1, laForm[#1, 20], True, laForm[#1, 50] <> "^" <> IntegerString[#2]] &, {nds, exps}], " * "];

LeanPolynomialProof[cert_Association, hypNames_List, ndNames_List : {}] := Module[{lc, exps = cert["FactorExponents"]},
  If[!TrueQ[cert["Found"]], Return["sorry"]];
  lc = LeanLinearCombination[cert, hypNames];
  If[exps === {} || Total[exps] == 0, Return[lc]];
  "have hprod : " <> laFactorText[cert["NonDegenerate"], exps] <> " * (" <> laForm[cert["Goal"], 0] <> ") = 0 := by\n  " <>
    StringReplace[lc, "\n" -> "\n  "] <> "\n" <>
  "exact (mul_eq_zero.mp hprod).resolve_left " <> laNonzeroTerm[exps, ndNames]];

Options[LeanPolynomialTheorem] = Join[{"NonDegenerate" -> {}, "MaxExponent" -> 3}, Options[LeanTheorem]];
LeanPolynomialTheorem[name_String, vars_List, hyps_List, goal_, opts : OptionsPattern[]] := Module[
  {hpolys, goals, nds, certs, hypNames, ndNames, used, proofs, proof, thmHyps, concl, thmOpts, ndUsed, type},
  type = OptionValue["Type"];
  hpolys = laToPoly /@ hyps;
  goals = laToPoly /@ Flatten[{goal}];
  nds = laToPoly /@ OptionValue["NonDegenerate"];
  hypNames = Table["h" <> ToString[i], {i, Length[hpolys]}];
  certs = LeanPolynomialCertificate[#, hpolys, laPolyVars[vars], "NonDegenerate" -> nds, "MaxExponent" -> OptionValue["MaxExponent"]] & /@ goals;
  (* nondegeneracy factors actually used by the certificates (each certificate carries its own factor list) *)
  ndUsed = DeleteDuplicates[Flatten[Table[Pick[c["NonDegenerate"], Positive /@ c["FactorExponents"]], {c, certs}]]];
  ndNames = Table["hnd" <> ToString[i], {i, Length[ndUsed]}];
  proofs = Table[With[{c = certs[[k]]},
    LeanPolynomialProof[Join[c, <|"NonDegenerate" -> ndUsed,
        "FactorExponents" -> Table[With[{pos = Position[c["NonDegenerate"], f, {1}, 1]}, If[pos === {}, 0, c["FactorExponents"][[pos[[1, 1]]]]]], {f, ndUsed}]|>],
      hypNames, ndNames]], {k, Length[goals]}];
  proof = If[Length[goals] == 1, First[proofs],
    "refine \:27e8" <> StringRiffle[ConstantArray["?_", Length[goals]], ", "] <> "\:27e9\n" <>
      StringRiffle["\:00b7 " <> StringReplace[#, "\n" -> "\n  "] & /@ proofs, "\n"]];
  (* hypotheses and conclusion as Lean text (a WL equation 0 == 0 would evaluate to True) *)
  thmHyps = Join[MapThread[#1 -> (laForm[#2, 10] <> " = 0") &, {hypNames, hpolys}], MapThread[#1 -> (laForm[#2, 10] <> " \:2260 0") &, {ndNames, ndUsed}]];
  concl = StringRiffle[laForm[#, 10] <> " = 0" & /@ goals, " \:2227 "];
  If[goals === {0}, proof = "rfl"];
  thmOpts = DeleteCases[FilterRules[{opts}, Options[LeanTheorem]], Rule["Data" | "Proof", _]];
  LeanTheorem[name, vars, thmHyps, concl, "Proof" -> proof,
    "Data" -> Join[<|"Certificates" -> certs, "CertificateStatus" -> If[AllTrue[certs, TrueQ[#["Found"]] &], "Found", "NotFound"],
      "Inconsistent" -> AnyTrue[certs, TrueQ[#["Inconsistent"]] &]|>, Lookup[{opts}, "Data", <||>]],
    Sequence @@ thmOpts]];

laPolyVars[vars_List] := Flatten[Replace[vars, {Rule[l_List, _] :> l, Rule[s_, _] :> s, s_String :> Symbol[StringTrim[First[StringSplit[s, ":"]]]]}, {1}]];

(* ------------------------------------------------------------ *)
(*  geometry: coordinates                                        *)
(* ------------------------------------------------------------ *)

Options[LeanGeometryCoordinates] = {"Normalize" -> True, "Coordinates" -> <||>};

laCoordSymbol[p_Symbol, axis_String] := Symbol[Context[p] <> axis <> SymbolName[p]];
laCoordSymbol[p_, axis_String] := Symbol["Global`" <> axis <> laIdent[ToString[p, InputForm]]];

LeanGeometryCoordinates[points_List, OptionsPattern[]] := Module[{pts = points, fixed = OptionValue["Coordinates"], coords, norm = TrueQ[OptionValue["Normalize"]]},
  fixed = Association[fixed];
  pts = Replace[pts, Rule[p_, c_] :> (fixed[p] = c; p), {1}];
  coords = Association @ Table[p -> Lookup[fixed, p, {laCoordSymbol[p, "x"], laCoordSymbol[p, "y"]}], {p, pts}];
  If[norm && Length[pts] >= 1 && !KeyExistsQ[fixed, pts[[1]]], coords[pts[[1]]] = {0, 0}];
  If[norm && Length[pts] >= 2 && !KeyExistsQ[fixed, pts[[2]]], coords[pts[[2]]] = {laCoordSymbol[pts[[2]], "x"], 0}];
  coords];

(* ------------------------------------------------------------ *)
(*  geometry: predicates -> polynomials                           *)
(* ------------------------------------------------------------ *)

laVec[c_, p_, q_] := c[q] - c[p];
laCross[{a_, b_}, {d_, e_}] := a e - b d;
laDot[u_, v_] := u . v;
laSq[u_] := u . u;
laPointQ[c_, p_] := KeyExistsQ[c, p];
(* CircleThrough[{a, b, c}] evaluates (with a message) on point symbols, so it stays Inactive *)
laStrip[e_] := e //. Inactive[h_] /; h =!= CircleThrough :> h;

(* line through two points: coefficients {a, b, c} with a x + b y + c == 0 *)
laLineCoeffs[c_, {p_, q_}] := With[{P = c[p], Q = c[q]}, {Q[[2]] - P[[2]], P[[1]] - Q[[1]], -((Q[[2]] - P[[2]]) P[[1]] + (P[[1]] - Q[[1]]) P[[2]])}];
laLinePoints[Line[{p_, q_}]] := {p, q};
laLinePoints[InfiniteLine[{p_, q_}]] := {p, q};
laLinePoints[HalfLine[{p_, q_}]] := {p, q};
laLinePoints[Line[{p_, q_, ___}]] := {p, q};
laLinePoints[_] := $Failed;

laConcyclicDet[c_, {p1_, p2_, p3_, p4_}] := Det[Table[With[{P = c[p]}, {laSq[P], P[[1]], P[[2]], 1}], {p, {p1, p2, p3, p4}}]];

laSignedArea[c_, pts_List] := Expand[Sum[With[{P = c[pts[[i]]], Q = c[pts[[Mod[i, Length[pts]] + 1]]]}, P[[1]] Q[[2]] - Q[[1]] P[[2]]], {i, Length[pts]}]/2];

(* record constructor *)
laRec[kind_, polys_, nd_ : {}, caveat_ : None] := <|"Kind" -> kind, "Polynomials" -> Expand /@ Flatten[{polys}], "NonDegenerate" -> Expand /@ Flatten[{nd}], "Caveat" -> caveat|>;

(* main translator: returns a record or $Failed; c = coordinate association (with substitutions applied) *)
laTranslate[hyp_, c_] := laTr[laStrip[hyp], c];

(* conjunctions: merge the records of the parts *)
laTr[e_And, c_] := Module[{recs = laTr[#, c] & /@ (List @@ e)},
  If[MemberQ[recs, $Failed], Return[$Failed]];
  <|"Kind" -> "And", "Polynomials" -> Flatten[#["Polynomials"] & /@ recs], "NonDegenerate" -> DeleteDuplicates[Flatten[#["NonDegenerate"] & /@ recs]],
    "Caveat" -> With[{cs = DeleteCases[#["Caveat"] & /@ recs, None]}, If[cs === {}, None, StringRiffle[DeleteDuplicates[cs], "; "]]],
    "AuxiliaryVariables" -> Flatten[Lookup[recs, "AuxiliaryVariables", {}]],
    "AuxiliaryHypotheses" -> Flatten[Lookup[recs, "AuxiliaryHypotheses", {}]],
    "AuxiliaryDefinitions" -> Flatten[Lookup[recs, "AuxiliaryDefinitions", {}]]|>];

laTr[Triangle[{p_, q_, r_}], c_] /; laPointQ[c, p] && laPointQ[c, q] && laPointQ[c, r] :=
  laRec["Triangle", {}, laCross[laVec[c, p, q], laVec[c, p, r]]];
laTr[Polygon[pts_List], c_] /; AllTrue[pts, laPointQ[c, #] &] := laRec["Polygon", {}];
laTr[(Circle | Disk)[_, _], c_] := laRec["Object", {}];
laTr[(Line | InfiniteLine | HalfLine)[_List], c_] := laRec["Object", {}];

laTr[Element[p_, l : (Line | InfiniteLine)[{a_, b_}]], c_] /; laPointQ[c, p] && laPointQ[c, a] && laPointQ[c, b] :=
  laRec["OnLine", laCross[laVec[c, a, p], laVec[c, a, b]]];
laTr[Element[p_, l : HalfLine[{a_, b_}]], c_] /; laPointQ[c, p] && laPointQ[c, a] && laPointQ[c, b] :=
  laRec["OnLine", laCross[laVec[c, a, p], laVec[c, a, b]], {}, "betweenness / half-line condition dropped"];
laTr[Element[p_, Circle[o_, r_]], c_] /; laPointQ[c, p] && laPointQ[c, o] :=
  laRec["OnCircle", laSq[laVec[c, o, p]] - laRadiusSq[r, c]];
laTr[Element[p_, (CircleThrough | Inactive[CircleThrough])[{a_, b_, d_}]], c_] /; AllTrue[{p, a, b, d}, laPointQ[c, #] &] :=
  laRec["Concyclic", laConcyclicDet[c, {a, b, d, p}], laCross[laVec[c, a, b], laVec[c, a, d]]];
laTr[Element[p_, Circumsphere[{a_, b_, d_}]], c_] /; AllTrue[{p, a, b, d}, laPointQ[c, #] &] :=
  laRec["Concyclic", laConcyclicDet[c, {a, b, d, p}]];
laTr[Element[p_, Circumsphere[Triangle[{a_, b_, d_}]]], c_] /; AllTrue[{p, a, b, d}, laPointQ[c, #] &] :=
  laRec["Concyclic", laConcyclicDet[c, {a, b, d, p}]];

laRadiusSq[HoldPattern[EuclideanDistance[p_, q_]], c_] /; laPointQ[c, p] && laPointQ[c, q] := laSq[laVec[c, p, q]];
laRadiusSq[r_, c_] := r^2;

laTr[Equal[p_, Midpoint[{a_, b_}]], c_] /; laPointQ[c, p] && laPointQ[c, a] && laPointQ[c, b] :=
  laRec["Midpoint", 2 c[p] - c[a] - c[b]];
laTr[Equal[Midpoint[{a_, b_}], p_], c_] := laTr[Equal[p, Midpoint[{a, b}]], c];
laTr[Equal[p_, TriangleCenter[{a_, b_, d_}, "Centroid"]], c_] /; AllTrue[{p, a, b, d}, laPointQ[c, #] &] :=
  laRec["Centroid", 3 c[p] - c[a] - c[b] - c[d]];
laTr[Equal[p_, TriangleCenter[Triangle[pts_], k_]], c_] := laTr[Equal[p, TriangleCenter[pts, k]], c];
laTr[Equal[p_, TriangleCenter[{a_, b_, d_}, "Circumcenter"]], c_] /; AllTrue[{p, a, b, d}, laPointQ[c, #] &] :=
  laRec["Circumcenter", {laSq[laVec[c, p, a]] - laSq[laVec[c, p, b]], laSq[laVec[c, p, a]] - laSq[laVec[c, p, d]]}];
laTr[Equal[p_, TriangleCenter[{a_, b_, d_}, "Orthocenter"]], c_] /; AllTrue[{p, a, b, d}, laPointQ[c, #] &] :=
  laRec["Orthocenter", {laDot[laVec[c, a, p], laVec[c, b, d]], laDot[laVec[c, b, p], laVec[c, a, d]]}];
laTr[Equal[p_, q_], c_] /; laPointQ[c, p] && laPointQ[c, q] := laRec["PointEqual", c[p] - c[q]];

(* assertions *)
laTr[GeometricAssertion[pts_List, "Collinear"], c_] /; AllTrue[pts, laPointQ[c, #] &] && Length[pts] >= 3 :=
  laRec["Collinear", Table[laCross[laVec[c, pts[[1]], pts[[2]]], laVec[c, pts[[1]], pts[[i]]]], {i, 3, Length[pts]}]];
laTr[HoldPattern[CollinearPoints[pts_List]], c_] := laTr[GeometricAssertion[pts, "Collinear"], c];
laTr[GeometricAssertion[lines_List, "Parallel"], c_] /; Length[lines] >= 2 && AllTrue[lines, laLinePoints[#] =!= $Failed &] :=
  With[{dirs = (laVec[c, #[[1]], #[[2]]] &) /@ (laLinePoints /@ lines)},
    laRec["Parallel", Table[laCross[dirs[[1]], dirs[[i]]], {i, 2, Length[dirs]}]]];
laTr[GeometricAssertion[{l1_, l2_}, "Perpendicular"], c_] /; laLinePoints[l1] =!= $Failed && laLinePoints[l2] =!= $Failed :=
  laRec["Perpendicular", laDot[laVec[c, Sequence @@ laLinePoints[l1]], laVec[c, Sequence @@ laLinePoints[l2]]]];
laTr[GeometricAssertion[lines_List, "Concurrent"], c_] /; Length[lines] >= 3 && AllTrue[lines, laLinePoints[#] =!= $Failed &] :=
  With[{cf = laLineCoeffs[c, laLinePoints[#]] & /@ lines},
    laRec["Concurrent", Table[Det[{cf[[1]], cf[[2]], cf[[i]]}], {i, 3, Length[cf]}], {}, "concurrent or all parallel (projective condition)"]];
laTr[GeometricAssertion[pts_List, "Concyclic"], c_] /; AllTrue[pts, laPointQ[c, #] &] && Length[pts] >= 4 :=
  laRec["Concyclic", Table[laConcyclicDet[c, {pts[[1]], pts[[2]], pts[[3]], pts[[i]]}], {i, 4, Length[pts]}], {}, "concyclic or collinear"];
laTr[GeometricAssertion[{Triangle[{a_, b_, d_}], Triangle[{e_, f_, g_}]}, "Congruent"], c_] :=
  laRec["Congruent", {laSq[laVec[c, a, b]] - laSq[laVec[c, e, f]], laSq[laVec[c, b, d]] - laSq[laVec[c, f, g]], laSq[laVec[c, d, a]] - laSq[laVec[c, g, e]]}];
laTr[GeometricAssertion[{Triangle[{a_, b_, d_}], Triangle[{e_, f_, g_}]}, "Similar"], c_] :=
  laRec["Similar", {laSq[laVec[c, a, b]] laSq[laVec[c, f, g]] - laSq[laVec[c, e, f]] laSq[laVec[c, b, d]],
    laSq[laVec[c, a, b]] laSq[laVec[c, g, e]] - laSq[laVec[c, e, f]] laSq[laVec[c, d, a]]}];
laTr[GeometricAssertion[Triangle[{a_, b_, d_}], "Equilateral"], c_] := laTr[GeometricAssertion[{a, b, d}, "Equilateral"], c];
laTr[GeometricAssertion[{a_, b_, d_}, "Equilateral"], c_] /; AllTrue[{a, b, d}, laPointQ[c, #] &] :=
  laRec["Equilateral", {laSq[laVec[c, a, b]] - laSq[laVec[c, b, d]], laSq[laVec[c, b, d]] - laSq[laVec[c, d, a]]}];
laTr[GeometricAssertion[{a_, b_, d_}, "Counterclockwise" | "Clockwise"], c_] /; AllTrue[{a, b, d}, laPointQ[c, #] &] :=
  laRec["Orientation", {}, laCross[laVec[c, a, b], laVec[c, a, d]], "orientation sign dropped (kept as nondegeneracy)"];
laTr[GeometricAssertion[Triangle[{a_, b_, d_}], "Counterclockwise" | "Clockwise"], c_] := laTr[GeometricAssertion[{a, b, d}, "Counterclockwise"], c];
laTr[GeometricAssertion[_, "Convex"], c_] := laRec["Convex", {}, {}, "convexity dropped"];
laTr[GeometricAssertion[Polygon[pts_], "Convex"], c_] := laRec["Convex", {}, {}, "convexity dropped"];

(* angles *)
laCosSq[th_] := With[{v = Simplify[Cos[th]^2]}, If[NumericQ[v] && Element[v, Rationals] === True, v, $Failed]];
laTr[Equal[PlanarAngle[{a_, b_, d_}], th_?NumericQ], c_] /; AllTrue[{a, b, d}, laPointQ[c, #] &] := Module[{u = laVec[c, b, a], v = laVec[c, b, d], cs},
  Which[
    Simplify[Cos[th]] === 0, laRec["RightAngle", laDot[u, v]],
    Simplify[th - Pi] === 0, laRec["StraightAngle", laCross[u, v], {}, "180 degrees: collinearity only (betweenness dropped)"],
    (cs = laCosSq[th]) =!= $Failed, laRec["Angle", laDot[u, v]^2 - cs laSq[u] laSq[v], {}, "angle or its supplement (cos^2 condition)"],
    True, $Failed]];
laTr[Equal[th_?NumericQ, PlanarAngle[pts_]], c_] := laTr[Equal[PlanarAngle[pts], th], c];
(* Angle relations have two translations.  The cos^2 form is implied by the unoriented statement (used for hypotheses).
   The full-angle form (oriented angles modulo 180 deg: z1 = conj(u1) v1 parallel to z2 resp. z2^2) implies the cos^2 form
   and has half the degree; it is offered as "Alternative" and used for a conclusion when the cos^2 certificate is missing or
   too large (LeanGeometryTheorem).  It is false for mirror-image configurations (base angles of an isosceles triangle). *)
laTr[Equal[PlanarAngle[{a_, b_, d_}], PlanarAngle[{e_, f_, g_}]], c_] /; AllTrue[{a, b, d, e, f, g}, laPointQ[c, #] &] :=
  Module[{u1 = laVec[c, b, a], v1 = laVec[c, b, d], u2 = laVec[c, f, e], v2 = laVec[c, f, g]},
    Append[laRec["AngleEqual", laDot[u1, v1]^2 laSq[u2] laSq[v2] - laDot[u2, v2]^2 laSq[u1] laSq[v1], {}, "angles equal or supplementary (cos^2 condition)"],
      "Alternative" -> laRec["AngleEqualFull", laCross[u1, v1] laDot[u2, v2] - laDot[u1, v1] laCross[u2, v2], {},
        "oriented angles equal modulo 180 deg (full-angle form; implies equal or supplementary)"]]];
laTr[Equal[PlanarAngle[{a_, b_, d_}], 2 PlanarAngle[{e_, f_, g_}]], c_] /; AllTrue[{a, b, d, e, f, g}, laPointQ[c, #] &] :=
  Module[{u1 = laVec[c, b, a], v1 = laVec[c, b, d], u2 = laVec[c, f, e], v2 = laVec[c, f, g], d2, x2},
    d2 = laDot[u2, v2]; x2 = laCross[u2, v2];
    (* cos th1 = 2 cos^2 th2 - 1, squared *)
    Append[laRec["AngleDouble", laDot[u1, v1]^2 (laSq[u2] laSq[v2])^2 - (2 d2^2 - laSq[u2] laSq[v2])^2 laSq[u1] laSq[v1], {}, "squared cosine condition (sign dropped)"],
      (* z1 parallel to z2^2 = (d2^2 - x2^2) + 2 i d2 x2 *)
      "Alternative" -> laRec["AngleDoubleFull", laDot[u1, v1] 2 d2 x2 - laCross[u1, v1] (d2^2 - x2^2), {},
        "oriented angle doubled modulo 180 deg (full-angle form; implies the squared cosine condition)"]]];
laTr[Equal[2 PlanarAngle[p2_], PlanarAngle[p1_]], c_] := laTr[Equal[PlanarAngle[p1], 2 PlanarAngle[p2]], c];

(* distances, areas, signed ratios: generic metric equations *)
laMetricQ[e_] := !FreeQ[e, EuclideanDistance | Area | SignedRatio | Norm | RegionMeasure];
laTr[eq : Equal[lhs_, rhs_], c_] /; laMetricQ[eq] := laMetric[lhs, rhs, c];
laTr[e_, c_] := $Failed;

(* products / powers of distances and positive constants *)
(* EuclideanDistance[_, _] evaluates when used as a pattern argument (MatchQ, Cases, rules): HoldPattern everywhere *)
laDistProductQ[e_, c_] := MatchQ[e, HoldPattern[_?(NumericQ[#] && Positive[#] &) | EuclideanDistance[_, _] | Power[EuclideanDistance[_, _], _Integer?Positive] |
    Times[(_?(NumericQ[#] && Positive[#] &) | EuclideanDistance[_, _] | Power[EuclideanDistance[_, _], _Integer?Positive]) ..]]] &&
  AllTrue[Cases[{e}, HoldPattern[EuclideanDistance[p_, q_]] :> laPointQ[c, p] && laPointQ[c, q], Infinity], TrueQ];
laSqForm[e_, c_] := Expand[e^2 /. HoldPattern[EuclideanDistance[p_, q_]] :> Sqrt[laSq[laVec[c, p, q]]]];

laMetric[lhs_, rhs_, c_] := Module[{l = laStrip[lhs], r = laStrip[rhs], expr, num, den, nd, dvars, hyps, caveat = None},
  Which[
    (* ratio products of distances: square both sides *)
    laDistProductQ[l, c] && laDistProductQ[r, c],
    laRec["DistanceProduct", laSqForm[l, c] - laSqForm[r, c]],
    (* rational expressions in signed ratios / areas / squared distances *)
    FreeQ[{l, r}, EuclideanDistance],
    expr = Together[laMetricExpand[l - r, c]];
    num = Numerator[expr]; den = Denominator[expr];
    nd = If[NumericQ[den], {}, First /@ Rest[FactorList[den]]];
    laRec["Rational", num, nd, If[FreeQ[{l, r}, Area], None, "signed areas (orientation of the polygons assumed consistent)"]],
    True,
    (* general distance relation: distance variables d_pq with d^2 = |pq|^2, d >= 0 *)
    dvars = Union[Cases[{l, r}, HoldPattern[EuclideanDistance[p_, q_]] /; laPointQ[c, p] && laPointQ[c, q], Infinity]];
    expr = Together[laMetricExpand[(l - r) /. HoldPattern[EuclideanDistance[p_, q_]] :> laDistSymbol[p, q], c]];
    num = Numerator[expr]; den = Denominator[expr];
    nd = If[NumericQ[den], {}, First /@ Rest[FactorList[den]]];
    <|"Kind" -> "DistanceRelation", "Polynomials" -> {Expand[num]}, "NonDegenerate" -> nd,
      "Caveat" -> "distance variables (d >= 0 needed; polynomial certificates may fail)",
      "AuxiliaryVariables" -> (laDistSymbol[#[[1]], #[[2]]] & /@ dvars),
      "AuxiliaryHypotheses" -> (laDistSymbol[#[[1]], #[[2]]]^2 - laSq[laVec[c, #[[1]], #[[2]]]] & /@ dvars),
      "AuxiliaryDefinitions" -> (laDistSymbol[#[[1]], #[[2]]] -> Sqrt[laSq[laVec[c, #[[1]], #[[2]]]]] & /@ dvars)|>]];

laDistSymbol[p_, q_] := Symbol["Global`d" <> laIdent[ToString[p]] <> laIdent[ToString[q]]];

laMetricExpand[e_, c_] := e /. {
  Area[Triangle[pts_List]] :> laSignedArea[c, pts],
  Area[Polygon[pts_List]] :> laSignedArea[c, pts],
  SignedRatio[a_, p_, b_] :> laDot[laVec[c, a, p], laVec[c, a, b]]/laDot[laVec[c, p, b], laVec[c, a, b]],
  HoldPattern[EuclideanDistance[p_, q_]^2] :> laSq[laVec[c, p, q]]};

(* ------------------------------------------------------------ *)
(*  geometry: scene -> polynomial data                           *)
(* ------------------------------------------------------------ *)

Options[LeanGeometryPolynomials] = {"Normalize" -> True, "Parametric" -> True, "Coordinates" -> <||>};

laScenePoints[scene_GeometricScene] := Module[{first = First[scene]},
  Replace[Flatten[{first}], Rule[p_, _] :> p, {1}]];
laSceneHyps[scene_GeometricScene] := Module[{h = scene["Hypotheses"]}, If[ListQ[h], h, {}]];

laParamSymbol[p_] := Symbol["Global`t" <> laIdent[ToString[p]]];

LeanGeometryPolynomials::point = "The point `1` is not a symbol (it has a value or is not a plain symbol); clear it (Clear[`1`]) or rename the point.";

LeanGeometryPolynomials[scene_GeometricScene, opts : OptionsPattern[]] := Module[
  {pts, hyps, coords0, coords, fixedPts, defs = <||>, paramDefs = <||>, params = {}, defHyps = {}, rules, iter, recs, unsupported = {}, caveats = {}, polys, nds, vars, auxVars = {}, auxHyps = {}, auxDefs = {}},
  pts = laScenePoints[scene];
  With[{bad = Select[pts, Head[#] =!= Symbol &]},
    If[bad =!= {}, Message[LeanGeometryPolynomials::point, Short[First[bad], 1]]; Return[$Failed]]];
  hyps = laStrip /@ laSceneHyps[scene];
  coords0 = LeanGeometryCoordinates[First[scene] // Flatten, FilterRules[{opts}, Options[LeanGeometryCoordinates]]];
  fixedPts = Select[pts, FreeQ[coords0[#], _Symbol] || (TrueQ[OptionValue["Normalize"]] && MemberQ[pts[[;; UpTo[2]]], #]) &];
  coords = coords0;
  (* parametric definitions *)
  If[TrueQ[OptionValue["Parametric"]],
    Do[
      With[{h = hyps[[i]]},
        Replace[h, {
          Equal[p_, Midpoint[{a_, b_}]] /; laPointQ[coords0, p] && !MemberQ[fixedPts, p] && !KeyExistsQ[defs, p] && laPointQ[coords0, a] && laPointQ[coords0, b] :>
            (defs[p] = (coords0[a] + coords0[b])/2; AppendTo[defHyps, i]),
          Equal[p_, TriangleCenter[{a_, b_, d_}, "Centroid"]] /; laPointQ[coords0, p] && !MemberQ[fixedPts, p] && !KeyExistsQ[defs, p] :>
            (defs[p] = (coords0[a] + coords0[b] + coords0[d])/3; AppendTo[defHyps, i]),
          Element[p_, (Line | InfiniteLine)[{a_, b_}]] /; laPointQ[coords0, p] && !MemberQ[fixedPts, p] && !KeyExistsQ[defs, p] && laPointQ[coords0, a] && laPointQ[coords0, b] :>
            With[{t = laParamSymbol[p]},
              defs[p] = coords0[a] + t (coords0[b] - coords0[a]);
              paramDefs[t] = {p, a, b};
              AppendTo[params, t]; AppendTo[defHyps, i]]}]],
      {i, Length[hyps]}];
    (* resolve chains; drop cyclic definitions *)
    rules = KeyValueMap[Thread[coords0[#1] -> #2] &, defs] // Flatten;
    iter = 0;
    coords = coords0;
    Do[coords = coords /. rules, {25}];
    Do[If[!FreeQ[coords[p], Alternatives @@ coords0[p]],
        (* cyclic: drop definition *)
        defHyps = DeleteCases[defHyps, _?(MemberQ[Cases[hyps[[#]], p, Infinity], p] &)];
        KeyDropFrom[defs, p]],
      {p, Keys[defs]}];
    rules = KeyValueMap[Thread[coords0[#1] -> #2] &, defs] // Flatten;
    coords = coords0; Do[coords = coords /. rules, {25}]; coords = Expand /@ coords];
  (* translate the remaining hypotheses *)
  recs = Table[
    If[MemberQ[defHyps, i], Nothing,
      With[{r = laTranslate[hyps[[i]], coords]},
        If[r === $Failed, AppendTo[unsupported, hyps[[i]]]; Nothing, Append[r, "Source" -> hyps[[i]]]]]],
    {i, Length[hyps]}];
  caveats = DeleteCases[DeleteDuplicates[#["Caveat"] & /@ recs], None];
  auxVars = Flatten[Lookup[recs, "AuxiliaryVariables", {}]];
  auxHyps = Flatten[Lookup[recs, "AuxiliaryHypotheses", {}]];
  auxDefs = Flatten[Lookup[recs, "AuxiliaryDefinitions", {}]];
  polys = DeleteCases[Join[Flatten[#["Polynomials"] & /@ recs], auxHyps], 0];
  nds = DeleteDuplicates[DeleteCases[Flatten[#["NonDegenerate"] & /@ recs], _?NumericQ]];
  vars = DeleteDuplicates[Join[
    Cases[Values[coords0], _Symbol, Infinity],
    params, auxVars,
    Cases[Values[coords], _Symbol, Infinity]]];
  vars = Select[vars, !FreeQ[{Values[coords], polys, nds}, #] &];
  <|"Scene" -> scene, "Points" -> pts, "BaseCoordinates" -> coords0, "Coordinates" -> coords,
    "Definitions" -> defs, "Parameters" -> params, "ParameterDefinitions" -> paramDefs,
    "Variables" -> vars, "AuxiliaryDefinitions" -> auxDefs,
    "Hypotheses" -> recs, "Polynomials" -> polys, "NonDegenerate" -> nds,
    "Unsupported" -> unsupported, "Caveats" -> caveats,
    "Normalized" -> If[TrueQ[OptionValue["Normalize"]], pts[[;; UpTo[2]]], {}]|>];

LeanGeometryStatement[concl_, geo_Association] := Module[{r = laTranslate[concl, geo["Coordinates"]]},
  If[r === $Failed, Return[<|"Kind" -> "Unsupported", "Source" -> concl, "Polynomials" -> {}, "NonDegenerate" -> {}, "Caveat" -> None|>]];
  Append[r, "Source" -> concl]];

(* ------------------------------------------------------------ *)
(*  geometry: numeric instance check                             *)
(* ------------------------------------------------------------ *)

laInstancePoints[inst_GeometricScene, pts_List] := Module[{p = inst["Points"]},
  If[!AssociationQ[p], p = Association[p]];
  KeySelect[p, MemberQ[pts, #] &]];

(* isometry taking p1 to the origin and p2 to the positive x axis *)
laNormalizeInstance[ptsVals_Association, norm_List] := Module[{o, d, th, rot},
  If[Length[norm] < 1, Return[ptsVals]];
  o = ptsVals[norm[[1]]];
  If[Length[norm] < 2, Return[(# - o) & /@ ptsVals]];
  d = ptsVals[norm[[2]]] - o; th = ArcTan[d[[1]], d[[2]]];
  rot = RotationMatrix[-th];
  (rot . (# - o)) & /@ ptsVals];

laInstanceValues[geo_Association, inst_GeometricScene] := Module[{pv, vals = <||>, coords0 = geo["BaseCoordinates"], t, p, a, b},
  pv = laNormalizeInstance[laInstancePoints[inst, geo["Points"]], geo["Normalized"]];
  Do[If[!FreeQ[coords0[q], _Symbol],
      MapThread[If[Head[#1] === Symbol, vals[#1] = #2] &, {coords0[q], pv[q]}]], {q, geo["Points"]}];
  (* parameters t_p : p = a + t (b - a) *)
  Do[{p, a, b} = geo["ParameterDefinitions"][t];
    vals[t] = ((pv[p] - pv[a]) . (pv[b] - pv[a]))/((pv[b] - pv[a]) . (pv[b] - pv[a])), {t, geo["Parameters"]}];
  Do[vals[d[[1]]] = d[[2]] /. vals, {d, geo["AuxiliaryDefinitions"]}];
  vals];

(* residual relative to the size of the monomials (1 + ... so that a single-monomial polynomial such as xb*yc,
   whose relative residual would otherwise be 1 for every nonzero value, is judged by its absolute value) *)
laRelativeResidual[poly_, vals_Association] := Module[{terms = MonomialList[poly], v, scale},
  v = Abs[poly /. vals]; scale = Total[Abs[terms /. vals]];
  v/(1 + scale)];

(* RandomInstance satisfies its constraints only to ~1e-4 (and likes thin triangles), so the instance is first
   projected onto the hypothesis variety by Gauss-Newton iterations in all variables; the conclusion is then
   evaluated at the refined point. *)
laRefineInstance[polys_List, vars_List, vals_Association] := Module[{x, F, J, rules, Fx, dx, k = 0},
  If[polys === {} || vars === {}, Return[vals]];
  x = N[Lookup[vals, vars, 0.]];
  F = polys; J = D[polys, {vars}];
  While[k < 40,
    rules = Thread[vars -> x];
    Fx = F /. rules;
    If[Max[Abs[Fx]] < 10^-13, Break[]];
    dx = Quiet @ Check[PseudoInverse[J /. rules] . Fx, Break[]];
    x = x - dx; k++];
  Join[vals, AssociationThread[vars -> x]]];

laInstanceCheck[geo_Association, st_Association, inst_GeometricScene, tol_ : 10^-6] := Module[{vals0, vals, vars, hres, cres},
  vals0 = laInstanceValues[geo, inst];
  vars = Select[Keys[vals0], !FreeQ[{geo["Polynomials"], st["Polynomials"]}, #] &];
  vals = laRefineInstance[geo["Polynomials"], vars, vals0];
  hres = laRelativeResidual[#, vals] & /@ geo["Polynomials"];
  cres = laRelativeResidual[#, vals] & /@ st["Polynomials"];
  <|"OK" -> AllTrue[Join[hres, cres], # < tol &], "HypothesisResiduals" -> hres, "ConclusionResiduals" -> cres,
    "Values" -> vals, "RawResiduals" -> (laRelativeResidual[#, vals0] & /@ Join[geo["Polynomials"], st["Polynomials"]])|>];

(* ------------------------------------------------------------ *)
(*  geometry: theorem                                            *)
(* ------------------------------------------------------------ *)

Options[LeanGeometryTheorem] = Join[{"Name" -> Automatic, "NonDegenerate" -> {}, "MaxExponent" -> 3, "InstanceCheck" -> True,
    "AlternativeThreshold" -> 3000},
  Options[LeanGeometryPolynomials], Options[LeanTheorem]];
LeanGeometryTheorem::unsup = "The conclusion `1` is not supported by the polynomial translation.";
LeanGeometryTheorem::instance = "The numeric instance check of the translation failed (residuals `1`); the Lean theorem may not express the intended statement.";

LeanGeometryTheorem[scene_GeometricScene, concl_, opts : OptionsPattern[]] := Module[
  {geo, st, hyps, nds, extraNd, vars, name, goals, thm, inst, chk, certs, data, caveats},
  geo = LeanGeometryPolynomials[scene, Sequence @@ FilterRules[{opts}, Options[LeanGeometryPolynomials]]];
  If[!AssociationQ[geo], Return[$Failed]];
  st = LeanGeometryStatement[concl, geo];
  If[st["Kind"] === "Unsupported", Message[LeanGeometryTheorem::unsup, concl]; Return[$Failed]];
  (* a conclusion that vanishes identically after the parametric substitution (e.g. Varignon's parallelism) is
     restated without substitution, so that the Lean theorem keeps the defining hypotheses and a real conclusion *)
  If[TrueQ[OptionValue["Parametric"]] && geo["Definitions"] =!= <||> && AllTrue[st["Polynomials"], # === 0 &],
    geo = LeanGeometryPolynomials[scene, "Parametric" -> False, Sequence @@ DeleteCases[FilterRules[{opts}, Options[LeanGeometryPolynomials]], Rule["Parametric", _]]];
    st = LeanGeometryStatement[concl, geo]];
  extraNd = laToPolyGeo[#, geo] & /@ OptionValue["NonDegenerate"];
  hyps = Join[geo["Polynomials"], Lookup[st, "AuxiliaryHypotheses", {}]];
  (* declared nondegeneracy candidates: Triangle, denominators of the conclusion, option.  Further factors (the
     coefficients of constructed parameters: feet of perpendiculars, intersection points) are found by the
     triangular elimination inside LeanPolynomialCertificate when plain ideal membership fails *)
  nds = DeleteDuplicates[DeleteCases[Join[st["NonDegenerate"], geo["NonDegenerate"], extraNd], _?NumericQ]];
  vars = DeleteDuplicates[Join[geo["Variables"], Lookup[st, "AuxiliaryVariables", {}], Cases[{hyps, st["Polynomials"], nds}, _Symbol, Infinity]]];
  vars = Select[vars, !MemberQ[{Pi, E, I}, #] &];
  name = OptionValue["Name"]; If[!StringQ[name], name = "geometry_theorem"];
  goals = DeleteCases[st["Polynomials"], 0];
  If[goals === {}, goals = {0}];
  thm = LeanPolynomialTheorem[name, vars, hyps, goals, "NonDegenerate" -> nds, "MaxExponent" -> OptionValue["MaxExponent"],
    Sequence @@ DeleteCases[FilterRules[{opts}, Options[LeanTheorem]], Rule["Data" | "Proof" | "Name", _]]];
  (* a stronger, lower-degree statement of the same conclusion (full-angle form of angle relations) is used when the first
     certificate is missing or its proof is long (Lean's ring normalisation of a 10000-character linear_combination does not
     finish): it implies the first statement, so the theorem only gets stronger *)
  If[AssociationQ[Lookup[st, "Alternative", None]] &&
      (thm["CertificateStatus"] =!= "Found" || StringLength[ToString[thm["Proof"]]] > OptionValue["AlternativeThreshold"]),
    Module[{alt = st["Alternative"], goals2, thm2},
      goals2 = DeleteCases[Expand /@ alt["Polynomials"], 0];
      If[goals2 =!= {},
        thm2 = LeanPolynomialTheorem[name, vars, hyps, goals2, "NonDegenerate" -> nds, "MaxExponent" -> OptionValue["MaxExponent"],
          Sequence @@ DeleteCases[FilterRules[{opts}, Options[LeanTheorem]], Rule["Data" | "Proof" | "Name", _]]];
        If[thm2["CertificateStatus"] === "Found" &&
            (thm["CertificateStatus"] =!= "Found" || StringLength[ToString[thm2["Proof"]]] < StringLength[ToString[thm["Proof"]]]),
          thm = thm2;
          st = Join[st, KeyTake[alt, {"Kind", "Polynomials", "NonDegenerate", "Caveat"}], <|"Form" -> "Alternative"|>]]]]];
  (* numeric check *)
  chk = None; inst = None;
  If[TrueQ[OptionValue["InstanceCheck"]],
    (* RandomInstance satisfies the constraints only numerically: accept the best of three instances *)
    Do[
      inst = Quiet @ Check[RandomInstance[scene], $Failed];
      If[Head[inst] === GeometricScene,
        chk = Quiet @ Check[laInstanceCheck[geo, st, inst], $Failed];
        If[AssociationQ[chk] && TrueQ[chk["OK"]], Break[]]],
      {3}];
    If[AssociationQ[chk] && !TrueQ[chk["OK"]], Message[LeanGeometryTheorem::instance, Max[Join[chk["HypothesisResiduals"], chk["ConclusionResiduals"]]]]]];
  caveats = DeleteCases[DeleteDuplicates[Join[geo["Caveats"], {st["Caveat"]}]], None];
  data = Join[First[thm]["Data"], <|"Scene" -> scene, "Conclusion" -> concl, "Geometry" -> geo, "Statement" -> st,
    "InstanceCheck" -> chk, "Caveats" -> caveats, "Unsupported" -> geo["Unsupported"], "Instance" -> If[Head[inst] === GeometricScene, inst, None]|>];
  LeanTheorem[Append[First[thm], "Data" -> data]]];

laToPolyGeo[e_, geo_] := laToPoly[laMetricExpand[laStrip[e], geo["Coordinates"]]];

(* non-constant factors of the coefficients of the parameters in the hypotheses linear in them *)
laAutoNonDegenerate[polys_List, params_List] := DeleteDuplicates[Flatten[Table[
  If[Exponent[h, t] == 1,
    With[{cf = Coefficient[h, t]}, If[NumericQ[cf], Nothing, First /@ Rest[FactorList[cf]]]],
    Nothing], {h, polys}, {t, params}]]];

Options[LeanGeometryReport] = Join[Options[LeanGeometryTheorem], Options[LeanCheck]];
LeanGeometryReport[scene_GeometricScene, concl_, opts : OptionsPattern[]] := Module[{thm, res, inst, g},
  thm = LeanGeometryTheorem[scene, concl, Sequence @@ FilterRules[{opts}, Options[LeanGeometryTheorem]]];
  If[Head[thm] =!= LeanTheorem, Return[thm]];
  res = LeanProve[thm, Sequence @@ FilterRules[{opts}, Options[LeanCheck]]];
  inst = thm["Instance"]; If[Head[inst] =!= GeometricScene, inst = RandomInstance[scene]];
  g = Quiet @ Check[Show[inst["Graphics"], ImageSize -> 300], Graphics[{}, ImageSize -> 300]];
  Grid[{{g, Column[{
      Style[thm["Name"], Bold],
      Row[{"Conclusion: ", Style[ToString[concl, InputForm], "Input", 10]}],
      Row[{"Status: ", Style[res["Status"], Bold, laStatusColor[res["Status"]]]}],
      Row[{"Certificate: ", thm["CertificateStatus"]}],
      Row[{"Instance check: ", If[AssociationQ[thm["InstanceCheck"]], thm["InstanceCheck"]["OK"], "skipped"]}],
      Row[{"Caveats: ", If[thm["Caveats"] === {}, "none", StringRiffle[thm["Caveats"], "; "]]}],
      Row[{"Axioms: ", StringRiffle[Flatten[Values[res["Axioms"]]] // DeleteDuplicates, ", "]}],
      OpenerView[{"Lean source", Style[LeanSource[thm], "Input", 10]}],
      OpenerView[{"Result", res}]}]}}, Alignment -> Top, Spacings -> 2]];

Options[LeanGeometryConjectures] = Join[{"Prove" -> True}, Options[LeanGeometryTheorem], Options[LeanCheck]];
LeanGeometryConjectures[scene_GeometricScene, opts : OptionsPattern[]] := Module[{conj, concls, thms, statuses, res, names},
  conj = FindGeometricConjectures[scene];
  concls = If[Head[conj] === GeometricScene, conj["Conclusions"], {}];
  If[!ListQ[concls], concls = {}];
  thms = Table[Quiet @ Check[LeanGeometryTheorem[scene, concls[[i]], "Name" -> "conjecture_" <> ToString[i], "InstanceCheck" -> False,
      Sequence @@ FilterRules[{opts}, Except["Name" | "InstanceCheck", Options[LeanGeometryTheorem]]]], $Failed], {i, Length[concls]}];
  statuses = Table[Which[
      Head[thms[[i]]] =!= LeanTheorem, "Unsupported",
      thms[[i]]["CertificateStatus"] =!= "Found", "NoCertificate",
      True, "Certificate"], {i, Length[concls]}];
  If[TrueQ[OptionValue["Prove"]] && MemberQ[statuses, "Certificate"],
    res = LeanProve[Pick[thms, statuses, "Certificate"], Sequence @@ FilterRules[{opts}, Options[LeanCheck]]];
    If[Head[res] === LeanCheckResult,
      statuses = Table[If[statuses[[i]] === "Certificate", Lookup[res["TheoremStatus"], thms[[i]]["Name"], res["Status"]], statuses[[i]]], {i, Length[concls]}]]];
  Dataset[Table[<|"Conjecture" -> concls[[i]], "Status" -> statuses[[i]],
    "Caveats" -> If[Head[thms[[i]]] === LeanTheorem, StringRiffle[thms[[i]]["Caveats"], "; "], ""],
    "Theorem" -> thms[[i]]|>, {i, Length[concls]}]]];

(* ------------------------------------------------------------ *)
(*  LeanLink bridge                                              *)
(* ------------------------------------------------------------ *)

LeanLinkImport::mathlib = "LeanLinkImport compiles standalone sources only; this source imports Mathlib. Use LeanCheck.";
LeanLinkImport::noleanlink = "The paclet Wolfram/LeanLink could not be loaded.";
LeanLinkImport[t : (_LeanTheorem | {__LeanTheorem})] := LeanLinkImport[LeanSource[t]];
LeanLinkImport[src_String] := Module[{f},
  If[laImportsMathlibQ[src], Message[LeanLinkImport::mathlib]; Return[$Failed]];
  If[!MemberQ[$Packages, "Wolfram`LeanLink`"], Quiet @ Check[Needs["Wolfram`LeanLink`"], Message[LeanLinkImport::noleanlink]; Return[$Failed]]];
  f = Symbol["Wolfram`LeanLink`LeanImportString"];
  f[src]];

End[];
EndPackage[];

(* === load message === *)
Print[Style["LeanAssist \:30d1\:30c3\:30b1\:30fc\:30b8\:304c\:30ed\:30fc\:30c9\:3055\:308c\:307e\:3057\:305f\:3002", Bold]];
Print["
  LeanAssistStatus[]                      \:2192 Lean toolchain / Mathlib project / LeanLink \:306e\:72b6\:614b
  LeanCheck[src] / LeanCheckFile[file]    \:2192 Lean \:30bd\:30fc\:30b9\:3092\:30b3\:30f3\:30d1\:30a4\:30eb: \:8a3a\:65ad\:30fbsorry\:30fb#print axioms \:3092\:69cb\:9020\:5316\:3057\:3066\:8fd4\:3059
  LeanTheorem[name, vars, hyps, concl]    \:2192 WL \:306e\:547d\:984c\:304b\:3089 Lean \:306e\:5b9a\:7406 (LeanForm \:3067\:5f0f\:3092\:5909\:63db)\:3001LeanSource / LeanProve
  LeanPolynomialCertificate[g, hs, vars]  \:2192 Groebner \:57fa\:5e95\:3067 linear_combination \:306e\:4fc2\:6570 (\:8a3c\:660e\:66f8) \:3092\:8a08\:7b97
  LeanPolynomialTheorem[name, vars, hs, g] \:2192 \:591a\:9805\:5f0f\:6052\:7b49\:5f0f\:306e\:5b9a\:7406 (\:8a3c\:660e\:306f\:8a3c\:660e\:66f8\:304b\:3089\:81ea\:52d5\:751f\:6210)
  LeanGeometryPolynomials[scene]          \:2192 GeometricScene \:306e\:4eee\:5b9a\:3092\:5ea7\:6a19\:591a\:9805\:5f0f\:3078
  LeanGeometryTheorem[scene, concl]       \:2192 \:5e7e\:4f55\:306e\:5b9a\:7406: \:5ea7\:6a19\:5316 \:2192 \:8a3c\:660e\:66f8 \:2192 Lean \:8a3c\:660e (RandomInstance \:3067\:6570\:5024\:691c\:67fb)
  LeanGeometryReport / LeanGeometryConjectures \:2192 \:56f3\:30fb\:5b9a\:7406\:30fbLean \:306e\:7d50\:679c\:3092\:307e\:3068\:3081\:3066\:8868\:793a / \:4e88\:60f3\:3092\:4e00\:62ec\:8a3c\:660e
  LeanDataDefinitions[<|name -> data|>]   \:2192 WL \:30c7\:30fc\:30bf\:3092 Lean \:306e def \:306b (decide \:578b\:306e\:6709\:9650\:691c\:8a3c\:7528)
  LeanLinkImport[thm]                     \:2192 Wolfram/LeanLink \:306e LeanEnvironment \:3078 (\:5f0f\:30b0\:30e9\:30d5\:30fbtactic \:72b6\:614b)
"];
