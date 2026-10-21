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
(*   6. proof process -- Lean goal states before/after every     *)
(*      tactic (trace_state, lean --json), goal tree, certificate *)
(*      graph, cancellation of monomials, geometry step by step  *)
(*      (LeanProofTrace, LeanProofView)                          *)
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
LeanCheck::usage = "LeanCheck[src] compiles the Lean 4 source string src and returns a LeanCheckResult with the parsed diagnostics, the axioms of every theorem (#print axioms) and the `sorry` status. LeanCheck[thm] / LeanCheck[{thm1, thm2, ...}] checks LeanTheorem objects. Options: \"Mathlib\" -> Automatic (use the Mathlib project when the source imports Mathlib), \"Timeout\", \"Axioms\" -> True, \"KeepFiles\" -> False, \"FileName\", \"Directory\", \"OutputFormat\" -> \"Text\" | \"JSON\" (lean --json: every message, info messages such as trace_state included, with its exact position).";
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
LeanPolynomialTheorem::usage = "LeanPolynomialTheorem[name, vars, {h1 == 0, ...}, goal, opts] builds a LeanTheorem over \[DoubleStruckCapitalR] whose proof is the certificate found by LeanPolynomialCertificate (goal may be a list: conjunction). Options: \"NonDegenerate\" -> {d1, ...} (become hypotheses d_j \[NotEqual] 0), \"Inequalities\" -> {p >= 0, q > 0, ...} (order conditions: a nondegeneracy factor they keep away from zero is proved, not assumed, and a branch they exclude is tried; thm[\"OrderHypotheses\"], thm[\"OrderProofs\"]), \"MaxExponent\", \"Type\", and the options of LeanTheorem. thm[\"Certificates\"] holds the certificates.";

(* --- geometry --- *)
LeanGeometryCoordinates::usage = "LeanGeometryCoordinates[points] assigns symbolic coordinates {xP, yP} to point symbols. Option \"Normalize\" -> True puts the first point at the origin and the second on the x axis (an isometry: valid for every Euclidean-invariant statement).";
LeanGeometryPolynomials::usage = "LeanGeometryPolynomials[scene] translates the hypotheses of a GeometricScene into polynomial equations in the coordinates. Returns an Association with \"Coordinates\", \"Variables\", \"Parameters\", \"Hypotheses\" (one record per hypothesis), \"Polynomials\", \"NonDegenerate\", \"Inequalities\" (order conditions: segment 0 <= t <= 1, ray t >= 0, SameSide / OppositeSides, Counterclockwise / Clockwise, inside a Triangle, distances >= 0), \"Unsupported\", \"Caveats\". Options: \"Normalize\" -> True, \"Parametric\" -> True (points defined by Midpoint / Centroid / Element[p, Line[...]] are substituted: p = a + t (b - a)), \"Coordinates\" -> <|p -> {x, y}|> fixed coordinates.";
LeanGeometryStatement::usage = "LeanGeometryStatement[concl, geo] translates a geometric conclusion (the vocabulary of GeometricScene plus SignedRatio) into polynomials in the coordinates of geo = LeanGeometryPolynomials[scene]. Rational conclusions give a numerator polynomial and nondegeneracy conditions (denominators).";
LeanGeometryTheorem::usage = "LeanGeometryTheorem[scene, concl, opts] builds a LeanTheorem for a GeometricScene and a conclusion: coordinates, hypothesis polynomials, nondegeneracy conditions, certificate (Mathematica) and the Lean proof. The translation is checked numerically on a RandomInstance. Options: \"Name\", \"NonDegenerate\" -> extra conditions, \"MaxExponent\", \"Normalize\", \"Parametric\", \"InstanceCheck\" -> True, \"OrderConditions\" -> True (the order conditions of the scene prove nondegeneracy factors and exclude branches; thm[\"OrderHypotheses\"]). thm[\"Geometry\"], thm[\"Statement\"], thm[\"Certificates\"], thm[\"InstanceCheck\"] give the details.";
LeanGeometryReport::usage = "LeanGeometryReport[scene, concl, opts] shows a RandomInstance of the scene, the generated Lean theorem and the result of the Lean check (options of LeanGeometryTheorem and LeanCheck). \"ProofView\" -> True adds the proof process below (LeanProofView: construction steps on the figure, certificate graph, cancellation, deformation, Lean goal states).";
LeanGeometryConjectures::usage = "LeanGeometryConjectures[scene] runs FindGeometricConjectures and tries to prove every conjecture in Lean. Returns a Dataset (Conjecture, Status, Caveats, Theorem). Option \"Prove\" -> False only searches the certificates.";
SignedRatio::usage = "SignedRatio[a, p, b] denotes the signed ratio ap/pb of the point p on the line ab (t/(1 - t) for p = a + t (b - a)), for use in conclusions of LeanGeometryTheorem (Menelaus, Ceva, Euler line).";

(* --- LeanLink bridge --- *)
LeanLinkImport::usage = "LeanLinkImport[thm | src] compiles a Mathlib-free source with Wolfram`LeanLink`LeanImportString and returns the LeanEnvironment (expression graphs, tactic states of LeanLink).";

(* --- proof process --- *)
LeanProofTrace::usage = "LeanProofTrace[thm] compiles the proof of a LeanTheorem (or a list of them, or the theorem of a LeanCheckResult) with a trace_state before every tactic and at the end, reads the goal states from `lean --json` and returns a LeanProofTrace object: the tactic steps with the goals before and after, the goal tree and the check result. A `linear_combination e` step is traced as `linear_combination (norm := skip) e` followed by `ring1`, which shows the polynomial identity Lean checks. Properties: \"Steps\", \"ProofDataset\", \"GoalGraph\", \"States\", \"Stepper\", \"ProofLength\", \"Status\", \"Result\", \"Source\", \"Theorem\". Options: \"ExpandLinearCombination\" -> True, \"StateDisplay\" -> Automatic (goal states as Wolfram/LeanLink LeanState / LeanGoal objects when LeanLink is loaded, otherwise the same layout by LeanAssist) | \"LeanAssist\", and the options of LeanCheck.";
LeanProofView::usage = "LeanProofView[thm] shows the proof process of a LeanTheorem in tabs. Geometry theorems: the construction step by step on the figure (\"Steps\") and a deformation where the residuals of the hypotheses and of the conclusion move together (\"Deform\"). Polynomial certificates: the derivation in the style of ProofObject[\"ProofGraph\"] (\"ProofGraph\"), the certificate identity d g = Sum c_i h_i (\"Identity\") and the cancellation of the monomials that ring checks (\"Cancellation\"). Every theorem: the Lean goal states from LeanProofTrace (\"Goals\", \"GoalGraph\", \"Tactics\"). LeanProofView[thm, view] returns one view. Options: \"Trace\" -> Automatic | False | a LeanProofTrace, and the options of LeanProofTrace.";

(* --- source guard --- *)
LeanSourceGuard::usage = "LeanSourceGuard[src] returns the list of constructs of the Lean source src that LeanCheck refuses to compile ({} = accepted): commands and attributes that run code or IO at compile time (#eval, run_cmd, run_tac, elab, macro, syntax, initialize, unsafe, implemented_by, extern, @[export]), the identifiers IO, EIO, BaseIO, System., Process, raw string literals, and imports other than Mathlib, Init, Std, Batteries, Aesop, Qq, Plausible and Lean. Comments, doc strings and string literals are ignored. Every LeanCheck / LeanProve call applies it (Status \"Rejected\").";

(* --- graphs --- *)
LeanGraphTheorem::usage = "LeanGraphTheorem[g, prop, opts] builds a Lean theorem about the finite simple undirected Graph g. Mathematica decides the property and computes a certificate; Lean checks it with decide (standalone Lean, LeanAssist_info/lean/graph/FinGraph_template.lean). prop: \"Bipartite\", {\"Colorable\", k}, \"ChromaticNumber\", \"Hamiltonian\", \"PerfectMatching\", \"Connected\", \"Eulerian\", {\"Isomorphic\", h}, {\"Clique\", k}, \"Handshake\". When the property fails, the negation is proved where possible (not k-colourable, not Hamiltonian, not isomorphic: exhaustive over an explicit enumeration of at most \"MaxCandidates\" candidates; disconnected: a separating vertex set). thm[\"Claim\"] states what is proved, thm[\"Holds\"] whether the property holds. Options: \"Name\", \"Method\" -> Automatic | \"decide\" | \"native_decide\", \"MaxCandidates\" -> 400000.";
LeanGraphReport::usage = "LeanGraphReport[g, prop, opts] shows the graph with the certificate highlighted (colouring, Hamiltonian cycle, matching, spanning tree, Euler circuit order, isomorphism, clique), the claim, the Lean source and the result of the Lean check. \"ProofView\" -> True adds the Lean goal states (LeanProofView).";

(* --- logic --- *)
LeanLogicTheorem::usage = "LeanLogicTheorem[expr, opts] builds a Lean theorem for a logical formula. Propositional formulas (And, Or, Not, Implies, Equivalent, Xor, Nand, Nor over symbols) are classified by Mathematica (TautologyQ / SatisfiableQ): a tautology is proved over Prop by tauto, a contradiction as its negation, a contingent formula as (not a tautology) and (satisfiable) with Mathematica's assignments. Quantified formulas over the reals or integers (ForAll / Exists with polynomial (in)equalities) are decided by Resolve; a true statement is proved with intros and a tactic search (positivity, nlinarith with square hints, linarith, ring, norm_num, omega) or with a witness from FindInstance, a false one through its negation with a counterexample. Options: \"Name\", \"Domain\" -> Automatic | Reals | Integers | NonNegativeIntegers, \"Statement\" -> Automatic | \"Tautology\" | \"Satisfiable\" | \"Unsatisfiable\" | \"True\" | \"False\". thm[\"Claim\"], thm[\"Kind\"], thm[\"Verdict\"] describe it.";
LeanLogicReport::usage = "LeanLogicReport[expr, opts] shows the formula with a visualization (truth table for propositional formulas, a plot or region plot for quantified formulas in one or two variables), Mathematica's verdict, the Lean source and the result of the Lean check. \"ProofView\" -> True adds the Lean goal states (LeanProofView).";

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
LeanCheck::guard = "The Lean source was not compiled: it uses `1` (code or IO at compile time, or an import outside Mathlib/Init/Std/Batteries/Aesop/Qq/Plausible/Lean). See LeanSourceGuard.";
LeanCheck::dir = "\"Directory\" -> `1` is outside $TemporaryDirectory; the work directory $LeanAssistWorkDirectory is used.";

(* ---- source guard ----
   LeanCheck compiles text that may come from an LLM.  Lean runs code at compile time through #eval, run_cmd,
   elab/macro/syntax extensions, initialize, unsafe/implemented_by/extern (also inside native_decide) and IO.
   None of that is needed for a proof, so such sources are refused.  Comments, doc strings and string /
   character literals are removed first (in one left-to-right pass, so "--" or "/-" inside a string cannot hide
   code); raw string literals are refused outright because their delimiters are not tracked. *)
$laGuardStrip = RegularExpression["'(?:[^'\\\\\\n]|\\\\.)'|\"(?:[^\"\\\\]|\\\\.)*\"|/-[\\s\\S]*?-/|--[^\\n]*"];
$laGuardPatterns = {
  {"#eval\\b", "#eval"}, {"\\brun_cmd\\b", "run_cmd"}, {"\\brun_elab\\b", "run_elab"}, {"\\brun_meta\\b", "run_meta"},
  {"\\brun_tac\\b", "run_tac"}, {"\\belab\\b", "elab"}, {"\\belab_rules\\b", "elab_rules"}, {"\\bmacro\\b", "macro"},
  {"\\bmacro_rules\\b", "macro_rules"}, {"\\bsyntax\\b", "syntax"}, {"\\bdeclare_syntax_cat\\b", "declare_syntax_cat"},
  {"\\binitialize\\b", "initialize"}, {"\\bbuiltin_initialize\\b", "builtin_initialize"}, {"\\bunsafe\\b", "unsafe"},
  {"\\bimplemented_by\\b", "implemented_by"}, {"\\bextern\\b", "extern"}, {"@\\[\\s*export\\b", "@[export]"},
  {"(?<![\\w.'])IO\\b", "IO"}, {"(?<![\\w.'])EIO\\b", "EIO"}, {"(?<![\\w.'])BaseIO\\b", "BaseIO"},
  {"(?<![\\w.'])System\\.", "System."}, {"\\bunsafe\\w*IO\\b", "unsafe*IO"}, {"(?<![\\w.'])Process\\b", "Process"}};
$laGuardImports = RegularExpression["(Mathlib|Init|Std|Batteries|Aesop|Qq|Plausible|Lean)(\\.[\\w.]+)?"];

LeanSourceGuard[src_String] := Module[{code, hits},
  hits = If[StringContainsQ[src, RegularExpression["(?<![\\w.'])r#*\""]], {"raw string"}, {}];
  code = StringReplace[src, $laGuardStrip -> " "];
  hits = Join[hits, Select[$laGuardPatterns, StringContainsQ[code, RegularExpression[#[[1]]]] &][[All, 2]]];
  hits = Join[hits, ("import " <> # &) /@ Select[StringCases[code, RegularExpression["(?m)^\\s*import\\s+(\\S+)"] -> "$1"],
    !StringMatchQ[#, $laGuardImports] &]];
  DeleteDuplicates[hits]];
LeanSourceGuard[_] := {"not a string"};

laRejectedResult[src_String, hits_List] := LeanCheckResult[<|"Status" -> "Rejected", "Success" -> False,
  "Theorems" -> laTheoremNames[src], "TheoremStatus" -> AssociationMap["Rejected" &, laTheoremNames[src]], "Axioms" -> <||>,
  "Sorries" -> {}, "Errors" -> {<|"Line" -> 0, "Column" -> 0, "Severity" -> "error",
    "Message" -> "not compiled: the source uses " <> StringRiffle[hits, ", "] <> " (LeanSourceGuard)"|>},
  "Warnings" -> {}, "Messages" -> {<|"Line" -> 0, "Column" -> 0, "Severity" -> "error",
    "Message" -> "not compiled: the source uses " <> StringRiffle[hits, ", "] <> " (LeanSourceGuard)"|>},
  "Other" -> "", "Output" -> "", "ExitCode" -> None, "Time" -> 0, "Source" -> src, "File" -> None, "Command" -> {},
  "Mathlib" -> laImportsMathlibQ[src], "Guard" -> hits|>];

laUnderTemporaryQ[d_String] := StringStartsQ[ExpandFileName[d], ExpandFileName[$TemporaryDirectory], IgnoreCase -> True];

Options[LeanCheck] = {"Mathlib" -> Automatic, "Timeout" -> Automatic, "Axioms" -> True,
  "KeepFiles" -> False, "FileName" -> Automatic, "Directory" -> Automatic, "OutputFormat" -> "Text"};
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

(* `lean --json` output ("OutputFormat" -> "JSON"): one JSON object per message with its exact position.  In the text
   format info messages (trace_state, #print axioms) carry no position header, so tactic states can only be told apart
   in this format.  The #print axioms answers become "Axioms" as in the text format. *)
laReadJSONLine[ln_String] := Module[{j = Quiet @ Check[Developer`ReadRawJSONString[ln], $Failed]},
  If[AssociationQ[j], j, Quiet @ Check[ImportByteArray[StringToByteArray[ln, "UTF-8"], "RawJSON"], $Failed]]];
laParseJSONOutput[out_String] := Module[{msgs = {}, axioms = <||>, rest = {}, j, sev, data, p},
  Do[
    j = If[StringStartsQ[StringTrim[ln], "{"], laReadJSONLine[StringTrim[ln]], $Failed];
    If[!AssociationQ[j], If[StringTrim[ln] =!= "", AppendTo[rest, ln]]; Continue[]];
    sev = Replace[Lookup[j, "severity", "info"], "information" -> "info"];
    data = Lookup[j, "data", ""]; If[!StringQ[data], data = ToString[data]];
    Which[
      sev === "info" && StringMatchQ[data, RegularExpression["(?s)^'\\S+' depends on axioms: \\[.*\\]\\s*$"]],
      p = StringCases[StringReplace[data, RegularExpression["\\s*\\n\\s*"] -> " "], RegularExpression["^'(\\S+)' depends on axioms: \\[(.*)\\]"] :> {"$1", "$2"}];
      If[p =!= {}, axioms[p[[1, 1]]] = StringTrim /@ StringSplit[p[[1, 2]], ","]],
      sev === "info" && StringMatchQ[data, RegularExpression["^'\\S+' does not depend on any axioms\\s*$"]],
      axioms[First @ StringCases[data, RegularExpression["^'(\\S+)' does not depend"] :> "$1"]] = {},
      True,
      AppendTo[msgs, <|"Line" -> Lookup[Lookup[j, "pos", <||>], "line", 0], "Column" -> Lookup[Lookup[j, "pos", <||>], "column", 0],
        "Severity" -> sev, "Message" -> data,
        "EndLine" -> Lookup[Replace[Lookup[j, "endPos", <||>], Null -> <||>], "line", None],
        "EndColumn" -> Lookup[Replace[Lookup[j, "endPos", <||>], Null -> <||>], "column", None]|>]],
    {ln, StringSplit[out, {"\r\n", "\n"}]}];
  <|"Messages" -> msgs, "Axioms" -> axioms, "Other" -> StringRiffle[rest, "\n"]|>];

(* Mathematica's \[DoubleStruckCapitalN] etc. are private-use characters (U+F7A4 + k), not the Unicode letters
   Lean reads (an LLM writes n -> "\[DoubleStruckCapitalN]"): map C, N, Q, R, Z to the Unicode double-struck letters *)
$laPrivateDoubleStruck = {"\:f7a6" -> "\:2102", "\:f7b1" -> "\:2115", "\:f7b4" -> "\:211a", "\:f7b5" -> "\:211d", "\:f7bd" -> "\:2124"};
laNormalizeChars[s_String] := StringReplace[s, $laPrivateDoubleStruck];

LeanCheck[src0_String, OptionsPattern[]] := Module[
  {src = laNormalizeChars[src0], mathlib, timeout, axioms, keep, dir, name, file, outFile, names, src2, lean, lake, cmd, cwd, run, parsed,
   msgs, errors, warnings, sorries, status, ranges, thmStatus, res, guard, json},
  guard = LeanSourceGuard[src];
  If[guard =!= {}, Message[LeanCheck::guard, StringRiffle[guard, ", "]]; Return[laRejectedResult[src, guard]]];
  mathlib = OptionValue["Mathlib"]; If[mathlib === Automatic, mathlib = laImportsMathlibQ[src]];
  timeout = OptionValue["Timeout"]; If[!NumericQ[timeout], timeout = $LeanAssistTimeout];
  axioms = TrueQ[OptionValue["Axioms"]]; keep = TrueQ[OptionValue["KeepFiles"]];
  dir = OptionValue["Directory"]; If[!StringQ[dir], dir = $LeanAssistWorkDirectory];
  (* the generated .lean file is written into dir: only below $TemporaryDirectory *)
  If[!laUnderTemporaryQ[dir], Message[LeanCheck::dir, dir]; dir = $LeanAssistWorkDirectory];
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
  json = OptionValue["OutputFormat"] === "JSON";
  If[mathlib,
    If[!laMathlibReadyQ[], Message[LeanCheck::nomathlib, $LeanAssistMathlibDirectory]; Return[$Failed]];
    cmd = Join[{lake, "env", "lean"}, If[json, {"--json"}, {}], {file}]; cwd = $LeanAssistMathlibDirectory,
    If[!FileExistsQ[lean], Message[LeanCheck::nolean, lean, laToolchainName[]]; Return[$Failed]];
    cmd = Join[{lean}, If[json, {"--json"}, {}], {file}]; cwd = dir];
  run = laRunToFile[cmd, cwd, outFile, timeout];
  If[run["TimedOut"], Message[LeanCheck::timeout, timeout]];
  parsed = If[json, laParseJSONOutput[run["Output"]], laParseOutput[run["Output"]]];
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
(* binder type of quantified variables ("" = none; LeanLogicTheorem sets "\:211d", "\:2124", ...) *)
$laBinderType = "";
laBinderSuffix[] := If[StringQ[$laBinderType] && $laBinderType =!= "", " : " <> $laBinderType, ""];
laForm[Verbatim[ForAll][x_Symbol, body_], p_] := laParen["\:2200 " <> LeanIdentifier[x] <> laBinderSuffix[] <> ", " <> laForm[body, 0], p > 0];
laForm[Verbatim[ForAll][xs_List, body_], p_] := laParen["\:2200 " <> StringRiffle[LeanIdentifier /@ xs, " "] <> laBinderSuffix[] <> ", " <> laForm[body, 0], p > 0];
laForm[Verbatim[ForAll][x_, cond_, body_], p_] := laForm[ForAll[x, Implies[cond, body]], p];
laForm[Verbatim[Exists][x_Symbol, body_], p_] := laParen["\:2203 " <> LeanIdentifier[x] <> laBinderSuffix[] <> ", " <> laForm[body, 0], p > 0];
laForm[Verbatim[Exists][xs_List, body_], p_] := laParen["\:2203 " <> StringRiffle[LeanIdentifier /@ xs, " "] <> laBinderSuffix[] <> ", " <> laForm[body, 0], p > 0];
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
  "tauto" -> "Mathlib.Tactic.Tauto", "push_neg" -> "Mathlib.Tactic.Push",
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
  laNormalizeChars @ StringJoin[
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
  {G = g, usedH = {}, steps = {}, cand, pick, h, t, c, m, Q, R, k = 0, rest, coeffs, ok, factorPoly, fl, facs = {}, exps = {}, const, pruned, prunedQ = False},
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
    AppendTo[steps, <|"Index" -> pick[[1]], "Q" -> Q, "c" -> c, "m" -> m, "Variable" -> t,
      "RemainderTerms" -> If[R === 0, 0, Length[MonomialList[R, vars]]]|>];
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
      If[ListQ[alt] && TrueQ[alt[[2]]], exps = pruned; coeffs = alt[[1]]; factorPoly = Times @@ MapThread[Power, {facs, exps}]; ok = True; prunedQ = True]]];
  (* the pseudo-division steps (how the nondegeneracy factor arose), for LeanProofView *)
  <|"Found" -> ok, "Coefficients" -> coeffs, "Factor" -> factorPoly, "FactorExponents" -> exps, "Verified" -> ok, "NonDegenerate" -> facs, "Method" -> "Elimination",
    "Steps" -> (<|"Hypothesis" -> #["Index"], "Variable" -> #["Variable"], "LeadingCoefficient" -> #["c"], "Exponent" -> #["m"],
      "RemainderTerms" -> #["RemainderTerms"]|> & /@ steps), "Pruned" -> prunedQ|>];

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

Options[LeanPolynomialTheorem] = Join[{"NonDegenerate" -> {}, "MaxExponent" -> 3, "Inequalities" -> {}}, Options[LeanTheorem]];
LeanPolynomialTheorem[name_String, vars_List, hyps_List, goal_, opts : OptionsPattern[]] := Module[
  {hpolys, goals, nds, certs, hypNames, ndNames, used, proofs, proof, thmHyps, concl, thmOpts, ndUsed, type, pv, signs, orderNds,
   ordCerts, usedSigns, ordNames, ordHyps, haves, thmVars},
  type = OptionValue["Type"];
  hpolys = laToPoly /@ hyps;
  goals = laToPoly /@ Flatten[{goal}];
  nds = laToPoly /@ OptionValue["NonDegenerate"];
  signs = Select[laToSign /@ Flatten[{OptionValue["Inequalities"]}], ListQ];
  pv = laPolyVars[vars];
  hypNames = Table["h" <> ToString[i], {i, Length[hpolys]}];
  certs = LeanPolynomialCertificate[#, hpolys, pv, "NonDegenerate" -> nds, "MaxExponent" -> OptionValue["MaxExponent"]] & /@ goals;
  (* no certificate on the whole variety: the conclusion may fail only on a branch that the order conditions exclude.  The
     factors they keep away from zero are tried as further nondegeneracy candidates *)
  If[signs =!= {} && !AllTrue[certs, TrueQ[#["Found"]] &],
    orderNds = laOrderCandidates[hpolys, pv, nds, signs];
    If[orderNds =!= {},
      certs = MapThread[If[TrueQ[#1["Found"]], #1,
        LeanPolynomialCertificate[#2, hpolys, pv, "NonDegenerate" -> Join[nds, orderNds], "MaxExponent" -> OptionValue["MaxExponent"]]] &, {certs, goals}]]];
  (* nondegeneracy factors actually used by the certificates (each certificate carries its own factor list; a missing
     certificate has no exponents) *)
  ndUsed = DeleteDuplicates[Flatten[Table[If[Length[c["FactorExponents"]] == Length[c["NonDegenerate"]],
    Pick[c["NonDegenerate"], Positive /@ c["FactorExponents"]], {}], {c, certs}]]];
  ndNames = Table["hnd" <> ToString[i], {i, Length[ndUsed]}];
  (* a factor that the order conditions keep away from zero is proved in the proof, not assumed *)
  ordCerts = If[signs === {}, ConstantArray[None, Length[ndUsed]], Quiet[TimeConstrained[laNonzeroCertificate[#, signs], 20, None]] & /@ ndUsed];
  usedSigns = Union[Flatten[Table[If[AssociationQ[oc], oc["Conditions"][[All, 2]], {}], {oc, ordCerts}]]];
  ordNames = AssociationThread[usedSigns -> Table["hord" <> ToString[i], {i, Length[usedSigns]}]];
  haves = StringJoin[MapThread[If[AssociationQ[#1], laOrderProofText[#1, #2, ordNames, signs] <> "\n", ""] &, {ordCerts, ndNames}]];
  proofs = Table[With[{c = certs[[k]]},
    LeanPolynomialProof[Join[c, <|"NonDegenerate" -> ndUsed,
        "FactorExponents" -> Table[With[{pos = Position[c["NonDegenerate"], f, {1}, 1]}, If[pos === {}, 0, c["FactorExponents"][[pos[[1, 1]]]]]], {f, ndUsed}]|>],
      hypNames, ndNames]], {k, Length[goals]}];
  proof = If[Length[goals] == 1, First[proofs],
    "refine \:27e8" <> StringRiffle[ConstantArray["?_", Length[goals]], ", "] <> "\:27e9\n" <>
      StringRiffle["\:00b7 " <> StringReplace[#, "\n" -> "\n  "] & /@ proofs, "\n"]];
  (* hypotheses and conclusion as Lean text (a WL equation 0 == 0 would evaluate to True) *)
  ordHyps = (ordNames[#] -> ("0 " <> If[signs[[#, 2]], "<", "\:2264"] <> " " <> laForm[signs[[#, 1]], 10])) & /@ usedSigns;
  thmHyps = Join[MapThread[#1 -> (laForm[#2, 10] <> " = 0") &, {hypNames, hpolys}], ordHyps,
    Pick[MapThread[#1 -> (laForm[#2, 10] <> " \:2260 0") &, {ndNames, ndUsed}], AssociationQ /@ ordCerts, False]];
  concl = StringRiffle[laForm[#, 10] <> " = 0" & /@ goals, " \:2227 "];
  If[goals === {0}, proof = "rfl", proof = haves <> proof];
  (* an order condition may mention a variable that no equation has (a point only constrained by a side condition) *)
  thmVars = Join[vars, Complement[Variables[signs[[usedSigns, 1]]], pv]];
  thmOpts = DeleteCases[FilterRules[{opts}, Options[LeanTheorem]], Rule["Data" | "Proof", _]];
  LeanTheorem[name, thmVars, thmHyps, concl, "Proof" -> proof,
    "Data" -> Join[<|"Certificates" -> certs, "CertificateStatus" -> If[AllTrue[certs, TrueQ[#["Found"]] &], "Found", "NotFound"],
      "Inconsistent" -> AnyTrue[certs, TrueQ[#["Inconsistent"]] &],
      "OrderConditions" -> signs,
      "OrderHypotheses" -> Table[<|"Name" -> ordNames[j], "Poly" -> signs[[j, 1]], "Strict" -> signs[[j, 2]]|>, {j, usedSigns}],
      "OrderProofs" -> DeleteCases[MapThread[If[AssociationQ[#1], Join[#1, <|"Name" -> #2,
          "Conditions" -> ({#[[1]], ordNames /@ #[[2]]} & /@ #1["Conditions"])|>], Nothing] &, {ordCerts, ndNames}], Nothing]|>,
      Lookup[{opts}, "Data", <||>]],
    Sequence @@ thmOpts]];

laPolyVars[vars_List] := Flatten[Replace[vars, {Rule[l_List, _] :> l, Rule[s_, _] :> s, s_String :> Symbol[StringTrim[First[StringSplit[s, ":"]]]]}, {1}]];

(* ------------------------------------------------------------ *)
(*  order conditions: nondegeneracy factors d != 0 proved from   *)
(*  inequalities (the branch where d vanishes is excluded)       *)
(* ------------------------------------------------------------ *)

(* p >= 0 / p > 0 as {p, strict} *)
laToSign[GreaterEqual[a_, b_]] := laSignPair[a - b, False];
laToSign[Greater[a_, b_]] := laSignPair[a - b, True];
laToSign[LessEqual[a_, b_]] := laSignPair[b - a, False];
laToSign[Less[a_, b_]] := laSignPair[b - a, True];
laToSign[_] := $Failed;
laSignPair[e_, strict_] := With[{p = Expand[e]}, If[NumericQ[p] || !PolynomialQ[p, Variables[p]], $Failed, {p, strict}]];

laMonomialsUpTo[n_Integer, d_Integer] := Flatten[Table[laExponentVectors[n, k], {k, 0, d}], 1];
laTotalDegree[p_, vars_] := Max[Join[{0}, Total /@ Keys[CoefficientRules[p, vars]]]];

(* f != 0 from the order conditions q >= 0 / q > 0: an identity
     f r == c + Sum lambda_q q + Sum mu_m m^2
   with a polynomial multiplier r, lambda, mu >= 0 and 0 <= c <= 1, over the conditions that share a variable with f and their
   pairwise products, and squares of monomials.  The right side is positive when c > 0 or a strict q has lambda_q > 0, so
   f r != 0 and f != 0.  The multiplier degree grows from 0 (the simplest certificate wins); for each degree two exact
   linear programs: maximize c, then the weight of the strict conditions.  None if there is no such identity. *)
laNonzeroCertificate[f0_, signs_List, maxDeg_Integer : 4] := Module[
  {f = Expand[f0], fv, idx, qs, qpolys, qstrict, vars, df, dq, res = None},
  fv = Variables[f];
  If[fv === {} || signs === {}, Return[None]];
  idx = Select[Range[Length[signs]], IntersectingQ[Variables[signs[[#, 1]]], fv] &];
  If[idx === {}, Return[None]];
  qs = Join[List /@ idx, Subsets[idx, {2}]];
  qpolys = Expand[Times @@ signs[[#, 1]]] & /@ qs;
  vars = Union[fv, Variables[qpolys]];
  With[{keep = Pick[Range[Length[qs]], laTotalDegree[#, vars] <= 2 maxDeg & /@ qpolys]}, qs = qs[[keep]]; qpolys = qpolys[[keep]]];
  qstrict = (And @@ signs[[#, 2]]) & /@ qs;
  df = laTotalDegree[f, vars]; dq = Max[laTotalDegree[#, vars] & /@ qpolys];
  Do[res = laNonzeroLP[f, signs, vars, qs, qpolys, qstrict, dr, df]; If[AssociationQ[res], Break[]],
    {dr, 0, Min[maxDeg, Max[0, dq - df]]}];
  res];

laNonzeroLP[f_, signs_, vars_, qs_, qpolys_, qstrict_, dr_, df_] := Module[
  {n = Length[vars], rMon, sqMon, mono, cols, rules, monos, A, b, nr, nq, ns, x, mk},
  rMon = laMonomialsUpTo[n, dr];
  sqMon = Select[laMonomialsUpTo[n, Floor[(df + dr)/2]], Total[#] >= 1 &];
  mono[e_] := Times @@ (vars^e);
  (* columns: c, the coefficients of r, lambda, mu; every monomial of f r - c - Sum lambda q - Sum mu m^2 must vanish *)
  cols = Join[{-1}, Expand[f mono[#]] & /@ rMon, -qpolys, -(mono[#]^2) & /@ sqMon];
  rules = Association[CoefficientRules[#, vars]] & /@ cols;
  monos = Union[Flatten[Keys /@ rules, 1]];
  A = Table[Lookup[r, Key[m], 0], {m, monos}, {r, rules}];
  b = ConstantArray[{0, 0}, Length[monos]];
  {nr, nq, ns} = Length /@ {rMon, qs, sqMon};
  mk[sol_] := Module[{r = Expand[(mono /@ rMon) . sol[[2 ;; nr + 1]]], lam = sol[[nr + 2 ;; nr + nq + 1]], mu = sol[[nr + nq + 2 ;;]], conds, sqs},
    conds = Select[Transpose[{lam, qs}], #[[1]] > 0 &];
    sqs = Select[Transpose[{mu, mono /@ sqMon}], #[[1]] > 0 &];
    If[r === 0 || Expand[f r - sol[[1]] - Total[#[[1]] Times @@ signs[[#[[2]], 1]] & /@ conds] - Total[#[[1]] #[[2]]^2 & /@ sqs]] =!= 0,
      None,
      <|"Factor" -> f, "Multiplier" -> r, "Constant" -> sol[[1]], "Conditions" -> conds, "Squares" -> sqs|>]];
  x = Quiet @ LinearProgramming[Join[{-1}, ConstantArray[0, nr + nq + ns]], A, b,
    Join[{{0, 1}}, ConstantArray[{-Infinity, Infinity}, nr], ConstantArray[{0, Infinity}, nq + ns]]];
  If[VectorQ[x, NumericQ] && x[[1]] > 0, Return[mk[x]]];
  If[!MemberQ[qstrict, True], Return[None]];
  x = Quiet @ LinearProgramming[Join[{0}, ConstantArray[0, nr], If[#, -1, 0] & /@ qstrict, ConstantArray[0, ns]], A, b,
    Join[{{0, 0}}, ConstantArray[{-Infinity, Infinity}, nr], If[#, {0, 1}, {0, Infinity}] & /@ qstrict, ConstantArray[{0, Infinity}, ns]]];
  If[VectorQ[x, NumericQ] && AnyTrue[Pick[x[[nr + 2 ;; nr + nq + 1]], qstrict], # > 0 &], mk[x], None]];

(* candidate factors d for d g = Sum c_i h_i that the order conditions keep away from zero: irreducible factors of the
   hypotheses, of their Groebner basis (a branch often splits off there) and of the strict conditions *)
laOrderCandidates[hpolys_List, vars_List, nds_List, signs_List] := Module[{gb, facs},
  gb = Quiet @ TimeConstrained[GroebnerBasis[hpolys, vars, MonomialOrder -> DegreeReverseLexicographic], 10, {}];
  facs = DeleteDuplicates[Expand /@ Flatten[(First /@ Rest[FactorList[#]]) & /@ Join[hpolys, If[ListQ[gb], gb, {}], Pick[signs[[All, 1]], signs[[All, 2]]]]]];
  facs = Select[facs, !NumericQ[#] && !MemberQ[Expand[Join[nds, -nds]], #] &];
  facs = Take[SortBy[facs, {laTotalDegree[#, vars] &, LeafCount}], UpTo[12]];
  Take[Select[facs, AssociationQ[Quiet @ TimeConstrained[laNonzeroCertificate[#, signs], 10, None]] &], UpTo[4]]];

(* have hnd_j : d != 0 := by (0 < d r by linear_combination over the order conditions) *)
laOrderProofText[oc_Association, ndName_String, ordNames_Association, signs_List] := Module[{f = oc["Factor"], r = oc["Multiplier"], lhs, terms},
  lhs = If[r === 1, laForm[f, 10], "(" <> laForm[f, 0] <> ") * (" <> laForm[r, 0] <> ")"];
  terms = Join[
    (laCoefficientText[#[[1]]] <> laSignProofTerm[#[[2]], ordNames, signs]) & /@ oc["Conditions"],
    (laCoefficientText[#[[1]]] <> "sq_nonneg (" <> laForm[#[[2]], 0] <> ")") & /@ oc["Squares"]];
  "have " <> ndName <> " : " <> laForm[f, 10] <> " \:2260 0 := by\n" <>
  "  have hsign : 0 < " <> lhs <> " := by linear_combination " <> StringRiffle[terms, " + "] <> "\n" <>
  "  exact " <> If[r === 1, "hsign.ne'", "left_ne_zero_of_mul hsign.ne'"]];
laCoefficientText[1] := "";
laCoefficientText[l_] := "(" <> laForm[l, 0] <> ") * ";
laSignProofTerm[{j_}, names_, signs_] := names[j];
laSignProofTerm[{j_, k_}, names_, signs_] := If[signs[[j, 2]] && signs[[k, 2]], "mul_pos " <> names[j] <> " " <> names[k],
  "mul_nonneg " <> laNonStrictTerm[j, names, signs] <> " " <> laNonStrictTerm[k, names, signs]];
laNonStrictTerm[j_, names_, signs_] := If[signs[[j, 2]], names[j] <> ".le", names[j]];

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
(* InfiniteLine[{o, x}] / HalfLine[{o, x}] with point symbols evaluate to InfiniteLine[{0, 0}, {o, x}] ({o, x} read as a direction
   vector), so they stay Inactive like CircleThrough; the patterns below accept both forms *)
laStrip[e_] := e //. Inactive[h_] /; !MemberQ[{CircleThrough, InfiniteLine, HalfLine}, h] :> h;

(* line through two points: coefficients {a, b, c} with a x + b y + c == 0 *)
laLineCoeffs[c_, {p_, q_}] := With[{P = c[p], Q = c[q]}, {Q[[2]] - P[[2]], P[[1]] - Q[[1]], -((Q[[2]] - P[[2]]) P[[1]] + (P[[1]] - Q[[1]]) P[[2]])}];
laLinePoints[Line[{p_, q_}]] := {p, q};
laLinePoints[(InfiniteLine | Inactive[InfiniteLine])[{p_, q_}]] := {p, q};
laLinePoints[(HalfLine | Inactive[HalfLine])[{p_, q_}]] := {p, q};
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
    "AuxiliaryDefinitions" -> Flatten[Lookup[recs, "AuxiliaryDefinitions", {}]],
    "Signs" -> Flatten[Lookup[recs, "Signs", {}], 1]|>];

(* order conditions of a record: "Signs" -> {{p, strict}, ...} for p >= 0 / p > 0 *)
laSigned[rec_Association, signs_List] := Append[rec, "Signs" -> ({Expand[#[[1]]], #[[2]]} & /@ signs)];

laTr[Triangle[{p_, q_, r_}], c_] /; laPointQ[c, p] && laPointQ[c, q] && laPointQ[c, r] :=
  laRec["Triangle", {}, laCross[laVec[c, p, q], laVec[c, p, r]]];
laTr[Polygon[pts_List], c_] /; AllTrue[pts, laPointQ[c, #] &] := laRec["Polygon", {}];
laTr[(Circle | Disk)[_, _], c_] := laRec["Object", {}];
laTr[(Line | InfiniteLine | HalfLine | Inactive[InfiniteLine] | Inactive[HalfLine])[_List], c_] := laRec["Object", {}];

(* Line[{a, b}] is the segment: (p - a).(b - p) >= 0 besides collinearity; a ray: (p - a).(b - a) >= 0 *)
laTr[Element[p_, l : (Line | InfiniteLine | Inactive[InfiniteLine])[{a_, b_}]], c_] /; laPointQ[c, p] && laPointQ[c, a] && laPointQ[c, b] :=
  laSigned[laRec["OnLine", laCross[laVec[c, a, p], laVec[c, a, b]]],
    If[Head[l] === Line, {{laDot[laVec[c, a, p], laVec[c, p, b]], False}}, {}]];
laTr[Element[p_, l : (HalfLine | Inactive[HalfLine])[{a_, b_}]], c_] /; laPointQ[c, p] && laPointQ[c, a] && laPointQ[c, b] :=
  laSigned[laRec["OnLine", laCross[laVec[c, a, p], laVec[c, a, b]]], {{laDot[laVec[c, a, p], laVec[c, a, b]], False}}];
(* inside the closed triangle: p is on the inner side of every edge, times the orientation (either orientation) *)
laTr[Element[p_, Triangle[{a_, b_, d_}]], c_] /; AllTrue[{p, a, b, d}, laPointQ[c, #] &] :=
  With[{o = laCross[laVec[c, a, b], laVec[c, a, d]]},
    laSigned[laRec["InsideTriangle", {}], {{o laCross[laVec[c, a, b], laVec[c, a, p]], False}, {o laCross[laVec[c, b, d], laVec[c, b, p]], False},
      {o laCross[laVec[c, d, a], laVec[c, d, p]], False}}]];
(* sides of a line: the signed areas of (a, b, p) and (a, b, q) have the same (opposite) sign *)
laTr[GeometricAssertion[pts_List, {"SameSide", l_}], c_] /; Length[pts] >= 2 && AllTrue[pts, laPointQ[c, #] &] && ListQ[laLinePoints[l]] &&
    AllTrue[laLinePoints[l], laPointQ[c, #] &] :=
  With[{ab = laLinePoints[l]}, With[{s = laCross[laVec[c, ab[[1]], ab[[2]]], laVec[c, ab[[1]], #]] &},
    laSigned[laRec["SameSide", {}], Table[{s[pts[[1]]] s[pts[[i]]], True}, {i, 2, Length[pts]}]]]];
laTr[GeometricAssertion[{p_, q_}, {"OppositeSides", l_}], c_] /; laPointQ[c, p] && laPointQ[c, q] && ListQ[laLinePoints[l]] &&
    AllTrue[laLinePoints[l], laPointQ[c, #] &] :=
  With[{ab = laLinePoints[l]}, With[{s = laCross[laVec[c, ab[[1]], ab[[2]]], laVec[c, ab[[1]], #]] &},
    laSigned[laRec["OppositeSides", {}], {{-s[p] s[q], True}}]]];
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
laTr[GeometricAssertion[{a_, b_, d_}, kind : "Counterclockwise" | "Clockwise"], c_] /; AllTrue[{a, b, d}, laPointQ[c, #] &] :=
  With[{o = laCross[laVec[c, a, b], laVec[c, a, d]]},
    laSigned[laRec["Orientation", {}, o], {{If[kind === "Counterclockwise", o, -o], True}}]];
laTr[GeometricAssertion[Triangle[{a_, b_, d_}], kind : "Counterclockwise" | "Clockwise"], c_] := laTr[GeometricAssertion[{a, b, d}, kind], c];
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
      "Caveat" -> "distance variables d with d^2 = |pq|^2 (d >= 0 is an order condition, a hypothesis only when the proof uses it; polynomial certificates may fail)",
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
  {pts, hyps, coords0, coords, fixedPts, defs = <||>, paramDefs = <||>, params = {}, rayParams = {}, segParams = {}, paramSrc = <||>, defHyps = {},
   rules, iter, recs, unsupported = {}, caveats = {}, polys, nds, vars, auxVars = {}, auxHyps = {}, auxDefs = {}, ineqs},
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
          Element[p_, l : (Line | InfiniteLine | Inactive[InfiniteLine])[{a_, b_}]] /; laPointQ[coords0, p] && !MemberQ[fixedPts, p] && !KeyExistsQ[defs, p] && laPointQ[coords0, a] && laPointQ[coords0, b] :>
            With[{t = laParamSymbol[p]},
              defs[p] = coords0[a] + t (coords0[b] - coords0[a]);
              paramDefs[t] = {p, a, b}; paramSrc[t] = h;
              AppendTo[params, t]; AppendTo[defHyps, i];
              If[Head[l] === Line, AppendTo[segParams, t]]],
          Element[p_, (HalfLine | Inactive[HalfLine])[{a_, b_}]] /; laPointQ[coords0, p] && !MemberQ[fixedPts, p] && !KeyExistsQ[defs, p] && laPointQ[coords0, a] && laPointQ[coords0, b] :>
            With[{t = laParamSymbol[p]},
              defs[p] = coords0[a] + t (coords0[b] - coords0[a]);
              paramDefs[t] = {p, a, b}; paramSrc[t] = h;
              AppendTo[params, t]; AppendTo[rayParams, t]; AppendTo[defHyps, i]]}]],
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
      With[{r = laTranslate[laRayDistances[hyps[[i]], paramDefs, rayParams], coords]},
        If[r === $Failed, AppendTo[unsupported, hyps[[i]]]; Nothing, Append[r, "Source" -> hyps[[i]]]]]],
    {i, Length[hyps]}];
  caveats = DeleteCases[DeleteDuplicates[#["Caveat"] & /@ recs], None];
  If[AnyTrue[hyps, laRayDistances[#, paramDefs, rayParams] =!= # &], AppendTo[caveats, $laRayCaveat]];
  (* a distance variable shared by several hypotheses (|ox| in OA = OB and OC = OD) is declared once *)
  auxVars = DeleteDuplicates[Flatten[Lookup[recs, "AuxiliaryVariables", {}]]];
  auxHyps = DeleteDuplicates[Flatten[Lookup[recs, "AuxiliaryHypotheses", {}]]];
  auxDefs = DeleteDuplicates[Flatten[Lookup[recs, "AuxiliaryDefinitions", {}]]];
  polys = DeleteCases[Join[Flatten[#["Polynomials"] & /@ recs], auxHyps], 0];
  nds = DeleteDuplicates[DeleteCases[Flatten[#["NonDegenerate"] & /@ recs], _?NumericQ]];
  vars = DeleteDuplicates[Join[
    Cases[Values[coords0], _Symbol, Infinity],
    params, auxVars,
    Cases[Values[coords], _Symbol, Infinity]]];
  vars = Select[vars, !FreeQ[{Values[coords], polys, nds}, #] &];
  (* order conditions p >= 0 / p > 0 (not hypotheses of the theorem unless a proof uses them): parameters of points on
     segments (0 <= t <= 1) and rays (t >= 0), the translated hypotheses (sides, orientation, inside), distance variables *)
  ineqs = Select[Join[
      Flatten[Table[If[KeyExistsQ[defs, paramDefs[t][[1]]],
        {<|"Poly" -> t, "Strict" -> False, "Source" -> paramSrc[t], "Kind" -> "Segment"|>,
         <|"Poly" -> 1 - t, "Strict" -> False, "Source" -> paramSrc[t], "Kind" -> "Segment"|>}, {}], {t, segParams}]],
      Flatten[Table[If[KeyExistsQ[defs, paramDefs[t][[1]]], {<|"Poly" -> t, "Strict" -> False, "Source" -> paramSrc[t], "Kind" -> "Ray"|>}, {}], {t, rayParams}]],
      Flatten[Table[<|"Poly" -> s[[1]], "Strict" -> s[[2]], "Source" -> r["Source"], "Kind" -> r["Kind"]|>, {r, recs}, {s, Lookup[r, "Signs", {}]}], 1],
      <|"Poly" -> #[[1]], "Strict" -> False, "Source" -> "distance", "Kind" -> "Distance"|> & /@ auxDefs],
    !NumericQ[Expand[#Poly]] &];
  <|"Scene" -> scene, "Points" -> pts, "BaseCoordinates" -> coords0, "Coordinates" -> coords,
    "Definitions" -> defs, "Parameters" -> params, "ParameterDefinitions" -> paramDefs, "RayParameters" -> rayParams,
    "Inequalities" -> ineqs,
    "Variables" -> vars, "AuxiliaryDefinitions" -> auxDefs,
    "Hypotheses" -> recs, "Polynomials" -> polys, "NonDegenerate" -> nds,
    "Unsupported" -> unsupported, "Caveats" -> caveats,
    "Normalized" -> If[TrueQ[OptionValue["Normalize"]], pts[[;; UpTo[2]]], {}]|>];

(* |op| = t |oa| when p = o + t (a - o) lies on the ray from o through a (t >= 0): the squared form |op|^2 = t^2 |oa|^2 loses the
   sign of t, and OA = OB on the two sides of an angle would then also allow A on the opposite ray *)
laRayDistances[e_, paramDefs_Association, rays_List] := If[rays === {}, e,
  e /. Flatten[Table[With[{tt = t, p = paramDefs[t][[1]], o = paramDefs[t][[2]], a = paramDefs[t][[3]]},
    {HoldPattern[EuclideanDistance[o, p]] :> tt EuclideanDistance[o, a], HoldPattern[EuclideanDistance[p, o]] :> tt EuclideanDistance[o, a]}], {t, rays}]]];

$laRayCaveat = "points on rays: p = o + t (x - o) and |op| = t |ox| (t >= 0 is used by the translation, not a hypothesis)";

LeanGeometryStatement[concl_, geo_Association] := Module[{c0 = laStrip[concl], c1, r},
  c1 = laRayDistances[c0, geo["ParameterDefinitions"], Lookup[geo, "RayParameters", {}]];
  r = laTranslate[c1, geo["Coordinates"]];
  (* an order conclusion (sides, inside, orientation) is an inequality: not provable by an equation certificate *)
  If[r === $Failed || (Lookup[r, "Signs", {}] =!= {} && DeleteCases[r["Polynomials"], 0] === {}),
    Return[<|"Kind" -> "Unsupported", "Source" -> concl, "Polynomials" -> {}, "NonDegenerate" -> {}, "Caveat" -> None|>]];
  If[c1 =!= c0, r["Caveat"] = If[r["Caveat"] === None, $laRayCaveat, r["Caveat"] <> "; " <> $laRayCaveat]];
  If[Lookup[r, "Signs", {}] =!= {}, r["Caveat"] = If[r["Caveat"] === None, $laOrderConclusionCaveat, r["Caveat"] <> "; " <> $laOrderConclusionCaveat]];
  Append[r, "Source" -> concl]];

$laOrderConclusionCaveat = "order part of the conclusion (segment / ray) dropped: only the collinearity is proved";

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
laRefineInstance[polys_List, vars_List, vals_Association] := Module[{x, F, J, rules, Fx, Jx, dx, k = 0},
  If[polys === {} || vars === {}, Return[vals]];
  x = N[Lookup[vals, vars, 0.]];
  (* the variables that are not projected keep their values (a symbolic remainder would make the iteration blow up) *)
  F = polys /. Normal[KeyDrop[N[vals], vars]]; J = D[F, {vars}];
  While[k < 40,
    rules = Thread[vars -> x];
    Fx = F /. rules;
    If[!VectorQ[Fx, NumericQ] || Max[Abs[Fx]] < 10^-13, Break[]];
    Jx = J /. rules;
    If[!MatrixQ[Jx, NumericQ], Break[]];
    dx = Quiet @ Check[PseudoInverse[Jx] . Fx, Break[]];
    x = x - dx; k++];
  Join[vals, AssociationThread[vars -> x]]];

(* variables fixed by the construction: parameters of points on lines, coordinates of points that a hypothesis defines
   (p == ..., p \[Element] ...) and auxiliary variables.  The others (the free points) are kept by the projection *)
laGeoDependentVars[geo_Association, vars_List] := Module[{subjects},
  subjects = DeleteDuplicates[Cases[laStrip /@ laSceneHyps[geo["Scene"]], (Equal[p_Symbol, _] | Element[p_Symbol, _]) :> p]];
  Select[vars, MemberQ[geo["Parameters"], #] || MemberQ[Flatten[Lookup[geo["BaseCoordinates"], subjects, {}]], #] ||
    MemberQ[geo["AuxiliaryDefinitions"][[All, 1]], #] &]];

laInstanceCheck[geo_Association, st_Association, inst_GeometricScene, tol_ : 10^-6] := Module[{vals0, vals, vars, hres, cres, dep},
  vals0 = laInstanceValues[geo, inst];
  vars = Select[Keys[vals0], !FreeQ[{geo["Polynomials"], st["Polynomials"]}, #] &];
  (* project the dependent variables first: projecting all of them can slide the free points to a degenerate configuration
     (a flat triangle for Menelaus), where the conclusion holds for the wrong reason *)
  dep = laGeoDependentVars[geo, vars];
  vals = laRefineInstance[geo["Polynomials"], dep, vals0];
  If[dep === {} || Max[Join[{0}, laRelativeResidual[#, vals] & /@ geo["Polynomials"]]] >= tol,
    vals = laRefineInstance[geo["Polynomials"], vars, vals0]];
  hres = laRelativeResidual[#, vals] & /@ geo["Polynomials"];
  cres = laRelativeResidual[#, vals] & /@ st["Polynomials"];
  <|"OK" -> AllTrue[Join[hres, cres], # < tol &], "HypothesisResiduals" -> hres, "ConclusionResiduals" -> cres,
    "Values" -> vals, "RawResiduals" -> (laRelativeResidual[#, vals0] & /@ Join[geo["Polynomials"], st["Polynomials"]])|>];

(* ------------------------------------------------------------ *)
(*  geometry: theorem                                            *)
(* ------------------------------------------------------------ *)

Options[LeanGeometryTheorem] = Join[{"Name" -> Automatic, "NonDegenerate" -> {}, "MaxExponent" -> 3, "InstanceCheck" -> True,
    "AlternativeThreshold" -> 3000, "OrderConditions" -> True},
  Options[LeanGeometryPolynomials], Options[LeanTheorem]];
LeanGeometryTheorem::unsup = "The conclusion `1` is not supported by the polynomial translation.";
LeanGeometryTheorem::instance = "The numeric instance check of the translation failed (residuals `1`); the Lean theorem may not express the intended statement.";

LeanGeometryTheorem[scene_GeometricScene, concl_, opts : OptionsPattern[]] := Module[
  {geo, st, hyps, nds, extraNd, vars, name, goals, thm, inst, chk, certs, data, caveats, ineqs, ineqExprs, ordHyps},
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
  (* order conditions (segments, rays, sides, orientation, inside, distances >= 0): a nondegeneracy factor they keep away
     from zero is proved from them, and a branch they exclude may give a certificate that the equations alone do not *)
  ineqs = If[TrueQ[OptionValue["OrderConditions"]],
    Join[Lookup[geo, "Inequalities", {}],
      <|"Poly" -> #[[1]], "Strict" -> False, "Source" -> "distance", "Kind" -> "Distance"|> & /@ Lookup[st, "AuxiliaryDefinitions", {}]], {}];
  ineqExprs = If[#Strict, Greater[#Poly, 0], GreaterEqual[#Poly, 0]] & /@ ineqs;
  thm = LeanPolynomialTheorem[name, vars, hyps, goals, "NonDegenerate" -> nds, "MaxExponent" -> OptionValue["MaxExponent"], "Inequalities" -> ineqExprs,
    Sequence @@ DeleteCases[FilterRules[{opts}, Options[LeanTheorem]], Rule["Data" | "Proof" | "Name", _]]];
  (* a stronger, lower-degree statement of the same conclusion (full-angle form of angle relations) is used when the first
     certificate is missing or its proof is long (Lean's ring normalisation of a 10000-character linear_combination does not
     finish): it implies the first statement, so the theorem only gets stronger *)
  If[AssociationQ[Lookup[st, "Alternative", None]] &&
      (thm["CertificateStatus"] =!= "Found" || StringLength[ToString[thm["Proof"]]] > OptionValue["AlternativeThreshold"]),
    Module[{alt = st["Alternative"], goals2, thm2},
      goals2 = DeleteCases[Expand /@ alt["Polynomials"], 0];
      If[goals2 =!= {},
        thm2 = LeanPolynomialTheorem[name, vars, hyps, goals2, "NonDegenerate" -> nds, "MaxExponent" -> OptionValue["MaxExponent"], "Inequalities" -> ineqExprs,
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
  (* the order hypotheses of the Lean theorem, with the scene hypothesis each comes from *)
  ordHyps = Function[oh, Join[oh, KeyTake[SelectFirst[ineqs, Expand[#Poly] === Expand[oh["Poly"]] &, <||>], {"Source", "Kind"}]]] /@
    Lookup[First[thm]["Data"], "OrderHypotheses", {}];
  data = Join[First[thm]["Data"], <|"OrderHypotheses" -> ordHyps, "Scene" -> scene, "Conclusion" -> concl, "Geometry" -> geo, "Statement" -> st,
    "InstanceCheck" -> chk, "Caveats" -> caveats, "Unsupported" -> geo["Unsupported"], "Instance" -> If[Head[inst] === GeometricScene, inst, None]|>];
  LeanTheorem[Append[First[thm], "Data" -> data]]];

laToPolyGeo[e_, geo_] := laToPoly[laMetricExpand[laStrip[e], geo["Coordinates"]]];

(* non-constant factors of the coefficients of the parameters in the hypotheses linear in them *)
laAutoNonDegenerate[polys_List, params_List] := DeleteDuplicates[Flatten[Table[
  If[Exponent[h, t] == 1,
    With[{cf = Coefficient[h, t]}, If[NumericQ[cf], Nothing, First /@ Rest[FactorList[cf]]]],
    Nothing], {h, polys}, {t, params}]]];

Options[LeanGeometryReport] = Join[{"ProofView" -> False}, Options[LeanGeometryTheorem], Options[LeanCheck]];
LeanGeometryReport[scene_GeometricScene, concl_, opts : OptionsPattern[]] := Module[{thm, res, inst, g},
  thm = LeanGeometryTheorem[scene, concl, Sequence @@ FilterRules[{opts}, Options[LeanGeometryTheorem]]];
  If[Head[thm] =!= LeanTheorem, Return[thm]];
  res = LeanProve[thm, Sequence @@ FilterRules[{opts}, Options[LeanCheck]]];
  inst = thm["Instance"]; If[Head[inst] =!= GeometricScene, inst = RandomInstance[scene]];
  g = Quiet @ Check[Show[inst["Graphics"], ImageSize -> 300], Graphics[{}, ImageSize -> 300]];
  laWithProofView[OptionValue["ProofView"], thm, res, FilterRules[{opts}, Options[LeanCheck]]] @ Grid[{{g, Column[{
      Style[thm["Name"], Bold],
      Row[{"Conclusion: ", Style[ToString[concl, InputForm], "Input", 10]}],
      Row[{"Status: ", Style[res["Status"], Bold, laStatusColor[res["Status"]]]}],
      Row[{"Certificate: ", thm["CertificateStatus"]}],
      Row[{"Instance check: ", If[AssociationQ[thm["InstanceCheck"]], thm["InstanceCheck"]["OK"], "skipped"]}],
      Row[{"Caveats: ", If[thm["Caveats"] === {}, "none", StringRiffle[thm["Caveats"], "; "]]}],
      With[{ohs = Lookup[First[thm]["Data"], "OrderHypotheses", {}]},
        If[ohs === {}, Nothing, Row[{"Order conditions used: ", Column[Row[{laOrderHypForm[#], "  ", Style[ToString[Lookup[#, "Source", ""], InputForm], GrayLevel[0.4], 9]}] & /@ ohs]}]]],
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
(*  shared report layout                                         *)
(* ------------------------------------------------------------ *)

(* prove; with Method Automatic a failed kernel decide is retried with native_decide *)
laProveAuto[thm_LeanTheorem, method_, checkOpts_List] := Module[{res},
  res = LeanProve[thm, Sequence @@ checkOpts];
  If[method === Automatic && Head[res] === LeanCheckResult && thm["Proof"] === "decide +kernel" &&
      !MemberQ[{"Proved", "Rejected"}, res["Status"]],
    res = LeanProve[LeanTheorem[thm, "Proof" -> "native_decide"], Sequence @@ checkOpts]];
  res];

(* Lean source without a long template preamble (the template is named instead) *)
laShortSource[thm_LeanTheorem, template_String, label_String] := Module[{src = LeanSource[thm]},
  If[template =!= "" && StringContainsQ[src, template],
    StringReplace[src, template -> "-- " <> label <> " (" <> ToString[Length[StringSplit[template, "\n"]]] <> " lines)\n", 1], src]];

(* "ProofView" -> True: the report gets the proof process (LeanProofView: certificate graph, goal states, ...) below it;
   the theorem actually checked (e.g. the native_decide retry) is the one traced *)
laWithProofView[flag_, thm_LeanTheorem, res_, checkOpts_List] := Function[grid,
  If[!TrueQ[flag], grid,
    Column[{grid, OpenerView[{Style["Proof process", Bold, 12],
      LeanProofView[If[Head[res] === LeanCheckResult && Head[res["Theorem"]] === LeanTheorem, res["Theorem"], thm], All,
        Sequence @@ DeleteCases[checkOpts, Rule["OutputFormat" | "FileName", _]]]}, True]}, Spacings -> 1.5]]];

laReportGrid[pic_, thm_LeanTheorem, res_, lines_List, src_String] := Grid[{{pic, Column[Join[
    {Style[thm["Name"], Bold]},
    lines,
    {Row[{"Status: ", If[Head[res] === LeanCheckResult, Style[res["Status"], Bold, laStatusColor[res["Status"]]], res]}],
     Row[{"Axioms: ", If[Head[res] === LeanCheckResult, StringRiffle[DeleteDuplicates[Flatten[Values[res["Axioms"]]]], ", "], "-"]}],
     OpenerView[{"Lean source", Style[src, "Input", 10]}],
     OpenerView[{"Result", res}]}], Spacings -> 0.6]}}, Alignment -> Top, Spacings -> 2];

(* ------------------------------------------------------------ *)
(*  graphs: Graph -> FinGraph data + certificate -> Lean         *)
(* ------------------------------------------------------------ *)

LeanGraphTheorem::graph = "LeanGraphTheorem needs a finite simple undirected Graph (no loops, no multiple or directed edges) with at least one vertex.";
LeanGraphTheorem::prop = "Unknown property `1`. Known: \"Bipartite\", {\"Colorable\", k}, \"ChromaticNumber\", \"Hamiltonian\", \"PerfectMatching\", \"Connected\", \"Eulerian\", {\"Isomorphic\", h}, {\"Clique\", k}, \"Handshake\".";
LeanGraphTheorem::big = "The negative statement for `1` needs an exhaustive check over `2` candidates (more than \"MaxCandidates\" -> `3`); not attempted.";
LeanGraphTheorem::nocert = "`1` does not hold for this graph (Mathematica), and LeanAssist has no Lean proof of the negation for this property.";

Options[LeanGraphTheorem] = {"Name" -> Automatic, "Method" -> Automatic, "MaxCandidates" -> 400000};
$laKernelCandidates = 60000;   (* exhaustive checks up to this many candidates go to the kernel first *)

laGraphTemplate[] := laReadUTF8[FileNameJoin[{$LeanAssistDirectory, "lean", "graph", "FinGraph_template.lean"}]];

(* vertices -> 0 .. n-1 in VertexList order, edges as sorted index pairs *)
laGraphIndex[g_Graph] := Module[{vs = VertexList[g], idx},
  idx = AssociationThread[vs -> Range[0, Length[vs] - 1]];
  <|"Vertices" -> vs, "Index" -> idx, "n" -> Length[vs],
    "Edges" -> Sort[DeleteDuplicates[Sort[{idx[#[[1]]], idx[#[[2]]]}] & /@ EdgeList[g]]]|>];

laNatList[l_List] := "[" <> StringRiffle[ToString /@ l, ", "] <> "]";
laPairList[l_List] := "[" <> StringRiffle[("(" <> ToString[#[[1]]] <> ", " <> ToString[#[[2]]] <> ")") & /@ l, ", "] <> "]";
laGraphDef[name_String, gi_Association] := "def " <> name <> " : G := \:27e8" <> ToString[gi["n"]] <> ", " <> laPairList[gi["Edges"]] <> "\:27e9";

laAdjacency[n_, es_] := Module[{nb = Table[{}, {n}]},
  Do[AppendTo[nb[[e[[1]] + 1]], e[[2]]]; AppendTo[nb[[e[[2]] + 1]], e[[1]]], {e, es}]; nb];

(* proper colouring with colours 0 .. k-1 by backtracking (largest degree first); None if there is none *)
laFindColoring[n_Integer, es_List, k_Integer] := Module[{nb = laAdjacency[n, es], col, order, rec},
  col = ConstantArray[-1, n];
  order = Ordering[Length /@ nb, All, Greater];
  rec[i_] := If[i > n, True,
    With[{v = order[[i]]},
      Catch[
        Do[If[FreeQ[col[[nb[[v]] + 1]], c], col[[v]] = c; If[rec[i + 1], Throw[True]]; col[[v]] = -1], {c, 0, k - 1}];
        False]]];
  If[k >= 1 && rec[1], col, None]];

(* the vertex sequence of a cycle given by its edges (index pairs) *)
laWalkCycle[pairs_List] := Module[{adj = <||>, seq, prev = None, cur, nxt},
  Do[adj[p[[1]]] = Append[Lookup[adj, p[[1]], {}], p[[2]]]; adj[p[[2]]] = Append[Lookup[adj, p[[2]], {}], p[[1]]], {p, pairs}];
  cur = pairs[[1, 1]]; seq = {cur};
  Do[nxt = First[DeleteCases[adj[cur], prev, 1, 1]]; prev = cur; cur = nxt; AppendTo[seq, cur], {Length[pairs] - 1}];
  seq];

(* BFS from vertex 0: {parent, depth} or None (disconnected) *)
laBFSTree[n_Integer, es_List] := Module[{nb = laAdjacency[n, es], depth = ConstantArray[-1, n], parent = ConstantArray[0, n], queue = {0}, v},
  depth[[1]] = 0;
  While[queue =!= {}, v = First[queue]; queue = Rest[queue];
    Do[If[depth[[w + 1]] < 0, depth[[w + 1]] = depth[[v + 1]] + 1; parent[[w + 1]] = v; AppendTo[queue, w]], {w, nb[[v + 1]]}]];
  If[MemberQ[depth, -1], <|"Tree" -> None, "Component" -> Flatten[Position[depth, _?NonNegative]] - 1|>,
    <|"Tree" -> {parent, depth}|>]];

(* Euler circuit as a closed vertex sequence (indices) from the edge sequence of FindEulerianCycle *)
laEulerWalk[g_Graph, gi_Association] := Module[{c = Quiet @ Check[FindEulerianCycle[g], {}], pairs, try},
  If[!ListQ[c] || c === {} || c === {{}}, Return[None]];
  pairs = {gi["Index"][#[[1]]], gi["Index"][#[[2]]]} & /@ First[c];
  try[start_] := Module[{cur = start, seq = {start}, ok = True},
    Do[Which[p[[1]] == cur, cur = p[[2]], p[[2]] == cur, cur = p[[1]], True, ok = False; Break[]]; AppendTo[seq, cur], {p, pairs}];
    If[ok && Last[seq] == start, seq, None]];
  Replace[try[pairs[[1, 1]]], None :> try[pairs[[1, 2]]]]];

laGraphProp[prop_] := Replace[prop, {
  s_String :> {ToLowerCase[s], None, None},
  {s_String, k_Integer?Positive} :> {ToLowerCase[s], k, None},
  {s_String, h_Graph} :> {ToLowerCase[s], None, h},
  _ :> {None, None, None}}];

LeanGraphTheorem[g_Graph, prop_, opts : OptionsPattern[]] := Module[
  {gi, n, es, key, k, h, hi, maxc = OptionValue["MaxCandidates"], name, defs, concl = None, claim, holds, cert = None, cand = 0,
   pic = <|"Kind" -> "Plain"|>, method, col, chi, cyc, m, bfs, w, iso, p, cl, template},
  If[!(UndirectedGraphQ[g] && SimpleGraphQ[g] && VertexCount[g] >= 1), Message[LeanGraphTheorem::graph]; Return[$Failed]];
  gi = laGraphIndex[g]; n = gi["n"]; es = gi["Edges"];
  {key, k, h} = laGraphProp[prop];
  defs = {laGraphDef["gr", gi]};
  Switch[key,
    "bipartite" | "colorable" | "vertexcoloring",
      If[key === "bipartite", k = 2];
      If[!IntegerQ[k], Message[LeanGraphTheorem::prop, prop]; Return[$Failed]];
      col = laFindColoring[n, es, k];
      If[col =!= None,
        holds = True; cert = col; pic = <|"Kind" -> "Coloring", "Coloring" -> col|>;
        AppendTo[defs, "def col : List Nat := " <> laNatList[col]];
        concl = "(simple gr && properColoring gr " <> ToString[k] <> " col) = true";
        claim = "the graph has a proper colouring with " <> ToString[k] <> " colours" <> If[k == 2, " (it is bipartite)", ""],
        holds = False; cand = k^n;
        If[cand > maxc, Message[LeanGraphTheorem::big, prop, cand, maxc]; Return[$Failed]];
        concl = "(simple gr && notColorable gr " <> ToString[k] <> ") = true";
        claim = "no colouring with " <> ToString[k] <> " colours is proper" <> If[k == 2, " (the graph is not bipartite)", ""] <>
          "; exhaustive over all " <> ToString[cand] <> " colourings"],
    "chromaticnumber",
      chi = SelectFirst[Range[n], laFindColoring[n, es, #] =!= None &];
      col = laFindColoring[n, es, chi]; cand = (chi - 1)^n;
      If[cand > maxc, Message[LeanGraphTheorem::big, prop, cand, maxc]; Return[$Failed]];
      holds = True; cert = col; pic = <|"Kind" -> "Coloring", "Coloring" -> col|>;
      AppendTo[defs, "def col : List Nat := " <> laNatList[col]];
      concl = "(simple gr && properColoring gr " <> ToString[chi] <> " col && notColorable gr " <> ToString[chi - 1] <> ") = true";
      claim = "the chromatic number is " <> ToString[chi] <> ": a proper colouring with " <> ToString[chi] <>
        " colours, and none of the " <> ToString[cand] <> " colourings with " <> ToString[chi - 1] <> " colours is proper",
    "hamiltonian",
      If[n < 3, Message[LeanGraphTheorem::graph]; Return[$Failed]];
      cyc = Quiet @ Check[FindHamiltonianCycle[g], {}];
      If[ListQ[cyc] && cyc =!= {},
        cyc = laWalkCycle[{gi["Index"][#[[1]]], gi["Index"][#[[2]]]} & /@ First[cyc]];
        holds = True; cert = cyc; pic = <|"Kind" -> "Cycle", "Cycle" -> cyc|>;
        AppendTo[defs, "def cyc : List Nat := " <> laNatList[cyc]];
        concl = "(simple gr && hamiltonianCycle gr cyc) = true";
        claim = "the graph has a Hamiltonian cycle",
        holds = False; cand = (n - 1)!;
        If[cand > maxc, Message[LeanGraphTheorem::big, prop, cand, maxc]; Return[$Failed]];
        concl = "(simple gr && notHamiltonian gr) = true";
        claim = "the graph has no Hamiltonian cycle; exhaustive over all " <> ToString[cand] <> " cyclic orders starting at vertex " <> ToString[First[gi["Vertices"]], InputForm]],
    "perfectmatching",
      m = Quiet @ Check[FindIndependentEdgeSet[g], {}];
      If[ListQ[m] && 2 Length[m] == n,
        m = Sort[{gi["Index"][#[[1]]], gi["Index"][#[[2]]]}] & /@ m;
        holds = True; cert = m; pic = <|"Kind" -> "Edges", "Edges" -> m|>;
        AppendTo[defs, "def matching : List (Nat \:00d7 Nat) := " <> laPairList[m]];
        concl = "(simple gr && perfectMatching gr matching) = true";
        claim = "the graph has a perfect matching",
        Message[LeanGraphTheorem::nocert, prop]; Return[$Failed]],
    "connected",
      bfs = laBFSTree[n, es];
      If[bfs["Tree"] =!= None,
        holds = True; cert = bfs["Tree"];
        pic = <|"Kind" -> "Edges", "Edges" -> Table[Sort[{v, bfs["Tree"][[1, v + 1]]}], {v, 1, n - 1}]|>;
        AppendTo[defs, "def parent : List Nat := " <> laNatList[bfs["Tree"][[1]]]];
        AppendTo[defs, "def depth : List Nat := " <> laNatList[bfs["Tree"][[2]]]];
        concl = "(simple gr && spanningTree gr 0 parent depth) = true";
        claim = "the graph is connected (a spanning tree rooted at vertex " <> ToString[First[gi["Vertices"]], InputForm] <> ")",
        holds = False; cert = bfs["Component"]; pic = <|"Kind" -> "Vertices", "Vertices" -> cert|>;
        AppendTo[defs, "def part : List Nat := " <> laNatList[cert]];
        concl = "(simple gr && separated gr part) = true";
        claim = "the graph is disconnected: no edge leaves the highlighted vertex set"],
    "eulerian",
      w = laEulerWalk[g, gi];
      If[w =!= None,
        holds = True; cert = w; pic = <|"Kind" -> "Walk", "Walk" -> w|>;
        AppendTo[defs, "def walk : List Nat := " <> laNatList[w]];
        concl = "eulerCircuit gr walk = true";
        claim = "the graph has an Euler circuit",
        Message[LeanGraphTheorem::nocert, prop]; Return[$Failed]],
    "isomorphic",
      If[Head[h] =!= Graph || !(UndirectedGraphQ[h] && SimpleGraphQ[h]), Message[LeanGraphTheorem::graph]; Return[$Failed]];
      hi = laGraphIndex[h];
      AppendTo[defs, laGraphDef["gr2", hi]];
      iso = Quiet @ Check[FindGraphIsomorphism[g, h], {}];
      If[ListQ[iso] && iso =!= {},
        p = Table[hi["Index"][First[iso][v]], {v, gi["Vertices"]}];
        holds = True; cert = p; pic = <|"Kind" -> "Isomorphism", "Map" -> p, "H" -> h, "HIndex" -> hi|>;
        AppendTo[defs, "def iso : List Nat := " <> laNatList[p]];
        concl = "isomorphism gr gr2 iso = true";
        claim = "the two graphs are isomorphic (vertex map certificate)",
        holds = False; cand = n!;
        If[cand > maxc, Message[LeanGraphTheorem::big, prop, cand, maxc]; Return[$Failed]];
        pic = <|"Kind" -> "Isomorphism", "Map" -> None, "H" -> h, "HIndex" -> hi|>;
        concl = "notIsomorphic gr gr2 = true";
        claim = "the two graphs are not isomorphic; exhaustive over all " <> ToString[cand] <> " vertex bijections"],
    "clique",
      If[!IntegerQ[k], Message[LeanGraphTheorem::prop, prop]; Return[$Failed]];
      cl = Quiet @ Check[FindClique[g, {k}], {}];
      If[ListQ[cl] && cl =!= {},
        cl = Sort[gi["Index"] /@ First[cl]];
        holds = True; cert = cl; pic = <|"Kind" -> "Vertices", "Vertices" -> cl|>;
        AppendTo[defs, "def cl : List Nat := " <> laNatList[cl]];
        concl = "(simple gr && clique gr cl && cl.length == " <> ToString[k] <> ") = true";
        claim = "the graph contains a clique with " <> ToString[k] <> " vertices",
        Message[LeanGraphTheorem::nocert, prop]; Return[$Failed]],
    "handshake",
      holds = True;
      concl = "(simple gr && handshake gr) = true";
      claim = "the degree sum " <> ToString[Total[VertexDegree[g]]] <> " equals twice the number of edges (" <> ToString[EdgeCount[g]] <> ")",
    _, Message[LeanGraphTheorem::prop, prop]; Return[$Failed]];
  method = Replace[OptionValue["Method"], {"decide" -> "decide +kernel", Automatic :> If[cand <= $laKernelCandidates, "decide +kernel", "native_decide"]}];
  name = Replace[OptionValue["Name"], Automatic -> "graph_" <> StringReplace[If[StringQ[key], key, "theorem"], Except[WordCharacter] -> "_"]];
  template = laGraphTemplate[];
  LeanTheorem[name, {}, {}, concl, "Proof" -> method, "Imports" -> {},
    "Preamble" -> template <> "\nopen FinGraph\n\n" <> StringRiffle[defs, "\n"],
    "DocString" -> claim,
    "Data" -> <|"Kind" -> "Graph", "Graph" -> g, "Property" -> prop, "Holds" -> holds, "Claim" -> claim, "Certificate" -> cert,
      "Candidates" -> cand, "Method" -> method, "Picture" -> pic, "Index" -> gi, "Template" -> template|>]];

laGraphPicture[thm_LeanTheorem] := Module[{d = First[thm]["Data"], g, gi, vs, pic, base},
  g = d["Graph"]; gi = d["Index"]; vs = gi["Vertices"]; pic = d["Picture"];
  base = Graph[g, VertexLabels -> "Name", ImageSize -> 320];
  Switch[pic["Kind"],
    "Coloring", Graph[base, VertexStyle -> Thread[vs -> (ColorData[97] /@ (pic["Coloring"] + 1))], VertexSize -> Medium],
    "Cycle", HighlightGraph[base, UndirectedEdge @@@ Partition[vs[[pic["Cycle"] + 1]], 2, 1, 1], GraphHighlightStyle -> "Thick"],
    "Edges", HighlightGraph[base, UndirectedEdge @@@ Map[vs[[# + 1]] &, pic["Edges"], {2}], GraphHighlightStyle -> "Thick"],
    "Vertices", HighlightGraph[base, vs[[pic["Vertices"] + 1]]],
    "Walk", Graph[base, EdgeLabels -> Table[UndirectedEdge[vs[[pic["Walk"][[i]] + 1]], vs[[pic["Walk"][[i + 1]] + 1]]] -> i, {i, Length[pic["Walk"]] - 1}]],
    "Isomorphism", Module[{h = pic["H"], hi = pic["HIndex"], p = pic["Map"]},
      If[p === None, GraphicsRow[{base, Graph[h, VertexLabels -> "Name", ImageSize -> 320]}, ImageSize -> 640],
        GraphicsRow[{Graph[base, VertexStyle -> Table[vs[[i]] -> ColorData[97][i], {i, Length[vs]}], VertexSize -> Medium],
          Graph[h, VertexLabels -> "Name", VertexStyle -> Table[hi["Vertices"][[p[[i]] + 1]] -> ColorData[97][i], {i, Length[vs]}],
            VertexSize -> Medium, ImageSize -> 320]}, ImageSize -> 640]]],
    _, base]];

Options[LeanGraphReport] = Join[{"ProofView" -> False}, Options[LeanGraphTheorem], Options[LeanCheck]];
LeanGraphReport[g_Graph, prop_, opts : OptionsPattern[]] := Module[{thm, res},
  thm = LeanGraphTheorem[g, prop, Sequence @@ FilterRules[{opts}, Options[LeanGraphTheorem]]];
  If[Head[thm] =!= LeanTheorem, Return[thm]];
  res = laProveAuto[thm, OptionValue["Method"], FilterRules[{opts}, Options[LeanCheck]]];
  laWithProofView[OptionValue["ProofView"], thm, res, FilterRules[{opts}, Options[LeanCheck]]] @ laReportGrid[laGraphPicture[thm], thm, res,
    {Row[{"Property: ", Style[ToString[prop, InputForm], "Input", 10]}],
     Row[{"Mathematica: ", If[TrueQ[thm["Holds"]], "holds", "fails"]}],
     Row[{"Claim: ", thm["Claim"]}],
     Row[{"Method: ", If[Head[res] === LeanCheckResult && MemberQ[Flatten[Values[res["Axioms"]]], _?(StringContainsQ[#, "native_decide"] &)],
       "native_decide (compiled code)", thm["Method"]]}]},
    laShortSource[thm, thm["Template"], "FinGraph template (LeanAssist_info/lean/graph/FinGraph_template.lean)"]]];

(* ------------------------------------------------------------ *)
(*  logic: propositional and quantified formulas -> Lean          *)
(* ------------------------------------------------------------ *)

LeanLogicTheorem::form = "`1` is neither a propositional formula (And, Or, Not, Implies, Equivalent, Xor, Nand, Nor over symbols) nor a quantified statement (ForAll / Exists) over the reals or integers.";
LeanLogicTheorem::undecided = "Mathematica could not decide the statement (Resolve returned `1`); the Lean proof is attempted for the statement as given.";

Options[LeanLogicTheorem] = {"Name" -> Automatic, "Domain" -> Automatic, "Statement" -> Automatic};

$laPropConnectives = {And, Or, Not, Implies, Equivalent, Xor, Nand, Nor, Xnor};
laPropositionalQ[e_] := Module[{heads = Union[Cases[e, f_[___] :> f, {0, Infinity}, Heads -> False]]},
  Complement[heads, $laPropConnectives] === {} && AllTrue[Level[e, {-1}], MatchQ[#, _Symbol] &]];
laPropNormalize[e_] := e //. {HoldPattern[Xor[a_, b_]] :> Not[Equivalent[a, b]], HoldPattern[Xor[a_, b_, c__]] :> Xor[Xor[a, b], c],
  HoldPattern[Nand[a__]] :> Not[And[a]], HoldPattern[Nor[a__]] :> Not[Or[a]], HoldPattern[Xnor[a__]] :> Not[Xor[a]]};
laPropVars[e_] := Sort[DeleteCases[Union[Level[e, {-1}]], True | False]];
laTF[b_] := If[TrueQ[b], "True", "False"];

laTruthTable[e_, vars_List] := Module[{rows},
  If[Length[vars] > 6, Return[Style["(" <> ToString[2^Length[vars]] <> " rows: truth table not shown)", Gray]]];
  rows = Table[Append[t, TrueQ[e /. Thread[vars -> t]]], {t, Tuples[{True, False}, Length[vars]]}];
  Grid[Prepend[Map[Style[If[#, "T", "F"], If[#, Darker[Green], Red]] &, rows, {2}], Append[vars, TraditionalForm[e]]],
    Frame -> All, Background -> {None, {LightGray}}, ImageSize -> 320]];

(* leading quantifier block: {kind, vars, body}; kind "ForAll" | "Exists" | "None"; nested blocks of the same kind merged *)
laLeadQuant[e_] := Module[{kind = "None", vars = {}, body = e, go = True},
  While[go,
    Which[
      MatchQ[body, Verbatim[ForAll][_, _]] && kind =!= "Exists",
        kind = "ForAll"; vars = Join[vars, Flatten[{body[[1]]}]]; body = body[[2]],
      MatchQ[body, Verbatim[ForAll][_, _, _]] && kind =!= "Exists",
        kind = "ForAll"; vars = Join[vars, Flatten[{body[[1]]}]]; body = Implies[body[[2]], body[[3]]],
      MatchQ[body, Verbatim[Exists][_, _]] && kind =!= "ForAll",
        kind = "Exists"; vars = Join[vars, Flatten[{body[[1]]}]]; body = body[[2]],
      MatchQ[body, Verbatim[Exists][_, _, _]] && kind =!= "ForAll",
        kind = "Exists"; vars = Join[vars, Flatten[{body[[1]]}]]; body = And[body[[2]], body[[3]]],
      True, go = False]];
  {kind, vars, body}];

laLeanType[Reals] = "\:211d"; laLeanType[Integers] = "\:2124"; laLeanType[NonNegativeIntegers] = "\:2115"; laLeanType[_] = "\:211d";

(* hints for nlinarith: squares of the variables, their differences and sums, and of squared factors and rational
   roots of a univariate slack; for each Sqrt[t] also sqrt t >= 0 and (sqrt t)^2 = t (side goal 0 <= t by nlinarith) *)
laSquareHints[body_, vars_List] := Module[{slacks, sq = {}, v, roots, sqrts},
  sq = Join[(laForm[#, 0] &) /@ vars,
    Flatten[Table[{laForm[vars[[i]] - vars[[j]], 0], laForm[vars[[i]] + vars[[j]], 0]}, {i, Length[vars]}, {j, i + 1, Length[vars]}]]];
  slacks = Cases[body, (Less | LessEqual | Greater | GreaterEqual)[a_, b_] :> a - b, {0, Infinity}];
  Do[If[PolynomialQ[s, vars] && Length[Variables[s]] == 1,
      v = First[Variables[s]];
      sq = Join[sq, (laForm[#, 0] &) /@ Cases[FactorList[s], {f_, ex_} /; EvenQ[ex] && !NumericQ[f] :> f]];
      roots = Cases[Quiet[Solve[s == 0, v, Reals]], {Rule[v, r_]} /; NumericQ[r] && Element[r, Rationals] === True :> r];
      sq = Join[sq, (laForm[v - #, 0] &) /@ roots]],
    {s, slacks}];
  sqrts = DeleteDuplicates[Cases[body, Power[t_, 1/2] :> t, {0, Infinity}]];
  Join["sq_nonneg (" <> # <> ")" & /@ DeleteDuplicates[sq],
    Flatten[{"Real.sqrt_nonneg (" <> laForm[#, 0] <> ")",
      "Real.sq_sqrt (show (0:\:211d) \:2264 " <> laForm[#, 0] <> " by nlinarith)"} & /@ sqrts]]];

laTacticSearch[hints_List, integer_] := StringRiffle[Join[
  If[integer, {"omega", "decide"}, {}],
  {"positivity", "nlinarith [" <> StringRiffle[hints, ", "] <> "]", "linarith", "ring", "norm_num",
   "(constructor <;> nlinarith [" <> StringRiffle[hints, ", "] <> "])"}], "\n  | "];

(* plain-text form of a formula for the theorem docstring and the report *)
laClaimText[HoldPattern[Implies[a_, b_]]] := laClaimText[a] <> " implies " <> laClaimText[b];
laClaimText[e_] := ToString[e, InputForm];

laRealValue[v_] := If[Element[v, Rationals] === True, v, RootReduce[v]];

LeanLogicTheorem[e_, opts : OptionsPattern[]] := Module[
  {name, kind, vars, en, taut, sat, stmt, concl, proof, claim, verdict, data, varSpec, fals, satis, domain, type, lead, qkind, qvars, body,
   eL, truth, hints, inst, assign},
  name = OptionValue["Name"];
  Which[
    laPropositionalQ[e],
      kind = "Propositional"; vars = laPropVars[e]; en = laPropNormalize[e];
      If[vars === {}, Message[LeanLogicTheorem::form, e]; Return[$Failed]];
      taut = TautologyQ[e, vars]; sat = SatisfiableQ[e, vars];
      verdict = Which[taut, "Tautology", !sat, "Unsatisfiable", True, "Contingent"];
      stmt = Replace[OptionValue["Statement"], Automatic -> verdict];
      varSpec = StringRiffle[LeanIdentifier /@ vars, " "];
      (* SatisfiabilityInstances[f, vars, 1] = {{value of vars[[1]], value of vars[[2]], ...}} *)
      fals = If[taut, None, laTF /@ First[SatisfiabilityInstances[Not[e], vars, 1]]];
      satis = If[!sat, None, laTF /@ First[SatisfiabilityInstances[e, vars, 1]]];
      Switch[stmt,
        "Tautology",
          concl = "\:2200 " <> varSpec <> " : Prop, " <> LeanForm[en]; proof = "tauto";
          claim = "the formula is a tautology (true for all propositions " <> varSpec <> ")",
        "Unsatisfiable",
          concl = "\:2200 " <> varSpec <> " : Prop, \:00ac(" <> LeanForm[en] <> ")"; proof = "tauto";
          claim = "the formula is unsatisfiable (false for all propositions " <> varSpec <> ")",
        "Satisfiable",
          concl = "\:2203 " <> varSpec <> " : Prop, " <> LeanForm[en];
          proof = If[ListQ[satis], "exact \:27e8" <> StringRiffle[satis, ", "] <> ", by simp\:27e9", "sorry"];
          claim = "the formula is satisfiable" <> If[ListQ[satis], " (" <> StringRiffle[MapThread[ToString[#1] <> " = " <> #2 &, {vars, satis}], ", "] <> ")", ""],
        _,
          concl = "\:00ac(\:2200 " <> varSpec <> " : Prop, " <> LeanForm[en] <> ") \:2227 (\:2203 " <> varSpec <> " : Prop, " <> LeanForm[en] <> ")";
          proof = If[ListQ[fals] && ListQ[satis],
            "constructor\n\:00b7 intro h\n  have h0 := h " <> StringRiffle[fals, " "] <> "\n  simp at h0\n\:00b7 exact \:27e8" <> StringRiffle[satis, ", "] <> ", by simp\:27e9",
            "sorry"];
          claim = "the formula is neither a tautology nor a contradiction: it fails for " <>
            If[ListQ[fals], StringRiffle[MapThread[ToString[#1] <> " = " <> #2 &, {vars, fals}], ", "], "?"] <> " and holds for " <>
            If[ListQ[satis], StringRiffle[MapThread[ToString[#1] <> " = " <> #2 &, {vars, satis}], ", "], "?"]];
      If[!StringQ[name], name = "logic_" <> ToLowerCase[stmt]];
      LeanTheorem[name, {}, {}, concl, "Proof" -> proof, "Imports" -> {"Mathlib.Tactic.Tauto"},
        "DocString" -> claim,
        "Data" -> <|"Kind" -> kind, "Formula" -> e, "Variables" -> vars, "Verdict" -> verdict, "Statement" -> stmt, "Claim" -> claim,
          "Falsifying" -> fals, "Satisfying" -> satis|>],
    !FreeQ[e, Verbatim[ForAll] | Verbatim[Exists]],
      kind = "Quantified";
      domain = Replace[OptionValue["Domain"], Automatic :> If[!FreeQ[e, Integers], Integers, Reals]];
      type = laLeanType[domain];
      (* Element[x, dom] conditions are expressed by the binder type *)
      eL = e /. HoldPattern[Element[_, Integers | Reals | NonNegativeIntegers]] -> True;
      {qkind, qvars, body} = laLeadQuant[eL];
      truth = Quiet @ TimeConstrained[Resolve[e, domain], 30, $Aborted];
      verdict = Which[truth === True, "True", truth === False, "False", True, "Undecided"];
      If[verdict === "Undecided", Message[LeanLogicTheorem::undecided, Short[truth]]];
      stmt = Replace[OptionValue["Statement"], Automatic :> If[verdict === "False", "False", "True"]];
      concl = Block[{$laBinderType = type}, LeanForm[eL]];
      hints = laSquareHints[body, qvars];
      Which[
        stmt === "True" && qkind === "ForAll" && FreeQ[body, Verbatim[ForAll] | Verbatim[Exists]],
          proof = "intro " <> StringRiffle[LeanIdentifier /@ qvars, " "] <> "\nintros\nfirst\n  | " <> laTacticSearch[hints, domain =!= Reals];
          claim = "for all " <> StringRiffle[ToString /@ qvars, ", "] <> " in " <> type <> ": " <> laClaimText[body],
        stmt === "True" && qkind === "Exists" && FreeQ[body, Verbatim[ForAll] | Verbatim[Exists]],
          inst = Quiet @ Check[FindInstance[body, qvars, Integers, 1], {}];
          If[inst === {} && domain =!= Integers, inst = Quiet @ Check[FindInstance[body, qvars, domain, 1], {}]];
          If[ListQ[inst] && inst =!= {},
            assign = laRealValue /@ (qvars /. First[inst]);
            proof = "refine \:27e8" <> StringRiffle[laForm[#, 0] & /@ assign, ", "] <> ", ?_\:27e9\nfirst\n  | norm_num\n  | positivity\n  | " <>
              "nlinarith [" <> StringRiffle[hints, ", "] <> "]";
            claim = "a witness: " <> StringRiffle[MapThread[ToString[#1] <> " = " <> ToString[#2, InputForm] &, {qvars, assign}], ", "],
            proof = "sorry"; claim = "no witness found by FindInstance"],
        stmt === "False" && qkind === "ForAll" && FreeQ[body, Verbatim[ForAll] | Verbatim[Exists]],
          concl = "\:00ac(" <> concl <> ")";
          inst = Quiet @ Check[FindInstance[Not[body], qvars, Integers, 1], {}];
          If[inst === {} && domain =!= Integers, inst = Quiet @ Check[FindInstance[Not[body], qvars, domain, 1], {}]];
          If[ListQ[inst] && inst =!= {},
            assign = laRealValue /@ (qvars /. First[inst]);
            proof = "intro h\nhave h0 := h " <> StringRiffle["(" <> laForm[#, 0] <> ")" & /@ assign, " "] <> "\nnorm_num at h0";
            claim = "false: a counterexample is " <> StringRiffle[MapThread[ToString[#1] <> " = " <> ToString[#2, InputForm] &, {qvars, assign}], ", "],
            proof = "sorry"; claim = "false (Mathematica), but no counterexample was found"],
        stmt === "False" && qkind === "Exists" && FreeQ[body, Verbatim[ForAll] | Verbatim[Exists]],
          concl = "\:00ac(" <> concl <> ")";
          proof = "push_neg\nintro " <> StringRiffle[LeanIdentifier /@ qvars, " "] <> "\nfirst\n  | " <> laTacticSearch[hints, domain =!= Reals];
          claim = "false: no " <> StringRiffle[ToString /@ qvars, ", "] <> " in " <> type <> " satisfies " <> laClaimText[body],
        True,
          proof = "sorry"; claim = "alternating quantifiers: no automatic proof strategy (statement only)"];
      If[!StringQ[name], name = "logic_" <> ToLowerCase[stmt]];
      LeanTheorem[name, {}, {}, concl, "Proof" -> proof,
        "Imports" -> {Automatic, "Mathlib.Data.Real.Basic", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Positivity", "Mathlib.Tactic.NormNum",
          "Mathlib.Tactic.Ring", "Mathlib.Tactic.Push"},
        "DocString" -> claim,
        "Data" -> <|"Kind" -> kind, "Formula" -> e, "Variables" -> qvars, "Quantifier" -> qkind, "Body" -> body, "Domain" -> domain,
          "Verdict" -> verdict, "Statement" -> stmt, "Claim" -> claim, "Instance" -> If[ListQ[assign], AssociationThread[qvars -> assign], None]|>],
    True, Message[LeanLogicTheorem::form, e]; $Failed]];

laLogicPicture[thm_LeanTheorem] := Module[{d = First[thm]["Data"], vars, body, pt, r = 4, plots},
  Switch[d["Kind"],
    "Propositional", laTruthTable[d["Formula"], d["Variables"]],
    "Quantified",
      vars = d["Variables"]; body = d["Body"];
      pt = If[AssociationQ[d["Instance"]], N[Values[d["Instance"]]], None];
      If[ListQ[pt], r = Max[4, 1.5 Max[Abs[pt]]]];
      Which[
        Length[vars] == 1,
          plots = Cases[body, (Less | LessEqual | Greater | GreaterEqual | Equal)[a_, b_] :> {a, b}, {0, Infinity}];
          Quiet @ Plot[Evaluate[Flatten[plots]], {vars[[1]], -r, r}, ImageSize -> 320, PlotLegends -> (TraditionalForm /@ Flatten[plots]),
            Epilog -> If[ListQ[pt], {Red, PointSize[Large], Point[{#, 0}] & /@ pt}, {}], PlotLabel -> TraditionalForm[d["Formula"]]],
        Length[vars] == 2 && FreeQ[body, Equal],
          Quiet @ RegionPlot[Evaluate[LogicalExpand[body]], {vars[[1]], -r, r}, {vars[[2]], -r, r}, ImageSize -> 320,
            FrameLabel -> vars, PlotLabel -> TraditionalForm[d["Formula"]],
            Epilog -> If[ListQ[pt], {Red, PointSize[Large], Point[pt]}, {}]],
        True, TraditionalForm[d["Formula"]]],
    _, TraditionalForm[d["Formula"]]]];

Options[LeanLogicReport] = Join[{"ProofView" -> False}, Options[LeanLogicTheorem], Options[LeanCheck]];
LeanLogicReport[e_, opts : OptionsPattern[]] := Module[{thm, res},
  thm = LeanLogicTheorem[e, Sequence @@ FilterRules[{opts}, Options[LeanLogicTheorem]]];
  If[Head[thm] =!= LeanTheorem, Return[thm]];
  res = LeanProve[thm, Sequence @@ FilterRules[{opts}, Options[LeanCheck]]];
  laWithProofView[OptionValue["ProofView"], thm, res, FilterRules[{opts}, Options[LeanCheck]]] @ laReportGrid[laLogicPicture[thm], thm, res,
    {Row[{"Formula: ", TraditionalForm[thm["Formula"]]}],
     Row[{"Mathematica: ", thm["Verdict"]}],
     Row[{"Claim: ", thm["Claim"]}]},
    LeanSource[thm]]];

(* ------------------------------------------------------------ *)
(*  LeanLink bridge                                              *)
(* ------------------------------------------------------------ *)

LeanLinkImport::mathlib = "LeanLinkImport compiles standalone sources only; this source imports Mathlib. Use LeanCheck.";
LeanLinkImport::noleanlink = "The paclet Wolfram/LeanLink could not be loaded.";
LeanLinkImport[t : (_LeanTheorem | {__LeanTheorem})] := LeanLinkImport[LeanSource[t]];
LeanLinkImport[src_String] := Module[{f, guard = LeanSourceGuard[src]},
  If[guard =!= {}, Message[LeanCheck::guard, StringRiffle[guard, ", "]]; Return[$Failed]];
  If[laImportsMathlibQ[src], Message[LeanLinkImport::mathlib]; Return[$Failed]];
  If[!MemberQ[$Packages, "Wolfram`LeanLink`"], Quiet @ Check[Needs["Wolfram`LeanLink`"], Message[LeanLinkImport::noleanlink]; Return[$Failed]]];
  f = Symbol["Wolfram`LeanLink`LeanImportString"];
  f[src]];

(* ------------------------------------------------------------ *)
(*  proof process 1: Lean goal states (trace_state)              *)
(* ------------------------------------------------------------ *)

(* A trace_state is put before every tactic and after the last one.  Lean prints info messages without a position
   header in its text output (and not in source order), so the compile runs with --json and every state is matched to
   its trace_state by the line number.  The marker comment makes those lines unique. *)
laTraceMarker[k_Integer] := "trace_state -- \:27e6LA " <> IntegerString[k] <> "\:27e7";
laSpaces[n_Integer] := StringJoin[ConstantArray[" ", Max[n, 0]]];
laLineIndent[s_String] := StringLength[s] - StringLength[StringReplace[s, StartOfString ~~ (" " ..) -> ""]];
laCodeOf[s_String] := StringTrim[StringReplace[s, RegularExpression["\\s*--.*$"] -> ""]];
laBracketBalance[s_String] := StringCount[s, "(" | "[" | "{" | "\:27e8"] - StringCount[s, ")" | "]" | "}" | "\:27e9"];

(* tactic units of a proof (Lean's layout rule): a line at the column of its block starts a tactic, a deeper line
   continues it; a line ending with `by` opens a nested block at the column of the next line, a bullet opens one at the
   column of its content.  Blocks after `=>` (alternatives, conv) are not entered: they stay part of their tactic. *)
laTraceUnits[proof_String] := Module[
  {lines = StringSplit[proof, "\n", All], uLines = <||>, uCol = <||>, uBlock = <||>, uBullet = <||>, uOpens = <||>,
   bCol = <||>, bParent = <||>, stack = {}, cur = 0, nb = 0, nu = 0, lead = {}, pendingBy = False, code, c, newBlock, startUnit, bm},
  newBlock[col_, parent_] := (nb++; bCol[nb] = col; bParent[nb] = parent; AppendTo[stack, nb];
    If[parent > 0, uOpens[parent] = Append[uOpens[parent], nb]]; nb);
  startUnit[col_, s_] := (nu++; cur = nu;
    uLines[nu] = {s}; uCol[nu] = col; uBlock[nu] = Last[stack]; uOpens[nu] = {};
    bm = StringCases[StringReplace[s, StartOfString ~~ (" " ..) -> ""], RegularExpression["^(\:00b7|\\.)\\s+"]];
    uBullet[nu] = bm =!= {};
    If[uBullet[nu], newBlock[col + StringLength[First[bm]], nu]]);
  Do[
    code = laCodeOf[s];
    If[code === "", If[cur == 0, AppendTo[lead, s], uLines[cur] = Append[uLines[cur], s]]; Continue[]];
    c = laLineIndent[s];
    Which[
      stack === {}, newBlock[c, 0]; startUnit[c, s],
      pendingBy && c > bCol[Last[stack]], newBlock[c, cur]; startUnit[c, s],
      True,
      While[Length[stack] > 1 && c < bCol[Last[stack]], stack = Most[stack]];
      If[c == bCol[Last[stack]], startUnit[c, s], uLines[cur] = Append[uLines[cur], s]]];
    pendingBy = StringMatchQ[code, RegularExpression["(?s)(.*[\\s(\\[])?by"]],
    {s, lines}];
  <|"Lead" -> lead,
    "Units" -> Table[<|"Unit" -> u, "Lines" -> uLines[u], "Column" -> uCol[u], "Block" -> uBlock[u], "Bullet" -> uBullet[u], "Opens" -> uOpens[u]|>, {u, nu}],
    "Blocks" -> Association @ Table[b -> <|"Column" -> bCol[b], "Parent" -> bParent[b]|>, {b, nb}]|>];

laUnitText[ls_List] := StringRiffle[StringTrim /@ Select[ls, laCodeOf[#] =!= "" &], " "];

(* instrumented proof text and the step records; markers are numbered from k0 + 1 *)
laTraceInstrument[proof_String, expandLC_, k0_Integer] := Module[{p = laTraceUnits[proof], out, k = k0, steps = {}, lcQ, top, content, inner, col2, blk, usedBlocks},
  out = p["Lead"];
  If[p["Units"] === {}, Return[<|"Proof" -> proof, "Steps" -> {}, "Blocks" -> <||>, "EndMarker" -> None, "MarkerCount" -> 0|>]];
  usedBlocks = DeleteDuplicates[#Block & /@ p["Units"]];
  Do[
    With[{col = u["Column"], ls = u["Lines"]},
      k++; AppendTo[out, laSpaces[col] <> laTraceMarker[k]];
      (* the text of the tactic proper (after a bullet) and whether it is a plain one-block linear_combination *)
      content = StringReplace[StringTrim[ls[[1]]], RegularExpression["^(\:00b7|\\.)\\s+"] -> ""];
      inner = u["Bullet"] && !MemberQ[usedBlocks, First[u["Opens"]]];
      lcQ = TrueQ[expandLC] && (!u["Bullet"] && u["Opens"] === {} || inner) &&
        StringStartsQ[content, "linear_combination" ~~ (WhitespaceCharacter | "(")] && !StringContainsQ[StringRiffle[ls, " "], "(norm"] &&
        laBracketBalance[StringRiffle[laCodeOf /@ ls, " "]] == 0;
      If[lcQ,
        (* linear_combination e  ->  linear_combination (norm := skip) e; trace_state; ring1  (inside the bullet for "\:00b7 linear_combination e") *)
        blk = If[u["Bullet"], First[u["Opens"]], u["Block"]];
        col2 = If[u["Bullet"], p["Blocks"][blk]["Column"], col];
        out = Join[out, {StringReplace[ls[[1]], "linear_combination" -> "linear_combination (norm := skip)", 1]}, Rest[ls]];
        AppendTo[steps, <|"Marker" -> k, "Unit" -> u["Unit"], "Block" -> u["Block"], "Bullet" -> u["Bullet"], "Opens" -> u["Opens"],
          "Tactic" -> StringReplace[laUnitText[ls], "linear_combination" -> "linear_combination (norm := skip)", 1], "Synthetic" -> False,
          "Note" -> "linear_combination with the ring normalization deferred: the goal becomes (goal) - (combination) = 0"|>];
        k++; out = Join[out, {laSpaces[col2] <> laTraceMarker[k], laSpaces[col2] <> "ring1"}];
        AppendTo[steps, <|"Marker" -> k, "Unit" -> u["Unit"], "Block" -> blk, "Bullet" -> False, "Opens" -> {},
          "Tactic" -> "ring1", "Synthetic" -> True, "Note" -> "the normalization step of linear_combination: both sides are expanded into monomials"|>],
        out = Join[out, ls];
        AppendTo[steps, <|"Marker" -> k, "Unit" -> u["Unit"], "Block" -> u["Block"], "Bullet" -> u["Bullet"], "Opens" -> u["Opens"],
          "Tactic" -> laUnitText[ls], "Synthetic" -> False, "Note" -> None|>]]],
    {u, p["Units"]}];
  top = p["Blocks"][1]["Column"];
  k++; AppendTo[out, laSpaces[top] <> laTraceMarker[k]];
  <|"Proof" -> StringRiffle[out, "\n"], "Steps" -> steps, "Blocks" -> p["Blocks"], "EndMarker" -> k, "MarkerCount" -> k - k0|>];

(* goal states as printed by trace_state: goals separated by blank lines; "case tag", context lines "names : type"
   (continued by indented lines), the target after the turnstile *)
laParseGoals[s_String] := If[MemberQ[{"", "no goals"}, StringTrim[s]], {},
  laParseGoal /@ Select[StringSplit[s, RegularExpression["\\n[ \\t]*\\n"]], StringTrim[#] =!= "" &]];
laParseGoal[g_String] := Module[{lines = StringSplit[StringTrim[g, "\n"], "\n"], case = None, pos, ctx = {}, target},
  If[lines =!= {} && StringStartsQ[First[lines], "case "], case = StringTrim[StringDrop[First[lines], 5]]; lines = Rest[lines]];
  pos = LengthWhile[lines, !StringStartsQ[#, "\:22a2"] &] + 1;
  target = StringTrim[StringReplace[StringRiffle[lines[[pos ;;]], "\n"], {StartOfString ~~ "\:22a2" -> "", RegularExpression["\\s*\\n\\s*"] -> " "}]];
  Do[If[StringStartsQ[ln, " " | "\t"] && ctx =!= {}, ctx[[-1]] = ctx[[-1]] <> " " <> StringTrim[ln], AppendTo[ctx, ln]], {ln, lines[[;; pos - 1]]}];
  <|"case" -> case, "target" -> target,
    "context" -> (With[{sp = StringSplit[#, " : ", 2]}, If[Length[sp] == 2, <|"name" -> sp[[1]], "type" -> sp[[2]]|>, <|"name" -> #, "type" -> ""|>]] & /@ ctx)|>];
laGoalKey[g_Association] := Hash[{g["context"], g["target"]}];

(* a goal / a goal state in the style of LeanLink's LeanGoal / LeanState *)
laGoalDisplay[g_Association] := Pane[Column[{
    If[g["case"] =!= None, Style["case " <> g["case"], GrayLevel[0.45], Italic, 10], Nothing],
    If[g["context"] =!= {}, Column[Style[#name <> " : " <> #type, "Input", 10] & /@ g["context"], Spacings -> 0.15], Nothing],
    Style[StringRepeat["\[LongDash]", 14], GrayLevel[0.6]],
    Style["\:22a2 " <> g["target"], Bold, "Input", 10]}, Spacings -> 0.2],
  ImageSize -> {UpTo[560], UpTo[420]}, Scrollbars -> Automatic, AppearanceElements -> None];
laStateDisplay[goals_] := Which[
  MissingQ[goals], Style["(not reached)", GrayLevel[0.5], Italic],
  goals === {}, Style["\:2713 No goals", Darker[Green, 0.3], Bold],
  True, Column[Join[{Style[ToString[Length[goals]] <> If[Length[goals] == 1, " goal", " goals"], GrayLevel[0.45], Italic]},
    laGoalDisplay /@ goals], Spacings -> 0.8]];

(* LeanLink is used when it is loaded (Needs["Wolfram`LeanLink`"] or LeanLinkImport); this never loads the paclet itself *)
laUseLeanLinkQ[mode_] := mode =!= "LeanAssist" && MemberQ[$Packages, "Wolfram`LeanLink`"];
(* symbolic LeanLink state: no stateId, so LeanLink's tactic application refuses it instead of calling the runtime *)
laLeanLinkState[goals_List] := Symbol["Wolfram`LeanLink`LeanState"][<|
  "goals" -> (Symbol["Wolfram`LeanLink`LeanGoal"][<|"target" -> #target, "context" -> #context|>] & /@ goals),
  "goalCount" -> Length[goals], "_Symbolic" -> True|>];

Options[LeanProofTrace] = Join[{"ExpandLinearCombination" -> True, "StateDisplay" -> Automatic}, Options[LeanCheck]];
LeanProofTrace::nothm = "LeanProofTrace needs a LeanTheorem (or a LeanCheckResult that carries one).";

LeanProofTrace[r_LeanCheckResult, opts : OptionsPattern[]] := With[{t = r["Theorem"]},
  If[MatchQ[t, _LeanTheorem | {__LeanTheorem}], LeanProofTrace[t, opts], Message[LeanProofTrace::nothm]; $Failed]];
LeanProofTrace[t_LeanTheorem, opts : OptionsPattern[]] := LeanProofTrace[{t}, opts];
LeanProofTrace[ts : {__LeanTheorem}, opts : OptionsPattern[]] := Module[
  {k = 0, inst, thms2, src, res, lines, markerLine, infos, stateOf, all = {}, errors, goalsOf, name},
  inst = Table[With[{r = laTraceInstrument[ToString[t["Proof"]], OptionValue["ExpandLinearCombination"], k]}, k += r["MarkerCount"]; r], {t, ts}];
  thms2 = MapThread[LeanTheorem[#1, "Proof" -> #2["Proof"]] &, {ts, inst}];
  name = If[Length[ts] == 1, ts[[1]]["Name"], "theorems"] <> "_trace";
  res = LeanCheck[LeanSource[thms2], "OutputFormat" -> "JSON", "FileName" -> name,
    Sequence @@ DeleteCases[FilterRules[{opts}, Options[LeanCheck]], Rule["OutputFormat" | "FileName", _]]];
  If[Head[res] =!= LeanCheckResult, Return[res]];
  lines = StringSplit[res["Source"], "\n", All];
  markerLine = Association @ Flatten @ MapIndexed[
    With[{m = StringCases[#1, "-- \:27e6LA " ~~ d : DigitCharacter .. ~~ "\:27e7" :> ToExpression[d]]}, If[m === {}, {}, First[m] -> #2[[1]]]] &, lines];
  infos = GroupBy[Select[res["Messages"], #Severity === "info" &], #Line &];
  stateOf[m_] := With[{ln = Lookup[markerLine, m, None]},
    If[ln =!= None && KeyExistsQ[infos, ln], laParseGoals[First[infos[ln]]["Message"]], Missing["NotReached"]]];
  errors = res["Errors"];
  Do[all = Join[all, laTraceSteps[ts[[i]], inst[[i]], stateOf, markerLine, errors]], {i, Length[ts]}];
  all = MapIndexed[Prepend[#1, "Step" -> #2[[1]]] &, all];
  LeanProofTrace[<|"Theorem" -> If[Length[ts] == 1, First[ts], ts], "Steps" -> all, "Result" -> res, "Status" -> res["Status"],
    "Source" -> res["Source"], "Final" -> Table[<|"Theorem" -> ts[[i]]["Name"], "Goals" -> If[inst[[i]]["EndMarker"] === None, {}, stateOf[inst[[i]]["EndMarker"]]]|>, {i, Length[ts]}],
    "StateDisplay" -> OptionValue["StateDisplay"]|>]];

(* goals before / after every step and its effect (which goal it acts on, which goals it creates or closes) *)
laTraceSteps[thm_LeanTheorem, inst_Association, stateOf_, markerLine_, errors_List] := Module[
  {steps = inst["Steps"], blocks = inst["Blocks"], blockSteps, after, firstOf, out = {}, B, A, focus, extra, removed, new, keysB, keysA, eff, line, nextLine, errs},
  blockSteps = GroupBy[steps, #Block &];
  firstOf[b_] := With[{bs = Lookup[blockSteps, b, {}]}, If[bs === {}, None, First[bs]]];
  after[s_] := Module[{bs = blockSteps[s["Block"]], pos},
    pos = FirstPosition[bs[[All, "Marker"]], s["Marker"]][[1]];
    Which[
      pos < Length[bs], stateOf[bs[[pos + 1]]["Marker"]],
      blocks[s["Block"]]["Parent"] === 0, stateOf[inst["EndMarker"]],
      (* a nested `by` block / bullet must close its goals: an error would have been reported *)
      errors === {}, {},
      True, Missing["Unknown"]]];
  Do[
    B = stateOf[s["Marker"]];
    line = Lookup[markerLine, s["Marker"], None]; line = If[line === None, None, line + 1];
    nextLine = Min[Select[Values[markerLine], IntegerQ[line] && # > line &] /. {} -> {Infinity}];
    errs = If[IntegerQ[line], Select[errors, line <= #Line < nextLine &], {}];
    If[MissingQ[B],
      AppendTo[out, Join[s, <|"Theorem" -> thm["Name"], "Line" -> line, "Before" -> B, "After" -> Missing["NotReached"], "Focus" -> {}, "New" -> {},
        "Closed" -> {}, "Effect" -> "not reached", "Errors" -> errs|>]]; Continue[]];
    {focus, A} = Which[
      s["Bullet"] && s["Opens"] =!= {} && firstOf[First[s["Opens"]]] =!= None, {Take[B, UpTo[1]], stateOf[firstOf[First[s["Opens"]]]["Marker"]]},
      s["Bullet"], {Take[B, UpTo[1]], With[{a = after[s]}, If[MissingQ[a], a, Select[a, !MemberQ[laGoalKey /@ Rest[B], laGoalKey[#]] &]]]},
      True, {B, after[s]}];
    extra = If[!s["Bullet"] && s["Opens"] =!= {},
      Flatten[Table[With[{f = firstOf[b]}, If[f === None, {}, Replace[stateOf[f["Marker"]], _Missing -> {}]]], {b, s["Opens"]}]], {}];
    keysB = laGoalKey /@ B;
    If[MissingQ[A],
      removed = {}; new = Select[extra, !MemberQ[keysB, laGoalKey[#]] &],
      keysA = laGoalKey /@ A;
      removed = Select[focus, !MemberQ[keysA, laGoalKey[#]] &];
      new = DeleteDuplicatesBy[Join[Select[A, !MemberQ[keysB, laGoalKey[#]] &], Select[extra, !MemberQ[keysB, laGoalKey[#]] &]], laGoalKey]];
    eff = Which[
      errs =!= {}, "error",
      MissingQ[A] && new === {}, "unknown",
      new === {} && removed =!= {}, If[Length[removed] == 1, "closes the goal", "closes " <> ToString[Length[removed]] <> " goals"],
      new =!= {}, If[Length[new] == 1, "\[RightArrow] 1 goal", "\[RightArrow] " <> ToString[Length[new]] <> " goals"],
      True, "no change"];
    AppendTo[out, Join[s, <|"Theorem" -> thm["Name"], "Line" -> line, "Before" -> B, "After" -> A, "Focus" -> focus, "New" -> new,
      "Closed" -> If[new === {}, removed, {}], "Acting" -> If[removed =!= {}, First[removed], If[focus =!= {}, First[focus], None]],
      "Effect" -> eff, "Errors" -> errs|>]],
    {s, steps}];
  out];

(* goal tree: goals are vertices, a tactic is an edge from the goal it acts on to the goals it creates;
   a goal a tactic closes gets an edge to a terminal vertex *)
$laColAxiom = Directive[Opacity[0.7], Hue[0.26, 0.45, 0.87], EdgeForm[RGBColor[0.19, 0.372, 0.048]]];
$laColHypothesis = Directive[Opacity[0.7], Hue[0.19, 0.87, 0.7], EdgeForm[RGBColor[0.41, 0.5, 0]]];
$laColLemma = Directive[RGBColor[1., 0.72, 0.22], EdgeForm[RGBColor[0.5, 0.3, 0., 0.75]]];
$laColIdentity = Directive[Opacity[0.75], Hue[0.58, 0.35, 0.95], EdgeForm[Hue[0.6, 0.6, 0.5]]];
$laColFaded = Directive[GrayLevel[0.88], EdgeForm[GrayLevel[0.65]]];
$laColOpen = Directive[RGBColor[0.95, 0.35, 0.3], EdgeForm[RGBColor[0.5, 0.1, 0.1]]];
$laEdgeInput = Hue[0.1, 0.34, 0.49];
$laEdgeConstruct = Directive[AbsoluteDashing[{3, 1}], AbsoluteThickness[1.2], Hue[0.1, 0.34, 0.49]];

laShortTactic[t_String, n_ : 34] := If[StringLength[t] <= n, t, StringTake[t, n - 1] <> "\[Ellipsis]"];

laGoalGraph[steps_List, final_List] := Module[{ids = <||>, goalOf = <||>, n = 0, id, edges = {}, elabels = {}, vlabels = {}, vstyle = {},
    roots = {}, seen = {}, terms = {}, openKeys, vs},
  id[g_] := With[{key = laGoalKey[g]}, If[KeyExistsQ[ids, key], ids[key], n++; ids[key] = "goal " <> ToString[n]; goalOf[ids[key]] = g; ids[key]]];
  Do[If[ListQ[s["Before"]], id /@ s["Before"]];
    (* the first state of every theorem holds its statement *)
    If[ListQ[s["Before"]] && s["Before"] =!= {} && !MemberQ[seen, s["Theorem"]], AppendTo[seen, s["Theorem"]]; roots = Join[roots, id /@ s["Before"]]];
    If[AssociationQ[s["Acting"]],
      With[{from = id[s["Acting"]]},
        Do[With[{e = DirectedEdge[from, id[g], s["Step"]]}, AppendTo[edges, e];
            AppendTo[elabels, e -> Placed[Style[laShortTactic[s["Tactic"]], 8, GrayLevel[0.3]], 0.5]]], {g, s["New"]}];
        Do[With[{t = "closed " <> ToString[s["Step"]] <> "." <> ToString[Length[terms] + 1], c = id[g]},
            AppendTo[terms, t];
            With[{e = DirectedEdge[c, t, s["Step"]]}, AppendTo[edges, e];
              AppendTo[elabels, e -> Placed[Style[laShortTactic[s["Tactic"]], 8, GrayLevel[0.3]], 0.5]]]], {g, s["Closed"]}]]],
    {s, steps}];
  openKeys = Flatten[Replace[#["Goals"], _Missing -> {}] & /@ final];
  openKeys = laGoalKey /@ openKeys;
  vs = Join[Values[ids], terms];
  vlabels = Join[
    KeyValueMap[With[{g = goalOf[#2]}, #2 -> Placed[{Style[laShortTactic[g["target"], 40], 8, "Input"], laGoalDisplay[g]}, {Above, Tooltip}]] &, ids],
    (# -> Placed[Style["\:2713", 11, Bold, Darker[Green, 0.4]], Below]) & /@ terms];
  vstyle = Join[
    KeyValueMap[#2 -> Which[MemberQ[openKeys, #1], $laColOpen, MemberQ[roots, #2], $laColLemma, True, Directive[RGBColor[1., 0.85, 0.55], EdgeForm[RGBColor[0.5, 0.3, 0., 0.75]]]] &, ids],
    (# -> $laColAxiom) & /@ terms];
  Graph[vs, edges, VertexLabels -> vlabels, EdgeLabels -> elabels, VertexStyle -> vstyle,
    VertexSize -> Join[(# -> Small) & /@ terms, (# -> Medium) & /@ Values[ids]], EdgeStyle -> $laEdgeInput,
    GraphLayout -> "LayeredDigraphEmbedding", ImageSize -> {Min[640, 220 + 70 Length[vs]], Min[600, 90 + 80 Length[vs]]}, PerformanceGoal -> "Quality"]];

laTraceState[goals_, mode_] := If[ListQ[goals] && laUseLeanLinkQ[mode], laLeanLinkState[goals], laStateDisplay[goals]];

laTraceStepper[a_Association] := Module[{steps = a["Steps"], pages, n},
  n = Length[steps];
  If[n == 0, Return[Style["no tactic steps", GrayLevel[0.5]]]];
  pages = Table[Column[{
      Row[{Style["Step " <> ToString[s["Step"]] <> " / " <> ToString[n], Bold, 12], "   ",
        Style[s["Effect"], If[s["Effect"] === "error", Red, Darker[Blue]], 11], "   ", Style[s["Theorem"], GrayLevel[0.5], 10]}],
      Framed[Style[s["Tactic"], "Input", 11], FrameStyle -> GrayLevel[0.8], Background -> GrayLevel[0.97]],
      If[StringQ[s["Note"]], Style[s["Note"], GrayLevel[0.4], Italic, 10], Nothing],
      If[s["Errors"] =!= {}, Column[Style[StringTake[#Message, UpTo[600]], Red, 10] & /@ s["Errors"]], Nothing],
      Grid[{{Style["before", GrayLevel[0.5], 10], "", Style["after", GrayLevel[0.5], 10]},
        {laTraceState[s["Before"], a["StateDisplay"]], Style["\[LongRightArrow]", 16, GrayLevel[0.5]], laTraceState[s["After"], a["StateDisplay"]]}},
        Alignment -> {Left, Top}, Spacings -> {2, 0.6}]}, Spacings -> 0.8], {s, steps}];
  With[{pp = pages, nn = n},
    Manipulate[pp[[k]], {{k, 1, "step"}, 1, nn, 1, Appearance -> "Labeled"}, SaveDefinitions -> False, TrackedSymbols :> {k}]]];

laTraceDataset[a_Association] := Dataset[Table[<|"Step" -> s["Step"], "Theorem" -> s["Theorem"], "Tactic" -> s["Tactic"], "Effect" -> s["Effect"],
  "GoalsBefore" -> If[ListQ[s["Before"]], Length[s["Before"]], Missing["NotReached"]],
  "GoalsAfter" -> If[ListQ[s["After"]], Length[s["After"]], Missing["NotReached"]],
  "Goal" -> If[ListQ[s["Before"]] && s["Before"] =!= {}, laShortTactic[s["Before"][[1]]["target"], 80], ""]|>, {s, a["Steps"]}]];

LeanProofTrace[a_Association][prop_String] := Switch[prop,
  "Steps", a["Steps"],
  "ProofDataset" | "Dataset", laTraceDataset[a],
  "GoalGraph" | "ProofGraph", laGoalGraph[a["Steps"], a["Final"]],
  "States", Table[<|"Step" -> s["Step"], "Tactic" -> s["Tactic"], "Before" -> laTraceState[s["Before"], a["StateDisplay"]],
    "After" -> laTraceState[s["After"], a["StateDisplay"]]|>, {s, a["Steps"]}],
  "Stepper", laTraceStepper[a],
  "ProofLength", Count[a["Steps"], s_ /; !TrueQ[s["Synthetic"]]],
  "Properties", {"Steps", "ProofDataset", "GoalGraph", "States", "Stepper", "ProofLength", "Status", "Result", "Source", "Theorem", "Final"},
  _, Lookup[a, prop, Missing["KeyAbsent", prop]]];

LeanProofTrace /: MakeBoxes[t : LeanProofTrace[a_Association], fmt : (StandardForm | TraditionalForm)] := Module[{icon, above, below, status = a["Status"]},
  icon = Graphics[{laStatusColor[status], Disk[{0, 0.55}, 0.32], Line[{{0, 0.55}, {-0.55, -0.45}}], Line[{{0, 0.55}, {0.55, -0.45}}],
    Disk[{-0.55, -0.55}, 0.22], Disk[{0.55, -0.55}, 0.22]}, ImageSize -> 28, PlotRange -> 1.05];
  above = {
    {BoxForm`SummaryItem[{"Status: ", Style[status, Bold, laStatusColor[status]]}], BoxForm`SummaryItem[{"Steps: ", Length[a["Steps"]]}]},
    {BoxForm`SummaryItem[{"Theorems: ", StringRiffle[DeleteDuplicates[#["Theorem"] & /@ a["Steps"]], ", "]}], SpanFromLeft}};
  below = {
    {BoxForm`SummaryItem[{"Tactics: ", Column[Style[laShortTactic[#Tactic, 70], "Input", 9] & /@ Take[a["Steps"], UpTo[12]]]}], SpanFromLeft}};
  BoxForm`ArrangeSummaryBox[LeanProofTrace, t, icon, above, below, fmt, "Interpretable" -> Automatic]];

(* ------------------------------------------------------------ *)
(*  proof process 2: polynomial certificates                     *)
(* ------------------------------------------------------------ *)

laCertQ[thm_LeanTheorem] := ListQ[thm["Certificates"]] && thm["Certificates"] =!= {} && AllTrue[thm["Certificates"], AssociationQ[#] && TrueQ[#["Found"]] &];
laGeoQ[thm_LeanTheorem] := AssociationQ[thm["Geometry"]];

(* compact display of a polynomial *)
laPolyForm[p_, n_ : 2500] := Module[{f = If[LeafCount[p] < n, Quiet @ TimeConstrained[Factor[p], 5, p], p]},
  If[LeafCount[f] > 400, Short[TraditionalForm[f], 3], TraditionalForm[f]]];

(* the geometric source of every hypothesis polynomial h_i (in the order of the theorem's hypotheses) *)
laHypSources[thm_LeanTheorem] := Module[{cert = First[thm["Certificates"]], geo = thm["Geometry"], st = thm["Statement"], pairs, n},
  n = Length[cert["Hypotheses"]];
  If[!AssociationQ[geo],
    Return[Table[<|"Name" -> "h" <> ToString[i], "Poly" -> cert["Hypotheses"][[i]], "Source" -> None, "Kind" -> "Hypothesis", "Index" -> 1|>, {i, n}]]];
  pairs = Join[
    Flatten[Table[With[{r = rec}, MapIndexed[<|"Poly" -> #1, "Source" -> r["Source"], "Kind" -> r["Kind"], "Index" -> #2[[1]]|> &, r["Polynomials"]]], {rec, geo["Hypotheses"]}], 1],
    DeleteDuplicatesBy[Flatten[Table[With[{r = rec}, <|"Poly" -> #, "Source" -> r["Source"], "Kind" -> "Distance", "Index" -> 1|> & /@ Lookup[r, "AuxiliaryHypotheses", {}]],
      {rec, geo["Hypotheses"]}], 1], #Poly &],
    <|"Poly" -> #, "Source" -> Lookup[st, "Source", None], "Kind" -> "Auxiliary", "Index" -> 1|> & /@ Lookup[st, "AuxiliaryHypotheses", {}]];
  pairs = Select[pairs, #Poly =!= 0 &];
  If[Length[pairs] =!= n, pairs = Table[<|"Poly" -> cert["Hypotheses"][[i]], "Source" -> None, "Kind" -> "Hypothesis", "Index" -> 1|>, {i, n}]];
  MapIndexed[Join[#1, <|"Name" -> "h" <> ToString[#2[[1]]], "Poly" -> cert["Hypotheses"][[#2[[1]]]]|>] &, pairs]];

(* nondegeneracy factors used by the certificates, as in LeanPolynomialTheorem (hnd1, hnd2, ...) *)
laNonDegUsed[thm_LeanTheorem] := DeleteDuplicates[Flatten[Table[Pick[c["NonDegenerate"], Positive /@ c["FactorExponents"]], {c, thm["Certificates"]}]]];
(* a nondegeneracy factor proved from the order conditions (not a hypothesis), and the order hypotheses it uses *)
laOrderProofFor[thm_LeanTheorem, d_] := SelectFirst[Lookup[First[thm]["Data"], "OrderProofs", {}], Expand[#Factor - d] === 0 &, None];
laOrderHypsOf[thm_LeanTheorem, op_Association] := With[{names = Flatten[op["Conditions"][[All, 2]]]},
  Select[Lookup[First[thm]["Data"], "OrderHypotheses", {}], MemberQ[names, #Name] &]];
laOrderHypForm[oh_Association] := Row[{oh["Name"], " : 0 ", If[TrueQ[oh["Strict"]], "<", "\[LessEqual]"], " ", laPolyForm[oh["Poly"]]}];
(* f r = c + Sum lambda q + Sum mu m^2 > 0 as a formula *)
laOrderIdentityForm[op_Association] := Row[{
  If[op["Multiplier"] === 1, laPolyForm[op["Factor"]], Row[{"(", laPolyForm[op["Factor"]], ")\[CenterDot](", laPolyForm[op["Multiplier"]], ")"}]],
  " = ", Row[Riffle[Join[If[op["Constant"] =!= 0, {op["Constant"]}, {}],
    Row[{If[#[[1]] === 1, "", Row[{#[[1]], "\[CenterDot]"}]], StringRiffle[#[[2]], "\[CenterDot]"]}] & /@ op["Conditions"],
    Row[{If[#[[1]] === 1, "", Row[{#[[1]], "\[CenterDot]"}]], "(", TraditionalForm[#[[2]]], ")\.b2"}] & /@ op["Squares"]], " + "]], " > 0"}];

laNonDegSource[thm_LeanTheorem, d_] := Module[{geo = thm["Geometry"], st = thm["Statement"], hit},
  If[AssociationQ[laOrderProofFor[thm, d]],
    Return["kept away from zero by the order conditions " <> StringRiffle[#Name & /@ laOrderHypsOf[thm, laOrderProofFor[thm, d]], ", "] <> " (proved in Lean)"]];
  If[!AssociationQ[geo], Return["declared nondegeneracy condition"]];
  hit = SelectFirst[geo["Hypotheses"], AnyTrue[#["NonDegenerate"], Function[e, PossibleZeroQ[Together[e/d]] === False && FreeQ[Together[e/d], _Symbol]]] &, None];
  Which[
    hit =!= None, hit["Source"],
    AnyTrue[Lookup[st, "NonDegenerate", {}], FreeQ[Together[#/d], _Symbol] &], "denominator of the conclusion",
    True, "leading coefficient of a constructed parameter (the construction does not degenerate)"]];

laKindText[kind_String, j_Integer] := Switch[{kind, j},
  {"Orthocenter", 1}, "orthocenter: altitude from the first vertex",
  {"Orthocenter", 2}, "orthocenter: altitude from the second vertex",
  {"Circumcenter", 1}, "circumcenter: equidistant from the first two vertices",
  {"Circumcenter", 2}, "circumcenter: equidistant from the first and third vertex",
  {"Concyclic", _}, "concyclic (4\[Times]4 determinant)",
  {"Collinear", _}, "collinear (cross product)",
  {"Perpendicular", _}, "perpendicular (dot product)",
  {"Parallel", _}, "parallel (cross product)",
  {"OnLine", _}, "point on a line (cross product)",
  {"OnCircle", _}, "point on a circle",
  {"Midpoint", _}, "midpoint",
  {"DistanceRelation", _}, "distance equality (|op| = t |ox| on a ray)",
  {"DistanceProduct", _}, "distance equality (squared)",
  {"Distance", _}, "distance variable d = |pq| (d\.b2 = |pq|\.b2)",
  {"RightAngle", _}, "right angle (dot product)",
  {"Angle" | "AngleEqual" | "AngleDouble", _}, "angle (cos\.b2 condition)",
  _, kind];

laKindShort[kind_String, j_Integer] := Switch[kind,
  "Orthocenter", "altitude " <> ToString[j], "Circumcenter", "equidistant " <> ToString[j], "Perpendicular", "\[UpTee]",
  "Parallel", "\[DoubleVerticalBar]", "OnLine" | "Collinear", "collinear", "OnCircle" | "Concyclic", "concyclic", "Midpoint", "midpoint",
  "Auxiliary", "auxiliary", "Distance", "d\[TwoWayRule]|pq|", "DistanceRelation", "distances", "DistanceProduct", "distances", "Hypothesis", "", _, ToLowerCase[kind]];

(* short text of a scene hypothesis / conclusion for graph labels *)
laPtStr[l_List] := StringRiffle[ToString /@ l, " "];
laSourceText[e0_] := Module[{e = laStrip[e0]}, Replace[e, {
  Equal[p_, TriangleCenter[{a_, b_, d_}, k_String]] :> ToString[p] <> " = " <> ToLowerCase[k] <> "(" <> laPtStr[{a, b, d}] <> ")",
  Equal[p_, Midpoint[{a_, b_}]] :> ToString[p] <> " = midpoint(" <> laPtStr[{a, b}] <> ")",
  Element[p_, (Line | InfiniteLine | Inactive[InfiniteLine])[{a_, b_}]] :> ToString[p] <> " \[Element] line(" <> laPtStr[{a, b}] <> ")",
  Element[p_, (HalfLine | Inactive[HalfLine])[{a_, b_}]] :> ToString[p] <> " \[Element] ray(" <> laPtStr[{a, b}] <> ")",
  Element[p_, (CircleThrough | Inactive[CircleThrough] | Circumsphere)[{a_, b_, d_}]] :> ToString[p] <> " \[Element] circle(" <> laPtStr[{a, b, d}] <> ")",
  Element[p_, Circle[o_, _]] :> ToString[p] <> " \[Element] circle centre " <> ToString[o],
  GeometricAssertion[{l1_, l2_}, "Perpendicular"] /; ListQ[laLinePoints[l1]] && ListQ[laLinePoints[l2]] :>
    laPtStr[laLinePoints[l1]] <> " \[UpTee] " <> laPtStr[laLinePoints[l2]],
  GeometricAssertion[ls_List, "Parallel"] /; AllTrue[ls, ListQ[laLinePoints[#]] &] :> StringRiffle[laPtStr[laLinePoints[#]] & /@ ls, " \[DoubleVerticalBar] "],
  GeometricAssertion[pts_List, kind_String] /; VectorQ[pts, MatchQ[#, _Symbol] &] :> ToLowerCase[kind] <> "(" <> laPtStr[pts] <> ")",
  Triangle[pts_List] :> "triangle " <> laPtStr[pts],
  HoldPattern[CollinearPoints[pts_List]] :> "collinear(" <> laPtStr[pts] <> ")",
  (* distances and angles as |pq| and \[Angle]pqr *)
  Equal[l_, r_] /; !FreeQ[{l, r}, EuclideanDistance | PlanarAngle] :> laShortTactic[laTermText[l] <> " = " <> laTermText[r], 40],
  _ :> laShortTactic[ToString[e, InputForm], 40]}]];
laTermText[HoldPattern[EuclideanDistance[p_Symbol, q_Symbol]]] := "|" <> SymbolName[p] <> SymbolName[q] <> "|";
laTermText[PlanarAngle[{p_Symbol, q_Symbol, r_Symbol}]] := "\[Angle]" <> SymbolName[p] <> SymbolName[q] <> SymbolName[r];
laTermText[t_Times] := StringRiffle[laTermText /@ (List @@ t), " "];
laTermText[t_] := ToString[t, InputForm];

laCertificateGraph[thm_LeanTheorem] := Module[{certs = thm["Certificates"], hs = laHypSources[thm], nds = laNonDegUsed[thm], geoQ = laGeoQ[thm],
    vs = {}, edges = {}, vlab = {}, vsty = {}, elab = {}, estyle = {}, used, srcs, srcId, sceneConcl, addV, addE, nc, ords},
  nc = Length[certs];
  addV[v_, label_, tip_, sty_] := (AppendTo[vs, v]; AppendTo[vlab, v -> Placed[{Style[label, 9], tip}, {Above, Tooltip}]]; AppendTo[vsty, v -> sty]);
  addE[e_, sty_, lab_ : None] := (AppendTo[edges, e]; AppendTo[estyle, e -> sty]; If[lab =!= None, AppendTo[elab, e -> Placed[Style[lab, 8, GrayLevel[0.3]], 0.5]]]);
  used = Table[AnyTrue[certs, #["Coefficients"][[i]] =!= 0 &], {i, Length[hs]}];
  (* scene hypotheses *)
  srcs = DeleteDuplicates[DeleteCases[#Source & /@ hs, None]];
  If[geoQ, srcs = DeleteDuplicates[Join[srcs, Select[#["Source"] & /@ thm["Geometry"]["Hypotheses"], MemberQ[DeleteCases[laNonDegSource[thm, #] & /@ nds, _String], #] &]]]];
  ords = Lookup[First[thm]["Data"], "OrderHypotheses", {}];
  srcs = DeleteDuplicates[Join[srcs, Select[Lookup[#, "Source", None] & /@ ords, # =!= None && !StringQ[#] &]]];
  srcId = AssociationThread[srcs -> Table["S" <> ToString[i], {i, Length[srcs]}]];
  KeyValueMap[addV[#2, laSourceText[#1], Style[ToString[#1, InputForm], "Input", 10], $laColAxiom] &, srcId];
  Do[With[{h = hs[[i]]},
      addV[h["Name"], h["Name"] <> If[laKindShort[h["Kind"], h["Index"]] === "", "", " (" <> laKindShort[h["Kind"], h["Index"]] <> ")"],
        Column[{Row[{h["Name"], " : ", laPolyForm[h["Poly"]], " = 0"}], If[h["Source"] =!= None, Style[ToString[h["Source"], InputForm], GrayLevel[0.4], 9], Nothing]}],
        If[used[[i]], $laColHypothesis, $laColFaded]];
      If[h["Source"] =!= None, addE[DirectedEdge[srcId[h["Source"]], h["Name"]], $laEdgeConstruct]]], {i, Length[hs]}];
  Do[With[{d = nds[[j]], v = "hnd" <> ToString[j], src = laNonDegSource[thm, nds[[j]]]},
      addV[v, "hnd" <> ToString[j] <> ": " <> laShortTactic[ToString[d, InputForm], 24] <> " \[NotEqual] 0", Column[{Row[{laPolyForm[d], " \[NotEqual] 0"}], Style[ToString[src, InputForm], GrayLevel[0.4], 9]}],
        If[AssociationQ[laOrderProofFor[thm, d]], $laColLemma, $laColHypothesis]];
      If[KeyExistsQ[srcId, src], addE[DirectedEdge[srcId[src], v], $laEdgeConstruct]]], {j, Length[nds]}];
  (* order conditions (0 <= p, 0 < p) that prove a nondegeneracy factor: scene hypothesis -> hord -> hnd *)
  Do[With[{oh = oh0},
      addV[oh["Name"], oh["Name"] <> ": 0 " <> If[TrueQ[oh["Strict"]], "<", "\[LessEqual]"] <> " " <> laShortTactic[ToString[oh["Poly"], InputForm], 20],
        Column[{laOrderHypForm[oh], Style[ToString[Lookup[oh, "Source", ""], InputForm], GrayLevel[0.4], 9]}], $laColHypothesis];
      If[KeyExistsQ[srcId, Lookup[oh, "Source", None]], addE[DirectedEdge[srcId[oh["Source"]], oh["Name"]], $laEdgeConstruct]]], {oh0, ords}];
  Do[With[{op = laOrderProofFor[thm, nds[[j]]]},
      If[AssociationQ[op], Do[addE[DirectedEdge[oh["Name"], "hnd" <> ToString[j]], $laEdgeInput, "sign"], {oh, laOrderHypsOf[thm, op]}]]], {j, Length[nds]}];
  Do[With[{c = certs[[k]], sfx = If[nc == 1, "", " " <> ToString[k]]},
      With[{fac = c["Factor"] =!= 1 && Total[c["FactorExponents"]] > 0, gv = "g = 0" <> sfx, iv = "ring identity" <> sfx, lv = "d\[CenterDot]g = 0" <> sfx},
        addV[iv, "ring: d\[CenterDot]g \[Minus] \[Sum] c\:1d62h\:1d62 \[Congruent] 0" <> sfx,
          Column[{"checked by ring1 in Lean (linear_combination)", Row[{"d = ", laPolyForm[c["Factor"]]}]}], $laColIdentity];
        addV[gv, "goal g = 0" <> sfx, Row[{"g = ", laPolyForm[c["Goal"]]}], $laColLemma];
        If[fac,
          addV[lv, "d\[CenterDot]g = 0" <> sfx, Row[{laPolyForm[c["Factor"] c["Goal"]], " = 0"}], $laColLemma];
          addE[DirectedEdge[iv, lv], $laEdgeConstruct];
          addE[DirectedEdge[lv, gv], $laEdgeInput, "mul_eq_zero"];
          Do[If[c["FactorExponents"][[j]] > 0,
              With[{pos = FirstPosition[nds, c["NonDegenerate"][[j]], None, {1}]},
                If[pos =!= None, addE[DirectedEdge["hnd" <> ToString[pos[[1]]], gv], $laEdgeInput, "cancel"]]]], {j, Length[c["NonDegenerate"]]}],
          addE[DirectedEdge[iv, gv], $laEdgeConstruct]];
        Do[If[c["Coefficients"][[i]] =!= 0, addE[DirectedEdge[hs[[i]]["Name"], If[fac, lv, gv]], $laEdgeInput, "\[Times]c" <> ToString[i]]], {i, Length[hs]}]]],
    {k, nc}];
  (* the conclusion of the scene (or the conjunction) *)
  sceneConcl = If[geoQ, laGeoConclusion[thm], If[nc > 1, "conjunction", None]];
  If[sceneConcl =!= None,
    addV["C", If[StringQ[sceneConcl], sceneConcl, laSourceText[sceneConcl]], Style[ToString[sceneConcl, InputForm], "Input", 10], $laColLemma];
    Do[addE[DirectedEdge["g = 0" <> If[nc == 1, "", " " <> ToString[k]], "C"], If[geoQ, $laEdgeConstruct, $laEdgeInput]], {k, nc}]];
  Graph[vs, edges, VertexLabels -> vlab, VertexStyle -> vsty, EdgeStyle -> estyle, EdgeLabels -> elab, VertexSize -> Medium,
    GraphLayout -> "LayeredDigraphEmbedding", ImageSize -> {UpTo[680], UpTo[520]}, PerformanceGoal -> "Quality"]];

laCertificateLegend[thm_LeanTheorem] := Module[{certs = thm["Certificates"], hs = laHypSources[thm]},
  Grid[Join[{Style[#, Bold, 10] & /@ {"", "hypothesis", "source", "coefficient"}},
    Flatten[Table[Table[{hs[[i]]["Name"], Row[{laPolyForm[hs[[i]]["Poly"]], " = 0"}],
        If[hs[[i]]["Source"] === None, "", Style[laShortTactic[ToString[hs[[i]]["Source"], InputForm], 60], 9, GrayLevel[0.35]]],
        If[certs[[k]]["Coefficients"][[i]] === 0, Style["not used", GrayLevel[0.55], Italic, 10],
          Row[{"c" <> ToString[i] <> If[Length[certs] > 1, " (goal " <> ToString[k] <> ")", ""] <> " = ", laPolyForm[certs[[k]]["Coefficients"][[i]]]}]]}, {i, Length[hs]}], {k, Length[certs]}], 1]],
    Alignment -> Left, Dividers -> {None, {2 -> GrayLevel[0.75]}}, Spacings -> {1.2, 0.5}]];

(* "d\:00b7g" with the factor written out (never a private symbol in the output) *)
laFactorTimesG[c_Association] := If[c["Factor"] === 1 || Total[c["FactorExponents"]] == 0, "g",
  Row[{"(", laPolyForm[c["Factor"]], ")\[CenterDot]g"}]];
laCombinationForm[c_Association, hs_List, coeffs_ : True] := Row[Riffle[Table[If[c["Coefficients"][[i]] === 0, Nothing,
  If[TrueQ[coeffs], Row[{"(", laPolyForm[c["Coefficients"][[i]]], ")\[CenterDot]", hs[[i]]["Name"]}], Row[{"c" <> ToString[i], "\[CenterDot]", hs[[i]]["Name"]}]]], {i, Length[hs]}], " + "]];

laIdentityView[thm_LeanTheorem] := Module[{certs = thm["Certificates"], hs = laHypSources[thm]},
  Column[Join[Flatten[Table[With[{c = certs[[k]]},
      {Style["Certificate" <> If[Length[certs] > 1, " for goal " <> ToString[k], ""] <> " (" <> ToString[c["Method"]] <> ")", Bold, 12],
       Row[{Style["goal  ", GrayLevel[0.4]], "g = ", laPolyForm[c["Goal"]]}],
       Row[{Style["identity  ", GrayLevel[0.4]], laFactorTimesG[c], " = ", laCombinationForm[c, hs]}],
       Row[{Style["check  ", GrayLevel[0.4]], "Expand[d g \[Minus] \[Sum] c\:1d62 h\:1d62] = ",
         With[{z = Expand[c["Factor"] c["Goal"] - c["Coefficients"] . c["Hypotheses"]]}, Style[z, If[z === 0, Darker[Green, 0.3], Red], Bold]],
         Style["   (what ring1 verifies after linear_combination)", GrayLevel[0.45], Italic, 10]}],
       If[ListQ[c["Steps"]] && c["Steps"] =!= {},
         Column[{Style["triangular elimination (how the nondegeneracy factor arose): c^m g = Q h + R, then R by ideal membership", GrayLevel[0.3], 10],
           Grid[Join[{Style[#, Bold, 10] & /@ {"step", "eliminate", "by", "leading coefficient c", "m", "terms of R"}},
             MapIndexed[{#2[[1]], #1["Variable"], hs[[#1["Hypothesis"]]]["Name"], laPolyForm[#1["LeadingCoefficient"]], #1["Exponent"], #1["RemainderTerms"]} &, c["Steps"]]],
             Alignment -> Left, Spacings -> {1.2, 0.4}, Dividers -> {None, {2 -> GrayLevel[0.75]}}]}], Nothing],
       ""}], {k, Length[certs]}]],
    (* nondegeneracy factors proved from the order conditions: f r = c + Sum lambda q + Sum mu m^2 > 0 *)
    With[{ops = Lookup[First[thm]["Data"], "OrderProofs", {}]},
      If[ops === {}, {}, {Style["Nondegeneracy from the order conditions (each right side is > 0, so the factor is nonzero)", Bold, 12],
        Column[laOrderHypForm /@ Lookup[First[thm]["Data"], "OrderHypotheses", {}]],
        Sequence @@ (Row[{Style[#Name <> "  ", GrayLevel[0.4]], laOrderIdentityForm[#]}] & /@ ops)}]]], Spacings -> 0.7]];

(* monomials of d g and of -c_i h_i: every column of the table sums to zero, which is exactly what ring checks *)
laMonomialForm[vars_, e_] := TraditionalForm[Times @@ MapThread[Power, {vars, e}]];
laCancellationView[thm_LeanTheorem, trace_ : None] := Module[{certs = thm["Certificates"], hs = laHypSources[thm], views},
  views = Table[Module[{c = certs[[k]], vars, rows, crs, mons, tab, labels, big, leanGoal},
      vars = c["Variables"];
      rows = Join[{{"d\[CenterDot]g", Expand[c["Factor"] c["Goal"]]}},
        Table[If[c["Coefficients"][[i]] === 0, Nothing, {"\[Minus]c" <> ToString[i] <> "\[CenterDot]" <> hs[[i]]["Name"], -Expand[c["Coefficients"][[i]] c["Hypotheses"][[i]]]}], {i, Length[hs]}]];
      crs = Association[CoefficientRules[#[[2]], vars]] & /@ rows;
      mons = SortBy[Union[Flatten[Keys /@ crs, 1]], {-Total[#], Reverse[#]} &];
      tab = Table[Lookup[cr, Key[m], 0], {cr, crs}, {m, mons}];
      labels = rows[[All, 1]];
      big = Length[mons] > 28 || Length[rows] > 8;
      leanGoal = If[Head[trace] === LeanProofTrace,
        SelectFirst[trace["Steps"], StringStartsQ[#Tactic, "linear_combination (norm := skip)"] && ListQ[#After] && #After =!= {} &, None], None];
      Column[{
        Style["Goal " <> ToString[k] <> ": " <> ToString[Length[mons]] <> " monomials, " <> ToString[Length[rows]] <> " rows; every column sums to 0", Bold, 11],
        If[!big,
          Grid[Join[
              {Join[{""}, Style[laMonomialForm[vars, #], 10] & /@ mons]},
              MapThread[Join[{Style[#1, 10, Bold]},
                Function[x, Item[Style[If[x === 0, "", x], 10], Background -> Which[x > 0, RGBColor[0.85, 0.9, 1.], x < 0, RGBColor[1., 0.87, 0.85], True, None]]] /@ #2] &, {labels, tab}],
              {Join[{Style["\[Sum]", Bold]}, Style[#, Darker[Green, 0.3], Bold, 10] & /@ Total[tab]]}],
            Dividers -> {{2 -> GrayLevel[0.7]}, {2 -> GrayLevel[0.7], -2 -> GrayLevel[0.35]}}, Spacings -> {0.6, 0.4}, Alignment -> Center],
          ArrayPlot[Sign[tab] Log[1 + Abs[tab]], ColorFunction -> (Blend[{RGBColor[0.85, 0.25, 0.2], White, RGBColor[0.2, 0.4, 0.85]}, (# + 1)/2] &),
            ColorFunctionScaling -> False, PlotRange -> {-1, 1} Max[1, Max[Abs[Log[1 + Abs[tab]]]]],
            FrameTicks -> {{Transpose[{Range[Length[labels]], labels}], None}, {None, None}}, AspectRatio -> Min[0.6, 3 Length[rows]/Max[1, Length[mons]]],
            ImageSize -> {UpTo[680], UpTo[260]}, PlotLabel -> Style["blue: positive, red: negative coefficient (log scale); column sums " <> ToString[Union[Total[tab]]], 9]]],
        If[AssociationQ[leanGoal],
          Column[{Style["Lean's goal after linear_combination (norm := skip) (step " <> ToString[leanGoal["Step"]] <> "):", GrayLevel[0.35], 10],
            Style[laShortTactic[leanGoal["After"][[1]]["target"], 900], "Input", 9]}], Nothing]}, Spacings -> 0.6]], {k, Length[certs]}];
  Column[Join[{Style["Lean's linear_combination subtracts \[Sum] c\:1d62\[CenterDot]h\:1d62 from the goal; ring1 expands everything into monomials, and the coefficients cancel column by column.", GrayLevel[0.35], 10]}, views], Spacings -> 1]];

(* ------------------------------------------------------------ *)
(*  proof process 3: geometry on the figure                      *)
(* ------------------------------------------------------------ *)

(* numeric values of the polynomial variables at a (refined) instance, in the normalized frame of the theorem *)
(* RandomInstance likes thin triangles (for Menelaus it meets the collinearity with an almost flat one), which makes a poor
   figure.  The instance of the check is used when its nondegeneracy polynomials are not small compared with the size of the
   figure; otherwise free coordinates are drawn at random and the dependent variables projected onto the hypotheses. *)
laGeoValues[thm_LeanTheorem] := Module[{geo = thm["Geometry"], vars = First[thm["Certificates"]]["Variables"], chk = thm["InstanceCheck"],
    polys, dep, free, nd, x2, good, cand, inst, c},
  polys = geo["Polynomials"]; dep = laGeoDependentVars[geo, vars]; free = Complement[vars, dep];
  nd = Select[DeleteDuplicates[Join[geo["NonDegenerate"], laNonDegUsed[thm]]], !FreeQ[#, Alternatives @@ vars] &];
  x2 = If[Length[geo["Normalized"]] >= 2, FirstCase[geo["BaseCoordinates"][geo["Normalized"][[2]]], _Symbol, None], None];
  (* a usable figure: hypotheses hold, the nondegeneracy polynomials are not small for the size of the figure, no point flies
     off, and points with different coordinate expressions do not land on each other *)
  good[v_] := AssociationQ[v] && Module[{pts = laGeoPoints[geo, v], s, pairs},
    s = Max[1., Max[Abs[Flatten[Values[KeyTake[pts, Select[Keys[pts], FreeQ[geo["BaseCoordinates"][#], Alternatives @@ dep] &]]]]]]];
    pairs = Select[Subsets[Keys[pts], {2}], geo["Coordinates"][#[[1]]] =!= geo["Coordinates"][#[[2]]] &];
    Length[pts] == Length[geo["Coordinates"]] && AllTrue[polys, laRelativeResidual[#, v] < 10^-8 &] &&
      AllTrue[nd, Abs[# /. v]/s^Max[1, Total /@ (First /@ CoefficientRules[#, vars])] > 0.08 &] && Max[Abs[Flatten[Values[pts]]]] < 6 s &&
      AllTrue[pairs, Norm[pts[#[[1]]] - pts[#[[2]]]] > 0.1 s &] &&
      (* points on rays stay on their rays, distance variables stay nonnegative, the order conditions hold (the figure shows
         the branch of the theorem) *)
      AllTrue[Join[Lookup[geo, "RayParameters", {}], geo["AuxiliaryDefinitions"][[All, 1]]], Lookup[v, #, 0] >= -10^-9 &] &&
      AllTrue[Lookup[geo, "Inequalities", {}], With[{x = N[#Poly /. v]}, !NumericQ[x] || If[#Strict, x > 10^-9, x >= -10^-9]] &]];
  If[AssociationQ[chk] && good[chk["Values"]], Return[chk["Values"]]];
  BlockRandom[SeedRandom[Hash[{polys, vars}]]; Do[
    cand = Association[Join[
      Table[v -> If[v === x2, RandomReal[{3, 6}], RandomReal[{-4, 4}]], {v, free}],
      Table[v -> If[MemberQ[geo["Parameters"], v], RandomReal[{0.15, 0.85}], RandomReal[{-4, 4}]], {v, dep}]]];
    (* distance variables start at their positive value *)
    cand = Join[cand, Association[Cases[geo["AuxiliaryDefinitions"], Rule[d_, e_] /; NumericQ[N[e /. cand]] :> (d -> N[e /. cand])]]];
    If[good[#], Return[#, Module]] & @ laRefineInstance[polys, dep, cand];
    If[good[#], Return[#, Module]] & @ laRefineInstance[polys, Select[vars, KeyExistsQ[cand, #] &], cand], {120}]];
  If[AssociationQ[chk] && AssociationQ[chk["Values"]], Return[chk["Values"]]];
  Do[inst = Quiet @ Check[RandomInstance[thm["Scene"]], $Failed];
    If[Head[inst] === GeometricScene,
      c = Quiet @ Check[laInstanceCheck[geo, thm["Statement"], inst], $Failed];
      If[AssociationQ[c], Return[c["Values"], Module]]], {3}];
  $Failed];
laGeoPoints[geo_Association, vals_Association] := Select[N[# /. vals] & /@ geo["Coordinates"], VectorQ[#, NumericQ] &];

(* what a hypothesis / conclusion refers to: drawing specs {"Line", {p, q}}, {"Segment", ...}, {"Polygon", pts},
   {"Circle3", {a, b, c}}, {"CircleCenter", o, p}, {"Right", {p, q}, {r, s}}, {"Points", pts} *)
laGeoSpecs[e0_, j_ : All] := Module[{e = laStrip[e0], specs = {}, pick},
  pick[l_List] := If[j === All, l, l[[{j}]]];
  specs = Join[specs, Replace[e, {
    Equal[p_, TriangleCenter[{a_, b_, d_}, "Orthocenter"]] :> Switch[j,
      1, {{"Line", {a, p}}, {"Segment", {b, d}}, {"Right", {a, p}, {b, d}}},
      2, {{"Line", {b, p}}, {"Segment", {a, d}}, {"Right", {b, p}, {a, d}}},
      _, {{"Line", {a, p}}, {"Line", {b, p}}, {"Line", {d, p}}, {"Polygon", {a, b, d}}}],
    Equal[p_, TriangleCenter[{a_, b_, d_}, "Circumcenter"]] :> Switch[j,
      1, {{"Segment", {p, a}}, {"Segment", {p, b}}}, 2, {{"Segment", {p, a}}, {"Segment", {p, d}}},
      _, {{"CircleCenter", p, a}, {"Polygon", {a, b, d}}}],
    Equal[p_, TriangleCenter[{a_, b_, d_}, _]] :> {{"Line", {a, p}}, {"Line", {b, p}}, {"Line", {d, p}}, {"Polygon", {a, b, d}}},
    Equal[p_, Midpoint[{a_, b_}]] :> {{"Segment", {a, b}}},
    Element[p_, (Line | InfiniteLine | Inactive[InfiniteLine])[{a_, b_}]] :> {{"Line", {a, b}}},
    Element[p_, (HalfLine | Inactive[HalfLine])[{a_, b_}]] :> {{"Ray", {a, b}}},
    Element[p_, Circle[o_, _]] :> {{"CircleCenter", o, p}},
    Element[p_, (CircleThrough | Inactive[CircleThrough] | Circumsphere)[{a_, b_, d_}]] :> {{"Circle3", {a, b, d}}},
    GeometricAssertion[{l1_, l2_}, "Perpendicular"] :> With[{p1 = laLinePoints[l1], p2 = laLinePoints[l2]},
      If[ListQ[p1] && ListQ[p2], {{"Line", p1}, {"Line", p2}, {"Right", p1, p2}}, {}]],
    GeometricAssertion[ls_List, "Parallel" | "Concurrent"] :> ({"Line", laLinePoints[#]} & /@ Select[ls, ListQ[laLinePoints[#]] &]),
    GeometricAssertion[pts_List, "Concyclic"] /; Length[pts] >= 4 :> {{"Circle3", pts[[1 ;; 3]]}, {"Points", If[j === All, pts, Join[pts[[1 ;; 3]], {pts[[3 + j]]}]]}},
    GeometricAssertion[pts_List, "Collinear"] /; Length[pts] >= 3 :> {{"Line", pts[[1 ;; 2]]}, {"Points", If[j === All, pts, Join[pts[[1 ;; 2]], {pts[[2 + j]]}]]}},
    _ :> {}}]];
  specs = Join[specs,
    Cases[{e}, Triangle[pts_List] :> {"Polygon", pts}, Infinity],
    Cases[{e}, Polygon[pts_List] :> {"Polygon", pts}, Infinity],
    Cases[{e}, HoldPattern[EuclideanDistance[p_, q_]] :> {"Segment", {p, q}}, Infinity],
    Cases[{e}, PlanarAngle[{a_, b_, d_}] :> Sequence[{"Segment", {b, a}}, {"Segment", {b, d}}], Infinity],
    Cases[{e}, SignedRatio[a_, p_, b_] :> {"Segment", {a, b}}, Infinity],
    If[MatchQ[e, _GeometricAssertion | Element[_, _]], {}, Cases[{e}, (Line | InfiniteLine | Inactive[InfiniteLine])[{p_, q_, ___}] :> {"Line", {p, q}}, Infinity]],
    If[MatchQ[e, Element[_, _]], {}, Cases[{e}, (HalfLine | Inactive[HalfLine])[{p_, q_, ___}] :> {"Ray", {p, q}}, Infinity]]];
  DeleteDuplicates[specs]];

laSpecPoints[specs_List] := DeleteDuplicates[Flatten[Replace[specs, {{"Points", l_} :> l, {_, l_List} :> l, {_, o_, p_} :> {o, p}, {_, l1_List, l2_List} :> Join[l1, l2]}, {1}]]];

$laPtBlue = RGBColor[0.12, 0.47, 0.88]; $laPtHot = RGBColor[0.93, 0.47, 0.1]; $laPtGreen = RGBColor[0.2, 0.62, 0.3];

(* The figure is drawn by pure functions that use System symbols only: the deformation view puts them into its dynamic
   output, which then keeps working without the package (a saved notebook opened in a fresh kernel). *)
$laDrawSpecsF = Function[{specs, pts, col, size}, Module[{P, circle3, right},
  P[p_] := Lookup[pts, p, None];
  circle3[l_List] := With[{s = Quiet[Circumsphere[l]]}, If[MatchQ[s, Sphere[{_?NumericQ, _?NumericQ}, _?NumericQ]], Circle @@ s, {}]];
  right[{p1_, p2_}, {q1_, q2_}] := Module[{sol, x, u, v},
    sol = Quiet[LinearSolve[Transpose[{p2 - p1, -(q2 - q1)}], q1 - p1]];
    If[!VectorQ[sol, NumericQ], {},
      x = p1 + sol[[1]] (p2 - p1);
      u = If[Norm[p1 - x] > Norm[p2 - x], p1 - x, p2 - x]; v = If[Norm[q1 - x] > Norm[q2 - x], q1 - x, q2 - x];
      If[Norm[u] == 0 || Norm[v] == 0, {}, u = size Normalize[u]; v = size Normalize[v]; Line[{x + u, x + u + v, x + v}]]]];
  Replace[specs, {
    {"Line", {p_, q_}} /; ListQ[P[p]] && ListQ[P[q]] && P[p] != P[q] :> {col, AbsoluteThickness[2], InfiniteLine[{P[p], P[q]}]},
    {"Ray", {p_, q_}} /; ListQ[P[p]] && ListQ[P[q]] && P[p] != P[q] :> {col, AbsoluteThickness[2], HalfLine[{P[p], P[q]}]},
    {"Segment", {p_, q_}} /; ListQ[P[p]] && ListQ[P[q]] :> {col, AbsoluteThickness[3], Line[{P[p], P[q]}]},
    {"Polygon", l_List} /; AllTrue[l, ListQ[P[#]] &] :> {FaceForm[{col, Opacity[0.12]}], EdgeForm[{col, AbsoluteThickness[2]}], Polygon[P /@ l]},
    {"Circle3", l_List} /; Length[l] == 3 && AllTrue[l, ListQ[P[#]] &] :> {col, AbsoluteThickness[2], circle3[P /@ l]},
    {"CircleCenter", o_, p_} /; ListQ[P[o]] && ListQ[P[p]] :> {col, AbsoluteThickness[2], Circle[P[o], Norm[P[p] - P[o]]]},
    {"Right", {p1_, p2_}, {q1_, q2_}} /; AllTrue[{p1, p2, q1, q2}, ListQ[P[#]] &] :> {col, AbsoluteThickness[1.5], right[{P[p1], P[p2]}, {P[q1], P[q2]}]},
    _ :> {}}, {1}]]];
$laDrawPointsF = Function[{pts, hot, hotCol}, KeyValueMap[
  {If[MemberQ[hot, #1], hotCol, RGBColor[0.12, 0.47, 0.88]], AbsolutePointSize[If[StringLength[ToString[#1]] > 2, 24, 19]], Point[#2],
   Text[Style[If[Head[#1] === Symbol, SymbolName[#1], ToString[#1]], White, Bold, If[StringLength[ToString[#1]] > 2, 8, 9]], #2]} &, pts]];
(* base: the objects of the scene in gray; then the highlighted specs and the points *)
$laFigureF = With[{ds = $laDrawSpecsF, dp = $laDrawPointsF},
  Function[{base, specs, hot, col, pts, range}, With[{size = 0.035 Max[#[[2]] - #[[1]] & /@ range]},
    Graphics[{
      ds[Select[base, First[#] === "Polygon" &], pts, GrayLevel[0.6], size],
      Dashing[{Small, Small}], ds[Select[base, First[#] === "Line" &], pts, GrayLevel[0.75], size], Dashing[{}],
      ds[Select[base, First[#] === "Ray" &], pts, GrayLevel[0.55], size],
      ds[Select[base, First[#] === "Segment" &], pts, GrayLevel[0.7], size],
      ds[specs, pts, col, size], dp[pts, hot, col]},
      PlotRange -> range, ImageSize -> 330, Axes -> True, AxesStyle -> GrayLevel[0.82], Ticks -> None, ImagePadding -> 12]]]];

laGeoBaseSpecs[thm_LeanTheorem] := Select[DeleteDuplicates[Flatten[laGeoSpecs /@ (laStrip /@ laSceneHyps[thm["Scene"]]), 1]],
  MatchQ[#, {"Polygon" | "Line" | "Ray" | "Segment", __}] &];
laGeoFigure[thm_LeanTheorem, pts_Association, specs_List, hot_List, col_, range_ : Automatic] :=
  $laFigureF[laGeoBaseSpecs[thm], specs, hot, col, pts, If[range === Automatic, CoordinateBounds[Values[pts], Scaled[0.12]], range]];
(* the geometric conclusion (thm["Conclusion"] is the Lean text) *)
laGeoConclusion[thm_LeanTheorem] := Lookup[First[thm]["Data"], "Conclusion", None];

laGeoStepPages[thm_LeanTheorem, trace_ : None, vals0_ : Automatic] := Module[{geo = thm["Geometry"], vals, pts, hs, certs = thm["Certificates"], nds, pages = {}, add, defs, hyps0,
    free, n, colH = RGBColor[0.93, 0.47, 0.1], colC = RGBColor[0.2, 0.62, 0.3], colD = RGBColor[0.55, 0.35, 0.8], leanLC},
  vals = If[AssociationQ[vals0], vals0, laGeoValues[thm]];
  If[!AssociationQ[vals], Return[{Style["no numeric instance of the scene", Red]}]];
  pts = laGeoPoints[geo, vals];
  hs = laHypSources[thm]; nds = laNonDegUsed[thm];
  hyps0 = laStrip /@ laSceneHyps[thm["Scene"]];
  add[title_, fig_, text_List] := AppendTo[pages, {title, fig, text}];
  (* 1. coordinates (the highlighted points have variable coordinates; FreeQ[{0, 0}, _Symbol] is False because of the head List) *)
  free = Select[Keys[geo["BaseCoordinates"]], !KeyExistsQ[geo["Definitions"], #] && !VectorQ[geo["BaseCoordinates"][#], NumericQ] &];
  add["Coordinates", laGeoFigure[thm, pts, {}, free, colH],
    {"Every point gets coordinates. " <> If[geo["Normalized"] =!= {}, "The first point is put at the origin and the second on the x axis (an isometry, so nothing is lost).", ""],
     Grid[Table[{Style[ToString[p], Bold], TraditionalForm[geo["BaseCoordinates"][p]]}, {p, Select[Keys[geo["BaseCoordinates"]], !KeyExistsQ[geo["Definitions"], #] &]}],
       Alignment -> Left, Spacings -> {1, 0.3}],
     Row[{"variables: ", TraditionalForm[Row[First[certs]["Variables"], ", "]]}]}];
  (* 2. constructed points are substituted *)
  Do[With[{src = FirstCase[hyps0, h : (Equal[p, _] | Element[p, _]) :> h, None]},
      add["Construction of " <> ToString[p], laGeoFigure[thm, pts, If[src === None, {}, laGeoSpecs[src]], {p}, colD],
        {Row[{Style[ToString[p], Bold], " = ", TraditionalForm[geo["Definitions"][p]]}],
         If[src =!= None, Style[ToString[src, InputForm], "Input", 10], Nothing],
         If[MemberQ[First /@ Values[geo["ParameterDefinitions"]], p],
           "A point on a line is written p = a + t (b \[Minus] a) with a new parameter t: no equation is needed.",
           "Its coordinates are substituted everywhere, so this hypothesis needs no equation."]}]], {p, Keys[geo["Definitions"]]}];
  (* 3. hypotheses *)
  Do[With[{h = hs[[i]]},
      add[h["Name"] <> ": " <> laKindText[h["Kind"], h["Index"]],
        laGeoFigure[thm, pts, If[h["Source"] === None, {}, laGeoSpecs[h["Source"], If[h["Kind"] === "Orthocenter" || h["Kind"] === "Circumcenter" || h["Kind"] === "Concyclic" || h["Kind"] === "Collinear", h["Index"], All]]],
          laSpecPoints[If[h["Source"] === None, {}, laGeoSpecs[h["Source"], All]]], colH],
        {If[h["Source"] =!= None, Style[ToString[h["Source"], InputForm], "Input", 10], Nothing],
         Row[{Style[h["Name"], Bold], " : ", laPolyForm[h["Poly"]], " = 0"}],
         Row[{"value at this instance: ", NumberForm[Chop[N[h["Poly"] /. vals], 10^-9], 3]}],
         Row[{"in the certificate: ", Sequence @@ Riffle[Table[If[c["Coefficients"][[i]] === 0, Style["not used", GrayLevel[0.5], Italic],
           Row[{"coefficient ", laPolyForm[c["Coefficients"][[i]]]}]], {c, certs}], "; "]}]}]], {i, Length[hs]}];
  (* 4. nondegeneracy: a hypothesis, or proved from the order conditions *)
  Do[With[{d = nds[[j]], src = laNonDegSource[thm, nds[[j]]], op = laOrderProofFor[thm, nds[[j]]]},
      If[AssociationQ[op],
        With[{ohs = laOrderHypsOf[thm, op]}, With[{specs = DeleteDuplicates[Flatten[laGeoSpecs /@ Select[Lookup[#, "Source", None] & /@ ohs, # =!= None && !StringQ[#] &], 1]]},
          add["hnd" <> ToString[j] <> ": nonzero by the order conditions", laGeoFigure[thm, pts, specs, laSpecPoints[specs], colD],
            {Row[{Style["hnd" <> ToString[j], Bold], " : ", laPolyForm[d], " \[NotEqual] 0"}],
             Column[Row[{laOrderHypForm[#], "   ", Style[ToString[Lookup[#, "Source", ""], InputForm], "Input", 9]}] & /@ ohs],
             laOrderIdentityForm[op],
             "It is proved in Lean (linear_combination over the order conditions), not assumed: the order conditions exclude the branch where d vanishes."}]]],
        add["hnd" <> ToString[j] <> ": nondegeneracy", laGeoFigure[thm, pts, If[StringQ[src], {}, laGeoSpecs[src]], If[StringQ[src], {}, laSpecPoints[laGeoSpecs[src]]], colD],
          {Row[{Style["hnd" <> ToString[j], Bold], " : ", laPolyForm[d], " \[NotEqual] 0"}],
           If[StringQ[src], src, Style[ToString[src, InputForm], "Input", 10]],
           "It is a hypothesis of the Lean theorem: the certificate proves d\[CenterDot]g = 0, and d \[NotEqual] 0 cancels."}]]], {j, Length[nds]}];
  (* 5. conclusion *)
  With[{specs = laGeoSpecs[laGeoConclusion[thm]]},
    add["Conclusion", laGeoFigure[thm, pts, specs, laSpecPoints[specs], colC],
      {Style[ToString[laGeoConclusion[thm], InputForm], "Input", 10],
       Sequence @@ Table[Row[{"g" <> If[Length[certs] > 1, ToString[k], ""] <> " = ", laPolyForm[certs[[k]]["Goal"]]}], {k, Length[certs]}],
       Row[{"value at this instance: ", NumberForm[Chop[N[certs[[1]]["Goal"] /. vals], 10^-9], 3]}],
       If[thm["Caveats"] =!= {}, Style["caveat: " <> StringRiffle[thm["Caveats"], "; "], GrayLevel[0.4], Italic, 10], Nothing]}]];
  (* 6. certificate and Lean *)
  leanLC = If[Head[trace] === LeanProofTrace, SelectFirst[trace["Steps"], #Tactic === "ring1" && TrueQ[#Synthetic] &, None], None];
  add["Certificate \[RightArrow] Lean", laGeoFigure[thm, pts, laGeoSpecs[laGeoConclusion[thm]], laSpecPoints[laGeoSpecs[laGeoConclusion[thm]]], colC],
    {Sequence @@ Table[With[{c = certs[[k]]}, Row[{laFactorTimesG[c], " = ", laCombinationForm[c, hs, False]}]], {k, Length[certs]}],
     "Mathematica finds the coefficients c\:1d62 (Groebner basis / elimination); Lean only checks the identity: linear_combination subtracts \[Sum] c\:1d62\[CenterDot]h\:1d62 and ring1 expands to 0.",
     Style[thm["Proof"], "Input", 9],
     If[AssociationQ[leanLC], Row[{"Lean (trace): ", Style[leanLC["Effect"], Darker[Green, 0.3], Bold], " at step ", leanLC["Step"]}], Nothing]}];
  n = Length[pages];
  Table[Grid[{{pages[[k, 2]], Column[Join[{Style["Step " <> ToString[k] <> " / " <> ToString[n] <> ": " <> pages[[k, 1]], Bold, 12]}, pages[[k, 3]]], Spacings -> 0.6]}},
    Alignment -> {Left, Top}, Spacings -> 2], {k, n}]];

laGeoStepsView[thm_LeanTheorem, trace_ : None, vals_ : Automatic] := With[{pages = laGeoStepPages[thm, trace, vals]},
  With[{pp = pages, n = Length[pages]},
    Manipulate[pp[[k]], {{k, 1, "step"}, 1, n, 1, Appearance -> "Labeled"}, SaveDefinitions -> False, TrackedSymbols :> {k}]]];

(* deformation: drag the free points (and points on lines); the hypotheses stop holding and the conclusion residual follows
   d g = Sum c_i h_i.  "project" moves the dependent points back onto the hypotheses (Gauss-Newton) *)
laGeoDeformView[thm_LeanTheorem, valsIn_ : Automatic] := Module[{geo = thm["Geometry"], certs = thm["Certificates"], hs, vals0, vars, handles, dep, polyF, coordF, goalF, coefF, factF,
    concl = laGeoConclusion[thm], hypPolys, slots},
  vals0 = If[AssociationQ[valsIn], valsIn, laGeoValues[thm]];
  If[!AssociationQ[vals0], Return[Style["no numeric instance of the scene", Red]]];
  hs = laHypSources[thm];
  vars = First[certs]["Variables"];
  vals0 = Association[Table[v -> N[Lookup[vals0, v, 0.]], {v, vars}]];
  slots = Thread[vars -> Table[Slot[i], {i, Length[vars]}]];
  (* pure functions of the variable values: no global symbol is evaluated inside the dynamic output *)
  hypPolys = #["Poly"] & /@ hs;
  polyF = Function @@ {hypPolys /. slots};
  goalF = Function @@ {(#["Goal"] & /@ certs) /. slots};
  coefF = Function @@ {(#["Coefficients"] & /@ certs) /. slots};
  factF = Function @@ {(#["Factor"] & /@ certs) /. slots};
  coordF = Function @@ {(Values[geo["Coordinates"]] /. slots)};
  dep = laGeoDependentVars[geo, vars];
  (* draggable points: free base points (the variable coordinates move) and points on lines (the parameter t moves) *)
  handles = Join[
    Cases[Keys[geo["BaseCoordinates"]], p_ /; !KeyExistsQ[geo["Definitions"], p] && !VectorQ[geo["BaseCoordinates"][p], NumericQ] :>
      {p, "Free", Map[If[MemberQ[vars, #], FirstPosition[vars, #][[1]], None] &, geo["BaseCoordinates"][p]]}],
    KeyValueMap[If[MemberQ[vars, #1], {#2[[1]], "Param", {FirstPosition[vars, #1][[1]], #2[[2]], #2[[3]]}}, Nothing] &, geo["ParameterDefinitions"]]];
  handles = Select[handles, #[[2]] === "Param" || AnyTrue[#[[3]], IntegerQ] &];
  With[{hf = handles, keys = Keys[geo["Coordinates"]], v0 = Values[vals0], pf = polyF, gf = goalF, cf = coefF, ff = factF, crf = coordF,
      depIdx = Flatten[Position[vars, #] & /@ dep], nv = Length[vars], names = #["Name"] & /@ hs,
      conSpecs = laGeoSpecs[concl], conPts = laSpecPoints[laGeoSpecs[concl]], base = laGeoBaseSpecs[thm], fig = $laFigureF,
      green = $laPtGreen, hot = $laPtHot,
      range = CoordinateBounds[Values[laGeoPoints[geo, vals0]], Scaled[0.35]]},
    DynamicModule[{v = v0, ptsOf, locsOf, setLocs, project, bar},
      ptsOf[x_] := AssociationThread[keys -> (crf @@ x)];
      locsOf[x_] := With[{P = ptsOf[x]}, P[#[[1]]] & /@ hf];
      setLocs[x_, new_] := Module[{y = x, P = ptsOf[x]},
        Do[With[{h = hf[[i]], q = new[[i]]},
            If[h[[2]] === "Free",
              Do[If[IntegerQ[h[[3, j]]], y[[h[[3, j]]]] = q[[j]]], {j, 2}],
              With[{A = P[h[[3, 2]]], B = P[h[[3, 3]]]}, If[Norm[B - A] > 0, y[[h[[3, 1]]]] = (q - A) . (B - A)/((B - A) . (B - A))]]]], {i, Length[hf]}];
        y];
      project[x_] := Module[{y = x, J, F, k = 0, idx = If[depIdx === {}, Range[nv], depIdx], dx},
        While[k < 40,
          F = pf @@ y; If[Max[Abs[F]] < 10^-12, Break[]];
          J = Table[(pf @@ ReplacePart[y, j -> y[[j]] + 10^-7] - F)/10^-7, {j, idx}] // Transpose;
          dx = Quiet @ Check[PseudoInverse[J] . F, Break[]]; y[[idx]] = y[[idx]] - dx; k++];
        y];
      bar[x_] := Graphics[{If[Abs[x] < 10^-8, green, hot], Rectangle[{0, 0}, {Min[1, 0.05 + Log10[1 + 10^6 Abs[x]]/7], 1}]},
        ImageSize -> {80, 10}, PlotRange -> {{0, 1}, {0, 1}}];
      Column[{
        Row[{Button["project onto the hypotheses", v = project[v], ImageSize -> Automatic], "  ", Button["reset", v = v0],
          Style["   drag the points; the dependent points stay where you put them until you project", GrayLevel[0.45], Italic, 9]}],
        Grid[{{
          LocatorPane[Dynamic[locsOf[v], (v = setLocs[v, #]) &],
            Dynamic[With[{P = ptsOf[v]}, fig[base, conSpecs, conPts, If[Max[Abs[gf @@ v]] < 10^-8, green, hot], P, range]]],
            Appearance -> Graphics[{RGBColor[0.93, 0.47, 0.1], AbsoluteThickness[2], Circle[]}, ImageSize -> 28]],
          Dynamic[With[{h = pf @@ v, g = gf @@ v, c = cf @@ v, d = ff @@ v},
            Column[{
              Style["hypotheses (should be 0)", Bold, 10],
              Grid[MapThread[{#1, NumberForm[Chop[#2, 10^-10], 4], bar[#2]} &, {names, h}], Alignment -> Left],
              Style["conclusion", Bold, 10],
              Grid[Table[{"g" <> If[Length[g] > 1, ToString[k], ""], NumberForm[Chop[g[[k]], 10^-10], 4],
                  Style[If[Abs[g[[k]]] < 10^-8, "holds", "fails"], If[Abs[g[[k]]] < 10^-8, green, hot], Bold]}, {k, Length[g]}], Alignment -> Left],
              Style["certificate at these values", Bold, 10],
              Grid[Table[{"d\[CenterDot]g = ", NumberForm[Chop[d[[k]] g[[k]], 10^-10], 5], "   \[Sum] c\:1d62\[CenterDot]h\:1d62 = ", NumberForm[Chop[c[[k]] . h, 10^-10], 5]}, {k, Length[g]}], Alignment -> Left],
              Style["The identity holds for every position; when every h\:1d62 = 0 the conclusion follows.", GrayLevel[0.4], Italic, 9]}, Spacings -> 0.5]]]}},
          Alignment -> {Left, Top}, Spacings -> 2]}],
      SaveDefinitions -> False]]];

(* non-geometric polynomial theorems: sliders for the variables *)
laPolyDeformView[thm_LeanTheorem] := Module[{certs = thm["Certificates"], hs = laHypSources[thm], vars, slots},
  vars = First[certs]["Variables"];
  slots = Thread[vars -> Table[Slot[i], {i, Length[vars]}]];
  With[{pf = Function @@ {(#["Poly"] & /@ hs) /. slots}, gf = Function @@ {(#["Goal"] & /@ certs) /. slots},
      cf = Function @@ {(#["Coefficients"] & /@ certs) /. slots}, ff = Function @@ {(#["Factor"] & /@ certs) /. slots},
      n = Length[vars], names = #["Name"] & /@ hs, labels = ToString /@ vars},
    DynamicModule[{v = RandomReal[{-1, 1}, Length[vars]]},
      Column[{
        Grid[Table[With[{i = i}, {labels[[i]], Slider[Dynamic[v[[i]]], {-3, 3}], Dynamic[NumberForm[v[[i]], 3]]}], {i, n}], Alignment -> Left],
        Dynamic[With[{h = pf @@ v, g = gf @@ v, c = cf @@ v, d = ff @@ v},
          Grid[Join[MapThread[{#1, NumberForm[Chop[#2, 10^-10], 4]} &, {names, h}],
            Table[{"d\[CenterDot]g" <> If[Length[g] > 1, ToString[k], ""], NumberForm[Chop[d[[k]] g[[k]], 10^-10], 5], "\[Sum] c\:1d62\[CenterDot]h\:1d62", NumberForm[Chop[c[[k]] . h, 10^-10], 5]}, {k, Length[g]}]],
            Alignment -> Left]]]}]]]];

(* ------------------------------------------------------------ *)
(*  LeanProofView                                                *)
(* ------------------------------------------------------------ *)

Options[LeanProofView] = Join[{"Trace" -> Automatic}, Options[LeanProofTrace]];
LeanProofView::view = "Unknown view `1`. Available for this theorem: `2`.";
$laLeanViews = {"Goals", "GoalGraph", "Tactics"};

laProofViews[thm_LeanTheorem] := Join[
  If[laGeoQ[thm] && laCertQ[thm], {"Steps"}, {}],
  If[laCertQ[thm], {"ProofGraph", "Identity", "Cancellation", "Deform"}, {}],
  $laLeanViews];

LeanProofView[r_LeanCheckResult, rest___] := With[{t = r["Theorem"]},
  If[Head[t] === LeanTheorem, LeanProofView[t, rest], Message[LeanProofTrace::nothm]; $Failed]];
LeanProofView[tr_LeanProofTrace, view_ : All, opts : OptionsPattern[]] := With[{t = tr["Theorem"]},
  If[Head[t] === LeanTheorem, LeanProofView[t, view, "Trace" -> tr, opts], Message[LeanProofTrace::nothm]; $Failed]];
LeanProofView[thm_LeanTheorem, opts : OptionsPattern[]] := LeanProofView[thm, All, opts];
LeanProofView[thm_LeanTheorem, view : (All | _String | {__String}), opts : OptionsPattern[]] := Module[{avail = laProofViews[thm], want, trace, mk, gvals},
  want = Which[view === All, avail, StringQ[view], {view}, True, view];
  If[!SubsetQ[avail, want], Message[LeanProofView::view, First[Complement[want, avail]], avail]; Return[$Failed]];
  trace = OptionValue["Trace"];
  (* one Lean compile with the trace_state instrumentation serves all Lean views (and annotates Cancellation / Steps) *)
  If[Head[trace] =!= LeanProofTrace && trace =!= False && IntersectingQ[want, $laLeanViews],
    trace = LeanProofTrace[thm, Sequence @@ FilterRules[{opts}, Options[LeanProofTrace]]]];
  If[Head[trace] =!= LeanProofTrace, trace = None; want = Select[want, !MemberQ[$laLeanViews, #] &]];
  (* the figure of the Steps and Deform tabs is the same instance *)
  gvals = If[laGeoQ[thm] && IntersectingQ[want, {"Steps", "Deform"}], laGeoValues[thm], Automatic];
  mk[v_] := Switch[v,
    "Steps", laGeoStepsView[thm, trace, gvals],
    "ProofGraph", Column[{laCertificateGraph[thm], laCertificateLegend[thm]}, Spacings -> 1],
    "Identity", laIdentityView[thm],
    "Cancellation", laCancellationView[thm, trace],
    "Deform", If[laGeoQ[thm], laGeoDeformView[thm, gvals], laPolyDeformView[thm]],
    "Goals", trace["Stepper"],
    "GoalGraph", trace["GoalGraph"],
    "Tactics", trace["ProofDataset"]];
  Which[
    want === {}, Style["nothing to show", GrayLevel[0.5]],
    Length[want] == 1, mk[First[want]],
    True, TabView[(# -> mk[#]) & /@ want, ImageSize -> Automatic]]];

End[];
EndPackage[];

(* ---- ClaudeEval integration: allowed heads (NBAccess, two layers) and keywords (claudecode docs injection) ----
   Only functions that are pure, or that compile Lean through LeanCheck (whose source guard refuses compile-time
   code / IO and whose files stay below $TemporaryDirectory), are trusted.  Not trusted (approval stays):
   LeanSaveSource (writes a file anywhere), LeanCheckFile (reads any file), LeanLinkImport (loads a paclet),
   the turtle certificate functions of the examples folder (minutes of CPU, tens of GB). *)
LeanAssist`Private`$laAgentHeads = {
  "LeanAssistStatus", "LeanToolchainBinary", "LeanSourceGuard",
  "LeanCheck", "LeanProve", "LeanCheckResult", "LeanDiagnostics",
  "LeanForm", "LeanIdentifier", "LeanLiteral", "LeanTuple", "LeanDataDefinitions",
  "LeanTheorem", "LeanSource",
  "LeanPolynomialCertificate", "LeanLinearCombination", "LeanPolynomialProof", "LeanPolynomialTheorem",
  "LeanGeometryCoordinates", "LeanGeometryPolynomials", "LeanGeometryStatement", "LeanGeometryTheorem",
  "LeanGeometryReport", "LeanGeometryConjectures", "SignedRatio",
  "LeanGraphTheorem", "LeanGraphReport", "LeanLogicTheorem", "LeanLogicReport", "LeanProofTrace", "LeanProofView"};
If[Length[Names["NBAccess`NBRegisterAllowedHeads"]] > 0,
  Quiet @ Check[NBAccess`NBRegisterAllowedHeads[LeanAssist`Private`$laAgentHeads], Null]];
If[Length[Names["NBAccess`NBRegisterTrustedPackageHeads"]] > 0,
  Quiet @ Check[NBAccess`NBRegisterTrustedPackageHeads["LeanAssist`", LeanAssist`Private`$laAgentHeads], Null]];
If[Length[Names["ClaudeCode`$ClaudePackageKeywordMap"]] > 0 && AssociationQ[ClaudeCode`$ClaudePackageKeywordMap],
  ClaudeCode`$ClaudePackageKeywordMap["LeanAssist"] =
    {"LeanAssist", "Lean4", "Lean 4", "Lean\:3067", "Lean \:3067", "Lean\:306e", "Lean \:306e", "in Lean", "Lean proof", "Mathlib",
     "\:5f62\:5f0f\:8a3c\:660e", "\:5f62\:5f0f\:5316", "\:5b9a\:7406\:8a3c\:660e", "\:8a3c\:660e\:3057\:3066", "\:8a3c\:660e\:305b\:3088",
     "\:8a3c\:660e\:3092", "GeometricScene", "\:521d\:7b49\:5e7e\:4f55", "\:30e1\:30cd\:30e9\:30a6\:30b9", "\:30c1\:30a7\:30d0",
     "\:30c8\:30fc\:30c8\:30ed\:30b8\:30fc", "\:6052\:771f\:5f0f",
     "\:5408\:540c", "\:932f\:89d2", "\:540c\:4f4d\:89d2", "\:5bfe\:9802\:89d2", "\:4e8c\:7b49\:8fba\:4e09\:89d2\:5f62", "\:5e73\:884c\:7dda"}];
If[Length[Names["ClaudeCode`$ClaudePackageAuxKeywordMap"]] > 0 && AssociationQ[ClaudeCode`$ClaudePackageAuxKeywordMap],
  ClaudeCode`$ClaudePackageAuxKeywordMap["LeanAssist"] =
    <|"turtle" -> {"\:30bf\:30fc\:30c8\:30eb", "turtle", "\:30da\:30f3\:30ed\:30fc\:30ba", "Penrose", "pass-substitution",
       "\:8a3c\:660e\:66f8", "certificate", "LeanTurtle"},
      (* api_proofview.md: LeanProofTrace / LeanProofView *)
      "proofview" -> {"LeanProofView", "LeanProofTrace", "ProofView", "trace_state", "\:8a3c\:660e\:306e\:904e\:7a0b", "\:8a3c\:660e\:904e\:7a0b",
       "\:30b4\:30fc\:30eb\:6728", "goal tree", "tactic state"}|>];

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
  LeanGraphReport[g, prop]                \:2192 Graph \:306e\:6027\:8cea (\:5f69\:8272\:30fb\:30cf\:30df\:30eb\:30c8\:30f3\:30fb\:9023\:7d50\:30fb\:540c\:578b\:2026): \:8a3c\:660e\:66f8\:3092\:56f3\:793a\:3057 Lean \:306e decide \:3067\:691c\:67fb
  LeanLogicReport[expr]                   \:2192 \:8ad6\:7406\:5f0f: \:771f\:7406\:5024\:8868 / \:30d7\:30ed\:30c3\:30c8\:3067\:53ef\:8996\:5316\:3057 Lean \:3067\:8a3c\:660e (tauto / nlinarith / \:53cd\:4f8b)
  LeanDataDefinitions[<|name -> data|>]   \:2192 WL \:30c7\:30fc\:30bf\:3092 Lean \:306e def \:306b (decide \:578b\:306e\:6709\:9650\:691c\:8a3c\:7528)
  LeanLinkImport[thm]                     \:2192 Wolfram/LeanLink \:306e LeanEnvironment \:3078 (\:5f0f\:30b0\:30e9\:30d5\:30fbtactic \:72b6\:614b)
  LeanProofTrace[thm] / LeanProofView[thm] \:2192 \:8a3c\:660e\:306e\:904e\:7a0b: \:5404 tactic \:524d\:5f8c\:306e\:30b4\:30fc\:30eb\:30fb\:30b4\:30fc\:30eb\:6728\:30fb\:8a3c\:660e\:66f8\:30b0\:30e9\:30d5\:30fb\:5358\:9805\:5f0f\:306e\:6253\:3061\:6d88\:3057\:30fb\:56f3\:306e\:624b\:9806 (Report \:306f "ProofView" -> True)
"];
