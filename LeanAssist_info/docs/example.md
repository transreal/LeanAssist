# LeanAssist 使用例

```mathematica
Block[{$CharacterEncoding = "UTF-8"},
  Get[FileNameJoin[{$packageDirectory, "LeanAssist.wl"}]]];
LeanAssistStatus[]          (* lean / lake / Mathlib / LeanLink の状態 *)
```

## 1. Lean を呼ぶ: 診断・sorry・公理

```mathematica
res = LeanCheck["
theorem t_sorry (n : Nat) : n + 0 = n := by sorry
theorem t_ok (n : Nat) : n + 0 = n := rfl
theorem t_bad (n : Nat) : n + 1 = n := rfl"];
res                          (* 要約ボックス: Status Failed *)
res["TheoremStatus"]         (* <|"t_sorry" -> "Sorry", "t_ok" -> "Proved", "t_bad" -> "Failed"|> *)
res["Axioms"]                (* t_sorry -> {"sorryAx"}, t_ok -> {} *)
LeanDiagnostics[res]         (* 行・列・種類・本文の Dataset *)
```

## 2. WL の命題から Lean の定理へ

```mathematica
thm = LeanTheorem["am_gm_two", {x, y}, {}, x^2 + y^2 >= 2 x y,
  "Proof" -> "nlinarith [sq_nonneg (x - y)]"];
LeanSource[thm]              (* import Mathlib... theorem am_gm_two (x y : ℝ) : x^2 + y^2 ≥ 2*x*y := by ... *)
rAM = LeanProve[thm];        (* Mathlib のコンパイル: 約 10 秒 *)
rAM["Status"]                (* "Proved" *)
```

整数の定理は型を指定する (Mathlib 不要、1 秒未満):

```mathematica
t2 = LeanTheorem["add_comm_nat", {{n, m} -> "Nat"}, {}, "n + m = m + n", "Proof" -> "omega", "Imports" -> {}];
LeanProve[t2]["Axioms"]      (* <|"add_comm_nat" -> {}|> *)
```

## 3. 多項式恒等式の証明書

メネラウスの定理をパラメータ座標で: A = (0,0), B = (1,0), C = (c1,c2), D = B + t(C − B), E = C + u(A − C), F = A + v(B − A)。

```mathematica
(* 点の名前 a, b, c, ..., g, h, o, p, q, r, s は後の GeometricScene で使うので変数には使わない *)
hcol = ((1 + t (c1 - 1)) - v) ((1 - u) c2) - (t c2) ((1 - u) c1 - v);   (* D, E, F 共線 *)
goal = t u v + (1 - t) (1 - u) (1 - v);                                (* BD/DC·CE/EA·AF/FB = -1 *)
cert = LeanPolynomialCertificate[goal, {hcol}, {c1, c2, t, u, v}, "NonDegenerate" -> {c2}]
(* Found -> True, Coefficients -> {1}, Factor -> c2 : c2 goal = 1·hcol *)
thm = LeanPolynomialTheorem["menelaus_param", {c1, c2, t, u, v}, {hcol == 0}, goal == 0, "NonDegenerate" -> {c2}];
LeanSource[thm]
LeanProve[thm]["Status"]     (* "Proved" *)
```

## 4. GeometricScene で可視化し Lean で証明する

### メネラウス

```mathematica
men = GeometricScene[{a, b, c, d, e, f}, {Triangle[{a, b, c}],
   d \[Element] Line[{b, c}], e \[Element] Line[{c, a}], f \[Element] Line[{a, b}],
   CollinearPoints[{d, e, f}]}];
RandomInstance[men]
geo = LeanGeometryPolynomials[men];
geo["Coordinates"]           (* a -> {0,0}, b -> {xb,0}, d -> b + td (c - b), ... *)
geo["Polynomials"]           (* 共線条件の多項式 *)
concl = SignedRatio[b, d, c] SignedRatio[c, e, a] SignedRatio[a, f, b] == -1;
thm = LeanGeometryTheorem[men, concl, "Name" -> "menelaus"];
thm["InstanceCheck"]["OK"]   (* True: RandomInstance で仮定と結論の残差を確認 *)
LeanSource[thm]
LeanProve[thm]
LeanGeometryReport[men, concl]
```

### チェバ、ヴァリニョン、タレス、オイラー線

```mathematica
ceva = GeometricScene[{a, b, c, d, e, f, p}, {Triangle[{a, b, c}],
   d \[Element] Line[{b, c}], e \[Element] Line[{c, a}], f \[Element] Line[{a, b}],
   p \[Element] Line[{a, d}], p \[Element] Line[{b, e}], p \[Element] Line[{c, f}]}];
LeanGeometryReport[ceva, SignedRatio[b, d, c] SignedRatio[c, e, a] SignedRatio[a, f, b] == 1]

var = GeometricScene[{a, b, c, d, p, q, r, s}, {Polygon[{a, b, c, d}],
   p == Midpoint[{a, b}], q == Midpoint[{b, c}], r == Midpoint[{c, d}], s == Midpoint[{d, a}]}];
LeanGeometryReport[var, GeometricAssertion[{Line[{p, q}], Line[{s, r}]}, "Parallel"] &&
   EuclideanDistance[p, q] == EuclideanDistance[s, r]]

th = GeometricScene[{a, b, c, o}, {Triangle[{a, b, c}], o == Midpoint[{a, b}],
   c \[Element] Circle[o, EuclideanDistance[o, a]]}];
LeanGeometryConjectures[th]  (* FindGeometricConjectures の予想 (∠bca = 90°) を Lean で確認 *)

eul = GeometricScene[{a, b, c, g, o, h}, {Triangle[{a, b, c}],
   g == TriangleCenter[{a, b, c}, "Centroid"], o == TriangleCenter[{a, b, c}, "Circumcenter"],
   h == TriangleCenter[{a, b, c}, "Orthocenter"]}];
LeanGeometryReport[eul, GeometricAssertion[{o, g, h}, "Collinear"]]
LeanGeometryReport[eul, SignedRatio[h, g, o] == 2]

(* 九点円: 辺の中点・垂線の足・頂点と垂心の中点は共円 *)
npc = GeometricScene[{a, b, c, ma, mb, mc, fa, h, mah}, {Triangle[{a, b, c}],
   ma == Midpoint[{b, c}], mb == Midpoint[{c, a}], mc == Midpoint[{a, b}],
   fa \[Element] Line[{b, c}], GeometricAssertion[{Line[{a, fa}], Line[{b, c}]}, "Perpendicular"],
   h == TriangleCenter[{a, b, c}, "Orthocenter"], mah == Midpoint[{a, h}]}];
LeanGeometryReport[npc, GeometricAssertion[{ma, mb, mc, fa}, "Concyclic"]]
LeanGeometryReport[npc, GeometricAssertion[{ma, mb, mc, mah}, "Concyclic"]]

(* シムソン線: 三角消去で非退化条件 xb ≠ 0, |ac|^2 ≠ 0, |bc|^2 ≠ 0 が見つかる (証明書に約 1 分) *)
sim = GeometricScene[{a, b, c, p, d, e, f}, {Triangle[{a, b, c}], p \[Element] CircleThrough[{a, b, c}],
   d \[Element] Line[{b, c}], GeometricAssertion[{Line[{p, d}], Line[{b, c}]}, "Perpendicular"],
   e \[Element] Line[{c, a}], GeometricAssertion[{Line[{p, e}], Line[{c, a}]}, "Perpendicular"],
   f \[Element] Line[{a, b}], GeometricAssertion[{Line[{p, f}], Line[{a, b}]}, "Perpendicular"]}];
thmSim = LeanGeometryTheorem[sim, GeometricAssertion[{d, e, f}, "Collinear"], "Name" -> "simson"];
thmSim["Certificates"][[1, "Method"]]     (* "Elimination" *)
LeanProve[thmSim]                          (* Proved *)
```

パップス (`b ∈ Line[{a, c}]`, `e ∈ Line[{d, f}]`, 交点 x, y, z) とデザルグ (中心 o からの透視、対応辺の交点) も同じ呼び方で Proved になる。

## 5. 応用 1: BlockingNimCA の保存則

`BNMassConservedQ` は局所収支を `Expand` で 0 にすることで質量保存を示す。同じ恒等式を Lean に書く (`f(v, k) = v + k·[v<0]`、`ind(v) = [v<0]`、3 倍して分母を払った形):

```mathematica
pre = "def ind (v : Int) : Int := if v < 0 then 1 else 0
def f (v k : Int) : Int := if v < 0 then v + k else v";
bal = "3 * (f x1 1 + f x2 1 + f x3 1 - f y1 2 - f y2 2 - f y3 2 + f z 3) - 3 * (z + 3 * ind z)
  + ((-2*x1 - 3*ind x1) - x1) + ((-2*x2 - 3*ind x2) - x2) + ((-2*x3 - 3*ind x3) - x3)
  + ((y1 + 3*ind y1) - (-2*y1 - 3*ind y1)) + ((y2 + 3*ind y2) - (-2*y2 - 3*ind y2)) + ((y3 + 3*ind y3) - (-2*y3 - 3*ind y3)) = 0";
bn = LeanTheorem["bn_mass_balance", {{x1, x2, x3, y1, y2, y3, z} -> "Int"}, {}, bal,
  "Preamble" -> pre, "Proof" -> "simp only [f, ind]\nomega", "Imports" -> {}];
LeanProve[bn]                (* Proved (公理は propext, Quot.sound のみ) *)
```

一般オフセット (al, be, ga) 版は仮定 `ga = 3 * (be - al)` 付き。`ga * ind z` のような「変数 × if」は omega には非線形に見えるので、先に `split` で場合分けする:

```mathematica
"Proof" -> "simp only [f, ind]\n(try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega"
```

## 6. 応用 2: タートル証明書の O2 を Lean カーネルで検査

```mathematica
Block[{$CharacterEncoding = "UTF-8"},
  Get[FileNameJoin[{$LeanAssistDirectory, "examples", "turtle_port_identities.wl"}]]];
(* 証明書は公開リポジトリ https://github.com/transreal/pt_turtle の results/unbounded_certs/ にある。
   $ptTurtle は git clone した先に合わせて変える *)
$ptTurtle = FileNameJoin[{$HomeDirectory, "src", "pt_turtle"}];
certFile = FileNameJoin[{$ptTurtle, "results", "unbounded_certs", "cert2_SSSR_1p_1.json"}];
res = LeanTurtlePortIdentities[certFile];
res["Status"]                (* "Proved": frames / port delta / O3 / O2 を decide +kernel で検査 (約 7 秒) *)
res["Axioms"]                (* o2_SSSR_verified -> {"propext"} *)
LeanTurtlePortIdentities[certFile, "Perturb" -> {1, "delta", 1}]["Status"]   (* "Failed": 壊した証明書は拒否 *)
```

生成された Lean ソースは `LeanAssist_info/lean/turtle/o2_SSSR_verified.lean` に保存される。

O1 (基底レベル B = 6 の 30 pass 族のシミュレーション) も同じ流儀で検査できる。Mathematica が標準超タイルで走行して N(π, B) を求め、Lean が超タイル・所有菱形・navigation・走行を定義から再計算して exit port と N を照合する:

```mathematica
sim = tpBaseSimulation[Import[certFile, "RawJSON"]];   (* <|"id", "N", "Exit", "ExitOK"|> × 30、N の合計 444 *)
r1 = LeanTurtleBaseSimulation[certFile];
r1["Status"]                 (* "Proved": decide +kernel で約 30 秒、公理は propext のみ *)
r1["Theorem"]["Simulation"]  (* Mathematica 側のシミュレーション *)
LeanTurtleBaseSimulation[certFile, "Method" -> "native_decide"]["Time"]        (* 数秒 (公理に native_decide の補助公理が付く) *)
LeanTurtleBaseSimulation[certFile, "Perturb" -> {"N", 5, 1}]["Status"]         (* "Failed": N を 1 変えると拒否 *)
LeanTurtleBaseSimulation[certFile, "Perturb" -> {5, "ref", 1}]["Status"]       (* "Failed": 入口 port を壊すと拒否 *)
```

保存先は `LeanAssist_info/lean/turtle/o1_SSSR_verified.lean`。証明の補題 1 (加法群上の漸化式の一意性) は Mathlib の定理として `lean/turtle/AffineRecurrence.lean` にあり、`LeanCheckFile[file]` で確認する (約 8 秒、`affine_unique` は公理無し)。

O4 (成長) と O6 (厳密漸化式) は、O1 の N(π, B) から長さを層ごとに再計算して検査する。根 4 (鈍角 +、奇数レベル) は自分の 2 レベル展開 21 個に 2 回現れ、N(7) = 202、N(m+2) = 4 N(m) + 66 が dim M + 3 = 33 ステップ成り立つ。Cayley–Hamilton (`CayleyHamiltonRecurrence.lean`) により全レベルで成り立つ:

```mathematica
r46 = LeanTurtleRecurrence[certFile];
r46["Status"]                          (* "Proved": decide +kernel で約 10 秒、公理は propext のみ *)
rec = First[r46["Theorem"]["Recurrence"]];
Take[rec["N"], 4]                      (* {202, 874, 3562, 14314} *)
Lookup[rec, {"a", "b", "Multiplicity", "ExpansionSize"}]   (* {4, 66, 2, 21} *)
LeanTurtleRecurrence[certFile, "Perturb" -> {"b", 4, 1}]["Status"]   (* "Failed": N(m+2) = 4 N(m) + 67 は拒否 *)
LeanCheckFile[FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", "CayleyHamiltonRecurrence.lean"}]]["Status"]  (* "Proved" *)
LeanCheckFile[FileNameJoin[{$LeanAssistDirectory, "lean", "turtle", "PassInduction.lean"}]]["Axioms"]["PassInduction.H_all"]  (* {"propext", "Quot.sound"} *)
```

`PassInduction.lean` の `H_all` は、超タイル・等長写像・所有の細分を抽象化した構造体 `PassSystem` の上で、O1・O2・O3・長さの漸化式と補題 2 (出口性質、明示的な仮定) から全レベルの H(m) を導く。具体的なペンローズ置換がこの構造体のフィールドを満たすことは `CheckerSoundness.lean` (下)。

O5 (補題 2 のうち証明書側の条件) は Z[ζ] の厳密算術で検査する。内積は 4·Re(u v̄) = A + B√5 (A, B は整数) で持ち、平方根は Lean で計算しない: Mathematica が sin 36° の有理下界と各 pass の |c| の有理上界を書き出し、Lean はそれが正しい向きの上下界であることと不等式を Z[√5] の符号判定で確かめる:

```mathematica
res5 = LeanTurtleExitProperty[certFile];
res5["Status"]                                        (* "Proved": decide +kernel で約 5 秒、公理は propext のみ *)
Min[Values[res5["Theorem"]["Surplus"]]]               (* 1.887: verify_cert_exact.py の値と一致 *)
LeanTurtleExitProperty[certFile, "Perturb" -> {"c", 1}]["Status"]   (* "Failed": |c| の上界が小さすぎる *)
LeanTurtleExitProperty[certFile, "Perturb" -> {"sin"}]["Status"]    (* "Failed": 3/5 は sin 36° の下界ではない *)
```

これで verify_cert.py の義務 O1–O6 がすべて Lean カーネルの `decide` で検査できる。22 本の証明書の結果は `lean/turtle/O2_results.md`、`O5_results.md`、`obligations_results.md` にある。

検査した Bool と論理をつなぐのが `lean/turtle/CheckerSoundness.lean` (Mathlib)。証明書から具体的な `PassSystem` (Z[ζ] 座標・置換 σ・正の三角形の所有菱形・等長写像・タートルの一歩) を作り、「検査器が true ⇒ H(m) の帰納法の仮定」を証明する。`LeanTurtleUnbounded` は定理 U(1) を 1 本の定理にしたソース (テンプレート + 論理 + 健全性 + データ + 最終定理) を作り、Mathlib で検査する (約 65 秒):

```mathematica
ru = LeanTurtleUnbounded[certFile];          (* lean/turtle/unbounded_SSSR_verified.lean に保存 *)
ru["Status"]                                  (* "Proved" *)
ru["Axioms"]["TurtleUnbounded.cert2_SSSR_1p_1"]
(* {"propext", "Classical.choice", "Quot.sound", "TurtleGeom.edgeUnique", "TurtleGeom.exitProperty_cert2_SSSR_1p_1"} *)
ru["Axioms"]["TurtleSound.model_H_all"]       (* 検査器 ⇒ ∀ m ≥ B, H(m): 幾何の公理は TurtleGeom.edgeUnique だけ *)
LeanTurtleUnbounded[certFile, "Perturb" -> {"b", 4, 1}, "SaveSource" -> False]["Status"]   (* "Failed" *)
```

主張は「根 4 の pass は N(7) = 202、全ての奇数レベルで N(m+2) = 4 N(m) + 66 (33 ステップの検査を Cayley–Hamilton で全レベルへ)、任意の M に対し、あるレベルの標準超タイルとその任意の等長な写しの中で M 回を超える S 移動の後に出口で終わり、その中でタートルの一歩と一致する任意の単射な crossing 写像の入口の軌道は M 以内で繰り返さない」。残る公理は 2 つ: `TurtleGeom.edgeUnique` (標準超タイルの所有菱形は有向辺を共有しない; 基底レベルでは O1 の検査器が確かめていること)、`TurtleGeom.exitProperty_cert2_SSSR_1p_1` (補題 2)。

有界性の証明 (定理 3/4) の計算部分は `examples/turtle_bounded.wl` と `lean/turtle/TurtleBounded_template.lean`。Mathematica が σ⁸(sun) の 30 個の印付き三角形コロナ (中心の枠で書く) と、各コロナ C について σⁿ(C) 内の全軌道の証明書を作り、Lean が閉包と軌道を再計算する:

```mathematica
Get[FileNameJoin[{$LeanAssistDirectory, "examples", "turtle_bounded.wl"}]];
LeanTurtleAtlasClosure[]["Status"]                          (* "Proved": decide +kernel で約 8 秒、公理は propext のみ *)
LeanTurtleAtlasClosure["Perturb" -> {"Drop", 5}]["Status"]  (* "Failed": エントリ 5 が無いと閉じない *)
d = tbBoundedData["SSR", 7];
{d["Starts"], d["Orbits"], d["Periods"]}                    (* {54240, 2860, {10, 12, 28, 30, 50, 80, 100}} *)
r = LeanTurtleBoundedRun["SSR", 7];                         (* native_decide、約 16 秒 *)
r["Axioms"]["bounded_SSR_n7_verified"]                      (* {"propext", "bounded_SSR_n7_verified._native.native_decide.ax_1_1"} *)
LeanTurtleBoundedRun["SSR", 7, "Perturb" -> {"DropOrbit", 2, 3}]["Status"]   (* "Failed": 軌道を 1 本抜くと始点が覆われない *)
LeanTurtleBoundedRun["SSR", 7, "Method" -> "decide", "Coronas" -> {12}]       (* kernel でコロナ 1 個、約 70 秒・5 GB *)
```

kernel だけで全 30 コロナを検査する版 (`"Method" -> "decide"`) はコロナごとの定理を 1 つずつ検査して同じ命題 `checkBounded prog 7 atlas certs periods = true` に組む。メモリ監視のもとで lean.exe を直接走らせるときは `tbBoundedTheorem["SSR", 7, "Method" -> "decide"]` の `LeanSource` を書き出す。

## 7. LeanLink へ

```mathematica
env = LeanLinkImport[t2];    (* Mathlib を使わない定理を LeanLink の LeanEnvironment に *)
env["add_comm_nat"]["ExprGraph"]
```
