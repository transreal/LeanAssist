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

### 中学の図形の定理 (シンプルな例)

```mathematica
(* ∠XOY の辺 OX, OY 上に OA = OB, OC = OD となる点をとる → AD = BC (二辺とその間の角) *)
sas = GeometricScene[{o, x, y, a, b, c, d}, {
   a \[Element] HalfLine[{o, x}], c \[Element] HalfLine[{o, x}],
   b \[Element] HalfLine[{o, y}], d \[Element] HalfLine[{o, y}],
   EuclideanDistance[o, a] == EuclideanDistance[o, b], EuclideanDistance[o, c] == EuclideanDistance[o, d]}];
LeanGeometryReport[sas, EuclideanDistance[a, d] == EuclideanDistance[b, c], "Name" -> "sas_ad_bc", "ProofView" -> True]
```

辺の上の点は半直線 `HalfLine[{o, x}]` で書く (a = o + t_a (x − o)、t_a ≥ 0)。OA = OB は t_a·|OX| = t_b·|OY| と訳す (|OX|, |OY| は距離変数 `dox`, `doy`)。|OA|² = |OB|² と 2 乗すると「A が反対側の半直線にある」解も入ってしまい、そこでは AD = BC が成り立たないので証明書が見つからない。Lean の定理は

```
theorem sas_ad_bc (xx xy yy ta tc tb td dox doy : ℝ)
    (h1 : dox*ta - doy*tb = 0) (h2 : dox*tc - doy*td = 0)
    (h3 : dox^2 - xx^2 = 0) (h4 : doy^2 - xy^2 - yy^2 = 0) (hnd1 : doy ≠ 0) :
    |AD|² − |BC|² を展開した式 = 0 := by
  have hprod : doy * (…) = 0 := by linear_combination … * h1 + … * h2 + … * h3 + … * h4
  exact (mul_eq_zero.mp hprod).resolve_left hnd1
```

で Proved (約 11 秒、公理 propext, Classical.choice, Quot.sound)。非退化条件 `doy ≠ 0` は「Y ≠ O」。

```mathematica
(* 平行線の錯角: ab ∥ cd、p, q が交わる点 → ∠bpq = ∠cqp *)
par = GeometricScene[{a, b, c, d, p, q}, {GeometricAssertion[{Line[{a, b}], Line[{c, d}]}, "Parallel"],
   p \[Element] Line[{a, b}], q \[Element] Line[{c, d}]}];
LeanGeometryReport[par, PlanarAngle[{b, p, q}] == PlanarAngle[{c, q, p}], "Name" -> "alternate_angles", "ProofView" -> True]

(* 対頂角: b は直線 ao 上、d は直線 co 上 → ∠aoc = ∠bod *)
vert = GeometricScene[{o, a, c, b, d}, {b \[Element] Line[{a, o}], d \[Element] Line[{c, o}]}];
LeanGeometryReport[vert, PlanarAngle[{a, o, c}] == PlanarAngle[{b, o, d}], "Name" -> "vertical_angles"]

(* 二等辺三角形の底角 *)
iso = GeometricScene[{a, b, c}, {Triangle[{a, b, c}], EuclideanDistance[a, b] == EuclideanDistance[a, c]}];
LeanGeometryReport[iso, PlanarAngle[{a, b, c}] == PlanarAngle[{a, c, b}], "Name" -> "isosceles_base_angles"]
```

角の等式の主張に注意: 錯角は「向き付きの角が 180° を法として等しい」(full-angle 形、`linear_combination` 511 文字) で証明され、これは「等しいか補角」を含意する。対頂角と底角は cos² 形 (「等しいか補角」) で証明される。どれも `Caveats` に書かれる。図の配置 (b と c が横断線の反対側にある、など) で「等しい」に絞るのは座標の符号の条件で、多項式の証明書の外にある (次節の順序条件は、非退化因子 d ≠ 0 を示すのに使う)。

### 順序条件で枝を選ぶ (線分上・半直線上・同じ側・向き)

等式だけでは図の「別の枝」でも仮定が成り立ち、そこで結論が偽になる定理は証明書が無い。場面の順序条件 (線分 `Line[{a, b}]` 上なら 0 ≤ t ≤ 1、同じ側なら符号付き面積の積 > 0 など) を使うと、その枝でだけ 0 になる因子 d を Lean の中で d ≠ 0 と証明できる。

```mathematica
(* 線分上の p で |ap| = |ab| なら p = b (直線上なら反対側の点もある): d = tp + 1, 0 ≤ tp から *)
seg = GeometricScene[{a, b, c, p}, {Triangle[{a, b, c}], p \[Element] Line[{a, b}], EuclideanDistance[a, p] == EuclideanDistance[a, b]}];
LeanGeometryReport[seg, p == b, "Name" -> "segment_branch"]          (* Proved、仮定 hord1 : 0 ≤ tp、hnd1 : xb*yc ≠ 0 *)
LeanGeometryTheorem[seg, p == b, "OrderConditions" -> False]["CertificateStatus"]   (* "NotFound" *)

(* 直線 ab の同じ側の c, d で |ac| = |ad|, |bc| = |bd| なら c = d (反対側なら鏡像) *)
mir = GeometricScene[{a, b, c, d}, {GeometricAssertion[{c, d}, {"SameSide", InfiniteLine[{a, b}]}],
   EuclideanDistance[a, c] == EuclideanDistance[a, d], EuclideanDistance[b, c] == EuclideanDistance[b, d]}];
thm = LeanGeometryTheorem[mir, c == d, "Name" -> "same_side_mirror"];
thm["Hypotheses"]          (* h1, h2 と hord1 : 0 < xb^2*yc*yd だけ: 非退化の仮定は残らない *)
thm["Proof"]
(* have hnd1 : xb ≠ 0 := by
     have hsign : 0 < (xb) * (xb*yc*yd) := by linear_combination hord1
     exact left_ne_zero_of_mul hsign.ne'
   have hnd2 : yc + yd ≠ 0 := by
     have hsign : 0 < (yc + yd) * (xb^2*yd) := by linear_combination hord1 + sq_nonneg (xb*yd)
     exact left_ne_zero_of_mul hsign.ne'
   refine ⟨?_, ?_⟩ … *)
LeanProofView[thm, "ProofGraph", "Trace" -> False]   (* 場面の SameSide → hord1 → hnd1, hnd2 (sign) → g = 0 *)

(* 向き: Counterclockwise があると三角形の非退化 xb*yc ≠ 0 も 0 < xb*yc から証明され、hnd が残らない *)
```

d·r = c + Σ λ q + Σ μ m² > 0 (q は順序条件とその積、m は単項式) を厳密な線形計画で探し、`linear_combination` にそのまま渡す。順序条件そのものを結論にする定理 (同じ側・内部・向き) や不等式の結論は対象外 (二乗和の証明書が要る)。

### 証明の過程を可視化する

```mathematica
(* 報告の下に証明の過程のタブを付ける (Lean のコンパイルがもう 1 回) *)
LeanGeometryReport[npc, GeometricAssertion[{ma, mb, mc, mah}, "Concyclic"], "ProofView" -> True]

thm = LeanGeometryTheorem[npc, GeometricAssertion[{ma, mb, mc, mah}, "Concyclic"]];
LeanProofView[thm, "Steps", "Trace" -> False]         (* 座標 → 構成点 → h1..h3 → 結論 → 証明書 を図の上で 1 手ずつ *)
LeanProofView[thm, "ProofGraph", "Trace" -> False]    (* 垂心の 2 条件 h2, h3 だけが使われ、垂線の足の条件 h1 は灰色 *)
LeanProofView[thm, "Cancellation", "Trace" -> False]  (* d·g と −cᵢ·hᵢ の 13 個の単項式: 各列の和が 0 *)
LeanProofView[thm, "Deform"]                          (* h を垂心から外すと h2, h3 と g が連動、project で戻すと g = 0 *)

tr = LeanProofTrace[thm];        (* trace_state を差し込んで lean --json *)
tr["ProofDataset"]               (* 1: linear_combination (norm := skip) …  → 1 goal (Lean の確かめる恒等式)
                                    2: ring1                                  closes the goal *)
tr["GoalGraph"]
LeanProofView[thmSim, "Identity", "Trace" -> False]   (* シムソン: 三角消去の 3 段 (tf, te, td を消去) と主係数 = 非退化条件 *)
```

## 4a. グラフ: Graph で表現し、証明書を Lean の decide で検査

```mathematica
pet = PetersenGraph[];
LeanGraphReport[pet, "ChromaticNumber"]   (* 3 色の彩色 + 2 色の 1024 通りを網羅、decide +kernel *)
LeanGraphReport[pet, "Hamiltonian"]       (* 無い: 9! = 362880 通りの巡回順を網羅、native_decide *)
LeanGraphReport[CycleGraph[5], {"Isomorphic", Graph[{1 <-> 3, 3 <-> 5, 5 <-> 2, 2 <-> 4, 4 <-> 1}]}]
LeanGraphReport[PathGraph[Range[4]], {"Isomorphic", StarGraph[4]}]   (* 同型でない: 24 通り *)
thmG = LeanGraphTheorem[pet, "PerfectMatching"];
{thmG["Claim"], thmG["Certificate"], LeanProve[thmG]["Status"]}
```

成り立つ性質は Mathematica の証明書 (彩色・閉路・マッチング・全域木・写像・クリーク) を、成り立たない性質は明示的な列挙の上の網羅を Lean が `decide` で検査する (`lean/graph/FinGraph_template.lean`、Mathlib 不要、1 秒前後)。網羅の件数は `Claim` に書かれる。

## 4b. 論理式: 真理値表・プロットで可視化し Lean で証明

```mathematica
LeanLogicReport[Equivalent[Not[p && q], Not[p] || Not[q]]]          (* 恒真: Prop 上の tauto *)
LeanLogicReport[Implies[p || q, p]]                                  (* どちらでもない: 反例 p = F, q = T と充足例 *)
LeanLogicReport[ForAll[{a, b}, a > 0 && b > 0, (a + b)/2 >= Sqrt[a b]]]  (* nlinarith + Real.sq_sqrt *)
LeanLogicReport[ForAll[x, x^2 > x]]                                  (* 偽: 反例 x = 0 で否定を証明 *)
LeanLogicReport[Exists[x, x^2 == 4 && x > 0]]                        (* 証拠 x = 2 *)
```

## 4c. ClaudeEval から使う

ClaudeEval に問題を与えると、`Claude Directives` の `rules/111-lean-proof-workflow.md` とスキル `lean-assisted-proof` に従って、まず Mathematica で設定を表現・可視化し (幾何 = `GeometricScene`、グラフ = `Graph`、論理 = 論理式)、`Lean*Report` で Lean に渡すコードが生成される。LeanAssist の関数は NBAccess の許可 head なので `Module` に閉じたコードは承認なしで実行される。

```mathematica
ClaudeEval["九点円の定理 (辺の中点 3 つと垂線の足 1 つは共円) を Lean で証明して"]
ClaudeEval["ペテルセングラフの彩色数が 3 であることを証明して"]
ClaudeEval["(p ⇒ q) ⇒ (¬q ⇒ ¬p) がトートロジーであることを Lean で示して"]
```

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

(* LeanLink をロードしておくと、LeanProofTrace の各状態が LeanLink の LeanState / LeanGoal として返る (Mathlib の証明でも) *)
Needs["Wolfram`LeanLink`"];
LeanProofTrace[thm]["States"][[1, "After"]]
```
