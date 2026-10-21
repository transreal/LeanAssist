# LeanAssist API リファレンス

パッケージ: `LeanAssist`
コンテキスト: `LeanAssist``
依存: Lean 4 (elan)、Mathlib を持つ Lake プロジェクト (既定 `~/src/mathlib4`)、任意で Wolfram/LeanLink

Lean の定理は **LeanTheorem オブジェクト**として組み立て、`LeanSource` でソースに、`LeanProve` でコンパイル結果 (**LeanCheckResult**) にする。
「Proved」は *コンパイルエラー無し・`sorry` 無し* を意味し、各定理が依存する公理 (`#print axioms`) が結果に入る。

## 設定

| シンボル | 説明 |
|---|---|
| `$LeanAssistDirectory` | `LeanAssist_info` フォルダ (lean/ テンプレート、examples/、docs/) |
| `$LeanAssistWorkDirectory` | 生成した `.lean`・コマンドファイル・出力の置き場 (既定 `$TemporaryDirectory/LeanAssist`) |
| `$LeanAssistToolchain` | Mathlib 無しのコンパイルに使う elan toolchain 名 (既定: LeanLink パクレットの `lean-toolchain`、`leanprover/lean4:v4.30.0`) |
| `$LeanAssistMathlibDirectory` | Mathlib をビルド済みの Lake プロジェクト。`import Mathlib...` を含むソースはここで `lake env lean` する (既定 `~/src/mathlib4`、無ければ `None`) |
| `$LeanAssistTimeout` | 1 回のコンパイルの制限時間 (秒、既定 600) |
| `LeanAssistStatus[]` | 上記と lean のバージョン・Mathlib の有無・LeanLink の有無を `Dataset` で返す |
| `LeanToolchainBinary["lean" \| "lake"]` | 使用する実行ファイルのパス |

## Lean のコンパイルと結果

### LeanCheck[src, opts] → LeanCheckResult
Lean 4 ソース文字列をコンパイルする。`theorem`/`lemma` 宣言ごとに `#print axioms` を付け足し、出力を解析する。

| オプション | 既定 | 説明 |
|---|---|---|
| `"Mathlib"` | `Automatic` | `import Mathlib` があれば Mathlib プロジェクトで `lake env lean`、無ければ toolchain の `lean` を直接呼ぶ |
| `"Timeout"` | `$LeanAssistTimeout` | 秒。超過すると子プロセスごと kill し、Status は `"Timeout"` |
| `"Axioms"` | `True` | `#print axioms` を付ける |
| `"KeepFiles"` | `False` | 生成ファイルを残す |
| `"FileName"`, `"Directory"` | 自動 | 生成する `.lean` の名前と場所 (`"Directory"` は `$TemporaryDirectory` の下に限る) |
| `"OutputFormat"` | `"Text"` | `"JSON"` で `lean --json`: info メッセージ (`trace_state` など) も含め全メッセージが正確な位置付きで `"Messages"` に入る (`"EndLine"`, `"EndColumn"` も)。テキスト形式の info は位置の見出しが付かず順序も保証されない |

`LeanCheck[thm]` / `LeanCheck[{thm1, ...}]` は `LeanProve` と同じ。`LeanCheckFile[file]` は既存の `.lean` をコンパイルする (作業フォルダにコピーしてコンパイルするので元のファイルは書き換えない。結果の `"SourceFile"` が元のパス)。`#print axioms` はファイル末尾に付け足すので、`namespace ... end` の中の定理は修飾名 (`theorem Foo.bar`) で宣言するか、名前空間の外に置く。

### LeanCheckResult[assoc]
`res["prop"]` で参照する。

| プロパティ | 内容 |
|---|---|
| `"Status"` | `"Proved"` (定理あり・エラー無し・sorry 無し) / `"OK"` (定理無し) / `"Sorry"` / `"Failed"` / `"Timeout"` / `"Error"` / `"Rejected"` (`LeanSourceGuard` が拒否、コンパイルしない; 理由は `"Guard"`) |
| `"Success"` | Status が Proved か OK |
| `"Theorems"`, `"TheoremStatus"` | 宣言された定理名と、定理ごとの Proved / Sorry / Failed (エラー行の位置で判定) |
| `"Axioms"` | 定理名 → 依存公理のリスト (`sorryAx` が入れば未完成、`<定理名>._native.native_decide.ax_1_1` (Lean v4.30、旧版は `Lean.ofReduceBool`) が入れば `native_decide` 使用) |
| `"Sorries"` | `sorryAx` に依存する定理 |
| `"Errors"`, `"Warnings"`, `"Messages"` | `<\|"Line", "Column", "Severity", "Message"\|>` のリスト |
| `"Output"`, `"ExitCode"`, `"Time"`, `"Source"`, `"File"`, `"Command"` | 生の出力など |
| `"Theorem"` | `LeanProve` 経由のとき元の LeanTheorem |
| `"Dataset"` | メッセージの Dataset (= `LeanDiagnostics[res]`) |

## 定理オブジェクト

### LeanTheorem[name, vars, hyps, concl, opts] → LeanTheorem[assoc]

* `vars`: `x` (型は `"Type"` オプション、既定 `ℝ`)、`x -> "Int"`、`{x, y} -> "Nat"`、生文字列 `"x : ℝ"`。
* `hyps`: WL の命題 (`x < y`、`p == 0`、`And[...]` など)、`"h" -> 命題`、または Lean の生文字列。無名のものは `h1, h2, ...`。
* `concl`: WL の命題か Lean の生文字列。

| オプション | 説明 |
|---|---|
| `"Proof"` | tactic ブロックの文字列 (複数行可、既定 `"sorry"`) |
| `"Type"` | 変数の既定型 |
| `"Imports"` | `Automatic` (型と tactic から推定: ℝ → `Mathlib.Data.Real.Basic`、`linear_combination`、`ring`、`nlinarith`、`split_ifs`、`Real.sqrt` など)、リスト、`{Automatic, "Mathlib.X"}` で追加 |
| `"Preamble"` | 定理の前に置く Lean テキスト (`def` など) |
| `"MaxHeartbeats"` | `Automatic` (証明文が 2000 文字を超えるとき `set_option maxHeartbeats 4000000 in` を付ける; 巨大な `linear_combination` の `ring` 正規化が既定の 200000 を超えるため)、整数で明示、`None` で付けない |
| `"DocString"`, `"Namespace"`, `"Data"` | docstring、namespace、付随データ (証明書など) |

`thm["Name"]`, `thm["Variables"]`, `thm["Hypotheses"]`, `thm["Conclusion"]`, `thm["Proof"]`, `thm["Source"]`, `thm["Properties"]` と、`"Data"` のキー (`thm["Certificates"]` など) で参照する。`LeanTheorem[thm, "Proof" -> "..."]` は変更したコピー。

### LeanSource[thm | {thms}] → String
import、preamble、定理の順の Lean ソース。複数の定理は 1 ファイルにまとめる。

### LeanSaveSource[thm, file] / LeanSaveSource[thm]
ソースを UTF-8 で書き出す (既定 `LeanAssist_info/lean/<name>.lean`)。

### LeanProve[thm | {thms}, opts] → LeanCheckResult
`LeanCheck[LeanSource[thm]]`。結果の `"Theorem"` に元の定理、`"TheoremStatus"` に定理ごとの判定。

### LeanForm[expr] → String
WL 式を Lean の式テキストにする。多項式・有理式 (`*`, `^`, `/`)、`Equal`/`Unequal`/不等式、`And`/`Or`/`Not`/`Implies`/`Equivalent`、`ForAll`/`Exists`、`Abs`、`Max`/`Min`、`If`/`Boole`/`Piecewise`、`Mod`、`Sqrt` (`Real.sqrt`)、`Pi` (`Real.pi`)。有理数は `(p/q)`、文字列はそのまま。未知の頭部は `f a b` 形式。

### LeanIdentifier[sym] → String
Lean の識別子 (`Subscript[x, 1]` → `x_1`、`$` → `_`)。

### LeanLiteral[data] / LeanTuple[...] / LeanDataDefinitions[<|name -> data, ...|>, "Types" -> <|...|>]
整数・有理数・真偽値・文字列・リスト (`[...]`)・`LeanTuple` (`(...)`) を Lean のリテラルにし、型を推定して `def name : Type := literal` を並べる。`decide` 型の有限検証にデータを渡すためのもの。深い入れ子のタプルは Lean の elaborator が遅いので、大きな表は構造体リテラルで書く (例: `examples/turtle_port_identities.wl`)。

## 多項式の証明書

### LeanPolynomialCertificate[goal, {h1, ...}, vars, opts] → Association
`d · goal = Σ c_i h_i` となる多項式 `c_i` と非退化因子 `d` を探す。2 段構え:

1. **Groebner 基底**: `GroebnerBasis` (DegreeReverseLexicographic) で `goal · Π d_j^{e_j}` (`d_j` は `"NonDegenerate"` の多項式、総次数 0, 1, ..., `"MaxExponent"`) のイデアル所属を調べ、見つかればタグ変数 `y_i` を加えた `GroebnerBasis[{h_i - y_i}]` (Lexicographic, 変数 > タグ) で簡約して余り `Σ y_i q_i` から `c_i = q_i(h)` を得る。
2. **三角消去** (1 が失敗したとき、`"Method" -> Automatic`): ある変数 `t` について 1 次の仮定 `h = c t + r` で goal を擬除算する (`c^m G = h Q + R`, `R` は `t` を含まない)。垂線の足・交点・外心のように「構成された点」のパラメータを順に消去し、残りの `R` を 1 でイデアル所属判定する。主係数 `c` の既約因子がそのまま非退化条件 (線分が退化しない、直線が平行でない) になり、指数も正確に出る。シムソン線・パップス・デザルグはこの段で証明書が得られる。最後に指数を下げられるだけ下げる (剪定)。

どちらの段でも最後に `Expand` で恒等式を検算する (`"Verified"`)。

| キー | 内容 |
|---|---|
| `"Found"`, `"Verified"` | 証明書の有無と WL 側での検算 |
| `"Coefficients"` | `c_i` |
| `"Factor"`, `"FactorExponents"`, `"NonDegenerate"` | `d` = 非退化因子の冪積、その指数ベクトル、因子のリスト (三角消去では既約因子) |
| `"Method"` | `"Groebner"` / `"Elimination"` |
| `"Inconsistent"` | 仮定が矛盾 (Groebner 基底が `{1}`) — 定理が空虚になる警告 |

オプション `"NonDegenerate" -> {d1, ...}` (≠ 0 と仮定する多項式)、`"MaxExponent" -> 3`、`"Method" -> Automatic | "Groebner"` (消去段を使わない)、`"TimeLimit" -> 30` (1 回のイデアル所属判定の秒数上限; 超えたら「所属しない」扱い)。

### LeanLinearCombination[cert, {"h1", ...}] → String
`linear_combination (c1) * h1 + ...` (仮定を使わないときは `ring`)。

### LeanPolynomialProof[cert, hypNames, ndNames] → String
因子 `d` が無ければ `linear_combination`、あれば
```
have hprod : d * (goal) = 0 := by linear_combination ...
exact (mul_eq_zero.mp hprod).resolve_left hnd
```
(`d` が冪積なら `pow_ne_zero` / `mul_ne_zero` を組む)。

### LeanPolynomialTheorem[name, vars, {h1 == 0, ...}, goal, opts] → LeanTheorem
証明書から証明を作った ℝ 上の定理。`goal` がリストなら連言 (`refine ⟨?_, ?_⟩`)。使った非退化多項式だけが `hnd_j : d_j ≠ 0` として仮定に入る。`thm["Certificates"]`, `thm["CertificateStatus"]` (`"Found"` / `"NotFound"`)、`thm["Inconsistent"]`。

`"Inequalities" -> {p >= 0, q > 0, ...}` (順序条件): 使った非退化因子 d のうち順序条件で 0 から遠ざけられるものは仮定にせず証明する — `d·r = c + Σ λ_q q + Σ μ_m m² > 0` (r は多項式、λ, μ ≥ 0、q は条件とその 2 つの積、m は単項式; 厳密な LP で探す) を `have hnd_j : d ≠ 0 := by have hsign : 0 < d * r := by linear_combination …; exact left_ne_zero_of_mul hsign.ne'` に。使った条件だけが `hord_k : 0 ≤ p` / `0 < p` として仮定に入る。等式だけでは証明書が無いとき (条件が除く枝でだけ結論が偽) は、仮定・Groebner 基底・厳密な条件の既約因子のうち 0 にならないと示せるものを非退化候補に足して探し直す。`thm["OrderHypotheses"]`, `thm["OrderProofs"]`。例: `u² = 1, u ≥ 0 ⇒ u = 1` (d = u + 1)。

## 幾何 (GeometricScene)

### LeanGeometryCoordinates[points, opts] → Association
点記号 `p` に座標 `{xp, yp}` を割り当てる。`"Normalize" -> True` (既定) で第 1 点を原点、第 2 点を x 軸上に置く (等長変換なので Euclid 不変な主張には影響しない)。`"Coordinates" -> <|p -> {..}|>` で固定。

### LeanGeometryPolynomials[scene, opts] → Association
`scene["Hypotheses"]` を座標多項式に翻訳する。

| キー | 内容 |
|---|---|
| `"Coordinates"`, `"BaseCoordinates"` | 置換後 / 置換前の座標 |
| `"Definitions"`, `"Parameters"`, `"ParameterDefinitions"` | `"Parametric" -> True` (既定) で `p == Midpoint[...]`、`TriangleCenter[..., "Centroid"]`、`p ∈ Line[{a, b}]` / `InfiniteLine` / `HalfLine` (→ `p = a + tp (b − a)`) を代入した点とパラメータ |
| `"RayParameters"` | 半直線 `p ∈ HalfLine[{o, x}]` (角の辺上の点) のパラメータ (t ≥ 0)。仮定と結論の中の `EuclideanDistance[o, p]` は `t·EuclideanDistance[o, x]` に書き換えてから訳す (OA = OB が t_a\|OX\| = t_b\|OY\| になり、2 乗した \|OA\|² = \|OB\|² と違って反対側の半直線の解を含まない)。Caveats に「t ≥ 0 は翻訳が使う (仮定には入らない)」と記録 |
| `"Inequalities"` | 順序条件 `<\|"Poly", "Strict", "Source", "Kind"\|>` (Poly ≥ 0 / > 0): 線分 `p ∈ Line[{a, b}]` の 0 ≤ t ≤ 1 (固定点なら (p−a)·(b−p) ≥ 0)、半直線の t ≥ 0、`p ∈ Triangle[{a, b, c}]` (各辺の内側 × 向き ≥ 0)、`GeometricAssertion[{p, q}, {"SameSide" \| "OppositeSides", line}]` (符号付き面積の積 > 0 / < 0)、`"Counterclockwise"` / `"Clockwise"` (符号付き面積 > 0 / < 0)、距離変数 d ≥ 0 |
| `"Hypotheses"` | 仮定ごとのレコード `<\|"Kind", "Polynomials", "NonDegenerate", "Caveat", "Source"\|>` |
| `"Polynomials"`, `"NonDegenerate"` | 全仮定の多項式 (= 0) と非退化候補 (≠ 0; `Triangle` の符号付き面積など) |
| `"Unsupported"`, `"Caveats"` | 翻訳できなかった仮定と注意 (角の等式は cos² 条件、面積は符号付き、など) |

対応する語彙: `Triangle`、`Polygon`、`Element[p, Line | InfiniteLine | HalfLine]`、`Element[p, Circle[o, r]]` (r は記号または `EuclideanDistance[o, a]`)、`Element[p, CircleThrough[...]]`、`p == Midpoint[{a, b}]`、`p == TriangleCenter[{a,b,c}, "Centroid" | "Circumcenter" | "Orthocenter"]`、`p == q`、`GeometricAssertion` の `"Collinear"`, `"Parallel"`, `"Perpendicular"`, `"Concurrent"`, `"Concyclic"`, `"Congruent"`, `"Similar"`, `"Equilateral"`, `"Counterclockwise"`/`"Clockwise"` (順序条件)、`{"SameSide" | "OppositeSides", line}` (順序条件)、`Element[p, Triangle[...]]` (内部、順序条件)、`CollinearPoints`、`PlanarAngle[...] == θ` (90° は内積 = 0、他は cos² 条件)、`PlanarAngle == PlanarAngle`、`PlanarAngle == 2 PlanarAngle` (どちらも cos² 条件; 結論では、より強く次数が半分の「向き付きの角の mod 180° の関係」(z₁ = ū₁v₁ と z₂ または z₂² が平行) を代替として持つ — `LeanGeometryTheorem` の `"AlternativeThreshold"` を参照)、`EuclideanDistance` の積・冪・定数倍の等式 (両辺を 2 乗)、その他の距離関係 (距離変数 `d ≥ 0` を導入)、`Area[Triangle | Polygon]` の等式 (符号付き面積)、`SignedRatio[a, p, b]` を含む有理式の等式 (分子 = 0、分母 ≠ 0)。連言 `And[...]` も可。`InfiniteLine[{o, x}]` / `HalfLine[{o, x}]` は点の記号のままだと `{o, x}` が方向ベクトルと解釈されて評価されてしまうので、場面の中の `Inactive` のまま扱う (2026-10-19 以前は未対応扱いになっていた)。

### LeanGeometryStatement[concl, geo] → Association
結論を同じ座標系で翻訳する (`"Kind"`, `"Polynomials"`, `"NonDegenerate"`, `"Caveat"`)。

### LeanGeometryTheorem[scene, concl, opts] → LeanTheorem
翻訳 → 証明書 → 定理。`"Name"`, `"NonDegenerate"` (追加条件、座標の式でも幾何の式でも可), `"MaxExponent"`, `"Normalize"`, `"Parametric"`, `"InstanceCheck" -> True` (RandomInstance を仮定多様体へ Gauss–Newton で射影してから仮定・結論の残差を調べる)、`"AlternativeThreshold" -> 3000` (結論の翻訳が代替形を持つとき、第 1 形の証明書が無いか証明文がこの文字数を超えるなら代替形でも証明書を探し、見つかって短ければそちらを使う。代替形は第 1 形を含意するので定理は強くなるだけ。`thm["Statement"]["Form"]` が `"Alternative"` になる)。結論がパラメータ置換で恒等的に 0 になるときは置換無しで言い直す (Varignon の平行性など)。

`"OrderConditions" -> True` (既定): 場面の順序条件 (`geo["Inequalities"]`、結論の距離変数 ≥ 0) を `LeanPolynomialTheorem` の `"Inequalities"` に渡す。線分上・半直線上・同じ側・向きで枝が決まる定理 (線分上の p で |ap| = |ab| ⇒ p = b、同じ側の c, d で |ac| = |ad|, |bc| = |bd| ⇒ c = d) は、等式だけでは証明書が無いが順序条件で証明できる。`"Counterclockwise"` があれば三角形の非退化も証明される (hnd が残らない)。`False` で従来どおり (順序は使わない)。順序だけの結論 (同じ側・内部・向き) は不等式なので未対応、線分・半直線上の結論は共線だけを示す (Caveat)。`thm["OrderHypotheses"]` は条件の出どころ (`"Source"`, `"Kind"`) 付き。

角の結論の代替形は「向き付きの角の mod 180° の関係」(full angle): 角の等式は Im(z₁ z̄₂) = 0、角の 2 倍は z₁ ∥ z₂² (zₖ = ūₖvₖ)。円周角・中心角のように向きが揃う定理では cos² 形 (12 次) より次数が半分で Lean の `linear_combination` が速い。二等辺三角形の底角のように鏡像の関係にある角では偽になるので、そのときは証明書が見つからず cos² 形が残る。
`thm["Geometry"]`, `thm["Statement"]`, `thm["Certificates"]`, `thm["CertificateStatus"]`, `thm["InstanceCheck"]`, `thm["Caveats"]`, `thm["Unsupported"]`, `thm["Instance"]`。

### LeanGeometryReport[scene, concl, opts]
RandomInstance の図、定理名・結論・Lean の判定・証明書・数値検査・注意・使った順序条件 (`hord_k` と場面の出どころ、あれば)・公理、Lean ソースと結果 (OpenerView) を 1 つの Grid に。`"ProofView" -> True` で下に証明の過程 (`LeanProofView` のタブ) を付ける (Lean のコンパイルがもう 1 回、約 10 秒)。

数値検査は、構成で決まる変数 (直線上の点のパラメータ、`p == …` / `p ∈ …` で定まる点の座標、補助変数) だけを仮定多様体へ射影し、自由な点は動かさない (全変数を射影すると三角形が潰れた退化解に落ち、結論が弱い意味でしか確かめられないことがある)。収束しないときは従来どおり全変数で射影する。

### LeanGeometryConjectures[scene, opts] → Dataset
`FindGeometricConjectures` の各結論を翻訳して証明書を探し、`"Prove" -> True` (既定) なら 1 ファイルにまとめて Lean で確認する。列: `Conjecture`, `Status` (`Proved` / `Failed` / `Sorry` / `NoCertificate` / `Unsupported`), `Caveats`, `Theorem`。

### SignedRatio[a, p, b]
結論の語彙。直線 ab 上の p について符号付き比 ap/pb (= `t/(1−t)`, p = a + t(b − a))。座標では `((p−a)·(b−a)) / ((b−p)·(b−a))`。メネラウス (積 = −1)、チェバ (積 = 1)、オイラー線 (`SignedRatio[h, g, o] == 2`) に使う。

## グラフ (Graph)

### LeanGraphTheorem[g, prop, opts] → LeanTheorem
有限・単純・無向の `Graph` の性質を Lean の定理にする。Mathematica が性質を判定して証明書を計算し、Lean は単独の Lean (Mathlib 不要) で `decide` 検査する。グラフは `LeanAssist_info/lean/graph/FinGraph_template.lean` の `FinGraph.G` (`⟨n, [(u, v), …]⟩`、頂点 0 … n−1、u < v) に番号付けして書く (図は元の頂点名)。

| `prop` | 成り立つとき (Lean の結論) | 成り立たないとき |
|---|---|---|
| `"Bipartite"`, `{"Colorable", k}` | 彩色 `col`: `(simple gr && properColoring gr k col) = true` | `notColorable gr k` (k^n 通りの全彩色を網羅) |
| `"ChromaticNumber"` | χ 色の彩色と `notColorable gr (χ−1)` | — |
| `"Hamiltonian"` | 閉路 `cyc`: `hamiltonianCycle gr cyc` | `notHamiltonian gr` ((n−1)! 通りの巡回順を網羅) |
| `"PerfectMatching"` | `perfectMatching gr matching` | 証明無し (`$Failed`、メッセージ `nocert`) |
| `"Connected"` | 全域木 `spanningTree gr 0 parent depth` | `separated gr part` (辺が出ない頂点集合) |
| `"Eulerian"` | オイラー回路 `eulerCircuit gr walk` | 証明無し |
| `{"Isomorphic", h}` | 頂点写像 `isomorphism gr gr2 iso` | `notIsomorphic gr gr2` (n! 通りの全単射を網羅) |
| `{"Clique", k}` | クリーク `clique gr cl && cl.length == k` | 証明無し |
| `"Handshake"` | `handshake gr` (次数和 = 辺数の 2 倍) | — |

| オプション | 既定 | 説明 |
|---|---|---|
| `"Name"` | `Automatic` | 定理名 (`graph_<性質>`) |
| `"Method"` | `Automatic` | 網羅の候補数が 60000 以下なら `"decide +kernel"`、超えると `"native_decide"`。`"decide"` / `"native_decide"` で固定 |
| `"MaxCandidates"` | 400000 | 網羅の上限。超えると `$Failed` (メッセージ `big`) |

`thm["Holds"]` (Mathematica の判定)、`thm["Claim"]` (証明される文、網羅の件数を含む)、`thm["Certificate"]`、`thm["Candidates"]`、`thm["Method"]`、`thm["Picture"]`。

### LeanGraphReport[g, prop, opts]
グラフに証明書 (彩色・閉路・マッチング・全域木・写像・クリーク) を重ねた図、性質・判定・Claim・方法、Lean のソース (テンプレート部分は省略)、`LeanCheckResult` を `Grid` で返す。kernel の `decide` が失敗・時間切れのとき `native_decide` で再検査する (方法の欄にそう出る)。オプションは `LeanGraphTheorem` と `LeanCheck` のもの。

```mathematica
LeanGraphReport[PetersenGraph[], "ChromaticNumber"]   (* 3 色の彩色 + 2 色の 1024 通りを網羅 *)
LeanGraphReport[PetersenGraph[], "Hamiltonian"]       (* 無い: 362880 通り、native_decide *)
LeanGraphReport[CycleGraph[5], {"Isomorphic", Graph[{1 <-> 3, 3 <-> 5, 5 <-> 2, 2 <-> 4, 4 <-> 1}]}]
```

## 論理式

### LeanLogicTheorem[expr, opts] → LeanTheorem
- **命題論理** (記号と `And`, `Or`, `Not`, `Implies`, `Equivalent`, `Xor`, `Nand`, `Nor`): `TautologyQ` / `SatisfiableQ` で分類。恒真は `∀ p q : Prop, …` を `tauto`、矛盾は否定を `tauto`、どちらでもないものは「恒真でない ∧ 充足可能」を `SatisfiabilityInstances` の割り当てで証明する。
- **量化式** (`ForAll[x, body]`, `ForAll[x, cond, body]`, `Exists[…]`、多項式・`Sqrt` の等式と不等式): `Resolve` で真偽を判定。真の全称は `intro` の後 `first | positivity | nlinarith [ヒント] | linarith | ring | norm_num` (整数は `omega`, `decide` も)、ヒントは変数・差・和の平方、1 変数の余裕の平方因子と有理根、`Sqrt[t]` には `Real.sqrt_nonneg t` と `Real.sq_sqrt`。真の存在は `FindInstance` の証拠、偽の全称は反例で否定、偽の存在は `push_neg` の後に同じ tactic 探索。交互の量化子は自動証明しない (`sorry`)。

| オプション | 既定 | 説明 |
|---|---|---|
| `"Name"` | `Automatic` | `logic_<statement>` |
| `"Domain"` | `Automatic` | `Reals` (既定) / `Integers` (`Element[x, Integers]` があれば) / `NonNegativeIntegers` |
| `"Statement"` | `Automatic` | 証明する文。命題論理は `"Tautology"`, `"Unsatisfiable"`, `"Satisfiable"`, `"Contingent"`、量化式は `"True"`, `"False"` |

`thm["Verdict"]` (Mathematica の判定)、`thm["Claim"]`、`thm["Falsifying"]` / `thm["Satisfying"]` (命題論理の割り当て)、`thm["Instance"]` (証拠・反例)。

### LeanLogicReport[expr, opts]
命題論理は真理値表 (6 変数まで)、量化式は 1 変数で `Plot` (証拠・反例の点つき)、2 変数で `RegionPlot` を描き、式・判定・Claim・Lean のソース・結果を `Grid` で返す。

```mathematica
LeanLogicReport[Equivalent[Not[p && q], Not[p] || Not[q]]]
LeanLogicReport[ForAll[{a, b}, a > 0 && b > 0, (a + b)/2 >= Sqrt[a b]]]
LeanLogicReport[ForAll[x, x^2 > x]]   (* 偽: 反例 x = 0 *)
```

## 証明の過程の可視化

`LeanProofTrace[thm]` は各 tactic の前後のゴールを Lean の `trace_state` (`lean --json`) から読み、ゴール木 (`"GoalGraph"`)・1 手ずつの表示 (`"Stepper"`)・手順の Dataset を返す (`linear_combination` は `(norm := skip)` + `ring1` に分けて、Lean が確かめる恒等式をゴールとして見せる)。`LeanProofView[thm]` は幾何の手順図 (`"Steps"`)・証明書の導出グラフ (`"ProofGraph"`, ProofObject の配色)・恒等式 (`"Identity"`)・単項式の打ち消し (`"Cancellation"`)・変形 (`"Deform"`)・Lean のゴール (`"Goals"`, `"GoalGraph"`, `"Tactics"`) をタブで見せる。`Lean*Report[…, "ProofView" -> True]` で報告の下に付く。詳細は **`api_proofview.md`**。

## ソース検査と ClaudeEval

### LeanSourceGuard[src] → {理由, …}
コンパイル時にコードを走らせる構文と I/O を検出する: `#eval`, `run_cmd`, `run_elab`, `run_meta`, `run_tac`, `elab`, `elab_rules`, `macro`, `macro_rules`, `syntax`, `declare_syntax_cat`, `initialize`, `unsafe`, `implemented_by`, `extern`, `@[export`, `IO`, `EIO`, `BaseIO`, `System.`, `Process`, raw string、`Mathlib` / `Init` / `Std` / `Batteries` / `Aesop` / `Qq` / `Plausible` / `Lean` 以外の `import`。文字列リテラルとコメントの中は見ない。`LeanCheck` / `LeanProve` / `LeanLinkImport` はコンパイル前にこれを通し、引っかかればコンパイルせず Status `"Rejected"` (結果の `"Guard"` に理由)。`"Directory"` は `$TemporaryDirectory` の下に限る (外なら `$LeanAssistWorkDirectory`)。また `LeanSource` と `LeanCheck` は、Mathematica の私用領域の二重線文字 (`\[DoubleStruckCapitalN]` などは Unicode の ℕ ではない) のうち C, N, Q, R, Z を ℂ ℕ ℚ ℝ ℤ に直す (型は `"Nat"`, `"Int"` と ASCII で書くのが確実)。

### ClaudeEval から使う
- ロード時に NBAccess の許可 head (`NBRegisterAllowedHeads` と `NBRegisterTrustedPackageHeads`) に登録される: `LeanCheck`, `LeanProve`, `LeanTheorem`, `LeanSource`, `LeanForm`, 多項式・幾何・グラフ・論理の各関数、`LeanAssistStatus`, `LeanSourceGuard` など。登録しないもの (承認が要る): `LeanSaveSource` (任意の場所に書く)、`LeanCheckFile` (任意のファイルを読む)、`LeanLinkImport` (パクレットを読む)、タートル証明書の関数 (数分・数十 GB)。
- `$ClaudePackageKeywordMap["LeanAssist"]` (Lean、Mathlib、形式証明、定理証明、証明して、GeometricScene、初等幾何、メネラウス、トートロジー …) で、プロンプトにそれらがあればこの api.md が注入される。タートル関係の語 (タートル、Penrose、証明書 …) では `api_turtle.md` も注入される。
- 手順は `Claude Directives` の `rules/111-lean-proof-workflow.md` とスキル `lean-assisted-proof`: Mathematica で設定を表現 (GeometricScene / Graph / 論理式) → 可視化 → `Lean*Report` で Lean へ。

## LeanLink との接続

### LeanLinkImport[thm | src] → LeanEnvironment
Mathlib を使わないソースを `Wolfram`LeanLink`LeanImportString` でコンパイルし、LeanLink の `LeanEnvironment` (式グラフ `"ExprGraph"`、呼び出しグラフ、`LeanState`/`LeanTactic` による対話的証明) に渡す。LeanLink 側はコンパイルエラーの本文や `sorry` を報告しないので、同じソースを先に `LeanCheck` に通すこと。

## 付属物

* `LeanAssist_info/lean/graph/FinGraph_template.lean`: グラフの検査器 (素の Lean、`namespace FinGraph`): `G`, `adj`, `simple`, `degree`, `handshake`, `properColoring`, `allColorings`, `notColorable`, `hamiltonianCycle`, `perms`, `allCycles`, `notHamiltonian`, `perfectMatching`, `spanningTree`, `separated`, `eulerCircuit`, `isomorphism`, `notIsomorphic`, `clique`。否定の文は明示的な列挙の上の網羅 (`List.all`) なので、定理はそのまま「どの候補も成り立たない」と読める。
* `LeanAssist_info/examples/LeanAssist_examples.nb`: 使い方のノートブック。
* `test codes/LeanAssist_test.wl`: テスト (Lean 無しのグループ 1–4、Lean のグループ 5–6、タートル証明書のグループ 7、ソース検査・グラフ・論理式のグループ 8、証明の過程の可視化のグループ 9)。
* タートル証明書 (pass-substitution、有界性) の検査器・Lean の補題・関数 (`LeanTurtle*`) は **`api_turtle.md`**。
