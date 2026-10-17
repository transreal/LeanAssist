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
| `"FileName"`, `"Directory"` | 自動 | 生成する `.lean` の名前と場所 |

`LeanCheck[thm]` / `LeanCheck[{thm1, ...}]` は `LeanProve` と同じ。`LeanCheckFile[file]` は既存の `.lean` をコンパイルする (作業フォルダにコピーしてコンパイルするので元のファイルは書き換えない。結果の `"SourceFile"` が元のパス)。`#print axioms` はファイル末尾に付け足すので、`namespace ... end` の中の定理は修飾名 (`theorem Foo.bar`) で宣言するか、名前空間の外に置く。

### LeanCheckResult[assoc]
`res["prop"]` で参照する。

| プロパティ | 内容 |
|---|---|
| `"Status"` | `"Proved"` (定理あり・エラー無し・sorry 無し) / `"OK"` (定理無し) / `"Sorry"` / `"Failed"` / `"Timeout"` / `"Error"` |
| `"Success"` | Status が Proved か OK |
| `"Theorems"`, `"TheoremStatus"` | 宣言された定理名と、定理ごとの Proved / Sorry / Failed (エラー行の位置で判定) |
| `"Axioms"` | 定理名 → 依存公理のリスト (`sorryAx` が入れば未完成、`Lean.ofReduceBool` が入れば `native_decide` 使用) |
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

## 幾何 (GeometricScene)

### LeanGeometryCoordinates[points, opts] → Association
点記号 `p` に座標 `{xp, yp}` を割り当てる。`"Normalize" -> True` (既定) で第 1 点を原点、第 2 点を x 軸上に置く (等長変換なので Euclid 不変な主張には影響しない)。`"Coordinates" -> <|p -> {..}|>` で固定。

### LeanGeometryPolynomials[scene, opts] → Association
`scene["Hypotheses"]` を座標多項式に翻訳する。

| キー | 内容 |
|---|---|
| `"Coordinates"`, `"BaseCoordinates"` | 置換後 / 置換前の座標 |
| `"Definitions"`, `"Parameters"`, `"ParameterDefinitions"` | `"Parametric" -> True` (既定) で `p == Midpoint[...]`、`TriangleCenter[..., "Centroid"]`、`p ∈ Line[{a, b}]` (→ `p = a + tp (b − a)`) を代入した点とパラメータ |
| `"Hypotheses"` | 仮定ごとのレコード `<\|"Kind", "Polynomials", "NonDegenerate", "Caveat", "Source"\|>` |
| `"Polynomials"`, `"NonDegenerate"` | 全仮定の多項式 (= 0) と非退化候補 (≠ 0; `Triangle` の符号付き面積など) |
| `"Unsupported"`, `"Caveats"` | 翻訳できなかった仮定と注意 (角の等式は cos² 条件、面積は符号付き、など) |

対応する語彙: `Triangle`、`Polygon`、`Element[p, Line | InfiniteLine | HalfLine]`、`Element[p, Circle[o, r]]` (r は記号または `EuclideanDistance[o, a]`)、`Element[p, CircleThrough[...]]`、`p == Midpoint[{a, b}]`、`p == TriangleCenter[{a,b,c}, "Centroid" | "Circumcenter" | "Orthocenter"]`、`p == q`、`GeometricAssertion` の `"Collinear"`, `"Parallel"`, `"Perpendicular"`, `"Concurrent"`, `"Concyclic"`, `"Congruent"`, `"Similar"`, `"Equilateral"`, `"Counterclockwise"`/`"Clockwise"` (非退化のみ)、`CollinearPoints`、`PlanarAngle[...] == θ` (90° は内積 = 0、他は cos² 条件)、`PlanarAngle == PlanarAngle`、`PlanarAngle == 2 PlanarAngle` (どちらも cos² 条件; 結論では、より強く次数が半分の「向き付きの角の mod 180° の関係」(z₁ = ū₁v₁ と z₂ または z₂² が平行) を代替として持つ — `LeanGeometryTheorem` の `"AlternativeThreshold"` を参照)、`EuclideanDistance` の積・冪・定数倍の等式 (両辺を 2 乗)、その他の距離関係 (距離変数 `d ≥ 0` を導入)、`Area[Triangle | Polygon]` の等式 (符号付き面積)、`SignedRatio[a, p, b]` を含む有理式の等式 (分子 = 0、分母 ≠ 0)。連言 `And[...]` も可。

### LeanGeometryStatement[concl, geo] → Association
結論を同じ座標系で翻訳する (`"Kind"`, `"Polynomials"`, `"NonDegenerate"`, `"Caveat"`)。

### LeanGeometryTheorem[scene, concl, opts] → LeanTheorem
翻訳 → 証明書 → 定理。`"Name"`, `"NonDegenerate"` (追加条件、座標の式でも幾何の式でも可), `"MaxExponent"`, `"Normalize"`, `"Parametric"`, `"InstanceCheck" -> True` (RandomInstance を仮定多様体へ Gauss–Newton で射影してから仮定・結論の残差を調べる)、`"AlternativeThreshold" -> 3000` (結論の翻訳が代替形を持つとき、第 1 形の証明書が無いか証明文がこの文字数を超えるなら代替形でも証明書を探し、見つかって短ければそちらを使う。代替形は第 1 形を含意するので定理は強くなるだけ。`thm["Statement"]["Form"]` が `"Alternative"` になる)。結論がパラメータ置換で恒等的に 0 になるときは置換無しで言い直す (Varignon の平行性など)。

角の結論の代替形は「向き付きの角の mod 180° の関係」(full angle): 角の等式は Im(z₁ z̄₂) = 0、角の 2 倍は z₁ ∥ z₂² (zₖ = ūₖvₖ)。円周角・中心角のように向きが揃う定理では cos² 形 (12 次) より次数が半分で Lean の `linear_combination` が速い。二等辺三角形の底角のように鏡像の関係にある角では偽になるので、そのときは証明書が見つからず cos² 形が残る。
`thm["Geometry"]`, `thm["Statement"]`, `thm["Certificates"]`, `thm["CertificateStatus"]`, `thm["InstanceCheck"]`, `thm["Caveats"]`, `thm["Unsupported"]`, `thm["Instance"]`。

### LeanGeometryReport[scene, concl, opts]
RandomInstance の図、定理名・結論・Lean の判定・証明書・数値検査・注意・公理、Lean ソースと結果 (OpenerView) を 1 つの Grid に。

### LeanGeometryConjectures[scene, opts] → Dataset
`FindGeometricConjectures` の各結論を翻訳して証明書を探し、`"Prove" -> True` (既定) なら 1 ファイルにまとめて Lean で確認する。列: `Conjecture`, `Status` (`Proved` / `Failed` / `Sorry` / `NoCertificate` / `Unsupported`), `Caveats`, `Theorem`。

### SignedRatio[a, p, b]
結論の語彙。直線 ab 上の p について符号付き比 ap/pb (= `t/(1−t)`, p = a + t(b − a))。座標では `((p−a)·(b−a)) / ((b−p)·(b−a))`。メネラウス (積 = −1)、チェバ (積 = 1)、オイラー線 (`SignedRatio[h, g, o] == 2`) に使う。

## LeanLink との接続

### LeanLinkImport[thm | src] → LeanEnvironment
Mathlib を使わないソースを `Wolfram`LeanLink`LeanImportString` でコンパイルし、LeanLink の `LeanEnvironment` (式グラフ `"ExprGraph"`、呼び出しグラフ、`LeanState`/`LeanTactic` による対話的証明) に渡す。LeanLink 側はコンパイルエラーの本文や `sorry` を報告しないので、同じソースを先に `LeanCheck` に通すこと。

## 付属物

* `LeanAssist_info/lean/turtle/TurtleO2_template.lean`: タートル証明書 (pass-substitution) の frames / port delta / O3 / O2 を検査する Lean の検査器 (Mathlib 不要)。port / pass 族は id をキーとする平衡二分探索木 `BTree` (燃料付き merge sort + 均等分割、重複キーと要素落ちを `ofList` が検査) で引く (`Cert.index`): 1560 port 族の証明書でも線形探索にならない。
* `LeanAssist_info/lean/turtle/TurtleO1_template.lean`: O1 (基底レベル B の超タイル内シミュレーション) の検査器。標準超タイルの三角形列挙、正の三角形による菱形の所有 (ghost half)、辺キーの二分探索木による navigation、タートル走行を Lean の計算可能定義として書き、`checkO1 cert prog o1Data` で各 pass 族の exit port と S 移動数 N(π,B) を再計算する。O2 テンプレートの後ろに連結して使う (`Z5` 算術と `portAt` を共有)。
* `LeanAssist_info/lean/turtle/AffineRecurrence.lean`: 証明の補題 1 (Mathlib、`AddGroup V` 上の `u (n+1) = M (u n) + d` 型の漸化式は 2 点で一致すれば定数も全項も一致; 偶奇類版の系 `parity_class_unique` / `parity_class_unique'`)。`LeanCheckFile` で Proved。
* `LeanAssist_info/lean/turtle/TurtleO46_template.lean`: O4 (成長) と O6 (厳密漸化式) の計算部分の検査器 (素の Lean、O2・O1 テンプレートの後ろに連結)。`o1Data` の N(π,B) から N(π,m+1) = Σ_子 N(子,m) で長さを層ごとに再計算し (id の `BTree`)、各根について自己再生 (O4)、偶奇類の 2 レベル恒等式 N(m+2) = M N(m)、閉じた漸化式 N(m+2) = a N(m) + b を dim M + 3 ステップ検査する (`checkO46 cert o1Data o6Data`)。
* `LeanAssist_info/lean/turtle/TurtleO5_template.lean`: O5 (補題 2 の出口性質のうち証明書側の条件 (i)–(iii)) の検査器 (素の Lean、O2 テンプレートの後ろに連結)。最後の子の出口ポートの affine 形、子三角形の辺 UW で (i) y が開線分 φ^{n₀}U—φ^{n₀}W 上、(ii) 置いた辺が親の辺の上、(iii) 両端から (1.903 + |c|)/sin 36° + 0.05 以上離れることを検査する (`checkO5 cert sn sd ws`)。内積は 4·Re(u v̄) = A + B√5 の整数対、符号は A² と 5B² の比較。平方根の代わりに Mathematica の有理数の証人 (sin 36° の下界 sn/sd、各 pass の |c| の上界) を Lean が検査する。
* `LeanAssist_info/lean/turtle/CayleyHamiltonRecurrence.lean`: O6 の論理部分 (Mathlib)。`Matrix.aeval_self_charpoly` により軌道 x(s+1) = M x(s) の線形汎関数は特性多項式の漸化式を満たし (`charpoly_recurrence`)、閉じた漸化式は dim M + 1 ステップ成り立てば全ステップで成り立つ (`affine_of_initial`、論文の dim M + 2 の形 `affine_of_initial'`)。`LeanCheckFile` で Proved。
* `LeanAssist_info/lean/turtle/PassInduction.lean`: H(m) の帰納法 (Mathlib)。型付き超タイル・G_{j,m}・所有の細分・crossing を抽象化した構造体 `PassSystem` 上で、O1・O2 (2 レベル)・O3・長さの漸化式・補題 2 (明示的な仮定) から ∀ m ≥ B, H(m) を導く `PassInduction.H_all`。補題 1 で O2 を全レベルへ持ち上げ、決定性 `distinct`、2 レベル漸化式 `N_two_level`、全仮定を満たす玩具模型 `toy_H` (仮定の両立性) を含む。公理 propext / Quot.sound のみ。
* `LeanAssist_info/lean/turtle/CheckerSoundness.lean`: 検査器の健全性と具体化 (Mathlib、単独ではコンパイルしない: import を先頭に集め、O2・O1・O46 テンプレート、`PassInduction.lean`、`CayleyHamiltonRecurrence.lean` の後ろに連結)。証明書から具体的な `PassSystem` (`TurtleSound.turtleSystem cert prog o1Data`: Z[ζ] 座標 ℤ⁴・置換 σ・正の三角形の所有菱形・等長写像 ρ^k x + t・タートルの一歩) を作り、局所性 `next_sub` 以外のフィールドを証明 (`next_sub` は公理 `TurtleGeom.edgeUnique`: 標準超タイルの所有菱形は有向辺を共有しない)。`decide` した Bool から H(m) の仮定と O4/O6 の命題へ (`BTree.ofList_sound`・`checkO3_sound`・`model_O2`・`model_H_base`・`checkO46_sound`・`model_H_all`)、定理 U(1) (`period_gt`: 出口で終わる N 個の区間の入口の軌道は N 以内で繰り返さない、`model_growth`・`root_recurrence_all`・`unbounded`)。テンプレートが暗黙にしていた前提 (標準フレーム・偶奇 0/1・O1 の入口 port がキーの範囲内) は `checkSide` で decide する。
* `LeanAssist_info/lean/turtle/unbounded_SSSR_verified.lean`: `LeanTurtleUnbounded` が書く完全なソース (上記 + データ + 検査 4 本 + 補題 2 の公理 + 最終定理 `TurtleUnbounded.cert2_SSSR_1p_1`)。`LeanCheckFile` で Proved、約 60 s、公理は propext / Classical.choice / Quot.sound / `TurtleGeom.edgeUnique` / `TurtleGeom.exitProperty_cert2_SSSR_1p_1`。
* `LeanAssist_info/examples/turtle_port_identities.wl`: 証明書 JSON → Lean データ → `decide +kernel` (`LeanTurtlePortIdentities[certFile]` が O2/O3/frames、`LeanTurtleBaseSimulation[certFile]` が O1、`LeanTurtleRecurrence[certFile]` が O4/O6 (結果の `res["Theorem"]["Recurrence"]` に根ごとの N 列・a・b・O4 の重複度)、`LeanTurtleExitProperty[certFile]` が O5 (結果の `res["Theorem"]["Witnesses"]` に各 pass の c・|c|・有理上界、`res["Theorem"]["Surplus"]` に数値の余裕; 反例は `"Perturb" -> {"c", passId}` / `{"sin"}`)。いずれも `"Perturb"` で反例テスト、`"Method" -> "decide" | "native_decide"`)。`LeanTurtleUnbounded[certFile]` は定理 U(1) を 1 本の定理にしたソース (`LeanTurtleSoundnessSource[]` + データ + 最終定理) を Mathlib で `LeanCheck` する (`"Perturb" -> {"a" | "b" | "N0", rootId, d}` / `{"N", passId, d}`、`"SaveSource" -> True` で `unbounded_<prog>_verified.lean` に保存、結果の `"FinalTheorems"`・`"Recurrence"`)。
* `LeanAssist_info/lean/turtle/TurtleBounded_template.lean`: 有界性の証明 (定理 3/4) の計算部分の検査器 (素の Lean、O2・O1 テンプレートの後ろに連結、`namespace TurtleBounded`)。Step 1 `checkAtlas atlas`: 各エントリ (中心の枠で書いた印付き三角形コロナ) が中心のコロナであること (3 頂点で角の和 10 単位 = 360°、全三角形が中心に触れる)、エントリ同士が非同値、中心の子 t′ ⊂ σ(t_C) のコロナが σ(C) の中で完全かつ正準形 (中心の枠で三角形を Nat に詰めて整列) がアトラスにあること。Step 2 `checkCorona prog n C cert` / `checkBounded prog n atlas certs periods`: 証明書 (使う細三角形の番地を昇順、菱形 = 正の三角形と鏡像の対、軌道ごとの代表状態と周期、航行表と軌道の状態をキーの昇順で) から σⁿ(C) の菱形を再計算し、全軌道を走らせて周期 p ちょうどで閉じること (証明書の菱形から出たら偽)、軌道の状態と主張を (軌道, サイクル) で 1 対 1 に照合、σⁿ(t_C) を自分で列挙して全始点が軌道上にあること、周期の集合を検査する。探索木は証明書の順序を狭義単調の確認だけで受け取り一度で組む (kernel での整列を避ける)、引く関数は再帰子と `Nat.ble`/`Nat.beq` (`tfind`、`@[csimp]` の双子)。データは 256 個ずつ大きな Nat (16 進リテラル、桁幅はチャンクの最大ビット長) に詰める (`unpack`; 数千要素のリストリテラルはコンパイルが遅い)。
* `LeanAssist_info/lean/turtle/turtle_atlas_closed.lean` / `bounded_SSR_n7_verified.lean`: `LeanTurtleAtlasClosure` / `LeanTurtleBoundedRun` が書く完全なソース (アトラス閉包 `decide +kernel`、V(SSR, 7) とアトラス閉包 `native_decide`)。
* `LeanAssist_info/examples/turtle_bounded.wl`: `tbAtlas[]` (σ⁸(sun) の 30 コロナ)、`tbBoundedData[prog, n]` (証明書、始点数・軌道数・周期・スペクトル)、`LeanTurtleAtlasClosure[]` (`"Perturb" -> {"Drop", i}` / `{"Shift", i, j}`)、`LeanTurtleBoundedRun[prog, n]` (`"Method" -> "native_decide"` (既定) | `"decide"` (kernel、コロナごとの定理を順に検査して同じ命題に組む)、`"Coronas" -> {i, …}` で一部のコロナ、`"Perturb" -> {"Period", c, o, d}` / `{"DropOrbit", c, o}` / `{"Address", c, k, d}` / `{"Periods", p}`)、`tbBoundedTheorem[prog, n, opts]` (Lean を走らせずに定理を作る)。
* `LeanAssist_info/examples/LeanAssist_examples.nb`: 使い方のノートブック。
* `LeanAssist_info/design/lean_turtle_feasibility.md`: turtle_boundedness の証明へ Lean を適用する考察。
* `test codes/LeanAssist_test.wl`: テスト (Lean 無しのグループ 1–4、Lean のグループ 5–6; タートル証明書の O1/O2/O4/O6 と補題 1・Cayley–Hamilton・H(m) の帰納法、それぞれの反例; グループ 7 は有界性の証明のアトラス閉包と V(SSR, 7) (native と kernel 1 コロナ) と反例)。
