# LeanAssist

Wolfram Language から Lean 4 を「検算器」として使うためのパッケージです。Mathematica が図を描き、証明書 (多項式恒等式の係数、有限データ) を計算し、Lean がそれを検証します。[Wolfram/LeanLink](https://resources.wolframcloud.com/PacletRepository/resources/Wolfram/LeanLink/) の上に、LeanLink に無い層 — コンパイル診断の構造化、`sorry` と依存公理の検出、Groebner 基底による `linear_combination` 証明書、`GeometricScene` の仮定・結論の座標多項式への翻訳、WL データの Lean 定義化 — を足します。

## 設計思想と実装の概要

### 役割分担

* **Mathematica**: 可視化 (`GeometricScene` / `RandomInstance`)、予想の探索 (`FindGeometricConjectures`)、証明書の計算 (`GroebnerBasis`)、データの生成。
* **Lean**: 証明の検証。多項式恒等式は `linear_combination` + `ring` (Mathlib)、有限データの性質は `decide` (素の Lean、カーネル検証) で確認する。
* **LeanAssist**: 両者の間の変換と、結果の構造化。「Proved」はコンパイルエラーが無く、`#print axioms` に `sorryAx` が出ないことを意味します。

### パイプライン (幾何の定理の場合)

```
GeometricScene[{a, b, c, ...}, {Triangle[{a,b,c}], d ∈ Line[{b,c}], ..., CollinearPoints[{d,e,f}]}]
   ↓ LeanGeometryPolynomials      座標 (第 1 点を原点、第 2 点を x 軸上)、直線上の点は a + t(b − a) に置換
仮定の多項式 h_i = 0、非退化条件 (三角形の符号付き面積 ≠ 0 など)
   ↓ LeanGeometryStatement        結論 (SignedRatio の積 = −1 など) → 分子多項式 g = 0
   ↓ LeanPolynomialCertificate    d·g = Σ c_i h_i を Groebner 基底 (タグ変数) で求める
   ↓ LeanPolynomialTheorem        theorem menelaus (xb xc yc td te tf : ℝ) (h1 : ... = 0) (hnd1 : xb*yc ≠ 0) : ... = 0 := by
                                     have hprod : xb*yc * (...) = 0 := by linear_combination (-1) * h1
                                     exact (mul_eq_zero.mp hprod).resolve_left hnd1
   ↓ LeanProve                    lake env lean (Mathlib プロジェクト)  →  LeanCheckResult (Proved / 公理 / 診断)
```

RandomInstance の点を仮定多様体へ射影した数値検査も同時に行い、翻訳の取り違えを検出します。`FindGeometricConjectures` が見つけた予想は `LeanGeometryConjectures` で一括して Lean に通せます。証明書は Groebner 基底によるイデアル所属判定を基本とし、垂線の足や交点のような構成点を含む定理 (シムソン線、パップス、デザルグ、九点円) では、構成パラメータについて 1 次の仮定で順に擬除算する三角消去が非退化条件 (線分が退化しない、直線が平行でない) を主係数として自動的に取り出します。

### 有限証明書の検証 (CA・タートルの証明への応用)

`LeanDataDefinitions` または構造体リテラルで WL のデータを Lean の `def` にし、検査器 (Lean の計算可能関数) に `decide +kernel` を適用します。付属の `TurtleO2_template.lean` は、ペンローズ菱形タイル張り上のタートル・プログラムの非有界性証明の証明書 (pass-substitution system) について、子フレームと置換 σ の整合、ポートの δ、表の閉包 (O3)、ポート恒等式 (O2) を検査します。`cert2_SSSR_1p_1.json` (60 pass 族、120 port 族) は約 7 秒で、依存公理 `propext` のみで検証できます。証明書を 1 か所壊すと Lean は拒否します (`"Perturb"`)。`TurtleO1_template.lean` は基底レベルのシミュレーション (O1) を同じ流儀で検査し (超タイルの三角形列挙・所有菱形・辺キーの二分探索木・タートル走行を Lean の定義として書き、30 pass 族の exit port と S 移動数を再計算)、`decide +kernel` で約 30 秒。証明の補題 1 (加法群上の漸化式の一意性) は Mathlib の定理 `AffineRecurrence.lean` です。`TurtleO46_template.lean` は成長 (O4) と厳密漸化式 (O6) の計算部分を検査し (cert2_SSSR_1p_1 の根で N(m+2) = 4 N(m) + 66 を 33 ステップ、約 10 秒)、`CayleyHamiltonRecurrence.lean` (Mathlib) がその論理部分を、`PassInduction.lean` (Mathlib) が H(m) の帰納法を抽象構造の上で (補題 2 を明示的な仮定として) 証明します。`CheckerSoundness.lean` (Mathlib) はこの抽象構造を具体的なペンローズ置換 (Z[ζ] 座標・所有菱形・タートルの一歩) で実装し、検査器の Bool から帰納法の仮定を導いて、定理 U(1) を 1 本の Lean 定理にします (`LeanTurtleUnbounded`、cert2_SSSR_1p_1 で約 65 秒; 依存する幾何の公理は所有菱形の非重なりと補題 2 の 2 つ)。`TurtleO5_template.lean` は補題 2 のうち証明書側の条件 (出口ポートが子の辺の内部にあり、その辺が親の辺の上にあり、両端から十分離れている) を、内積を A + B√5 (A, B は整数) として厳密に検査します。平方根は Lean で計算せず、Mathematica が出す有理数の証人 (sin 36° の下界、|c| の上界) を Lean が確かめます。これで証明書の有限の義務 O1–O6 はすべて Lean カーネルで検査でき、22 本の証明書の結果は `lean/turtle/*_results.md` にまとめてあります。有界性の証明 (定理 3/4) の計算部分は `TurtleBounded_template.lean` が検査します: σ⁸(sun) の 30 個の印付き三角形コロナからなるアトラスの閉包 (`decide +kernel` 約 8 秒) と、(SSR)* の n = 7 の網羅検査 V(P, n) (54,240 始点がすべて σ⁷(C) の中で閉じ、周期は {10, 12, 28, 30, 50, 80, 100}; `native_decide` 約 16 秒)。証明書 (使う菱形の番地、軌道の代表と周期、探索木の順序) は Mathematica が出し、Lean は菱形を置換から再計算して全軌道を走らせ、始点を自分で列挙して照合します。タートルの証明書 JSON (22 本) は公開リポジトリ [transreal/pt_turtle](https://github.com/transreal/pt_turtle) の `results/unbounded_certs/` にあります (例では clone した先を `$ptTurtle` とします)。

### LeanLink との関係

LeanLink の `LeanImportString` はネイティブシム経由で速く、式グラフや tactic 状態の可視化に向きますが、コンパイルエラーの本文を返さず、`sorry` を含む定理も成功として返します。LeanAssist は `lean` / `lake env lean` を直接呼んで stdout を解析し、`#print axioms` を必ず確認します。LeanLink の機能を使いたいときは `LeanLinkImport[thm]` で同じソースを渡せます。

## 詳細説明

### 動作環境

* Wolfram Mathematica 14.0 以上 (15.0 で検証)、Windows 11 (パス区切りを読み替えれば他 OS でも動くはず)
* Lean 4 (elan)。既定の toolchain は `leanprover/lean4:v4.30.0` (LeanLink 1.0.9 のシムと同じ版)
* Mathlib: `~/src/mathlib4` に Lake プロジェクトがあり、Mathlib がビルド済み (`lake exe cache get`)。`import Mathlib.Data.Real.Basic` 程度のコンパイルが約 10 秒
* 任意: Wolfram/LeanLink 1.0.9 (Windows ではネイティブシムの再ビルドと `lean-toolchain` の v4.30.0 固定が必要な場合があります)

### インストール

`LeanAssist.wl` と `LeanAssist_info/` を `$packageDirectory` に置きます。

```mathematica
Block[{$CharacterEncoding = "UTF-8"},
  Get[FileNameJoin[{$packageDirectory, "LeanAssist.wl"}]]];
LeanAssistStatus[]
```

### 最小例

```mathematica
res = LeanCheck["theorem t (n : Nat) : n + 0 = n := by sorry"];
res["Status"]      (* "Sorry" *)
res["Axioms"]      (* <|"t" -> {"sorryAx"}|> *)

thm = LeanTheorem["am_gm_two", {x, y}, {}, x^2 + y^2 >= 2 x y, "Proof" -> "nlinarith [sq_nonneg (x - y)]"];
LeanSource[thm]
LeanProve[thm]["Status"]   (* "Proved" *)
```

### メネラウスの定理

```mathematica
men = GeometricScene[{a, b, c, d, e, f}, {Triangle[{a, b, c}],
   d \[Element] Line[{b, c}], e \[Element] Line[{c, a}], f \[Element] Line[{a, b}], CollinearPoints[{d, e, f}]}];
RandomInstance[men]
thm = LeanGeometryTheorem[men, SignedRatio[b, d, c] SignedRatio[c, e, a] SignedRatio[a, f, b] == -1, "Name" -> "menelaus"];
LeanSource[thm]
LeanProve[thm]
LeanGeometryReport[men, SignedRatio[b, d, c] SignedRatio[c, e, a] SignedRatio[a, f, b] == -1]
```

他の例 (チェバ、ヴァリニョン、タレス、オイラー線、BlockingNimCA の保存則、タートル証明書) は `LeanAssist_info/examples/LeanAssist_examples.nb` と `docs/example.md` にあります。

### 制約

* 多項式の証明書は「仮定のイデアル (+ 非退化因子)」の範囲で成り立つ結論にだけ見つかります。順序 (距離の和の等式、角の向き、凸性) を要する主張は `Caveats` に記録し、証明書が無ければ `sorry` 付きの定理を返します。
* 角の等式は cos² の条件 (角またはその補角)、面積は符号付き面積として翻訳します。
* Mathlib のコンパイルは 1 回 10 秒程度 (olean の読み込み)。複数の定理は `LeanProve[{thm1, thm2}]` で 1 ファイルにまとめると速い。
* `native_decide` を使った定理は公理 `Lean.ofReduceBool` に依存します (結果の `"Axioms"` に出ます)。

## ライセンス

MIT License — Copyright (c) 2026 Katsunobu Imai
