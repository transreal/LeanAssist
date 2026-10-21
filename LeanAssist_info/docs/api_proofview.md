# LeanAssist API: 証明の過程の可視化

パッケージ: `LeanAssist`
本体の API は `api.md`。ここは `LeanProofTrace` / `LeanProofView` と各 Report の `"ProofView"` オプション。

### LeanProofTrace[thm, opts] → LeanProofTrace[assoc]
LeanTheorem (またはそのリスト、`LeanProve` の結果) の証明を、**各 tactic の直前と最後に `trace_state` を差し込んで** `lean --json` でコンパイルし、各時点のゴールを読み取る。差し込みは Lean の段組みに従う: ブロックの列にある行が新しい tactic、深い行は続き、行末の `by` と箇条書き `·` は入れ子のブロックを開く (`=>` の後ろ、`conv` などは入らない)。各 `trace_state` には `-- ⟦LA k⟧` の印を付けて行番号で対応づける (テキスト出力の info は位置が付かず順序も崩れるため)。`linear_combination e` は `linear_combination (norm := skip) e` と `ring1` に分けて追うので、**Lean が実際に確かめる恒等式 `goal − (Σ cᵢ·hᵢ) = 0` がゴールとして見える**。元の証明と同じ定理を証明する (状態と公理は同じ) が、表示用のコンパイルなので `LeanProve` の結果とは別にもう 1 回走る。証明が失敗していれば、止まった tactic (`"Effect" -> "error"`) と閉じなかったゴールが分かる。

| プロパティ | 内容 |
|---|---|
| `"Steps"` | tactic ごとの `<\|"Step", "Theorem", "Tactic", "Before", "After", "Effect", "New", "Closed", "Errors", "Synthetic", "Note", "Line", …\|>`。ゴールは `<\|"case", "context" -> {<\|"name", "type"\|>…}, "target"\|>` (LeanLink の `LeanGoal` と同じ形) |
| `"ProofDataset"` | 手順の Dataset (tactic、効果、前後のゴール数、対象ゴール) |
| `"GoalGraph"` | ゴール木: ゴールが頂点、tactic が辺 (作用したゴール → 生まれたゴール)、閉じたゴールは ✓ の葉、最後に残ったゴールは赤。頂点のツールチップにゴール全体 |
| `"Stepper"` | 1 手ずつの表示 (前のゴール → 後のゴール、Lean のエラー) |
| `"States"` | 各手の前後の状態。Wolfram/LeanLink がロード済みなら LeanLink の `LeanState` / `LeanGoal` オブジェクト (`"StateDisplay" -> "LeanAssist"` で LeanAssist の同じ体裁)。LeanLink を自分ではロードしない |
| `"ProofLength"`, `"Status"`, `"Result"` (JSON 形式の `LeanCheckResult`), `"Source"` (差し込み後), `"Theorem"`, `"Final"` (最後に残ったゴール) | |

オプション: `"ExpandLinearCombination" -> True`, `"StateDisplay" -> Automatic | "LeanAssist"`, `LeanCheck` のもの。

### LeanProofView[thm, view, opts]
証明の過程をタブで見せる (`view` を省略すると使えるもの全部、文字列で 1 つ)。

| view | 対象 | 内容 |
|---|---|---|
| `"Steps"` | 幾何 | 座標の置き方 → 構成点 (中点・直線上の点は代入で、方程式は要らない) → 仮説 hᵢ (図の上で該当する直線・直角・円を強調、多項式、この例での値、証明書での係数 / 不使用) → 非退化条件 (順序条件で証明したものは、使った条件の出どころを図で強調し d·r の式を示す) → 結論 g → 証明書と Lean、を 1 手ずつ |
| `"ProofGraph"` | 証明書 | 導出グラフ (`ProofObject["ProofGraph"]` の配色: 場面の仮定 = Axiom の緑、多項式の仮説・非退化条件 = Hypothesis の黄緑、d·g = 0・g = 0・結論 = 橙、ring 恒等式 = 青、使われない仮説は灰色)。辺は ×cᵢ・mul_eq_zero・cancel。順序条件で証明した非退化因子は橙で、場面の仮定 → hord_k → hnd_j (sign) の辺が付く。下に hᵢ・出どころ・係数の表 |
| `"Identity"` | 証明書 | d·g = Σ cᵢ·hᵢ を因数分解した形で、`Expand[d g − Σ cᵢ hᵢ] = 0` の確認、三角消去で求めたときは擬除算の手順 (消去した変数・使った仮説・主係数 = 非退化条件・余りの項数)、順序条件で証明した非退化因子の d·r = c + Σ λ q + Σ μ m² > 0 |
| `"Cancellation"` | 証明書 | d·g と −cᵢ·hᵢ の単項式ごとの係数表 (各列の和が 0 = `ring1` が確かめること)。大きいときは符号付き対数のマップ。トレースがあれば Lean の `(norm := skip)` 後のゴールも |
| `"Deform"` | 証明書 | 幾何: 自由な点と直線上の点をドラッグすると仮説の残差 hᵢ と結論の残差 g が変わり、どの位置でも d·g = Σ cᵢ·hᵢ が成り立つ様子 (「project onto the hypotheses」で構成点を仮説へ戻すと g = 0)。描画は System の関数だけの純関数を埋め込むので、パッケージを読まないカーネルでも動く。多項式の定理: 変数のスライダー |
| `"Goals"`, `"GoalGraph"`, `"Tactics"` | 全部 | `LeanProofTrace` の `"Stepper"`, `"GoalGraph"`, `"ProofDataset"` |

オプション: `"Trace" -> Automatic` (Lean のタブがあれば `LeanProofTrace` を 1 回走らせる) | `False` (Lean を呼ばない) | 既存の `LeanProofTrace`、および `LeanProofTrace` のもの。`LeanProofView[res]` (`LeanProve` の結果) と `LeanProofView[trace]` も可。`LeanGeometryReport` / `LeanGraphReport` / `LeanLogicReport` は `"ProofView" -> True` でこれを下に付ける。

図の数値例: 数値検査の例の非退化条件が図の大きさに比べて小さい (RandomInstance は細い三角形を出しやすく、メネラウスでは共線条件をほぼ潰れた三角形で満たす) ときは、自由な座標を乱数で選び直して構成で決まる変数を射影する。

```mathematica
npc = GeometricScene[{a, b, c, ma, mb, mc, fa, h, mah}, {Triangle[{a, b, c}],
   ma == Midpoint[{b, c}], mb == Midpoint[{c, a}], mc == Midpoint[{a, b}],
   fa \[Element] Line[{b, c}], GeometricAssertion[{Line[{a, fa}], Line[{b, c}]}, "Perpendicular"],
   h == TriangleCenter[{a, b, c}, "Orthocenter"], mah == Midpoint[{a, h}]}];
thm = LeanGeometryTheorem[npc, GeometricAssertion[{ma, mb, mc, mah}, "Concyclic"]];
LeanProofView[thm]                    (* Steps / ProofGraph / Identity / Cancellation / Deform / Goals / GoalGraph / Tactics *)
LeanProofView[thm, "Cancellation", "Trace" -> False]
tr = LeanProofTrace[thm]; tr["ProofDataset"]
LeanGeometryReport[npc, GeometricAssertion[{ma, mb, mc, mah}, "Concyclic"], "ProofView" -> True]
```

LeanLink について: LeanLink のネイティブな `LeanState[env, name]` + `LeanTactic` でも 1 手ずつ進められるが、v1.0.9 (Windows で修正済みのシム) では定理の束縛子が `∀` のまま開かれ (`intro` が要る)、`⟨?_, ?_⟩` を含む tactic や `simp` は `$Failed` になり、Mathlib の環境も扱えない。そのため状態は Lean 本体の `trace_state` から取り、LeanLink はその状態を `LeanState` / `LeanGoal` として渡す側で使う。
