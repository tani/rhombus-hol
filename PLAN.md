# Rhombus/HOL — 実装リファレンス

R1〜R5 完了。`raco test rhombus-hol/rhombus/hol/tests` → 1123 tests passed。
§10 に外部レビュー対応の状況をまとめてある。

---

## 0. 再開手順

```sh
export PATH="/Applications/Racket v9.3/bin:$PATH"
cd /path/to/rhombus-hol

# 初回のみ
raco pkg install --batch --auto --link rhombus-hol-kernel/ rhombus-hol-lib/ rhombus-hol/

# 通常のループ
raco make rhombus-hol-lib/rhombus/hol.rkt          # 言語がコンパイルされるか
raco test rhombus-hol/rhombus/hol/tests             # 全テスト
raco test rhombus-hol/rhombus/hol/tests/kernel.rhm  # 単体
```

`raco make` は `raco test` とは別に CI に入れること。証明は展開時に走るので、
**証明の失敗はテストの失敗ではなくコンパイルの失敗として現れる。**

### Rhombus / shrubbery のよくある落とし穴

| 症状 | 原因と対処 |
|---|---|
| `wrong indentation (or missing ':' on previous line)` | shrubbery は**括弧の中でしか行継続できない**。`check X` の次行に `~is Y` を書くと落ちる → `check:` ブロック形式にする。`let (a, b) =` の次行に式を置くのも不可 → `let (a, b):` ブロック形式か 1 行に。 |
| `match: expected ~else clause` | `match`/`cond` の枝の中に**インラインの `if a \| b \| c`** を書くと `\|` が枝の区切りと解釈される → 括弧で囲む `(if a \| b \| c)`。 |
| `empty block not allowed after ':'` | `cond \| for all (...): expr:` のように `for` の本体ブロックの直後に `:` が来ている → `cond \| (for all (...): expr):` と括弧で囲む。 |
| `misplaced comma` / `expected closer` | `#'x'` は `#'x` + 開き引用。プライム付き識別子は書けない（→ `variant` が `_1` 接尾辞を使う理由）。`export: A, B` も不可 → ブロック形式。 |
| `no such field or method` | `List.index_of` は無い（`contains` / `index`）、`.join` は無い（`String.join`）、`zip` は無い（`for (x in xs, y in ys)` の並列反復）、`filter` はキーワード引数（`~keep:` / `~skip:`）。 |
| `not bound as an annotation` | 注釈は展開時に解決されるので、**クラス定義より後に**それを使う関数を置く。値の相互再帰は問題ない。 |
| `~is` 節で束縛が見えない | `check:` ブロックの `let` は `~is` 側から見えない。定数はブロックの外に出す。 |
| `not bound as a reducer` | `let all = ...` が `for all` の `all` を隠す。ローカル名を変える。 |
| マクロが返した構文で `def: unbound identifier` | phase-0 モジュールで作った構文リテラルは、`meta:` import 越しにマクロ出力として使うと束縛を失う。テンプレートはマクロモジュール（`#lang rhombus/and_meta`）に置くこと。 |
| エラーにファイル・行が出ない | `raise-syntax-error` に渡す構文が**グループ**だとテンプレート側の位置になる。宣言の**先頭の項**（`head_term`）を渡す。 |
| `type: type: ...` と who が二重になる | 捕まえた例外のメッセージは既に `who: ` 前置を持つ。`strip_who` で剥がす。 |
| `$alias.field` がマクロ実行時に評価される | `$` が `alias.field` 全体を取る。`$(alias).field` と括る。 |
| `fun (...): ...` を引数やリスト要素に置くと構文エラー | ブロックが後続を飲む。`(fun (...): ...)` と括る。 |
| `Syntax.make_id` が `maybe(Term)` で落ちる | コンテキストは**項**でなければならない。グループは渡せない。 |
| テンプレート内に `#'sym` が書けない | `'` がテンプレートを閉じる。文字列を使うか、識別子を渡して受け側で `Syntax.unwrap` する。 |
| 生成した名前を別モジュールから参照したい | 衛生的な名前は import 越しに見えない。ユーザーの宣言の構文をコンテキストにして `Syntax.make_id` し、`export:` も生成する。 |

---

## 1. 現在の構成

```
rhombus-hol/
├── PLAN.md                       ← このファイル
├── rhombus-hol-kernel/            LCF カーネル（信頼境界①）。deps: base, rhombus-lib 1.1
│   ├── info.rkt
│   └── rhombus/hol/private/
│       ├── names.rhm             論理定数の正準名（eq/imp/conj/…）
│       ├── htype.rhm             型：TyVar / TyApp、subst・match・unify・order
│       ├── term.rhm              項：locally nameless（下記 §2）
│       ├── printer.rhm           De Bruijn → 名前付き逆変換（kernel.rhm がエラー整形に使うため同居）
│       └── kernel.rhm            十の基本推論規則、Thm/Theory の唯一の発行元
├── rhombus-hol-lib/              派生層 + 言語面（deps: base, rhombus-lib 1.1, rhombus-hol-kernel）
│   ├── info.rkt
│   └── rhombus/
│       ├── hol.rkt               #lang rhombus。言語本体 + reader サブモジュール
│       ├── hol.rhm               #lang rhombus/lang_bridge → "hol.rkt"
│       └── hol/private/
│           ├── bool.rhm          論理定数の定義 + 3 公理 + base_theory()
│           ├── conv.rhm          変換（equal.ml 相当）
│           ├── drule.rhm         派生規則（bool.ml + drule.ml 相当）
│           ├── datatype.rhm      データ型の公理（信頼境界②）
│           ├── algebra.rhm         `unit`/`prod`/`sum` の導出（datatype 公理の代替、フェーズ1土台完成、§9.2.1）
│           ├── datatype_derived.rhm  enum 限定の `DatatypeSpec -> DatatypeThms`（axiom-free、§9.2.1）
│           ├── datatype_gen.rhm   enum を一般化: 任意の非再帰 `DatatypeSpec`（フィールド付き）の `DatatypeThms` 全 7 フィールド（axiom-free、§9.2.1）
│           ├── wellfounded.rhm  `WF` <-> 整礎帰納法（recdef 導出化の第一段、§9.1.1）
│           ├── wfrec.rhm        `WFREC` 存在定理（recdef 導出化の第二段、`recdef.rhm` へは未配線、§9.1.2）
│           └── module_block.rhm  #%module_block 差し替え
└── rhombus-hol/                  ドキュメント + テスト（deps: rhombus-hol-lib, rhombus-hol-kernel）
    ├── info.rkt
    └── rhombus/hol/
        ├── info.rkt, scribblings/（6 章、§8 参照）
        └── tests/                各モジュールに 1 対 1 対応するテスト一式
```

`rhombus-hol-kernel/` のファイルは他パッケージの `private/` 内ファイルから、
相対パスの文字列 (`"kernel.rhm"`) ではなく `rhombus/hol/private/kernel open`
のようなコレクション相対のむき出しパスで参照する。同じコレクション
`rhombus/hol/private/` に複数パッケージが合流する（`collection 'multi`）ため、
ファイル名が衝突しない限り問題なく解決される。

境界に何を入れるかは「信頼境界そのもの」と「ビルド上の依存」の 2 つの基準がある。
`printer.rhm` は trust.scrbl の「十の基本推論規則」ではないが、`kernel.rhm` が
実際に import しているので、`rhombus-hol-lib` 側に置くと循環になり置けない。
逆に `order.rhm` は `kernel.rhm` からもどのカーネルファイルからも参照されておらず、
使うのは派生層の `ruledb.rhm` だけなので `rhombus-hol-lib` 側に置く。

### 位相（phase）の設計 — 最重要

証明は**展開時**に走るのでカーネルは phase 1 で動く。しかしカーネル自体は
`meta:` ブロックを一切含まない**通常の `#lang rhombus/static` モジュール**である。
言語層（`hol.rkt` と `decl_*.rhm` 相当のコード）だけが
`import: meta: rhombus/hol/private/kernel open` で位相を 1 ずらして取り込む。

このおかげで:
1. カーネルのテストが素の phase 0 の `.rhm` で書ける（`raco test` がそのまま効く）
2. カーネルが `.zo` に完全コンパイルされる — コンパイル時証明の速度の最大のレバー
3. `import: rhombus/hol/kernel` で phase 0 から証明をスクリプトできる

**この分離を壊さないこと。** 証明器のロジックを `meta:` ブロックの中に書くと (2) が消える。

---

## 2. 項の表現（locally nameless）

```rhombus
class FVar(name :: Symbol, ty :: HType)     // 自由変数：名前を持つ
class BVar(index :: NonnegInt, ty :: HType) // 束縛変数：直近の Abs からの相対位置
class Const(name :: Symbol, ty :: HType)
class Comb(func :: Term, arg :: Term)
class Abs(arg_ty :: HType, body :: Term)    // 束縛変数名を持たない
```

**新しいコードを書くときの前提:**

- α 同値は**構造的等価そのもの**。`aconv` は存在しない。`==` を使う。
- 置換に捕獲回避は不要。`inst_fvar` は単なる再帰走査。
- `mk_abs(v :: FVar, body)` = `Abs(v.ty, abstract_fvar(v, body))`。
  `dest_abs(t)` は**新しい自由変数で開く**（`x, y, z, u, v, w, x1…` の順で
  本体に自由な名前を避ける。printer と同じ方針なので、残余項に現れる名前と
  `SPEC_ALL` が実際に作る名前が一致する）。
- 局所閉性（loose な `BVar` が無いこと）が well-formedness の一部。
  `is_locally_closed` があり、`check_term` が検査する。
- `BETA` は**任意の redex**に対する 1 ステップ簡約（捕獲が起きないため）。
- `ABS(thy, v, th)` は理論を取る（束縛変数の型を検査するため）。
- **局所閉性だけでなく、`BVar` の型が束縛子と一致することも `check_term` が検査する。**
  `BVar` は型フィールドを持つので、外側の `Abs` と食い違うと `type_of` が嘘をつく。
  `check_open_term` は束縛子の型スタック `env :: List.of(HType)` を引き回して
  `env[i] == ty` を照合する。
- **系統（lineage）は祖先集合で追跡する。** 線形カウンタでは
  イミュータブル理論の分岐を区別できず、矛盾が導ける
  （同一ベースの兄弟拡張で同名同型の定数を別々に定義すると
  `|- c = zero` と `|- c = one` が合成できて `|- zero = one`）。
  ```rhombus
  class Stamp(id :: Symbol, gen :: Int, ancestors :: Set.of(Symbol))
  ```
  `descends(a, b)` = `a.id in b.ancestors`。`gen` は**エラーメッセージ専用**で
  何の判定にも使わない。2 定理を合成する規則（`TRANS` / `MK_COMB` / `EQ_MP` /
  `DEDUCT_ANTISYM_RULE`）は `combine_stamps` を通し、どちらも他方の祖先でなければ
  **エラー**、そうでなければ後の方を採る。
- **理論を引数に取る規則は、結果を「その理論」で刻印する。**
  `INST` / `INST_TYPE` / `ABS` は `th.stamp` ではなく `thy.stamp` を使う。
  代入項は `thy` に対して検査されるので、`th` が証明された古い理論には
  存在しない定数を含みうる。
- **1 回の拡張は 1 ノード。** `new_axiom` / `new_basic_definition` /
  `new_basic_type_definition` は先にスタンプを鋳造してから理論と定理を組み立てる。
  `extend` を 2 回呼ぶと定理が理論より 1 世代古くなり、帰属が食い違う。
- `INST` の代入対象は `FVar` でなければならない（`Const` などを渡すと黙って
  何も起きず、呼び出し側のバグが隠れる）。
- `INST` / `INST_TYPE` は仮説を `.map` した後に必ず `rehash_hyps` で
  再ソート・重複排除する（代入は仮説を併合も並べ替えもするため）。

### カーネルの不変条件（触るときはここを読む）

| 不変条件 | 強制場所 | 破ると |
|---|---|---|
| 定数は宣言済みで、総称型のインスタンスとして使われる | `check_open_term` | 未宣言定数が定理に入る |
| `BVar(i, ty)` は `i` 番目の束縛子を指し、その型は `ty` | `check_open_term` の `env` | `type_of` が嘘をつき subject reduction が壊れる |
| loose な `BVar` は存在しない | 同上（`i >= env.length()`） | 意味を持たない項についての定理 |
| 仮説リストは `term_ord` 順・重複なし | `hyp_insert` / `rehash_hyps` | `==` が実在しない差異を報告する |
| 定理は自分の理論かその拡張でのみ使える | `in_theory` / `combine_stamps` | 分岐した理論の合成で矛盾 |
| `Thm` はカーネル外で構築できない | `constructor ~none` + 非公開 `internal` | すべてが終わる |

回帰テストは `tests/kernel.rhm` の "Soundness regressions" 節にある。
**この節のテストを緩めないこと** — それぞれが実際に通った攻撃に対応している。

### 書き換え器を書くときの注意

De Bruijn 表現では**束縛子の下での書き換え**に注意が要る。
書き換え規則の左辺のパターン変数（`FVar`）が、loose な `BVar` を含む部分項に
束縛されてはならない。

**採用している方式:** 束縛子の下に降りるときは `dest_abs` で開く
（`ABS_CONV` が既にこれを行う）。開いてから書き換え、`ABS` で閉じ直す。
マッチ側は常に局所閉な項だけを見るので、`tmatch.rhm` は「局所閉な項どうしの
一階マッチ」だけを実装すればよい。`conv.rhm` の `SUB_CONV` / `DEPTH_CONV` 系は
すべてこの形になっている。

---

## 3. 実装済みの範囲

| 領域 | 主なファイル | テスト |
|---|---|---|
| 言語ペア | `hol.rkt`（`#lang rhombus/hol` が `#lang rhombus` と同一に振る舞う） | `lang_smoke` `lang_meta` `lang_export` |
| 項・型の表現 | `htype` `term`（locally nameless）`order` `printer` `names` | `htype` `term` `order` `printer` |
| カーネル | `Theory` `Stamp`（祖先集合）不可侵 `Thm`、基本 10 規則、理論拡張原理 | `kernel` |
| 論理定数 | `bool`（Church 流定数 + ETA/SELECT/BOOL_CASES）`conv` `drule` | `bool` `conv` `drule` |
| データ型 | `datatype`：正値性チェッカ + 公理スキーマ | `datatype` `positivity` |
| 非公理的型構成子 | `algebra`：`unit`/`prod`/`sum` を `new_basic_type_definition` から導出（フェーズ1土台完成、§9.2.1）。`datatype_derived`：enum（0引数コンストラクタのみ）を `DatatypeThms` まで配線。`datatype_gen`：任意の非再帰 `DatatypeSpec`（フィールド付き）を `DatatypeThms` まで配線 -- いずれも `datatype_axioms` と差分テストで完全一致 | `algebra` `datatype_derived` `datatype_gen` |
| 停止性 | `terminate`（辞書式構造的降下 + 測度）`recdef`（節形式の再帰定義、現状は `new_axiom`）。`wellfounded`：`WF` <-> 整礎帰納法の導出。`wfrec`：`WFREC` 存在定理の完全導出（`recdef.rhm` へは未配線、§9.1.2） | `recdef` `wellfounded` `wfrec` |
| 書き換え | `tmatch` `ruledb` `simp`：一階マッチ、規則 DB（rewrite ルール + type-prescription 事実の二重分類）、順序付き書き換え | `ruledb` |
| 証明探索 | `goal` `induct` `waterfall`（簡約・デストラクタ除去・フェルティライズ・一般化・irrelevance 除去・帰納法の固定パイプライン、ACL2 準拠） | `spec_4_1` |
| 一般化・デストラクタ除去・フェルティライズ・irrelevance 除去 | `general`（type-prescription 事実を一般化に反映）`destruct` `fertilize` `irrelevance` | `spec_4_2` `destruct` `fertilize` `irrelevance` |
| 表層構文 | `expand` `elab` `driver` `taut` `module_block` | `lang_state` `decl_type` `decl_fun` `decl_theorem` |
| モジュール間の理論伝播 | 通常の `import` が理論を採用する（`Evaluator.module_is_declared` で検出） | `import_theory` |
| プロパティテスト | `check_property`（実マクロ）+ `qc.rhm` の実行時レジストリ + 型ごとの生成器・縮小器 | `qc` |

共有フィクスチャ `tests/spec_prelude.rhm` が `Nat` / `List` / `Tree` と
`plus` `app` `rev` `length` `size` `flatten` を組み立てる。仕様書 §4.1〜§4.3 は
`tests/spec/` の 3 ファイル（`list_proofs.rhm` `tree_proofs.rhm` `test_run.rhm`）に
そのまま対応する。

### 現在の設計上の要点

- **規則のパターン変数は「全称量化されていた変数」だけ**（`ruledb.rhm` の
  `spec_all_vars`）。`free_vars(lhs)` を使うと仮定がスキーマとして扱われ、
  無関係な項にマッチしてしまう。
- **名前ベースのヒント（`~induct: xs`）は項からは解決できない。** 束縛子は名前を
  持たないので、`prove` に `~names:` で表層の名前を渡す。
- **一般化の候補は適用スパイン全体だけ。** 部分項全体を素朴に走査すると
  部分適用まで候補になり、関数型の変数で置き換えて項を壊す。
- **ゴールは節ではなく sequent**（仮定 + 結論）。ドライバは `Step` しか見ないので、
  後から節層を挟める。
- **`max_induction_depth` は 2 に固定**（`waterfall.rhm`）。タクティクごとの
  fuel/timeout は入れない方針 — 帰納法は同じ型の新しい変数を作るので、
  上限がないと永遠に帰納法を試し続ける。
- **フェルティライズは使った等式を子ゴールの仮定から落とす。** `x === f(y)` と
  `y === g(x)` はそれぞれ単独では occurs check を通るが、交互に使うと
  `x` を消しては `y` 経由で復活させ、を無限に繰り返せる。使った等式を
  二度と使えなくする（`fertilize.rhm` 参照）と、この手の循環はどれだけ
  複雑でも「使える等式が尽きる」で必ず止まる。ここで実際に `raco test` が
  ハングする回帰を踏んだ — 新しいステージをパイプラインに足すときは、
  他のステージが作る仮定の**形**まで見て、循環できないか確認すること。
- **`auto(~do_not: [段階名, ...])`** で 1 つの証明だけ特定の段階（`simplify`
  `eliminate` `fertilize` `generalize` `irrelevance` `induct`）を止められる。
  ヒューリスティックが証明の邪魔をするときの逃げ道（ACL2 の `:do-not`）。
  健全性には無関係 — 段階を止めても `Step` が正当化できることの意味は
  変わらず、単に試さなくなるだけなので、悪い指定は残証拠になるだけ。

---

## 4. 現在の制限・既知の課題

- `type` / `function` / `theorem` / `disable_rules` / `enable_rules` / `declare` /
  `expect` は `#%module_block` が本体を走査して認識する形式で、束縛ではない。
  ユーザー定義マクロの中や `block:` の中には書けない。`check_property` だけが
  実マクロとして再実装済みで、この制限を受けない。
- `@doc` ブロックが使えていない（`check_property` 以外）。上記の理由で
  for-label 束縛を要求する `@doc` に載らないため、`@verbatim` の文法表示 +
  `@section` で代用している。
- `function` の本体は `match` / `if` / 変数 / 名前付き適用 / Boolean 演算子と
  `#true` / `#false` のみ。`let` / 算術 / リテラルは文法外でコンパイルエラーになる。
- `match` の入れ子は 1 引数につき 1 段。ワイルドカード節・構築子パターンの入れ子は不可。
- 測度は宣言済みデータ型に着地しなければならない。入れ子再帰には義務を立てられない。
- 構造的降下が成立する定義では `~measure` は検査されない（健全性の問題ではないが、
  誤った測度を書いても黙って通る）。
- 理論の取り込みは通常の `import`。自分の宣言より前に、複数あるなら依存順に書く。
  兄弟理論（どちらも他方の拡張でない 2 つの理論）は合流できない。
- importer のコンパイルは提供側モジュールを visit するので、提供側の証明が
  importer ごとに再実行される（1 モジュールあたり約 1 秒）。
- `check_property` の量化変数は具体型でなければならない。
- **書き換えの停止性は保証されない。** タクティクごとの fuel/timeout は入れない方針。
  置換可能規則は `term_order` で下り方向にしか発火しないので発振しないが、
  `mk_rule` は「変数だけの左辺」「右辺の未束縛変数・型変数」「自明な等式」しか
  弾かない。非対称かつ非停止な規則（`f(x) === g(f(x))` 等）は現状のまま通ってしまい、
  `raco make` が停止しなくなりうる。防ぐなら `mk_rule` の受け入れ条件を強めるべき
  （fuel ではなく）。
- `import` の認識は既知の修飾子リストを持たない（最長接頭辞方式）。読めない形は
  エラーにしてあるが、Rhombus の import 文法が変われば影響を受けうる。

---

## 5. 表層構文の確定事項

| 仕様書 | 採用する綴り | 理由 |
|---|---|---|
| `type List('a)` | `type List(~a)` | `'` は syntax literal の開き括弧で字句解析できない |
| `@rewrite_rule` | `theorem ~rewrite_rule name:` | `@` は at-記法として消え、別グループになる |
| `theorem` + `proof` | `expand.rhm` が本体走査で 1 段先読み | 2 つの別グループとして解析される |
| `auto ~induct: xs ~using: [a]` | 単独なら可。複数指定は `auto(~induct: xs, ~using: [a, b], ~do_not: [induct])` | 2 つ目の `~kw:` が 1 つ目のブロックに入れ子になる |
| `fun app(...)` | `function app(...)` | 通常の Rhombus `fun` と衝突させない |
| `and` / `or` / `not` | 命題専用の構文空間で定義 | 優先順位制御とエラーメッセージのため分離する |

そのまま使えることを確認済み: `a === b`、`p ==> q`、`forall (x :: Ty): P`。

---

## 6. `idris-hol-kernel/` — 独立検証ツール（ランタイムには不接続）

`htype.rhm` / `term.rhm` / `kernel.rhm` を Idris2 に移植し、Racket バックエンド
（`idris2 --cg racket`）でコンパイルしたもの。`kernel.rhm` は 100% ネイティブ
Rhombus のままで、これが今も Rhombus/HOL が実際に走らせる信頼境界である。
`raco make` / `raco test` はこのディレクトリを一切参照しない。

十原始規則すべてについて「出力する定理が整形式である」ことを Idris2 で機械検証
済み（`%default total`、`believe_me` なし、hole なし）。テストパッケージの
`idris_differential.rhm`（両カーネルを120項のコーパスで並走比較）と
`idris_replay.rhm`（実際の起動導出を Idris 側に再生させて照合）で、
Racket 生成コードをテストパッケージ内に検証データとして持ち、両者の一致を
確認している。生成コードはテストパッケージのみが依存するので `rhombus/hol.rkt`
の依存グラフには入らず、`raco make` に影響しない。

詳細（証明の構造、Idris/Rhombus 間の差分、ベンチマーク、設計の経緯）は
`idris-hol-kernel/README.md` を参照。

---

## 7. 参照したソフトウェア

- **HOL Light** — カーネルの十個の基本推論規則、locally nameless の項表現、
  等式変換（`conv.rhm` は `equal.ml` の設計を踏襲）、型の表現。
- **HOL4** — 論理定数の定義のしかたと、3 つの公理（ETA・SELECT・BOOL_CASES）の選び方。
- **ACL2** — Waterfall（簡約・デストラクタ除去・一般化・帰納法の固定パイプライン）の設計、
  項順序（`order.rhm`）、規則データベースの優先順序（`ruledb.rhm`）。
- **QuickCheck** の系譜 — `check_property` / `qc.rhm` の設計（生成・収縮・反例の最小化）。

---

## 8. ドキュメント

`rhombus-hol/rhombus/hol/scribblings/` に multi-page で 6 章:

| ファイル | 内容 |
|---|---|
| `rhombus-hol.scrbl` | 表紙・`docmodule(~lang, rhombus/hol)`・目次 |
| `overview.scrbl` | 1 つの宣言の 2 つの読み・いつ何が起きるか・完全な例 |
| `declarations.scrbl` | 全 10 形式のリファレンス |
| `grammar.scrbl` | 型・式・命題の文法と優先順位表 |
| `termination.scrbl` | 辞書式構造的降下・測度・部分項関係・未対応のもの |
| `prover.scrbl` | Waterfall の 4 段・失敗したときの読み方・正当化の合成 |
| `trust.scrbl` | カーネル・3 公理・公準化しているもの・漏れているところ |

ビルドは `raco setup --pkgs rhombus-hol`（`doc/` は .gitignore 済み）。

---

## 9. 設計: `datatype` / `recdef` を公理から導出に置き換える

`trust.scrbl` が明言している通り、公理化されているのは 2 箇所だけで、
それぞれ「境界の内側で検査条件が全ソウンドネス論証」というナローシームに
なっている。ここでは両方を実際に導出に置き換える設計を固める。
**両者は独立に進められ、`recdef` の方が先に着手できる**というのが、
このメモの一番の結論。

### 9.0 決定的な事実: 再帰的な datatype には新しい公理が要る

`new_basic_type_definition` は既存の型の部分集合を型に仕立てる原理でしかない
（`kernel.rhm` の実装通り）。無限の公理を持たない現状のカーネルでは、
`bool` と `fun` から有限回の型構成で作れる型はすべて**有限**である
（`A -> B` は `|B|^|A|` で、両方有限なら有限。無限公理なしに無限型を作る
経路は存在しない）。`List` や `Nat` のような再帰的 datatype は無限型なので、
**`new_basic_type_definition` だけをいくら組み合わせても導出できない** ---
review が示唆する「`new_basic_type_definition` に置き換えれば済む」という
見立ては、非再帰的 datatype にしか成り立たない。

したがって再帰的 datatype の完全な導出は、HOL Light / HOL4 と同様に
**無限の公理を 1 つ新設する**ことを意味する。これは公理の数を増やすが、
質的には改善である: 現状は「datatype 宣言の数だけ」公理スキーマのインス
タンスが生成される（`check_spec` を信頼する箇所が宣言のたびに増える）のに
対し、無限公理は **1 個だけ、一度だけ監査すればよい、標準的でよく研究された
公理**であり、`ETA`/`SELECT`/`BOOL_CASES` と同格の「4 本目の公理」として
`trust.scrbl` にそのまま書ける。

### 9.1 `recdef`: 公理を増やさずに導出できる（先に着手）

`subterm.rhm` が既に指摘している通り、各 datatype の構造的部分項関係
`T_lt` は導出済みの関数であり、その整礎性は「datatype の帰納法公理が
無限降下列を禁じるから」という**書かれてはいるが証明されていない**論証に
依拠している（`subterm.rhm` 冒頭のコメント参照）。`recdef.rhm` は
`check_termination` が `T_lt` に沿った構造的減少を確認した後、各節を
`new_axiom` で導入している（`install_function` 内、唯一のシーム）。

導出への置き換えは 3 段:

1. **`WF(R) := forall P. (exists x. P(x)) ==> exists m. P(m) and forall y. R(y, m) ==> not P(y)`**
   という `bool` だけで書ける整礎性の定義を `lib` に追加する（新しい公理は
   不要 --- 論理定数の上の定義）。
2. **`|- WF(T_lt)` を datatype ごとに導出する。** 各 `DatatypeThms.induction`
   （帰納法の公理--- 9.2 で導出に変わるがそれまでは公理のまま）から、
   「`P` を反例の否定として `WF` の存在部分を構成する」という標準的な
   一階論証で `|- WF(T_lt)` を証明する。ここは `datatype` が公理のままでも
   進められる: 依拠しているのは「induction という命題」であって「それが
   `new_axiom` 経由で得られたか `new_basic_type_definition` 経由で得られたか」
   ではないから。
3. **`WFREC` の一般定理を一度だけ証明する。**
   `WF(R) ==> exists f. forall x. f(x) === M(RESTRICT(f, R, x), x)`
   （`RESTRICT(f, R, x)` は `R`-worse な引数では未定義に潰す関数）という形の
   存在定理を、`SELECT`（既存の公理 #2）と `WF` の整礎帰納法だけで証明する
   （HOL4 の `relationTheory.WF_RECURSION` / TFL 相当、Slind の構成）。
   これは **一度書けば全 `function` 宣言が共有する**、datatype 非依存の
   定理であることが肝心 --- ここに手間をかける価値が最も高い。

`install_function` はその後:
- `new_constant` の代わりに `f = @f. forall x. f(x) === M(...)` を
  `new_basic_definition`（Hilbert choice による一点定義）で導入する。
- ユーザーに見える各節の等式は、`WFREC` の定義方程式を termination proof
  （節ごとの再帰呼び出しが `T_lt` で真に減ることの証明、`check_termination`
  が今も生成している情報）で書き換えて**導出する** --- `new_axiom` は
  もう出てこない。

この節の変更は `datatype.rhm` に一切触れずに完結する。9.2 が未着手のままでも
`recdef.rhm` だけ先に閉じられる。

### 9.1.1 進捗（本セッション）: `WF_INDUCTION` とその逆を導出、`WFREC` は未着手

9.1 の 3 段のうち、段 1（`WF` の定義）は既に完了していた
（`bool.rhm` の `mk_wf`/`c_wf`、"Add WF as a base logical constant" コミット）。
本セッションで `rhombus-hol-lib/rhombus/hol/private/wellfounded.rhm` を追加し、
段 2 が必要とする双方向の補題を両方とも**導出**（`new_axiom` なし、
`drule.rhm` の `CCONTR`/`EXISTS`/`CHOOSE`/`GEN`/`SPEC`/`MP`/`DISCH` だけで）した:

```text
prove_wf_induction        : |- !R. WF(R) ==> !P. (!x. (!y. R y x ==> P y) ==> P x) ==> !x. P x
prove_wf_from_induction    : ind_scheme(R) の証明を受け取り |- WF(R) を返す（規則）
```

`prove_wf_induction` は閉じた定理（仮説 0 個）。`prove_wf_from_induction` は
段 2 が要求する向き（帰納法の公理 → `WF`）そのもので、`tests/wellfounded.rhm`
で両方向とも実カーネルに対して確認済み（947 → 961 テスト）。

**未着手、次に続ける人へ:**

1. `prove_wf_from_induction` は「`!P. (!x. (!y. R y x ==> P y) ==> P x) ==> !x. P x`」
   という**一般形**の証明を受け取る。`datatype.rhm`/`DatatypeThms.induction` は
   コンストラクタごとの場合分け形（`(!args. P(C1(args))) and ... ==> !x. P(x)`、
   各コンストラクタの再帰フィールドについて帰納法の仮定を伴う）なので、
   これを一般形に変換する橋渡しの補題がまだない。橋渡しは
   「`R` = "直近の子である"（`subterm_spec` の `T_lt` ではなく、コンストラクタの
   再帰フィールドちょうど 1 段の関係）」を選び、コンストラクタごとの場合分けを
   単一の `!x. (!y. R y x ==> P y) ==> P x` へ畳み込む、datatype ごとに
   ほぼ機械的な変換になるはずである。
2. `T_lt`（`subterm.rhm`）は「直近の子」ではなく**その推移閉包**（等しいか、
   子孫か）。`WF(直近の子) ==> WF(推移閉包)` という汎用補題が別途要る
   （one-time, `wellfounded.rhm` に足す）。
3. **`WFREC` の存在定理**（9.1 の段 3）はまったく手つかず。本セッションで
   HOL Light 本家の `wf.ml` を直接読み、正確な依存関係を確認した:
   `WF_REC`（求める存在定理そのもの）は `WF_REC_INVARIANT` から出るが、
   `WF_REC_INVARIANT` 自身の証明は `prove_inductive_relations_exist`
   （**汎用の inductive relation 定義パッケージ**、Knaster-Tarski の
   最小不動点を関係の束上で取る、`ind_defs.ml` 相当）を土台にしている
   （「近似」を場当たり的にではなく、`H`から生成される最小の関係`R`として
   一発で存在・一意性を得るため）。すなわち実際の依存順序は:
   ```text
   汎用 inductive-relations パッケージ（未着手、それ自体が独立した課題）
       ↓
   WF_REC_INVARIANT / WF_REC（今回目標の WFREC 存在定理）
       ↓
   recdef.rhm の install_function 書き換え
   ```
   「近似の一意性論法を直接書く」という当初の見立ては、複数の局所的な
   近似関数を「一つの無矛盾な大域関数」へ貼り合わせる操作が結局
   同じ最小不動点構成を必要とすることが分かり、有望な近道ではなかった
   （HOL Light 自身がこの経路を選んでいるのが根拠）。したがって本項目は
   9.1 単独ではなく、**まず汎用 inductive-relations パッケージを
   `rhombus-hol-lib` に追加することが前提条件**であり、これ自体が
   `datatype_gen.rhm` 級の独立したセッション規模の作業になる。
   `install_function` は kernel.rhm にも `recdef.rhm` にも触れず、この上に
   積むだけでよい（`recdef.rhm`/`kernel.rhm` は不変のまま）。
4. 上記が揃うまで `recdef.rhm`/`datatype.rhm` は変更していない
   （`new_axiom` は今もそのまま）。

### 9.1.2 進捗（後続セッション）: `WFREC` 存在定理を完全導出 --- 上記項目 3 の結論を覆す

項目 3 で「汎用 inductive-relations パッケージが前提条件」と結論したが、
これは**覆った**。実際には汎用パッケージは不要で、`H` からその場で
作る**単一の**最小不動点関係を、高階論理の全称量化を使って一つの
閉じた `new_basic_definition` として直接書き下せる（`prove_inductive_relations_exist`
を経由せず、その特殊化・単一インスタンス分だけを直接構成する）。
`rhombus-hol-lib/rhombus/hol/private/wfrec.rhm` に実装し、`tests/wfrec.rhm`
で実カーネルに対して確認済み（1106 → 1112 テスト）。

```text
wfrec_rel(Rwf, H) := \x y. !P. (!f x'. (!z. Rwf z x' ==> P z (f z))
                                       ==> P x' (H f x'))
                              ==> P x y
```

`wfrec_rel(Rwf,H)` は構成により、"`f` が `x'` の `Rwf`-下位すべてで
関係と一致するなら、関係は `x'` と `H(f)(x')` についても成り立つ"
というルールで閉じた**最小の**関係である。閉性・最小性はどちらも
外側の `!P` を具体化するだけの 1 行の帰結（`wfrec_closure`/`wfrec_least`）。
ここから次を導出した（すべて `new_axiom` なし、`drule.rhm` の規則だけ）:

```text
wfrec_closure    : |- !f x'. (!z. Rwf z x' ==> Rel z (f z)) ==> Rel x' (H f x')
wfrec_inversion  : |- !x y. Rel(x,y) ==> ?f. (!z. Rwf z x ==> Rel z (f z)) /\ y = H f x
wfrec_unique     : WF(Rwf), congr |- !x y1 y2. Rel(x,y1) /\ Rel(x,y2) ==> y1 = y2
wfrec_exists     : WF(Rwf) |- !x. ?y. Rel(x,y)
WFREC            : WF(Rwf), congr |- soln x = H soln x   (soln は具体的な閉じた項)
```

`wfrec_closure`（最小不動点の通常の「閉じている」半分）は `!P` を specialize
するだけの直接証明。**`wfrec_inversion`（逆方向、"`(x,y)` が関係に入るなら
ルールから来た" ）が鍵**で、これも汎用パッケージなしで `wfrec_least` から
出る: 述語 `Q(x,y) := ?f. (!z. Rwf z x ==> Rel z (f z)) /\ y = H f x` 自身が
ルールに閉じていることを示せば（＝ `Q` がルールの右辺に来る「証人」として
自分自身を 1 段委譲するだけの純代数的な議論）、`Rel` は**最小**なので
`Rel ⊆ Q`、すなわち `wfrec_inversion` が出る。ここが `prove_inductive_relations_exist`
が一般に手当てする核心の性質（最小不動点は自身が生成する演算子の像に
含まれる）だが、**この一関係だけ**なら特別な仕掛けは要らない。
`wfrec_unique`/`wfrec_exists` は `wellfounded.rhm` の `prove_wf_induction`
による整礎帰納法（`WF(Rwf)` が必要になるのはここだけ）。最終定理は
`soln := \x. select(\y. Rel(x,y))`（`SELECT_INTRO` --- `SELECT_UNIQUE` の
双対、"証人を選ぶだけ"版を新規実装）を `wfrec_inversion` で 1 回反転し、
一致した `f` が `wfrec_unique` により `soln` 自身と一致することを示して
`soln x = H soln x` を得る。

実装上の罠: `BETA_RULE`（`TOP_DEPTH_CONV` によるフルベータ簡約）を
不用意に使うと、`soln(x)` のように**それ自体が別のベータ基を含む項**を
specialize した箇所まで簡約してしまい、後続で組み立てる「期待される形」の
項と構造的に食い違って `CHOOSE`/`MP` が拒否する。`SPEC`/`SPECL` 自身の
的を絞った簡約（`HEAD_BETA_CONV`、量化子の適用一段だけ）に留め、
`BETA_RULE` は「もう埋め込みの再帰がない」箇所だけに使うこと。

**残作業**: `WFREC` は具体的な `Rwf`/`H`/`WF(Rwf)`/congruence を受け取る
一般定理として完成したが、`recdef.rhm` はまだこれを呼んでいない
（`new_axiom` は今もそのまま）。配線を検討し、以下の 5 点が独立した
作業項目になることを確認した（`install_function`/`terminate.rhm` を
読んで具体的に特定 --- 前回セッションの見立てより詳細化）:

1. **`terminate.rhm` が実際の discharge 証明を捨てている** -- **本セッションで解消**。
   §9.1.3 参照。
2. **datatype 帰納法 → 汎用 WF スキームの橋渡し補題がまだ無い**（§9.1.1
   項目 1）。構造的降下の場合、`Rwf` は datatype の `T_lt`（`subterm.rhm`、
   これ自体まだ `install_function`/`new_axiom` 経由で導出されている）だが、
   `WF(T_lt)` を`DatatypeThms.induction`（コンストラクタ場合分け形）から
   一般形の帰納法スキームへ変換してから `prove_wf_from_induction` に渡す
   変換がまだ無い。
3. **測度ベースの場合は追加の一般補題が要る。** `Rwf(x,y) := T_lt(measure(x),
   measure(y))` という「測度を通した引き戻し」が整礎であることは、
   `WF(T_lt) ==> WF(\x y. T_lt(m(x),m(y)))` という一般的な pullback 補題
   （one-time、`wellfounded.rhm` に足す）が要る。
4. **多引数関数のタプル化。** `WFREC` は単一の型 `A` 上の `Rwf :: A->A->bool`
   を取るので、`FunSpec.arg_types` が複数ある場合は `algebra.rhm` の
   `prod` で引数列を 1 つの型へエンコードする必要がある（構造的降下の
   辞書式順序 `RecursionInfo.positions` も、この符号化上の関係として
   再構成する必要がある）。
5. **`H`（step 関数）をクロージャ節から実際に組み立てる。** 現在の
   `DefClause` リストはパターンマッチの節でしかなく、`WFREC` が要求する
   「`f :: A->B` を引数に取り `H(f, x) :: B` を返す」という単一の項は
   まだどこにも構築されていない。`cover()` が持つ決定木を、各再帰呼び出し
   位置で元の `fn` の代わりに引数 `f` を挿入する形でコンパイルし直す
   必要がある（`check_coverage` 自体は §9.4 の入れ子パターン課題と同じ
   決定木コンパイラ基盤を必要とする可能性が高い）。

以上のうち残る 4 点（datatype 帰納法の橋渡し・pullback 補題・多引数
タプル化・`H` の決定木コンパイル）はいずれも独立に大きく、項目 5（決定木
コンパイラ）は §9.4 で入れ子パターンについて記録したのと同種の
ソウンドネス隣接の設計判断を伴う。したがって配線自体は本セッションでは
完了させず、`WFREC` という**汎用定理の完成**と項目 1 の解消をこの
セッションの成果として確定し、残りは独立したセッション規模の作業として
次に持ち越す。

### 9.1.3 進捗（本セッション）: `terminate.rhm` に実際の discharge 証明を保持させた

§9.1.2 の残作業リスト項目 1 を解消した。`terminate.rhm`/`driver.rhm` を
読み直したところ、`driver.rhm` の `discharger` は既に `prove(...)` から
**本物の `Thm`** を受け取っていた -- ただし `match th | #false: ... | _:
#false` で成功時に**その場で握り潰し**、`check_measure` 側へは
「成功／失敗メッセージ」という真偽値的なプロトコルしか伝えていなかった。
つまり証明自体は既に waterfall がやっており、握り潰しているのは
**プロトコルの形**だけだったので、waterfall には一切触れずに直せた:

```text
Measure.discharge :: (Term) -> maybe(String)                    -- 旧
Measure.discharge :: (Term) -> values(maybe(Thm), maybe(String)) -- 新
RecursionInfo(positions, method, sites)                          -- 旧
RecursionInfo(positions, method, sites, decrease_proofs)         -- 新
```

`decrease_proofs` は測度ベースの呼び出し箇所ごとに 1 つ、`sites` と同じ
順序で実際の `Thm`（各々の結論はその呼び出し箇所の decrease obligation
そのもの）を保持する。構造的降下は今も純粋に構文的な事実
（`descends_at`）であり対応する `Thm` は存在しないので空リストのまま。
`driver.rhm` の唯一の呼び出し元（`discharger`）を更新し、
`tests/terminate.rhm` に `RecursionInfo` の 4 フィールド目を追加、
さらに新規に、実際の discharge callback（`ASSUME` で本物の `Thm` を返す）
を渡して `decrease_proofs` の**長さ**と**結論の文字列**の両方を検証する
テストを追加した（実カーネルに対して確認済み、1112 → 1116 テスト）。

踏んだ罠: `match th_opt | th :~ Thm: th | #false: error(...)` という
アーム順序で書いたところ、`~false` 側の測度失敗ケースで**`error` が
呼ばれずに `#false` がそのまま返る**という回帰を smoke test で踏んだ
（`measure.rhm` の `bad(#'constant)` が「例外を投げる」代わりに
「`result does not satisfy annotation`」で落ちた）。原因は `:~` が
**実行時判別をしないアノテーション**であること: `th :~ Thm: th` は
文字通り「何にでもマッチして `th` に束縛する」パターンであり、`Thm`
条件を検査しない。したがって最初のアームに置くと後続のアーム
（ここでは `#false`）が到達不能になる。判別が要る場合は、リテラル
パターン（`#false`）を**先に**書き、`:~` は「もう他の可能性がない」
ことが分かっている最後のアームでのみ使うこと -- この codebase 全体の
既存コードは一貫してこの順序（例: 直前の `check_measure` 自身の旧コード
`match ... | #false: ... | residue: ...`）を守っており、今回はそれを
破って書いてしまった。

**残作業（§9.1.2 参照）**: 4 点のうち項目 3 も本セッションで解消（§9.1.4）。
残るは 3 点 -- 項目 2（datatype 帰納法 → 汎用 WF スキームの橋渡し）と
項目 5（`H` の決定木コンパイル）が次に着手すべき最有力候補、項目 4
（多引数タプル化）は比較的独立した one-time のエンコーディング作業。

### 9.1.4 進捗（本セッション）: `WF` の pullback 補題（測度の整礎性の一般化）

§9.1.2 の残作業リスト項目 3 を解消した。`WF(R) ==> WF(\x y. R(f x, f y))`
（`wellfounded.rhm` の `prove_wf_pullback`）を、`prove_wf_induction`/
`prove_wf_from_induction` と同じ流儀（`CHOOSE`/`EXISTS`/`GEN`/`SPEC`/`MP`/
`DISCH` だけ、`new_axiom` なし）で導出した。

標準的な議論: `A` 上の空でない `P` を `f` に沿って `B` へ押し出し
`Q(z) := ?x. f(x)=z and P(x)` を作る。`WF(R)` が `Q` の最小元 `z0` を返し、
`Q(z0)` の証人 `x0`（`f(x0)=z0` かつ `P(x0)`）が求める `Rf`-最小元になる:
`R(f(y),z0)`（すなわち `Rf(y,x0)`）かつ `P(y)` なる `y` があれば、`f(y)`
自身が `Q(f(y))` の証人になり、`z0` の最小性（`R(f(y),z0) ==> not Q(f(y))`）
と矛盾する。実カーネルに対して確認済み（`wf(R)` の 1 仮説のみで
`wf(\x y. R(f x, f y))` を導出、1116 → 1117 テスト）。

これで測度ベースの `~measure(e)` は、宣言済み datatype の `T_lt` が
整礎であること（§9.1.2 項目 2、まだ未着手）さえ手に入れば、
`Rwf(x,y) := T_lt(measure(x), measure(y))` の整礎性を
`prove_wf_pullback(thy, wf_t_lt, measure_fn)` の 1 呼び出しで得られる
ようになった。

### 9.1.5 進捗（本セッション）: 多引数タプル化（`WFREC` を多引数関数へ適用する下準備）

§9.1.2 の残作業リスト項目 4 を解消した。`WFREC` は単一の型 `A` 上の
`Rwf :: A->A->bool` しか取らないので、複数引数を持つ `function` 宣言は
引数列を 1 つの `A` へタプル化する必要がある。`algebra.rhm` に、既存の
`prod`（`ProdThms`）を再利用する形で N 項タプルのユーティリティを追加した:

```text
tuple_ty(tys)          -- 右結合 prod の入れ子型: prod(t1, prod(t2, ... tn))
mk_tuple(args)          -- 対応する項: pair(a1, pair(a2, ... an))
tuple_proj(tys, i, t)   -- i 番目（0 始まり）の要素を取り出す fst/snd の合成項
prove_tuple_proj(thy, prod_thms, tys, i, args)
                        -- |- tuple_proj(tys, i, mk_tuple(args)) = args[i]
```

`prove_tuple_proj` は `fst_pair`/`snd_pair`（`ProdThms`、多相なので呼び出し
ごとに `INST_TYPE` で具体型に当てる）を、タプルの入れ子を 1 段ずつ剥がす
再帰で合成するだけで、新しい公理は一切要らない。実カーネルに対して
3 要素タプルの 3 つの射影すべてが期待通りの項に等しく、仮説 0 個である
ことを確認済み（`tests/algebra.rhm`、1117 → 1123 テスト）。

**残作業（§9.1.2 参照）**: 2 点。datatype 帰納法 → 汎用 WF スキームの
橋渡し（項目 2）と `H` の決定木コンパイル（項目 5）。どちらも
per-datatype のコード生成 + 一般補題という組み合わせが要る、
`datatype_gen.rhm`/`subterm.rhm` 級の独立したセッション規模の作業と
判断し、本セッションでは着手しなかった。

### 9.2 `datatype`: 段階的に閉じる

**フェーズ 1 (公理追加なし, 実利がすぐ出る)**: 自己再帰フィールドを一切持たない
datatype (enum、非再帰レコード/バリアント) に限定して `new_basic_type_definition`
で導出する。土台として `unit` / `sum` / `prod` の 3 つの型構成子を一度だけ
`new_basic_type_definition` で作る（HOL Light の `pair.ml` 相当、これも
有限型の組み合わせなので無限公理は不要）。任意の非再帰 `DatatypeSpec` は
`sum(prod(F1_1, ..., F1_k1), sum(prod(F2_1, ...), ...))` の入れ子にエンコード
でき、コンストラクタは `inl`/`inr`/`pair` の合成、injectivity/distinctness/
cases/induction/discriminators/selectors はすべて sum と prod のその性質
（一度だけ証明する）から**定理として**出る。`check_spec` の
`nonrecursive_ctors` チェックは既にこの場合分けの入り口になっている。

### 9.2.1 進捗（本セッション）: `unit`/`prod`/`sum` を導出し、enum の全数列を配線して差分テスト

フェーズ 1 が要求する 3 つの型構成子（`unit`/`prod`/`sum`）をすべて
`rhombus-hol-lib/rhombus/hol/private/algebra.rhm` に実装し、
`new_basic_type_definition` 経由で（公理を一切追加せず）導出した。
`tests/algebra.rhm` で実カーネルに対して確認済み（980 → 1005 テスト）。

```text
build_unit(thy) : Theory * Thm
  |- forall (x :: unit): x === one          -- 1点のみ、cases も induction もこれ1本

build_prod(thy) : Theory * ProdThms
  pair_eq    : |- forall a1 b1 a2 b2. pair(a1,b1)===pair(a2,b2) <=> a1===a2 and b1===b2
  surjective : |- forall p. exists a b. p === pair(a,b)         -- datatype の cases 相当
  fst_pair   : |- forall a b. fst(pair(a,b)) === a
  snd_pair   : |- forall a b. snd(pair(a,b)) === b

build_sum(thy) : Theory * SumThms
  inl_inj  : |- forall a1 a2. inl(a1) === inl(a2) <=> a1 === a2
  inr_inj  : |- forall b1 b2. inr(b1) === inr(b2) <=> b1 === b2
  distinct : |- forall a b. not (inl(a) === inr(b))
  cases    : |- forall s. (exists a. s === inl(a)) or (exists b. s === inr(b))
```

すべて仮説 0 個。`unit` は HOL Light 流に、`bool` の中で述語 `\x. x` が
切り出す一点部分集合との全単射として構成した（唯一の値は `abs(true)`）。
`prod` も HOL Light `pair.ml` 流に、`mk_pair_rep(a,b) := \x y. x===a and y===b`
という非再帰的な `bool` 上の定義を経由し、`A -> B -> bool` の中でその像が
切り出す部分集合との全単射として構成した。`sum` は `mk_inl_rep(a) := \x y t.
t and x===a`、`mk_inr_rep(b) := \x y t. (not t) and y===b` という 2 つの
非再帰的定義を経由し、`A -> B -> bool -> bool` の中でどちらかの像が切り出す
部分集合との全単射として構成した（`t` スロットがどちらの構成子から来たかの
タグ）。単射性・distinctness・全射性/cases の各定理は、いずれも
`mk_*_rep`/`abs_*`/`rep_*` の性質から出る一般的な補題で、特定の datatype に
依存しない。

実装時に踏んだ罠（`prod` で発生、`sum` では踏まなかった）: `mk_pair_rep(a,b)`
は **定数**（`new_basic_definition` で導入した `Const`）の 2 引数適用で
あって、`(\a b x y. ...)` という生の lambda ではない。したがって
`mk_pair_rep(a,b)` をさらに 2 点 `(x,y)` に適用した結果を簡約するには
`BETA_RULE` ではなく `unfold_def`（定義方程式を経由する展開）が要る。最初
`BETA_RULE` で済ますと誤り、`TRANS` が `"middle terms do not match"` で
弾いてくれたので実カーネル相手のテストで即座に発覚した -- kernel が
自分の主張をどこまで信用してよいかの実例。`sum` の単射性/distinctness
証明では最初からこの区別を意識して `unfold_def` を使ったため、同じ罠は
踏まなかった。

**残作業**: `unit`/`prod`/`sum` に加え、それらを実際に `DatatypeSpec` へ
配線する第一例を `rhombus-hol-lib/rhombus/hol/private/datatype_derived.rhm`
に実装した -- **全コンストラクタが 0 引数（enum）の場合限定**で、
`build_enum_thms(thy, spec)` が `DatatypeThms` を丸ごと導出する:

```text
E(1)   := unit
E(n)   := sum(unit, E(n-1))                         -- n個の値を持つ表現型
Ci     := abs(inj(n, i))                            -- abs/rep は真の全単射
          (predicate `\e. true` -- E(n) は n 個の値しかなく、n 個のコンス
          トラクタで使い切るので、部分集合ではなく全体との全単射になる)
is_Ci  := \x. x === Ci                                -- 0引数なので判別子はこれで十分
```

`distinctness`/`cases` は `enum_inject` の入れ子（右結合の `sum` チェーン）
を再帰的に辿って導出するが、`datatype.rhm` の `build_cases`/`build_distinctness`
は結合を**左**に畳む（`for values(acc=a0)(a in rest): mk_disj(acc,a)`）。
これは実装中に踏んだ 2 つ目の罠で、最初は右結合のまま作って
`tests/datatype_derived.rhm` の差分テストで「命題としては等価だが `show` の
文字列が食い違う」ことが判明した。任意の右結合の論理式を左結合へ変換する
一般的な再結合補題は書かずに済んだ -- `to_ctor_eq` の各葉が「位置 `i` で
`x === Ci` が成り立つ」という**具体的にどの選言肢か分かっている事実**を
持っているので、それを目的の左結合の式へ直接 `DISJ1`/`DISJ2` で埋め込む方が
（既存の証明を後から組み替えるより）ずっと単純だった。

`tests/datatype_derived.rhm` は `n = 1, 2, 3, 4, 5` について、
`datatype_axioms`（公理的）と `build_enum_thms`（導出）の両方から
`DatatypeThms` を作り、`injectivity`（両方空）/`distinctness`/`induction`/
`cases`/`discriminators`/`selectors`（両方空）/`elim_rules` の**すべての
フィールドが `show` した文字列として完全一致し**、導出側のすべての定理が
**仮説 0 個**であることを確認している（1005 → 1047 テスト）。これは
PLAN.md §9.3 が要求する差分テストそのものであり、enum という限定的な
部分集合について、"axiom-free の構成が既存の公理的構成と寸分違わぬ
`DatatypeThms` を生成する" ことを実カーネルに対して証明している。

**まだ残っているもの（更新: フィールド付きコンストラクタへの一般化が完了）**:

`rhombus-hol-lib/rhombus/hol/private/datatype_gen.rhm`
(`build_nonrecursive_datatype_thms`) が上記の項目 1・2 を実装し、
`DatatypeThms` の 7 フィールドすべて（injectivity/distinctness/induction/
cases/discriminators/selectors/elim_rules）を、フィールド付き・0 引数
混在・複数型変数の任意の非再帰 `DatatypeSpec` について導出する。
`tests/datatype_gen.rhm` が 6 通りの spec（1 引数、2 引数、多相 2 型変数
3 引数、0/1 引数混在、0〜3 引数混在の 4 コンストラクタ、自己再帰の拒否）
について `datatype_axioms`（公理的）と差分テストし、7 フィールド全部が
`show` した文字列として完全一致し、導出側の全定理が仮説 0 個であることを
実カーネルに対して確認済み（1047 → 1094 テスト）。エンコーディングは
9.2.1 冒頭の `E(n)` を `sum(prod(F1_1,...,F1_k1), sum(prod(F2_1,...),...))`
へ一般化しただけで、非再帰フィールドの構造は変わらない。

判別子は `is_Ci(x) := exists a0...ak-1. x = Ci(a0,...,ak-1)`
（`ctor_leaf_target` と同じ形の述語で、`i=j` なら `ys` 自身が証人、
`i!=j` なら既存の `distinctness` から矛盾を導く）、選択子は
`Ci_fj(x) := select(\v. exists z0...zk-1. x=Ci(zs) and zj=v)`
（`select` による全域関数、一意性は `injectivity` から）として導出した。
`select` の一意性補題 `SELECT_UNIQUE`（`|- pred(a)`, `|- forall v. body
==> v=a` (簡約形) ==> `|- select(pred)=a`）を `drule.rhm` に新規追加した。

この過程で `drule.rhm` の 2 つの既存バグを発見・修正した（`tests/` 全体は
回帰なし、994→1047→1094 で単調増加のみ）:

1. **`EXISTS` の変数捕獲**: 存在量化する変数と `exists` 自身の CPS 変換が
   使う「答え変数」がたまたま同じ型（例: 束縛変数が `bool` 型で、
   `exists` の答え変数も常に `bool`）を持つと、両方が独立な `fresh_for`
   呼び出しで "x" と自動命名され、同一の `FVar` に潰れて証人のスコープに
   答え変数を巻き込んでいた。`genvar`（`fresh_for` とは別の命名系統）で
   衝突を回避。
2. **`project`（`CONJUNCT1`/`CONJUNCT2`、ひいては `DISCH`/`MP` の内部）の
   過剰簡約**: 選択関数の 2 引数適用をちょうど 2 段だけ簡約するために
   `BINOP_CONV(HEAD_BETA_CONV)` を使っていたが、`HEAD_BETA_CONV` は
   「止めるべき場所」を知らない open-ended な head-spine 簡約であり、
   選び出した論理式自身がベータ基（適用されていない `Abs`）だった場合、
   その論理式の**中身まで**簡約してしまっていた。選び出した論理式を
   超えて簡約できない、ちょうど 3 段の明示的な簡約に置き換えた。
   どちらのバグも、この一般化以前は誰も踏んでいなかった（`bool` 型の
   存在量化や、簡約前の適用そのものを discharge/projection することは
   これまでの呼び出し元のどれもしていなかった）ため、既存の証明には
   影響がない。

**実接続、完了**: `driver.rhm` の `add_type` を、`is_nonrecursive_spec(spec)`
が真なら `build_nonrecursive_datatype_thms`、そうでなければ（自己再帰
フィールドを持つ場合）従来通り `datatype_axioms` を呼ぶよう切り替えた。
`datatype_gen.rhm` はもう並行モジュールではなく、非再帰 `type` 宣言の
実際の実装になった。既存テストへの影響はゼロ（テストスイート中で唯一の
非再帰 `type`、`tests/fixtures/theory_after_decl.rhm` の 2 引数なし
enum `Colour` が対象になるだけで、その他はすべて `Nat`/`List`/`Tree` 等の
自己再帰型なので従来通り公理的パスを通る）。1094 テストは変わらず全通過。さらに`tests/datatype_gen_wired.rhm`/`fixtures/nonrecursive_field_type_ok.rhm`として専用の回帰テストに昇格（1094 → 1098）
（速度に有意な変化なし）。加えてフィールド付き非再帰型を**実際の
`#lang rhombus/hol` ソース**から宣言するスモークテストで、`type` → 導出
された `injectivity`/`selectors` がルールベースに入り `match` で定義した
`function` の等式が証明できること、さらにその `function` についての
`theorem`（`swap`を2回で元に戻る、および導出 injectivity を書き換え
規則として使う iff）が `auto()` だけで証明できることを確認した
（`match(p) | MkPair(a,b): MkPair(b,a)` を持つ2値フィールドの `Pair` 型）。

**まだ残っている（複数セッション規模）**:
1. 自己再帰フィールドを持つ datatype（フェーズ 2・3、無限公理が必要）。
`datatype.rhm` 自体（`datatype_axioms` の実装本体）はまだ一切変更していない
-- 自己再帰型は今も axiom スキーマのままで、これは意図通り（フェーズ 2・3
待ち）。

**フェーズ 2 (無限公理の新設)**: `trust.scrbl` に「4 本目の公理」として
明記した上で、`exists f :: ind -> ind. injective(f) and not (surjective(f))`
という標準形の無限公理を導入し、そこから `Nat`（あるいは `ind` をそのまま
使う）を HOL Light の `nums.ml` / HOL4 の `arith.ml` に相当する手順で構成する。
これは 1 回限りの、既に何十年も監査されてきた構成であり、datatype の個数に
スケールしない。

**フェーズ 3 (再帰 datatype の一般導出)**: フェーズ 2 の `Nat`/`ind` を使い、
`check_spec` が既に課している制約（有限・厳密正・非入れ子・非相互再帰・
直接の自己再帰のみ）のもとで、HOL Light `ind-types.ml` を単純化した構成を
実装する: 各コンストラクタを「タグ + フィールドの有限タプル（非再帰
フィールドは既存の型の表現、再帰フィールドは `U` 自身）」として `NUMPAIR`
的なペアリングで `U`（`ind`/`Nat` 上の普遍型）へ単射に符号化し、「コンス
トラクタの像で閉じた最小部分集合」を強い帰納法で特徴づけて
`new_basic_type_definition` で切り出す。injectivity はペアリングの単射性
から、distinctness はタグの違いから、induction はその集合の**最小性**から、
cases は**構成による全射性**から、それぞれ定理として出る。これが 3 段の
うち唯一「入れ子でない self 再帰専用」の制約を陽に使う箇所で、この制約が
`check_spec` に既にあるおかげでフェーズ 3 は HOL Light 本家より大幅に単純化
できる（相互再帰・他の型構成子を介したネストへの対応が要らない）。

### 9.3 実装順序と検証方法

1. `recdef`（9.1） --- 公理を増やさず、`kernel.rhm` にも触れない。
2. `datatype` フェーズ 1（9.2） --- 非再帰 datatype のみ、公理を増やさない。
3. `datatype` フェーズ 2・3（9.2） --- 無限公理の新設を伴う、複数セッション
   規模。

各段で `idris_differential.rhm` / `idris_replay.rhm` と同じ発想の
**差分テスト**を追加する: 旧（公理的）実装と新（導出）実装を両方コンパイル
できる状態にしばらく残し、同じ `DatatypeSpec`/`FunSpec` から出る
`DatatypeThms`/`FunInfo` の**命題（`show` した文字列）が一致すること**を
確認してから、旧実装を消す。命題以外は誰も見ていない
（`datatype.rhm` 冒頭のコメント「Everything above this module depends
solely on the statements in DatatypeThms, never on how they were obtained」
の通り）ので、この一致確認が正しさの実用的な担保になる。

### 9.4 進捗（本セッション）: 反映される部分集合に `cond` と局所 `let` を追加

レビュー項目 8 の「第一段階」（`if`/`cond`/局所 `def`/`let`/入れ子適用/
Boolean 演算子）のうち、`cond` と局所 `let` を `elab.rhm` に実装した。
`function` の本体は「emit verbatim」（実行時コードは字句通りそのまま出力
する）ので、実行側は元々の Rhombus がすでに `cond`/`let` を持っており
**無変更**で済む。変更が要るのは論理側（`elab.rhm`）だけ。

```rhombus
function classify(b1 :: Boolean, b2 :: Boolean, m :: Nat, n :: Nat, k :: Nat) :: Nat:
  let mid = n            // 局所 `let`: 束縛を評価環境に追加するだけ
  cond                    // `cond`: 入れ子の `if` へ脱糖
  | b1: m
  | b2: mid
  | ~else: k
```

`cond`は`mk_cond`への入れ子`if`へ脱糖するだけで、`~else`節を必須にした
（`match`と違い、任意のBoolean条件についての網羅性解析はできないため）。
局所`let`は新しいHOL構成子を一切必要としない、純粋にelaborator側の環境
拡張（`env ++ {name: elaborated_term}`）で、`function`本体を複数の
`;`区切りグループとして受け取り、先頭が`let name = expr`でなければ
（既存の）`not_admitted`エラーに落ちる。`match`節の内部でも同様に働く
（`parse_clause`が同じ`parse_body`を再帰的に呼ぶため）。

**踏んだ罠**: shrubbery の quoted pattern で複数グループ（`;` 区切り）を
捉える構文は、`$name; ...`という**組**（メタ変数に直接 `;` を後置した
もの）としてしか書けない。素朴に `$rhs ... $rest ...`（改行のみ）や
`$rhs ...; $rest ...`（`...`の後に生の`;`）を試すと**サイレントに
マッチ失敗**し、実行時まで気づけない（`raco make`は通り、`raco test`で
初めて「本体全体が`not_admitted`に落ちた」という形で表面化する）。正しい
書き方は:
```rhombus
| 'let $(n :: Identifier) = $rhs ...
   $more; ...':
    ...
    parse_body(..., '$more; ...', at)   -- 使う側もテンプレートとして `; ...` を保つ
```
`$rhs ...`（`;`なし）は「**このグループ内**の残り全部」を表し、グループ
境界で自動的に止まる（ドキュメント通り）。`$more; ...`（`;`あり）は
「**残りのグループ全部**」を表す、別のイディオムであり、両者は混同
できない。

**回帰テスト**: `tests/decl_cond.rhm`/`fixtures/cond_ok.rhm`（`cond`の
正常系・`~else`欠落の異常系）、`tests/decl_let.rhm`/`fixtures/let_ok.rhm`
（局所`let`の正常系、`match`節内部での使用、`let`なしの複数文本体の
異常系）。1098 → 1106 テスト、既存テストへの回帰なし。

**入れ子パターン（未着手）に進む前に必ず読むこと -- ソウンドネス隣接の罠**:

当初、`match n | succ(m): match m | succ(k): ...`のような**パターン束縛
変数への再`match`**（真の入れ子）を、単に`parse_body`の列追跡を
「元の引数だけ」から「現在生きているどの束縛変数でも」へ一般化すれば
実現できると考え、設計まで進めた。しかし詳細検討で、これは
**`recdef.rhm`の`cover()`（網羅性検査）が見逃す穴を作る**ことが判明した:

`cover()`は各列について`pattern_ctor(pats[col])`で**その列の最上位の
コンストラクタ**だけを見て「この列は割れているか」を判定する。もし
ユーザーが`match a | Cons(h,t): match h | Cons(hh,tt): ... | Nil(): ...`
と書いたとき、`h`への再`match`は**同じ列**（列aの中身が`Cons(h,t)`から
`Cons(Cons(hh,tt),t)`へと入れ子で深まる）を更新するだけなので、`cover()`
視点では列aは相変わらず「全部`Cons`」（トップだけ見ている）にしか
見えず、**`h`自身の`Cons`/`Nil`分岐が本当に網羅されているかは一度も
検査されない**。ユーザーが`h=Nil()`のケースを書き忘れても`check_coverage`
は気づかず、`install_function`は「網羅済み」として通してしまう。

これは`new_axiom`を経由するので直接カーネルの不健全性にはならないが
（未網羅な入力については単に`f`の値が公理に拘束されないだけ）、
「論理側と実行側が食い違う」というレビュー自身が懸念していた種類の
バグそのものである（実行側の`match`は網羅性を要求する通常のRhombusの
ままなので、未網羅なら**実行時にマッチ失敗で落ちる**が、論理側は
`install_function`が黙って通す）。

したがって、入れ子パターンに着手する場合は、**まずパース面ではなく
`cover()`/`check_coverage`自体を、列の最上位だけでなく再帰的に
（各コンストラクタの各フィールド位置についても、そこがさらに
コンストラクタパターンで割れているなら再帰的に網羅性を検査するよう）
一般化することが前提条件**である。これは事実上、決定木コンパイラを
`recdef.rhm`の中に正しく実装することを意味し、パーサ側の変更だけでは
安全に実現できない。`terminate.rhm`の`descends_at`も同じ「列は最大1回
だけ、コンストラクタ1段だけ」という前提に依存しているため、あわせて
一般化が必要になる可能性が高い。

### 9.5 進捗（本セッション）: Core IR 調査 -- 現行の反映範囲では未着手のままでよい

レビュー項目 7（`Surface -> CoreExpr -> HOL + Rhombus` の共通 IR）を、
実装ではなく**まず調査**した。`expand.rhm`/`module_block.rhm` を読み、
実際に「二つの読み」がどう配線されているかを追った結論:

`expand.rhm`の`plan_one`（`#'function`分岐）は`elab.function_decl_shape(form)`
を呼び、その`body`をそのまま`Decl`に積む。`module_block.rhm`の`emit_function`
は**その`body`を一切解釈せず、そのままテンプレートへ埋め込むだけ**
（`'fun $name($p, ...): $body'`）。論理側は`driver.rhm`が**改めて`d.form`
全体を`elab.parse_function_decl`で再パース**する（`elab.rhm`冒頭のコメント
「Everything here is called twice ... Both go through the same functions
on the same syntax」の通り）。したがって:

- 実行側は「解釈ゼロの逐語コピー」であり、そもそも**独自の第二の意味論を
  持たない** -- 変な言い方をすれば、実行側は「Rhombus自身が、たまたま
  同じソースを普通に展開したもの」そのものである。
- 論理側（`elab.rhm`）は識別子を`Syntax.unwrap`で**裸のSymbol名**に
  落として`const_type(thy, name)`のような**名前ベース**の照合をする。
  実行側はRhombus自身の**束縛ベース**の名前解決を使う。この二つが
  食い違い得るのは、ある綴りについて名前ベースの照合結果と束縛ベースの
  解決結果が異なる場合だけである。

現行の反映される部分集合（裸の識別子・名前付き適用・`if`/`cond`/`let`/
ブール演算子・ハードコードされた演算子表のみ、モジュール修飾名も
ユーザー定義演算子もインポート別名の参照も文法外）では、この食い違いが
**そもそも起こり得ない**:

- 修飾名（`f.Cons`のような）は`parse_application`が`'$(id :: Identifier)'`
  （裸の識別子）しか受け付けないため、書けたら即座に構文エラーになる。
  インポート別名を経由した名前の食い違いはこの経路を通らない。
- ローカルの`let`/パターン変数によるシャドウイングは、`env`（名前→`Term`
  のマップ）を`elab.rhm`が唯一の権威として、ソースの字面上のネストと
  厳密に同じ順序で拡張・参照するので、Rhombus自身のレキシカルシャドウ
  イングと**構造的に同じ**規則になる（内側の束縛が勝つ）。
- ユーザー定義演算子（項目10、別項目）はまだ導入していない。

つまり、**現行の反映範囲に対しては「同じソースを2回読む」設計は健全**
であり、共通IRを今導入するのは解決すべき実際のバグがない状態での
先行投資になる。共通IR（束縛identity を保持する`CoreDecl`/`CoreExpr`）
が実際に必要になる、具体的な引き金は以下のいずれかを反映範囲に
追加する時である:

1. インポート別名・モジュール修飾参照（`import: "x.rhm" as f` の後
   `f.Cons`のような参照）を許すとき -- 名前ベース照合ではエイリアスの
   先を辿れない。
2. ユーザー定義演算子（項目10）に論理的解釈を持たせるとき -- 演算子の
   優先順位・結合はRhombus側のマクロ定義が持つので、名前だけでは
   引けない。
3. `function`本体の外側（`type`宣言のフィールド型等）でも同様の
   識別子経由の参照が増えるとき。

これらのどれかに着手する回にあわせて、`elab.rhm`/`module_block.rhm`を
今の「同じソースを関数を共有して2回読む」設計から、`Syntax`の束縛
identity（`Syntax.bind_id`相当）をキーにした共通の中間表現へ切り替える
ことを検討する。それまでは、現状維持がむしろ正しい判断である。

### 9.6 進捗（本セッション）: namespace・複数 theory import は未着手・調査のみ

レビューの最終まとめ表にある P2 最終項目「binding-aware logical names・
namespace・複数 theory import」を調査した。現状の制約
（PLAN.md §4 に既出）は `driver.rhm` の `adopt` に起因する: `import` で
取り込んだ理論を**丸ごと置き換える**（`HolState(imported.thy, ...)`）
実装で、直前の `descends`/スタンプ等価チェックにより、取り込む理論が
現在の理論の祖先か同一でなければ拒否される。これは`combine_stamps`が
片方が他方の祖先でない2理論の定理を混在させられないことの反映であり、
**互いに拡張関係にない「兄弟理論」は合流できない**。

`Const(name :: Symbol, ty :: HType)`（`term.rhm`）を確認したところ、
定数の identity は**裸の `Symbol` のみ**で、名前空間・モジュール修飾の
概念が一切ない。したがって「兄弟理論を安全に合流する」ためには、まず
定数名にモジュール由来の修飾（またはそれに相当する一意化）を持たせる
**カーネルの項表現そのものの変更**が要る -- `term.rhm`/`kernel.rhm`
（`Theory.consts`/`Theory.defs` の `Symbol` キー）は言うに及ばず、
`printer.rhm`・`elab.rhm`・全 datatype/recdef 導出コードなど、`Symbol`
を定数識別子として扱っている箇所全てに影響する。§9.5 の Core IR や
入れ子パターンと同様、**パーサ面の変更ではなくカーネルの表現面の変更が
前提**であり、独立したセッション規模の課題と判断し、着手しなかった。

---

## 10. 外部レビュー（2026-09-07）への対応状況

レビューは `rhombus-hol-kernel` を標準 HOL Light 型カーネルへ寄せ、
`rhombus-hol-lib` を Rhombus/ACL2 側へ広げる、という非対称な方向性を
提案した。15 項目のうち、本セッションで扱ったものの状況:

| # | 項目 | 状況 |
|---|---|---|
| 1 | `Theory`/`Stamp` を forge 不能にする (P0) | **完了**（本セッション以前）。`constructor ~none` + `reconstructor ~none` + `internal`、raw field は非公開、`type_arity`/`const_type`/`axioms_of`/`definition_of`/`descends` だけを公開。`tests/kernel.rhm` に回帰テストあり。 |
| 2 | `datatype` の `new_axiom` を `new_basic_type_definition` に置換 (P0) | **非再帰は完了、自己再帰は未着手**。`unit`/`prod`/`sum` を導出し、**任意の非再帰 `DatatypeSpec`**（フィールド付き・0引数混在・複数型変数、自己再帰のみ拒否）について `DatatypeSpec -> DatatypeThms` の配線（7 フィールド全部、仮説 0 個）を実装し `datatype_axioms` と完全一致することを差分テストで確認済み（`datatype_gen.rhm`、§9.2.1）。**`driver.rhm` の `add_type` から実接続済み** -- 非再帰 `type` 宣言は実際にこの導出を使う（テストスイート内で該当するのは `Colour` 一件のみ、1098 テスト全通過（専用の回帰テストtests/datatype_gen_wired.rhm追加込み）、速度に有意な変化なし）。自己再帰 datatype（フェーズ 2・3、無限公理が必要）は未着手 -- なお複数セッション規模。 |
| 3 | `recdef` の `new_axiom` を導出に置換 (P0) | **`WFREC` 存在定理は完全導出**（§9.1.2）。`wellfounded.rhm` の `WF_INDUCTION`/逆方向（§9.1.1）に加え、汎用 inductive-relations パッケージなしで単一の最小不動点関係 `wfrec_rel` を直接構成し、closure/inversion/uniqueness/existence を経て `soln x = H soln x`（`WF(Rwf)`・congruence を仮説に）を導出（`wfrec.rhm`）。配線の前提のうち 3 点解消: `terminate.rhm` の discharge 証明保持（§9.1.3）、`WF` の pullback 補題（§9.1.4）、多引数タプル化（§9.1.5、`algebra.rhm` に `mk_tuple`/`tuple_proj`/`prove_tuple_proj` を追加）。**残るのは配線 2 点**（datatype 帰納法→汎用WFの橋渡し、`H` の決定木コンパイル。§9.1.2/9.1.5 参照）-- `recdef.rhm`/`datatype.rhm` はまだ `new_axiom` を使っている。 |
| 3(raw Term) | raw `Term`/`HType` construction を隠す (P1) | **`Term`側は完了**、**`HType` 側は意図的に見送り**。下記参照。 |
| 4 | 内部は locally nameless、外部 API は標準 HOL にする | **`mk_abs`/`dest_abs` により実質的に達成済みと判断**。詳細下記。 |
| 5 | kernel から unification/printer/tracing を追い出す (P1) | **`type_unify` は完了**（本セッション以前、`rhombus-hol-lib/elab` へ移動済み）。printer は `kernel.rhm` 自身がエラー整形に使っており、追い出すと循環になるため据え置き（PLAN.md §1 が既にこの理由を記録済み）。tracing は独立した書き込み専用ログで健全性に無関係と説明済み。`hyp_insert`/`hyp_union`/`hyp_remove`/`rehash_hyps` の非公開化は**調査済み、現状維持と判断**: `rhombus-hol-lib` のどこからも実際には呼ばれておらず（`Thm` は raw hyps リストではなく既に不可侵なので、これらは項リスト上の純粋なユーティリティであり公開してもソウンドネスに影響しない）、唯一の外部利用者は `rhombus-hol-kernel` に対応するテストパッケージが無いために `tests/kernel.rhm`/`tests/drule.rhm`（外側の `rhombus-hol` パッケージ）に置かれている kernel 自身の単体テスト。非公開化には kernel 専用のテストパッケージ新設が要り、得られる利益（API 美観）に見合わないと判断した。 |
| 6 | 公開 kernel API を HOL Light `fusion.ml` に揃える | 大枠は既に一致（十規則、同じ命名）。**`BETA` の trivial-redex 化は検討し、見送りと判断**（詳細下記）。残る未着手部分は printer/tracing 分離のみ（§5 で対応済みと説明）。 |
| 6b | base logic は HOL Light型かHOL4型かを明示する | **既に明示済み**。`bool.rhm` 冒頭のコメントが "ETA, SELECT and BOOL_CASES -- following HOL4 rather than HOL Light" と明記し、`kernel.rhm`/PLAN.md §1 が原始規則は HOL Light 型（十規則）であることを明記している。レビューが望む「どちらの型を実装しているか」の明示は既存のドキュメントで満たされている。 |
| 7 | `Surface → CoreExpr → HOL + Rhombus` の共通 IR | **調査済み、現行範囲では不要と判断**。`module_block.rhm`の実行側emitは`body`を一切解釈しない逐語コピーで、独自の第二の意味論を持たない。裸の識別子・ハードコード演算子表のみの現行反映範囲では名前ベース(elab.rhm)と束縛ベース(Rhombus)の解決が食い違い得ない。共通IRが要る具体的な引き金（インポート別名越しの参照・ユーザー定義演算子）を§9.5に記録した。 |
| 8 | `match`/`cond`/局所 `def`/入れ子パターンの追加 | **`cond`/局所 `let` は完了、入れ子パターンは未着手**。詳細と、入れ子パターンを安全に進めるための必須の前提条件（下記参照）は §9.4 にまとめた。 |
| 9 | `function` はロジック性マーカーのみとし、grammar は Rhombus `fun` を再利用 | **設計判断として達成、コード内に既存の理由コメントあり**。`elab.rhm` 冒頭が「`fun` を intercept せず別キーワードにする」理由を明記済み。宣言レベルの多節 `\|` 構文（Rhombus 本来の `fun` の書き方）への接近は §8/§9.4 の入れ子パターン課題と同じ決定木コンパイラを要求するため、そちらに一本化して追跡する。 |
| 10 | user-defined operator に logical interpretation を登録可能にする | **調査済み、v0.1 の範囲では不要と判断（既存コメントあり）**。`elab.rhm` の手書き precedence parser 自体が "What `space.enforest` would buy is user extensibility, which v0.1 does not need" と明記しており、固定・小さい命題文法である現状ではレビューが望む拡張性の需要が実際に発生していない。§9.5 の Core IR 同様、需要が生じた時点（ユーザー定義演算子が実際に使われる時点）で再検討する。 |
| 11 | fertilization / irrelevance 除去 / induction pool | fertilization と irrelevance 除去は**完了**（本セッション以前）。induction pool は**試みて撤回**。下記参照。 |
| 13 | rule classes | **完了**。`ruledb.rhm` の `RuleDB` が type-prescription 事実を rewrite ルールと独立に分類・保持（`type_facts_of`）、`general.rhm` の `generalize_goal` が一般化時にそれを消費する。 |
| 14 | conditional rewriting | **完了**。`RewriteRule` が `conds :: List.of(Term)` を持ち、`apply_rule` が（自分自身を除外した db で）各条件を `simp_conv` により再帰的に discharge する。 |
| 15 | hints の拡充（`~cases`/`~expand`/`~in_theory`） | **`~in_theory:` と `~cases:` は完了**。`~expand:` は見送り（下記）。`~do_not:` は本セッション以前に追加済み。 |
| (最終まとめ表 P2) | binding-aware logical names・namespace・複数 theory import | **調査済み、未着手**。`driver.rhm` の `adopt` が兄弟理論（互いに拡張関係にない2理論）を合流できないのは、`Const` の identity が裸の `Symbol` のみで名前空間の概念がないため。安全な合流にはカーネルの項表現そのもの（`Symbol` を定数識別子に使っている全箇所）の変更が要り、独立したセッション規模の課題。詳細は §9.6。 |

### `HType`（`TyVar`/`TyApp`）の raw construction は意図的に隠していない

`Term` 側（`FVar`/`BVar`/`Const`/`Comb`/`Abs`）は `constructor ~none` +
`internal` + testing 専用の `raw_fvar`/`raw_bvar`/`raw_const`/`raw_comb`/
`raw_abs` で閉じた（`term.rhm`）。同じ手当てを `HType` にも、と検討したが
見送った: `TyVar`/`TyApp` の生構築は `bool.rhm`・`datatype.rhm`・
`subterm.rhm`・`elab.rhm`・`expand.rhm`・`terminate.rhm`・`kernel.rhm` 自身
など 15 ファイル以上に、`mk_fun` 相当の「賢い構築子」なしで直接ちりばめ
られており、レビューが実際に懸念していたのは（`BVar` の binder 型不一致の
ような）型ではなく項固有の不変条件であって、型の生構築を隠す動機は
「防御的 API・教育性」のみである。100+ 箇所の機械的だが広範なリネームを
この一点の見た目のためだけに行うのは、費用対効果で見送るべきと判断した。
着手する場合は `mk_tyvar`/`mk_tyapp` を `htype.rhm` に追加し、上記ファイル
群の**構築**箇所（パターンマッチ箇所は触らなくてよい ── `constructor ~none`
は構築だけを塞ぐ）を機械的に置き換える。


### `BETA` を trivial-redex 専用にする件は検討し、見送った（locally nameless では概念自体が成立しない）

レビュー項目 5 は「`kernel.BETA` は HOL Light 同様 `(\x.t)x = t` という
trivial redex 専用にし、任意の redex への一般 beta 変換は派生層
（`lib.BETA_CONV`）に置くべき」と提案している。`kernel.rhm` の `BETA` 実装
コメントは既にこれを検討済みで、見送りの理由を一行で記録している
（"under a locally nameless representation `subst_bvar` cannot capture,
so the general case needs no renaming and is exactly as primitive as the
trivial one"）。今回、この一行の主張を掘り下げて検証した。

HOL Light で trivial redex と一般 redex を区別する理由は**変数捕獲**
である: named representation では `(\x.t)x` （引数が束縛変数自身と同名）
は無条件に安全だが、`(\x.t)u`（任意の `u`）は `u` の自由変数が `t` の中の
別の束縛子に捕獲されないよう、束縛変数のリネームという**追加の機構**が
要る。だからこそ HOL Light は前者だけを無条件に安全な原始規則とし、
後者は `INST`（自由変数の置換、捕獲回避込み）を経由する派生規則
（`BETA_CONV`）として構成する:
`(\x.t)x = t`（trivial BETA）を `INST [u/x]` で書き換えて
`(\x.t)u = t[u/x]` を得る、という段取りである。

ところが locally nameless 表現では、束縛変数はそもそも**名前を持たない**
（`Abs(arg_ty, body)` は `body` 内の `BVar(0)` を束縛するだけで、"どの名前の
変数を束縛しているか" という情報が最初から存在しない）。したがって
"引数が束縛変数**自身と同名**" という trivial redex の定義そのものが、
この表現の上では**書き下せない**。`BVar` を一旦 `dest_abs`/`open_abs` で
新鮮な `FVar` に開いてから、その変数を引数として「trivial redex」を
作ろうとしても、それは実質的に `subst_bvar(fresh_var, body)` という
**現在の一般 `BETA` と同じ 1 ステップの置換**を、わざわざ遠回りして
書いているだけになる（開いた新鮮変数を使う分、むしろ手数が増える）。
しかも locally nameless の `subst_bvar` は定義上**捕獲が起こり得ない**
（`BVar` の de Bruijn 添字は `Abs` を跨ぐたびに shift されるので、任意の
項 `u` を代入しても `u` の中の自由変数が新しく `t` の束縛子に捕まる余地が
ない）。つまり HOL Light が「trivial 専用」にする**唯一の理由**（捕獲回避
機構をカーネルに持ち込みたくない）が、この表現では最初から発生しない。

結論: 「trivial 版だけを原始規則にする」という区別は、locally nameless
表現の上では**意味のある選択肢として存在しない**（名前を持たない束縛変数
について「引数が束縛変数と同名か」を問うこと自体ができない）。無理に
"trivial 版" を定義しようとしても、それは一般版の言い換えにしかならず、
実装の複雑さもカーネルの信頼境界も一切変わらない。したがって、この項目は
「HOL Light の見た目に合わせるためだけの空虚な書き換え」であり、
実施を見送った。一方で `conv.rhm` の `BETA_CONV`/`HEAD_BETA_CONV`/
`BETA_RULE` は既に「派生層のユーティリティ」として存在しており
（`kernel.BETA` を安全にラップし、redex でなければ `#false` を返す
total な wrapper。§2 参照）、レビューが望む「kernel には最小限、
便利な反復簡約は派生層に」という**役割分担そのもの**は既に達成されている
── 変わるとすれば「原始規則の宣言が一つ trivial になる」という表面上の
ラベルだけで、実質的な設計は不変である。

### 「locally nameless 内部・標準 HOL API 外部」は `mk_abs`/`dest_abs` で実質達成済み

レビュー項目 4 は、内部表現は locally nameless のまま、公開 API では
`FVar`/`BVar` の区別を見せず、`Var(name,ty)`/`Const(name,ty)`/`Comb(f,x)`/
`Abs(v,body)` という標準的な見た目にし、構築・分解を
`mk_abs : var -> term -> term` / `dest_abs : term -> var * term` 経由に
する、という提案である。

`term.rhm` を確認したところ、**この API 自体は既に存在する**:

```rhombus
fun mk_abs(v :: FVar, body :: Term) :: Abs           // 名前付き変数を渡して抽象化
fun dest_abs(t :: Term) :: values(FVar, Term)        // 新鮮な名前付き変数で開く
fun strip_abs(t :: Term) :: values(List.of(FVar), Term)
```

`dest_abs` は `Abs` の中の `BVar` を直接見せず、`fresh_for` で選んだ新鮮な
`FVar` に置き換えた `(変数, 本体)` の組を返す（`term.rhm` 冒頭のコメント
"callers never need to build a `BVar` by hand" の通り）。したがって
`mk_abs`/`dest_abs`/`strip_abs`/`list_mk_abs` だけを使う限り、呼び出し側は
`BVar` の存在を一度も意識しない -- これは提案の API 形そのものである。

**まだ達成していないのは、`FVar`/`BVar` を判別する `match` パターン自体を
完全に塞ぐこと**（例えば `match t | FVar(_,_): ... | BVar(_,_): ...` という
分岐が今も型として可能）。これを塞ぐには `Term` を「外部向けの `Var`/
`Const`/`Comb`/`Abs` の 4 種だけを見せるビュー」と「内部実装の 5 種
（`FVar`/`BVar` 分離）」の 2 層に分離する必要があるが、`drule.rhm`/
`conv.rhm` の相当数の関数（`ETA_CONV` の `Abs(aty, Comb(f, BVar(0,_)))`
パターン、`is_locally_closed`、`ABS_CONV` の新鮮変数処理など）は**まさに
この `FVar`/`BVar` の区別に本質的に依存して実装されている**。これらは
`dest_abs`/`mk_abs` の**内部実装**であって、この区別を隠すと実装できなく
なる（そもそも `dest_abs` 自身が `BVar` を見て `FVar` に置換する関数
なので、`BVar` を完全に見えなくするとその実装場所が無くなる）。

したがって「`FVar`/`BVar` をユーザー向け `match` から完全に塞ぐ」ことは、
kernel 自身の実装言語からこの区別を奪うに等しく、レビューが `HType` の
生構築非公開化について許容している「型ではなく項固有の不変条件が本質」
という区別を思い出すと、ここでの本質は「構築を smart constructor 経由に
すること」であって「分解時にどう見えるか」ではない。構築は既に
`constructor ~none` で閉じており（本セッション以前に完了）、分解の
標準 HOL 的な入り口（`mk_abs`/`dest_abs`）も既に用意されている。
残っているのは「実装の道具箱としての `FVar`/`BVar` を kernel 自身からも
隠す」という、review の意図（教育的な公開 API を整える）を超えた作業に
なるため、追加の対応はしないと判断した。

### `~expand:` は見送った（この設計では素直な意味論がない）

ACL2 の `:expand` は「その関数呼び出しを、引数の形によらず定義本体で
置き換える」というものだが、それは ACL2 の関数が `(if ...)` を内蔵した
**単一の再帰方程式**として定義されているから成り立つ。このシステムの
`function` はコンストラクタごとの**複数の節**（`recdef.rhm`）で定義されて
おり、`f(v)`（`v` が構築子適用の形をしていないバインダ）にマッチする節は
どの節にも存在しない ── つまり「引数の形によらず展開する」に対応する
単一の方程式が最初から無い。素直に実装すると destructor elimination
（すでに waterfall の一段）が自動でやっていることを手動で強制するだけの
ヒントになり、追加の表現力を持たない。導入するなら「節ごとの等式を
ヒントに使ってよい変数を明示する」形の別の意味論を設計する必要があり、
今回は見送った。

### induction pool は実装して撤回した（性能退行）

`waterfall.rhm` の `max_induction_depth = 2` を、繰り返しゴール検出
（同じ `(asms, concl)` を持つゴールに再度帰納法を試みない）+ 大きめの
安全弁（200）に置き換える版を実装し、`tests/decl_theorem.rhm` で検証した
ところ、以前 29 秒で終わっていたファイルが 108 秒以上かかるようになった
（`conditional_stuck.rhm`/`theorem_stuck.rhm` 等、意図的に失敗するはずの
フィクスチャが、以前は深さ 2 ですぐ諦めていたのに対し、繰り返し検出が
「進展なし」を捕まえられないケースでずっと深く帰納法を試すようになった
ため）。各帰納法はコンストラクタの数だけ分岐するので、深さに対して
作業量は指数的に増える。厳密な繰り返し一致だけでは ACL2 が実際に使っている
「進展なし」ヒューリスティック（ゴールのサイズ・構造が悪化していないか等）
の代わりにならず、安全弁を大きく取ると退行、小さく取ると元の 2 とほとんど
変わらない。**この変更は撤回済み**（`waterfall.rhm` は元の固定深度 2 の
ままで、リポジトリに退行は残っていない）。正しくやるなら、単純な深さや
繰り返し検出ではなく、ACL2 の「進展があったかどうか」判定
（生成された部分項の集合が真に増えたか、生成された仮定が本当に新しいか等）
を実装する必要がある。

### サブエージェント委譲について

P2 の 4 項目（induction pool・rule classes・conditional rewriting・
richer hints）をまとめて 4 並列のサブエージェントに委譲しようとしたが、
基盤モデル（当時 `openai-codex/gpt-5.6-terra`）の利用上限に達しており
即座に全滅した（probe も再試行も同様に失敗）。そのため本セッションでは
残り 3 項目（rule classes・conditional rewriting・hints のうち
`~in_theory:`/`~cases:`）を逐次、自分で実装した。次にサブエージェントへ
委譲する場合は、まず可用性を probe してから並列委譲するか、使えなければ
最初から逐次実装を選ぶか判断すること。
