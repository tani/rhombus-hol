# Rhombus/HOL — 実装リファレンス

R1〜R5 完了。`raco test rhombus-hol/rhombus/hol/tests` → 961 tests passed。
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
│           ├── order.rhm         ACL2 term-order（順序付き書き換え用、ruledb.rhm 専用）
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
| 停止性 | `terminate`（辞書式構造的降下 + 測度）`recdef`（節形式の再帰定義） | `recdef` |
| 書き換え | `tmatch` `ruledb` `simp`：一階マッチ、規則 DB、順序付き書き換え | `ruledb` |
| 証明探索 | `goal` `induct` `waterfall`（簡約・デストラクタ除去・フェルティライズ・一般化・irrelevance 除去・帰納法の固定パイプライン、ACL2 準拠） | `spec_4_1` |
| 一般化・デストラクタ除去・フェルティライズ・irrelevance 除去 | `general` `destruct` `fertilize` `irrelevance` | `spec_4_2` `destruct` `fertilize` `irrelevance` |
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
3. **`WFREC` の存在定理**（9.1 の段 3）はまったく手つかず。これが一番大きく、
   最も価値がある残作業: `RESTRICT(f, R, x)` の定義、近似の一意性論法、
   `SELECT` を使った構成 --- 本格的な HOL4 `relationTheory.WF_RECURSION` 相当の
   証明で、他の何よりも分量がある。`recdef.rhm` の `install_function` が
   `new_axiom` をやめられるのはこれが揃ってから。
4. 上記が揃うまで `recdef.rhm`/`datatype.rhm` は変更していない
   （`new_axiom` は今もそのまま）。

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

---

## 10. 外部レビュー（2026-09-07）への対応状況

レビューは `rhombus-hol-kernel` を標準 HOL Light 型カーネルへ寄せ、
`rhombus-hol-lib` を Rhombus/ACL2 側へ広げる、という非対称な方向性を
提案した。15 項目のうち、本セッションで扱ったものの状況:

| # | 項目 | 状況 |
|---|---|---|
| 1 | `Theory`/`Stamp` を forge 不能にする (P0) | **完了**（本セッション以前）。`constructor ~none` + `reconstructor ~none` + `internal`、raw field は非公開、`type_arity`/`const_type`/`axioms_of`/`definition_of`/`descends` だけを公開。`tests/kernel.rhm` に回帰テストあり。 |
| 2 | `datatype` の `new_axiom` を `new_basic_type_definition` に置換 (P0) | **未着手**（§9.2 のまま）。フェーズ 1（非再帰 datatype）ですら `unit`/`sum`/`prod` の構成から要り、複数セッション規模。 |
| 3 | `recdef` の `new_axiom` を導出に置換 (P0) | **部分的**。`wellfounded.rhm` で `WF_INDUCTION` とその逆を導出（§9.1.1）。`WFREC` 本体（一番価値が高く、一番大きい部分）は未着手。`recdef.rhm`/`datatype.rhm` はまだ `new_axiom` を使っている。 |
| 3(raw Term) | raw `Term`/`HType` construction を隠す (P1) | **`Term`側は完了**、**`HType` 側は意図的に見送り**。下記参照。 |
| 5 | kernel から unification/printer/tracing を追い出す (P1) | **`type_unify` は完了**（本セッション以前、`rhombus-hol-lib/elab` へ移動済み）。printer は `kernel.rhm` 自身がエラー整形に使っており、追い出すと循環になるため据え置き（PLAN.md §1 が既にこの理由を記録済み）。tracing は独立した書き込み専用ログで健全性に無関係と説明済みだが、hyp_insert 等の非公開化は未着手。 |
| 6 | 公開 kernel API を HOL Light `fusion.ml` に揃える | 大枠は既に一致（十規則、同じ命名）。未着手部分は上記の printer/tracing 分離のみ。 |
| 7 | `Surface → CoreExpr → HOL + Rhombus` の共通 IR | **未着手**。`elab.rhm`（HOL 側）と `module_block.rhm`（Rhombus 側）は今も同じソースを別々に読む二経路のまま。 |
| 8 | `match`/`cond`/局所 `def`/入れ子パターンの追加 | **未着手**。現状は `elab.rhm` の `parse_body`/`parse_clause` が「1 引数につき 1 段」の制約を持ち、`terminate.rhm` の `descends_at` も同じ制約に依存しているため、単なる文法追加ではなく決定木コンパイラ相当の設計変更になる。 |
| 11 | fertilization / irrelevance 除去 / induction pool | fertilization と irrelevance 除去は**完了**（本セッション以前）。induction pool は**試みて撤回**。下記参照。 |
| 13 | rule classes | **未着手**（依頼したサブエージェントが基盤モデルの利用上限で失敗、本セッション内では再着手できず）。 |
| 14 | conditional rewriting | **未着手**（同上）。 |
| 15 | hints の拡充（`~cases`/`~expand`/`~in_theory`） | **未着手**（同上）。`~do_not:` は本セッション以前に追加済み。 |

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
即座に全滅した。再試行も同様に失敗したため、本セッションでは induction
pool のみ自分で試みて上記の理由で撤回し、残り 3 項目には着手できなかった。
次にこの作業を再開する際は、まずサブエージェント基盤が使えるか probe
してから並列委譲するか、使えなければ逐次に自分で実装するかを判断すること。
