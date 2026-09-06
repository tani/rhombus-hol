# Rhombus/HOL — 実装リファレンス

R1〜R5 完了。`raco test rhombus-hol/rhombus/hol/tests` → 921 tests passed。

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
| 証明探索 | `goal` `induct` `waterfall`（簡約・デストラクタ除去・一般化・帰納法の固定パイプライン） | `spec_4_1` |
| 一般化・デストラクタ除去 | `general` `destruct` | `spec_4_2` `destruct` |
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
| `auto ~induct: xs ~using: [a]` | 単独なら可。複数指定は `auto(~induct: xs, ~using: [a, b])` | 2 つ目の `~kw:` が 1 つ目のブロックに入れ子になる |
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
