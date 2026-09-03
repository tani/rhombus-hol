# Rhombus/HOL — 実装状況と再開計画

最終更新: M8 完了（論理コア）。`raco test rhombus-hol/rhombus/hol/tests` → 724 tests passed

---

## 0. 5 分で再開するために

```sh
export PATH="/Applications/Racket v9.3/bin:$PATH"
cd /Users/tani/ghq/git.sr.ht/~tani/rhombus-hol

# 初回のみ
raco pkg install --batch --auto --link rhombus-hol-lib/ rhombus-hol/

# 通常のループ
raco make rhombus-hol-lib/rhombus/hol.rkt        # 言語がコンパイルされるか
raco test rhombus-hol/rhombus/hol/tests           # 全テスト
raco test rhombus-hol/rhombus/hol/tests/kernel.rhm  # 単体
```

`raco make` は `raco test` とは別に CI に入れること。証明は展開時に走るので、
**証明の失敗はテストの失敗ではなくコンパイルの失敗として現れる。**

### Rhombus / shrubbery で繰り返し踏んだ落とし穴

新しくコードを書く前にこれだけは頭に入れておくと時間を大幅に節約できる。

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

---

## 1. 現在の構成

```
rhombus-hol/
├── PLAN.md                       ← このファイル
├── rhombus-hol-lib/              実装（deps: base, rhombus-lib 1.1）
│   ├── info.rkt
│   └── rhombus/
│       ├── hol.rkt               #lang rhombus。言語本体 + reader サブモジュール
│       ├── hol.rhm               #lang rhombus/lang_bridge → "hol.rkt"
│       └── hol/private/
│           ├── names.rhm         論理定数の正準名（eq/imp/conj/…）
│           ├── htype.rhm         型：TyVar / TyApp、subst・match・unify・order
│           ├── term.rhm          項：locally nameless（下記 §2）
│           ├── order.rhm         ACL2 term-order（順序付き書き換え用）
│           ├── printer.rhm       De Bruijn → 名前付き逆変換
│           ├── kernel.rhm        LCF カーネル（信頼境界①）
│           ├── bool.rhm          論理定数の定義 + 3 公理 + base_theory()
│           ├── conv.rhm          変換（equal.ml 相当）
│           ├── drule.rhm         派生規則（bool.ml + drule.ml 相当）
│           ├── datatype.rhm      データ型の公理（信頼境界②）
│           └── module_block.rhm  #%module_block 差し替え（現在は素通し）
└── rhombus-hol/                  ドキュメント + テスト
    ├── info.rkt
    └── rhombus/hol/
        ├── info.rkt, scribblings/rhombus-hol.scrbl（雛形のみ）
        └── tests/                htype term order printer kernel bool conv
                                  drule datatype positivity lang_smoke
                                  lang_meta lang_export
```

### 位相（phase）の設計 — 最重要

証明は**展開時**に走るのでカーネルは phase 1 で動く。しかしカーネル自体は
`meta:` ブロックを一切含まない**通常の `#lang rhombus/static` モジュール**である。
言語層（`hol.rkt` と今後の `decl_*.rhm`）だけが `import: meta: "private/kernel.rhm"`
で位相を 1 ずらして取り込む。

このおかげで:
1. カーネルのテストが素の phase 0 の `.rhm` で書ける（`raco test` がそのまま効く）
2. カーネルが `.zo` に完全コンパイルされる — コンパイル時証明の速度の最大のレバー
3. `import: rhombus/hol/kernel` で phase 0 から証明をスクリプトできる

**この分離を壊さないこと。** 証明器のロジックを `meta:` ブロックの中に書くと (2) が消える。

---

## 2. 項の表現（locally nameless）

```rhombus
class FVar(name :: Symbol, ty :: HType)   // 自由変数：名前を持つ
class BVar(index :: NonnegInt, ty :: HType) // 束縛変数：直近の Abs からの相対位置
class Const(name :: Symbol, ty :: HType)
class Comb(func :: Term, arg :: Term)
class Abs(arg_ty :: HType, body :: Term)  // 束縛変数名を持たない
```

**帰結（新しいコードを書くときの前提）:**

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
  `Abs(num, Comb(p, BVar(0, bool)))` は局所閉で型もすべて宣言済みだが
  `type_of` は `num -> bool` になり、beta 簡約すると型の合わない項が定理に入る。
  `check_open_term` は束縛子の型スタック `env :: List.of(HType)` を引き回して
  `env[i] == ty` を照合する。
- **系統（lineage）は祖先集合で追跡する。** 線形カウンタでは
  **イミュータブル理論の分岐を区別できず、実際に矛盾が導ける**
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


### 書き換え器を書くときの注意（M6 で効いてくる）

De Bruijn 表現では**束縛子の下での書き換え**に注意が要る。
書き換え規則の左辺のパターン変数（`FVar`）が、loose な `BVar` を含む部分項に
束縛されてはならない。実務的な選択肢は 2 つ:

1. **束縛子の下に降りるときは `dest_abs` で開く**（`ABS_CONV` が既にこれを行う）。
   開いてから書き換え、`ABS` で閉じ直す。マッチ側は常に局所閉な項だけを見る。
2. 開かずに降りて、マッチ結果が局所閉であることを検査する。

**推奨は (1)**。`conv.rhm` の `ABS_CONV` が既にその形になっており、
`SUB_CONV` / `DEPTH_CONV` 系はすべてそれを通る。`tmatch.rhm` は
「局所閉な項どうしの一階マッチ」だけを実装すればよい、という前提で書くこと。

---

## 3. 完了済みマイルストーン

| M | 内容 | テスト |
|---|---|---|
| M0 | 言語ペア。`#lang rhombus/hol` が `#lang rhombus` と同一に振る舞い、重量級の `meta:` import が回る | `lang_smoke` `lang_meta` `lang_export` |
| M1 | `htype` `term`（locally nameless）`order` `printer` `names` | `htype` `term` `order` `printer` |
| M2 | カーネル：`Theory` `Stamp`（祖先集合）不可侵 `Thm` 基本 10 規則 + 理論拡張原理 + `import_theorem` | `kernel` |
| M3 | `bool`（Church 流定数 + ETA/SELECT/BOOL_CASES）`conv` `drule` | `bool` `conv` `drule` |
| M4 | `datatype`：正値性チェッカ + 公理スキーマ | `datatype` `positivity` |
| M5 | `terminate`（構造的降下）`recdef`（節形式の再帰定義） | `recdef` |
| M6 | `tmatch` `ruledb` `simp`：一階マッチ、規則 DB、順序付き書き換え | `ruledb` |
| M7 | `goal` `induct` `waterfall` | **`spec_4_1`** |
| M8 | `general`（一般化）`destruct`（デストラクタ除去） | **`spec_4_2`** `destruct` |

共有フィクスチャ `tests/spec_prelude.rhm` が `Nat` / `List` / `Tree` と
`plus` `app` `rev` `length` `size` `flatten` を組み立てる。M5 以降のテストは
すべてこれを使うので、同じ対象について議論している。

### 受け入れ状況

- **仕様書 §4.1**: `app_nil_r` `app_assoc` `rev_app_distr` `rev_involutive`
  すべてカーネル定理として証明済み。誤った予想（`rev(app(xs,ys)) === app(rev(xs),rev(ys))`）は
  residue を出して落ちる。
- **仕様書 §4.2**: `plus_succ` `length_app` `flatten_preserves_size` 証明済み。
  さらに**一般化を入れたことで `plus_succ` 補題なしでも `flatten_preserves_size` が通る**
  — 詰まった算術ゴール `plus(size(y), succ(size(z))) === succ(plus(size(y), size(z)))` の
  `size(y)` `size(z)` を新変数に置き換えると、帰納法が片付けられる形になる。
  これが ACL2 が一般化段を持つ理由そのもの。

### 実装中に見つかった要点

- **規則のパターン変数は「全称量化されていた変数」だけ。** `free_vars(lhs)` を
  使うと、仮定 `app(y, nil) === y` がスキーマとして扱われ `y := cons(x, y)` で
  マッチしてしまう。ゴールが `true` に書き換わる一方、正当化定理は
  **ゴール自身を仮説として抱える**ため、ずっと後の `GEN` で失敗する。
  `ruledb.rhm` の `spec_all_vars` がこれを分けている。
- **名前ベースのヒント（`~induct: xs`）は項からは解決できない。** 束縛子は名前を
  持たないので、`prove` に `~names:` で表層の名前を渡す。閉じた言明を印字すると
  printer が名前を作り直す（`xs` ではなく `x`）のは正常。
- **一般化の候補は適用スパイン全体だけ。** `Comb(f, x)` を素朴に走査すると部分適用
  `app(xs)` まで候補になり、関数型の変数で置き換えて項を壊す。
- **ゴールは節ではなく sequent**（仮定 + 結論）。節は `if` の場合分けが要るように
  なったとき正しい形だが、現段階の 4 段はすべて sequent → sequent で自然に書ける。
  ドライバは `Step` しか見ないので、後から節層を挟める。
- **`max_induction_depth` は 2 に固定**（`waterfall.rhm`）。タクティクごとの
  fuel/timeout は入れない方針。この定数はチューニング用の予算ではなく、
  ドライバを探索ではなく関数にするためのもの — 帰納法は同じ型の新しい変数を
  作るので、上限がないと永遠に帰納法を試し続ける。

## 4. 残りの作業

### R1 — 表層構文層（旧 M5 の後半 + 旧 M6 の一部）

論理コアは完成しているが、**`#lang rhombus/hol` のマクロ層はまだ無い**。
現在テストは phase-0 の API を直接叩いている。残っているのは:

- `private/hexp.rhm` — 中間 AST（`HVar` `HLit` `HApp` `HIf` `HMatch` `HLet` `HCase`）。
  **唯一の意味の源**。
- `private/elab.rhm` — `parse_hexp : Syntax -> HExp`（ホワイトリストの門）と
  `to_term`。表層の `fun` 本体から `recdef.rhm` の `DefClause` を作る。
- `private/emit.rhm` — `to_rhombus : HExp -> Syntax`。型消去して実行可能コードを出す。
- 命題パーサ。`space.enforest` ではなく**手書きの Pratt パーサ**を推奨:
  shrubbery は優先順位を知らずグループを平坦に返すので、命題の文法は固定で小さく、
  80 行程度で書ける。`space.enforest` が買うのはユーザー拡張性で、v0.1 には要らない。
  優先順位は `printer.rhm` の定数（`=== 70 / not 60 / and 50 / or 40 / ==> 30 / <=> 20 / 量化子 10`）に合わせること。
- `private/decl_type.rhm` `decl_fun.rhm` `decl_theorem.rhm` `decl_rules.rhm`。
  `theorem` は **`defn.sequence_macro`**（後続の `proof:` グループを消費）。
  `theorem ~rewrite_rule name:` の属性、`~induct:` は `prove` の `~names:` に
  表層の束縛子名を渡すこと。
- `space.transform hol_rule` + `bridge_definer`（規則の名前引き）。
  雛形は `/Users/tani/Documents/rhombus/rhombus/rhombus/tests/space-lookup.rhm:1-55`。

**着手順の推奨**: `hexp` → `elab`（`to_term` だけ）→ `decl_type`/`decl_fun` →
命題パーサ → `decl_theorem`。`emit` は最後でよい。

### R2 — 測度による停止性（旧 M8 の一部、意図的に未着手）

構造的降下だけを実装した。測度版を入れるには先に 3 つ必要で、それらが揃うまでは
書いても動かせない:

1. **`if` の書き換え規則**（`if true | a | b === a` など）。`cond` は `select` で
   定義されているので、`bool.rhm` に導出定理として足す必要がある。
2. **論理側の順序関係**（`lt`）とその補題。`lt(n, succ(n))` すら帰納法が要る。
3. **`recdef` のパターン制限の緩和**。現在は「構築子でマッチする引数は 1 列だけ・
   1 段だけ」なので、構造的降下では足りないが測度では通る関数が事実上書けない。

義務の生成と Waterfall への流し込み自体は `terminate.rhm` の
`check_termination` と同じ形で書ける。

### R3 — モジュール間の理論伝播（旧 M9）

設計は §6.3（下）のまま。`Thm` 値は位相をまたげないので、マニフェストは
**言明（`Term`）と出自**を持ち、カーネルの `import_theorem` が読み込む。
`Term` を構文として書き出す `to_syntax : Term -> Syntax` が必要。

> **初日にやること**: `module ~splice` 内の引用識別子のスコープ保存を
> 2 モジュールテストで実測する（仮定しない）。`import` 介在が脆いと分かった場合の
> 逃げ道として、明示の `use_theory "a.rhm"` を常設し文書化する。

### R4 — `check_property`（旧 M10）

**コンパイル時ではなく、生成した `module test:` ブロック内で実行時に走らせる。**
性質は生成された実行コードで評価されるべきで、それはコンパイル時には存在しない。
生成器は `type` 宣言から導出、乱数は `rhombus/random` を明示シードで、縮小は型駆動。

### R5 — 性能とドキュメント（旧 M11）

着手順（**まず計測**）:
1. 書き換え内ループ — `ruledb.rhm` の `by_head` 索引はあるが、`key` 事前フィルタは未実装。
2. `check_term` は `REFL`/`ASSUME`/`BETA`/`INST` が毎回呼び、束縛子環境を伸ばしながら
   全域を歩く。検査済み項のメモ化が効くかもしれない（未計測）。
3. 代入と具体化 — 自由変数集合をノードにキャッシュし、触れない部分項は `===` で短絡。
4. 項の等価性 — 構造ハッシュを `Int` でキャッシュ。ハッシュコンスするなら
   `Map.by(===)` を子リストで引くのは**不可**（リストの `===` は要素同一性ではない）。
5. **`Equatable` の罠** — メモ用の private 可変フィールドを足した瞬間に既定の `==` が
   `===` に劣化する（`equatable.scrbl:78-82`）。`Term` の各クラスに
   `Equatable.equals`/`hash_code` を手書きしてから足すこと。
6. ホットパスでは `::` でなく `:~`。
7. 書き換え器では例外ベースの `ORELSEC` を避ける — `conv.rhm` は既に `maybe(Thm)` を
   返す設計。この方針を崩さないこと。

## 5. 表層構文の確定事項（shrubbery で字句検証済み）

| 仕様書 | 採用する綴り | 理由 |
|---|---|---|
| `type List('a)` | `type List(~a)` | `'` は syntax literal の開き括弧で字句解析できない |
| `@rewrite_rule` | `theorem ~rewrite_rule name:` | `@` は at-記法として消え、別グループになる |
| `theorem` + `proof` | `defn.sequence_macro` で後続グループを消費 | 2 つの別グループとして解析される |
| `auto ~induct: xs ~using: [a]` | 単独なら可。複数指定は `auto(~induct: xs, ~using: [a, b])` | 2 つ目の `~kw:` が 1 つ目のブロックに入れ子になる |
| `and` / `or` / `not` | 命題専用の構文空間で定義 | `#lang rhombus` では未束縛なので衝突はしないが、優先順位制御とエラーメッセージのため分離する |

そのまま使えることを確認済み: `a === b`、`p ==> q`、`forall (x :: Ty): P`。

---

## 6. 未解決のリスク

1. **`import` への介在**（M9）が最も未検証。`use_theory` を常設の逃げ道にする。
2. **`module ~splice` 内の引用識別子のスコープ**（M9 初日に実測）。
3. **書き換えの停止性** — タクティクごとの fuel/timeout は入れない方針。
   置換可能規則は `term_order` で下り方向にしか発火しないので発振しないが、
   停止しない書き換え規則をユーザーが登録すると `raco make` が停止しない。
   `mk_rule` の受け入れ条件を強めるのが正しい防ぎ方（fuel ではなく）。
4. **`fun` の上書き** が最もユーザーから見えるリスク。劣化許容規則が安全弁で、
   `fun_opaque.rhm`（M5）が絶対に退行させてはならないテスト。
5. **束縛子の下での書き換え**（§2 末尾）。`ABS_CONV` 経由で開いて閉じる方針を
   `tmatch` / `simp` でも貫くこと。
