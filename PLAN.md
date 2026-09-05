# Rhombus/HOL — 実装状況と再開計画

最終更新: R1〜R4 完了。`raco test rhombus-hol/rhombus/hol/tests` → 814 tests passed

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


### マクロ層を書くときの注意（R1 で判明したこと）

| 症状 | 原因と対処 |
|---|---|
| マクロが返した構文で `def: unbound identifier` | **phase-0 モジュールで作った構文リテラルは、`meta:` import 越しにマクロ出力として使うと束縛を失う。** テンプレートはマクロモジュール（`#lang rhombus/and_meta`）に置くこと。`expand.rhm` / `elab.rhm` は解析だけを担い、生成は `module_block.rhm` が行う。 |
| エラーにファイル・行が出ない | `raise-syntax-error` に渡す構文が**グループ**だとテンプレート側の位置になる。宣言の**先頭の項**（`head_term`）を渡す。 |
| `type: type: ...` と who が二重になる | 捕まえた例外のメッセージは既に `who: ` 前置を持ち、`raise-syntax-error` も付ける。`strip_who` で剥がす。 |
| `$alias.field` がマクロ実行時に評価される | `$` が `alias.field` 全体を取る。`$(alias).field` と括る。 |
| `fun (...): ...` を引数やリスト要素に置くと構文エラー | ブロックが後続を飲む。`(fun (...): ...)` と括る。 |
| `Syntax.make_id` が `maybe(Term)` で落ちる | コンテキストは**項**でなければならない。グループは渡せない。 |
| テンプレート内に `#'sym` が書けない | `'` がテンプレートを閉じる。文字列を使うか、識別子を渡して受け側で `Syntax.unwrap` する。 |
| 生成した名前を別モジュールから参照したい | 衛生的な名前（`id_ctx` 由来）は import 越しに見えない。**ユーザーの宣言の構文をコンテキストにして** `Syntax.make_id` し、`export:` も生成する（生成器・縮小器がこれ）。 |

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
| R1 | 表層構文層。`expand` `elab` `driver` `taut` `module_block` | `lang_state` `decl_type` `decl_fun` `decl_theorem` |
| R3 | モジュール間伝播。通常の `import` が理論を採用する | `import_theory` |
| R4 | `check_property`。`qc` + 型ごとの生成器・縮小器 | `qc` |

共有フィクスチャ `tests/spec_prelude.rhm` が `Nat` / `List` / `Tree` と
`plus` `app` `rev` `length` `size` `flatten` を組み立てる。M5 以降のテストは
すべてこれを使うので、同じ対象について議論している。

### 受け入れ状況（すべて仕様書のソースのまま）

`tests/spec/` の 3 ファイルが仕様書そのもの:
`list_proofs.rhm`（§4.1）、`tree_proofs.rhm`（§4.2、`import` で §4.1 を取り込む）、
`test_run.rhm`（§4.3、素の `#lang rhombus`。`check_property` の生成器/縮小器が
実行時レジストリ経由になったことで、§4.3 の `check_property` も
仕様書どおりこのファイルに直接書けるようになった。以前は「型宣言と同じ
モジュールでしか使えない」という制約のために別ファイル `properties.rhm` に
分けていたが、その制約が無くなったので統合し、`properties.rhm` は削除した）。

### 旧・受け入れ状況

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

R1〜R4 は完了。残るのは R5 のみ。

### R2 — 測度による停止性（完了）

停止性は 2 段構えになった。

1. **辞書式の構造的降下**（`terminate.rhm` の `lexicographic_order`）。
   「どの引数を、どの順で見るか」を貪欲に探す。ある段で使える列は後の段でも使えるので、
   貪欲で完全 — 順序が存在すれば見つかる。単一引数の降下はその 1 要素の特別な場合なので、
   旧来の検査を置き換えている。Ackermann と `merge` がこれで通る。
2. **測度**（`~measure(e)`）。再帰呼び出し 1 つにつき義務 1 つを立て、Waterfall に流す。
   証明できなければ義務と residue を添えたコンパイルエラー。

そのための前提 3 つも入った:

1. **`if`** — `cond` は `select` で定義されているので、`if true | a | b === a` は
   `taut.rhm` で**導出**した（選択公理をその条件式自身の述語で具体化し、残った連言から
   等式を取り出す）。新しい公理は増えていない。表層は Rhombus と同じ綴り
   （`#true` / `!` / `&&` / `||` / `==` / `if`）で、本体はそのまま実行コードとして
   出力されるので、綴りが一致していなければ 2 つの読みがずれる。
   命題と式のパーサは 1 つの優先順位パーサの 2 モードに統合した。
2. **順序関係** — `lt` を手書きするのではなく、再帰的なデータ型 1 つにつき構造的部分項関係
   `T_lt` を自動生成する（`subterm.rhm`）。`Nat` に対してはそれがちょうど `<`。
   通常の節形式の定義として `install_function` を通るので、新しい公理は増えない。
   整礎性はそのデータ型自身の帰納法公理そのもの — これが「測度は宣言済みデータ型に
   着地しなければならない」理由。
3. **パターン行列** — `match` の入れ子を平坦化し、被覆検査を「列で分割し、その型の
   構築子をちょうど 1 回ずつ要求し、各枝に再帰する」形に一般化した。
   分割する列は左から順ではなく**探索**する（`match n` が外側で `match m` が内側の
   場合、きれいに割れるのは 2 列目が先）。

**仮説の簡約**（`simp.rhm` の `simplify_asms`）も必要だった。仮説はこれまで結論を
書き換える規則でしかなく、`not nul(zero)` のような仮説では何も起きない
（規則としては出現しない語句を書き換える）。簡約すれば `false` になり、結論が何であれ
ゴールは閉じる。ガード付き再帰は 1 義務につき分岐条件 1 つ、そのほとんどが矛盾、
という形をしているので、測度はこれに依存している。

### R3 の作り直し — マニフェスト → 値渡し → 通常の `import`

**第 1 段: 前提が誤りだった。** 当初は「`Thm` はモジュール境界を越えられない」という
前提で、宣言の**記述**を `hol_manifest` サブモジュールに publish し、importer 側で
replay していた。実際には越えられる。これで `emit_manifest` / `manifest_item` /
`replay` / `replay_theorem` / `import_theorem` / `trusted_imports` が全部消え、
**トラスト境界そのものが消えた**。推移性の欠如と、手書きマニフェストによる偽造
（実際に偽の定理を通せることを確認した）も同時に直った。

**第 2 段: `use_theory` を廃止し、通常の `import` に統合した。**

理論は `hol_theory` サブモジュール（`~lang rhombus`、phase 0）が持つ。値の export を
やめたのは、`_hol_theory` がどの理論でも同じ名前で、`open` を 2 つ書くと衝突するから。
サブモジュールはパスで辿るので `open` と無関係になり、**ユーザーの `import` 節に一切
手を触れずに済む** — これが `import` に載せられた理由。

`~lang` 付きサブモジュールは本体より先に定義されるので、モジュール自身が
`import: meta: self!hol_theory` で取り込める。これで証明はコンパイル時に走る。

検出は推測ではなく照会: `Evaluator.module_is_declared(<path>!hol_theory, ~load: #true)`。
理論でないモジュールの import は素通し。1 つの `import` に両方混ざっていてもよい。

パスの取り出しは「節の接頭辞のうち `ModulePath.maybe` が通る最長のもの」。修飾子名の
リストを持たずに済むので、Rhombus の import 文法への結合が最小になる。
読めない形（`import: meta: "a.rhm"` のようにパスがブロックの中にあるもの）は
**黙って落とさずエラーにする**。

実装上の罠を 2 つ踏んだ:

1. `expand.rhm`（phase-0 ヘルパ）で組んだ `'$t ...'` グループは、phase-1 マクロから
   出ていくときに束縛を失う。パスは**項のリスト**で返し、`module_block.rhm` で組み直す。
2. それでも足りない。サブモジュールの言語は素の `rhombus` なので、ユーザーの
   `rhombus/hol` コンテキストを持つ項はそこで暗黙の import 形（文字列に対する
   `#%literal`）に届かない。`Syntax.make(Syntax.unwrap(t), id_ctx)` で組み直す。
   モジュールパスに必要なのは datum だけなので失うものはない。

副産物: 仕様書 §4.2 が `import:` をそのまま書けるようになり、仕様との綴りの差が 1 つ減った。

### R5 — 性能（ドキュメントは完了）

クリーンビルドからの全テストが 3 分 37 秒（870 tests）。証明は展開時に走るので、
この大半は `raco make` の時間である。着手順（**まず計測**）:

1. 書き換え内ループ — `ruledb.rhm` の `by_head` 索引はあるが `key` 事前フィルタは未実装。
2. `check_term` は `REFL`/`ASSUME`/`BETA`/`INST` が毎回呼び、束縛子環境を伸ばしながら
   項全域を歩く。検査済み項のメモ化が効くかもしれない（未計測）。
3. 代入と具体化 — 自由変数集合をノードにキャッシュし、触れない部分項は `===` で短絡。
4. 項の等価性 — 構造ハッシュを `Int` でキャッシュ。ハッシュコンスするなら
   `Map.by(===)` を子リストで引くのは**不可**（リストの `===` は要素同一性ではない）。
5. **`Equatable` の罠** — メモ用の private 可変フィールドを足した瞬間に既定の `==` が
   `===` に劣化する（`equatable.scrbl:78-82`）。`Term` の各クラスに
   `Equatable.equals`/`hash_code` を手書きしてから足すこと。
6. ホットパスでは `::` でなく `:~`。
7. 書き換え器では例外ベースの `ORELSEC` を避ける — `conv.rhm` は既に `maybe(Thm)` を
   返す設計。この方針を崩さないこと。

### 付録 — `idris-kernel/`（検証専用ツールとして共存、ランタイムには不接続）

`htype.rhm` / `term.rhm` / `kernel.rhm` を Idris2 に移植し、Racket バックエンド
（`idris2 --cg racket`）でコンパイルしたもの。詳細は `idris-kernel/README.md`。

**`kernel.rhm` は 100% ネイティブ Rhombus のまま** — これが今も
Rhombus/HOL が実際に走らせる信頼境界であり、`raco make` / `raco test` は
このディレクトリを一切参照しない。このディレクトリの役割は、同じカーネル
ロジックの性質を Idris2 の依存型で独立に証明すること。`raco make` とは
別スケジュールで（`idris2 --build kernel.ipkg` を手動 / CI などで）検証する。

**カーネルの十原始規則すべてについて、「出力する定理が整形式である」ことを
証明済み。** `idris2 --cg racket --build kernel.ipkg` で機械検証、`:metavars`
で未解決ホールが無いことも確認済み。**公理はゼロ**
（`grep believe_me src/*.idr` が空）。すべて通常の構造的帰納法。

**公理がゼロな理由 — 名前を `String` ではなく帰納型にした。** `String` は
コンストラクタを持たないプリミティブなので、抽象的な `x`,`y` について
`x = y` を作る手段は `believe_me` による強制変換しかない（base の
`DecEq String` も同じ実装なので、乗り換えても公理が標準ライブラリへ移るだけ）。
`src/Name.idr` の
`data Name = NFun | NBool | NEq | NAlpha | NUser Nat`
なら `nameEqRefl`/`nameEqSound` がただの帰納法で証明でき、
`htypeEqSound`/`termEqSound` 等もそこから導出できる。正準名 4 つは
カーネルが特別扱いする名前（`names.rhm` と同じ設計）で、ユーザー宣言は
`NUser Nat` — Rhombus の `Symbol` の等価性は文字列比較ではなく
インターンされた同一性なので、こちらの方がむしろ忠実。`Stamp` の識別子も
同じ理由で `Nat` にした。Rhombus へ再接続する場合は境界で
`Symbol`→`Nat` のインターンを行えばよい。

| 規則 | 定理 | 要となる補題 |
|---|---|---|
| `REFL` | `reflWellFormed` | `mkEqCheckSound` |
| `ASSUME` | `assumeWellFormed` | 結論が検査済みの項そのもの |
| `BETA` | `betaWellFormed` | 下記の主辞保存3点セット |
| `TRANS` | `transWellFormed` | 整形式な等式の両辺は整形式 |
| `EQ_MP` | `eqMpWellFormed` | 結論は等式の右辺 |
| `DEDUCT_ANTISYM_RULE` | `deductAntisymWellFormed` | 両辺は入力の結論そのもの |
| `MK_COMB` | `mkCombWellFormed` | `eqOperandTypes`（`typeMatch` の逆転） |
| `ABS` | `absWellFormed` | `abstractAtCheck`（代入の逆向き） |
| `INST` | `instWellFormed` | `instFvarGoCheck` |
| `INST_TYPE` | `instTypeWellFormed` | `instTypeGoCheck` + `typeMatchSubst` |

土台となる主な定理:

- **系譜**: `combineStampsSound` — `combine_stamps` が選ぶスタンプは両方の
  入力から到達可能。`kernel.rhm` の「後の方を採る」戦略が健全である根拠。
- **型安全性**: `checkTermTypeOfSound`（整形式な項は必ず型を持つ）、
  `typeOfWellFormed`（その型自身も理論の中で整形式）。
- **BETA の主辞保存（3点セット）**: `betaTypeSound`（型が変わらない）、
  `betaClosedSound`（宙に浮いた de Bruijn 添字が生じない）、
  `betaCheckSound`（簡約結果も `checkTerm` を通る）。束縛子の下へ潜る
  一般化代入補題（`substAtTypeSound` / `substShiftClosed` /
  `substAtCheckSound`）に支えられ、後者はさらに `checkWeakenRight`（弱化）
  と `checkClosed` を使う。`shiftClosedId`（閉じた項に対する `shift` は
  恒等）のおかげで `shift` の `Integer` 添字演算に関する推論は一切不要。
- **理論拡張の単調性**: `newTypeMonotone` / `newConstantMonotone`。
  `in_theory`/`descends` が意味を持つための前提そのもの。
- **理論の整形式性と等式構築**: `WellFormedTheory`（`fun` は 2 引数、
  `bool` は 0 引数、`eq` は `'a -> 'a -> bool`）、`initialTheoryWellFormed`、
  `mkEqCheckSound`。
- **仮説リストの操作**: `hypInsertChecked` / `hypUnionChecked` /
  `hypRemoveChecked` / `rehashChecked`。

**証明していない・できないもの**: 論理の**無矛盾性**（公理と規則から偽が
導けないこと）は構文ではなくモデルについての主張なので、この移植で述べられる
種類の命題ではない。理論拡張原理の**保存拡大性**も同様に意味論的性質で、
ここで証明したのはカーネルが依拠する構文的な半分（単調性）だけ。

**停止性は証明済み**: 全モジュールが `%default total`。Idris2 は網羅性と
停止性の両方を検査し、`total` な関数は `total` な関数しか呼べないので、
性質は基底ライブラリまで下向きに閉じている。したがって十規則の
`*WellFormed` は部分正当性ではなく全正当性の主張になる。LCF カーネルは
本質的に構造再帰しか使わない（不動点反復も新名探索ループも無い。`variant`
に相当するものは locally nameless 表現によって不要）ので、これは難しく
なかった。唯一引っかかったのは `termOrd` で、`case (a, b) of` とタプルで
分岐していたためサイズ変化解析が構造的降下を見失っていた。二引数を直接
パターンマッチする形に書き直すだけで通る。詳細は
`idris-kernel/README.md` の「Termination」節。

**経緯 — なぜランタイムに接続しなかったか:** 以前のイテレーションでは
十原始規則すべてを実際に `kernel.rhm` から Idris 実装(生成した Racket
モジュール経由)へ委譲していた。動作はした — 872 件全テスト通過 — が:

- クリーンビルド込みの全テストが 3 分 52 秒(ネイティブ)→ 約5分
  (Idris 経由)と、約 30% の実測回帰があった。
- 原因は呼び出し回数に比例するコストではなく、生成 Racket モジュールを
  `raco test` の各サブプロセスごとに読み込み・初期化する固定コストが
  支配的だと判明(`libidris2_support.so` の FFI 依存を完全に除去しても
  改善は誤差の範囲内だった)。

同じロジックを2言語で毎回実行し直すランタイムコストに見合うだけの価値は
なく、「1つの権威ある実装について性質を証明し、実行コストゼロでチェック
できる」方が価値が高いと判断し、現在の設計(検証専用・共存)に変更した。
詳細と技術的な学び(idris2 の到達可能性ベースの codegen、`libify.py`、
停止性検査の落とし穴など)は `idris-kernel/README.md` に集約。

### ドキュメント（完了）

`rhombus-hol/rhombus/hol/scribblings/` に multi-page で 6 章:

| ファイル | 内容 |
|---|---|
| `rhombus-hol.scrbl` | 表紙・`docmodule(~lang, rhombus/hol)`・目次 |
| `overview.scrbl` | 1 つの宣言の 2 つの読み・いつ何が起きるか・完全な例・`fun` は横取りしない |
| `declarations.scrbl` | 全 10 形式のリファレンス |
| `grammar.scrbl` | 型・式・命題の文法と優先順位表 |
| `termination.scrbl` | 辞書式構造的降下・測度・部分項関係・未対応のもの |
| `prover.scrbl` | Waterfall の 4 段・失敗したときの読み方・正当化の合成 |
| `trust.scrbl` | カーネル・3 公理・公準化しているもの・**漏れているところ** |

ビルドは `raco setup --pkgs rhombus-hol`（`doc/` は .gitignore 済み）。

**掲載したコード例と residue はすべて実際にコンパイルして確認した。**
最初に書いた residue は想像で書いたもので、実物と違っていた（変数名も分岐も）。
文書のたぐいは実行して確かめること。

**既知の欠点（`check_property` は解消、他は未解消）: `@doc` ブロックが
使えていない。** `type` / `function` / `theorem` などは `#%module_block` が
本体を走査して認識しているだけで、束縛ではない。`@doc` は for-label 束縛を
要求するので、これらを索引付きの項目として書けず、`@verbatim` の文法表示 +
`@section` で代用している。検索性が落ちる。同じ理由でユーザー自身のマクロの
展開結果としてこれらの形式を使うこともできない（`#%module_block` は展開前の
生の構文を綴りで照合するので、マクロの呼び出しそのものしか見えない）。

`check_property` だけは実際に束縛された `defn.macro` として再実装した
（`module_block.rhm`）。`driver.rhm` に対応する状態遷移が一切無い
（`HolState` を読みも書きもしない）唯一の形式だったので、状態糸通しの仕組みに
一切触れずに済んだ。これにより:

- `@doc(defn.macro 'check_property ...')` で文書化できる（未着手、次の一手）。
- ユーザー自身のマクロが展開結果として `check_property` を生成できる
  （`tests/fixtures/check_property_composed.rhm` で固定）。

移行で 1 つ罠を踏んだ（当時の記録。**この節の仕組み自体は下の「実行時
レジストリ」節で置き換え済み**）: `gen_id`/`shrink_id`（`_hol_gen_Foo`/
`_hol_shrink_Foo`）は非衛生的識別子で、「構築に使う context 構文オブジェクト
がユーザー自身の書いたトークンであること」に依存していた。旧設計では
`check_property` の発行が `module_block` **自身の 1 回の展開**の一部だった
ので、`head_term(d.form)`（`check_property` という**リテラル語**）を
context に使っても、`type` 側の定義（同じく `module_block` の展開由来）と
同じ扱いになっていた。`check_property` を**別の**マクロ展開に切り出すと、
その リテラル語は「このマクロ定義自身が書いたテンプレート語」になり、
`type` 側の定義とは違う導入スコープを持つ ── 綴りは同じでも別の束縛になる。
その場しのぎの直しは、context に `check_property` という語ではなく、
性質の名前（`$rest` から捕捉した、正真正銘ユーザーが書いたトークン）を
使うことだった。

#### 生成器・縮小器を非衛生的識別子から実行時レジストリへ（密結合 → 疎結合）

上の「その場しのぎの直し」は、依然として `check_property` と `type` の間に
**命名規則という暗黙の契約**を残していた。加えて、`type` は
`gen_id(at, Syntax.unwrap(name))` の識別子をわざわざ `export:` していた
（他モジュールの `check_property` が参照できるように）。これを、
`qc.rhm` に持たせた実行時レジストリに置き換えた:

```rhombus
fun register_gen(name :: String, build :: Function) :: Void
fun register_shrink(name :: String, shrink :: Function) :: Void
fun lookup_gen(name :: String) :: Function
fun lookup_shrink(name :: String) :: Function
```

`type` は生成器・縮小器を `_hol_gen_Foo` という**当てずっぽうの名前**で
束縛する代わりに、モジュールが実行されたときに
`_hol_qc.register_gen("Foo", fun (...): ...)` と**明示的に登録**する。
`check_property` は `Syntax.make_id` を一切使わず、
`_hol_qc.lookup_gen("Foo")` を呼ぶだけになった。

これは property check が**実行時**に走る（コンパイル時に評価すると
定義の二重実装になるので意図的にそうなっている）という既存の設計を
利用している ── `HolState` の糸通し（コンパイル時 = phase 1、マクロ間で
共有できないと確認済み）とは別の制約空間なので、可変マップで問題なく
共有できる。

得られたもの:

- **非衛生的識別子の脆さが消えた。** コンテキスト構文オブジェクトの
  選択ミスというクラスのバグ（上で踏んだ罠）が構造的に無くなった。
  `gen_id`/`shrink_id`/`ctx` 引数は全て削除。
- **`check_property` が型の宣言モジュールを `import: ... open` する必要すら
  無くなった。** 生成器の解決は実行時の名前引きなので、宣言モジュールが
  **推移的に**（別の import 経由で間接的に）取り込まれてさえいれば、
  直接 import していなくても解決できることを実測で確認した。
  §4.3 の `check_property`（`tests/spec/properties.rhm` に分離していたもの）
  はこれにより仕様書どおり `test_run.rhm`（素の `#lang rhombus`）に直接
  書けるようになったので、統合して `properties.rhm` を削除した。
- **拡張性。** `rhombus/hol` の `type` 以外の任意の Rhombus 型にも、
  誰かが `_hol_qc.register_gen(...)` すれば `check_property` から使える
  （今回は未検証・未使用だが、経路としては開いている）。

トレードオフ: 「型に生成器が無い」が実行時エラーになる
（`error(~who: #'check_property, "no generator registered for this type", ...)`）。
コンパイル時に検出したいなら、`check_property` 展開時に
「その型に対応する `type` 宣言が事前に処理されたか」を確認するチェックが
別途要るが、それは静的な話であって、レジストリの疎結合設計とは独立の話。
未着手。

**`type`/`function`/`theorem`/`disable_rules`/`enable_rules`/`declare`/`expect`
は依然としてスキャン方式のまま。** これらは `driver.rhm` の `HolState` を
読み書きするので、束縛だけの独立マクロにするには「連番カウンタなしで
宣言間の状態をどう糸通しするか」を解かねばならず、これは**実測で不成立と
確認済み**（詳細は次項）。`check_property` が「たまたま状態を持たない
唯一の形式」だったから解けた話であり、他の形式には**そのまま**は適用できない。

#### 状態糸通しの独立マクロ化を試して、成立しないと確認した設計（記録）

「可変ボックス + `~lang` なしサブモジュールの合流」で連番カウンタを廃止する
案を実測した。3 つとも、Rhombus の実機で不成立だった:

1. **`~lang` なし（または `~splice ~lang`）のサブモジュールは、複数の
   独立したマクロ展開から同名で断片を出すと最終的な出現順で 1 つに
   合流する**（`module.scrbl` の記述どおりで、これ自体は成立する）。
   しかし**この合流後のサブモジュールは、囲みモジュール自身からは
   import できない**（`self!id` で "syntax-local-module-exports: unknown
   module" になる ── ドキュメントの「`~lang` が無ければ囲みモジュールは
   サブモジュールを import できない、循環になるから」という記述どおり）。
   `~splice ~lang` も同じ理由で同じエラーになることを実測した
   （late-expanding な形はどれも同じ壁に当たる）。
   囲みモジュール自身から強制 visit できなければ、`raco make` の間に
   証明を走らせる仕組みが成立しない。
2. **`meta:`（ブロック形式）はマクロ自身の展開結果の中では使えない**
   （"meta: misuse as an expression; allowed only in a non-nested
   declaration context"）。これは `meta def`（定義形式）とは別物 ──
   `meta def` は今の設計で実際に機能している（マクロ展開結果に含めても
   問題ない）が、可変ボックスへの逐次代入をマクロ展開の中に書く手段が
   無いことを意味する。
3. **`meta def` の同名再定義（シャドーイングでの糸通し）は不可**
   （"identifier already defined"）。カウンタなしで「今の状態」を
   参照し続ける手段が、結局どこにも残らない。

（参考までに、"`raco make` は対象モジュール自身を instantiate しない
（run しない）" ことも実測で確認した ── ただの実行時可変状態に逃げても
`raco make` の間に証明の失敗を検出できない。だからこそ現行設計は
`meta def` で phase 1 に状態を置いている。）

残る道は「マクロ定義モジュール自身が持つ、囲みモジュールの識別子で
キーイングした可変ハッシュ」のような、より低レベルでリスクの高い手法
（この文書の初期の設計メモが最初から避けていたもの）で、これは
確認していない。**現実的な結論: `check_property` 以外の形式を、
状態糸通しをやめて独立マクロにする道は今のところ無い。**
これらの形式を `@doc` で文書化するだけなら、`#%module_block` の外では
「ここでは使えません」というエラーを出すだけの薄い `defn.macro` を
束縛するという最小案が残っている（未着手）。

### v0.1 で残っている制限（文書化すべきもの）

- `type` / `function` / `theorem` は `#%module_block` が認識する形式なので、ユーザー定義
  マクロの中や `block:` の中には書けない。`check_property` だけは例外
  （実マクロなので両方できる。上の「既知の欠点」節を参照）。
- `function` の本体は `match` / `if` / 変数 / 名前付き適用 / Boolean 演算子
  （`!` `&&` `||` `==`）と `#true` / `#false` のみ。`let` / 算術 / リテラルは文法外で、
  **コンパイルエラー**になる（違反した式を名指しする）。
- `match` の入れ子は 1 引数につき 1 段。同じ列を 2 度マッチすることはできず、
  節に順序はない（ワイルドカード節は書けない）。構築子パターンの入れ子（`succ(succ(k))`）
  も不可 — この版の帰納法スキームが構築子 1 段しか追えないため。
- 測度は宣言済みデータ型に着地しなければならない（`T_lt` があるのはそこだけ）。
  入れ子再帰（再帰呼び出しの引数の中の再帰呼び出し）に対しては義務を立てられない。
- 辞書式の構造的降下が成立する定義では `~measure` は**検査されない**。
  構造的降下だけで停止性の議論は完結しているので健全性の問題はないが、
  誤った測度を書いても黙って通る。
- 理論の取り込みは通常の `import`。専用の形式は無い。
- 理論の `import` は**自分の宣言より前**に、複数あるなら**依存順**に書く。採用は
  「入ってくる理論が今の理論の拡張であること」が条件（`descends` 1 回）。
- パスがブロックの中にある import（`import: meta: "a.rhm"`）は読めないのでエラー。
- **兄弟理論は合流できない。** どちらも他方の拡張でない 2 つの理論を 1 モジュールで
  使うことはできない。必要になったら theory merge を書く必要がある（今は無い）。
- importer のコンパイルは提供側モジュールを visit するので、**提供側の証明が
  importer ごとに再実行される**。現状 1 モジュールあたり約 1 秒。
- `check_property` の量化変数は具体型でなければならない（型変数の生成器は作れない）。
  本体は実行可能な任意の Rhombus Boolean 式。

## 5. 表層構文の確定事項（shrubbery で字句検証済み）

| 仕様書 | 採用する綴り | 理由 |
|---|---|---|
| `type List('a)` | `type List(~a)` | `'` は syntax literal の開き括弧で字句解析できない |
| `@rewrite_rule` | `theorem ~rewrite_rule name:` | `@` は at-記法として消え、別グループになる |
| `theorem` + `proof` | `expand.rhm` が本体走査で 1 段先読み | 2 つの別グループとして解析される。`defn.sequence_macro` で同じことを独立マクロとして書けることは実測で確認済み（§4「実マクロとして再実装する」参照）だが、`theorem` 自体は `HolState` を糸通す側なので、その独立マクロ化自体が今のところ不成立 |
| `auto ~induct: xs ~using: [a]` | 単独なら可。複数指定は `auto(~induct: xs, ~using: [a, b])` | 2 つ目の `~kw:` が 1 つ目のブロックに入れ子になる |
| `fun app(...)` | `function app(...)` | 通常の Rhombus `fun` と衝突させない。`function` は `rhombus` で未束縛 |
| `and` / `or` / `not` | 命題専用の構文空間で定義 | `#lang rhombus` では未束縛なので衝突はしないが、優先順位制御とエラーメッセージのため分離する |

そのまま使えることを確認済み: `a === b`、`p ==> q`、`forall (x :: Ty): P`。

---

## 6. 未解決のリスク

1. **`import` の認識**は既知の修飾子リストを持たない（最長接頭辞方式）が、
   Rhombus の import 文法が変わればここが影響を受けうる。読めない形はエラーにしてある。
2. ~~**`module ~splice` 内の引用識別子のスコープ**~~ — この版の実装は `~splice` を
   どこでも使っていない（`grep` で確認済み）。R3 の作り直しで `hol_theory`
   サブモジュールは常時プレーンな `module ... ~lang rhombus:` で、複数箇所からの
   合流も試みていない（試して不成立と確認したのは別の設計、§4 参照）。この項目は
   古い記録で、今のコードには対応する懸念が存在しない。
3. **書き換えの停止性** — タクティクごとの fuel/timeout は入れない方針。
   置換可能規則は `term_order` で下り方向にしか発火しないので発振しないが、
   `mk_rule` は「変数だけの左辺」「右辺の未束縛変数・型変数」「自明な等式」しか
   弾かない。`f(x) === g(f(x))` のような非対称かつ非停止な規則は**現状のまま
   通ってしまい**、`TOP_DEPTH_CONV` が無限に書き換え続けて `raco make` が
   停止しなくなる。実際に確認していない（意図的に踏んでいない）が、
   `mk_rule` のコードを読む限り防御が無いことは確認済み。
   `mk_rule` の受け入れ条件を強めるのが正しい防ぎ方（fuel ではなく）— 未着手。
4. ~~**`fun` の上書き**~~ — 解消。論理定義は `function` という別のキーワードになり、
   通常の Rhombus `fun` には一切介入しない。したがって「文法外なら素通し」という
   劣化許容規則も不要になり、`function` の文法違反は違反式を名指しするエラーになる
   （`decl_fun.rhm` の `no_result_type` / `bad_body` が固定している）。
5. ~~**束縛子の下での書き換え**~~ — 解消。`conv.rhm` の `SUB_CONV` が `Abs` に対して
   `ABS_CONV` を呼ぶので、`TOP_DEPTH_CONV`（`simp_conv` が使う）は束縛子の中も
   自然に降りる。`tmatch.rhm` の `term_match` も束縛変数捕獲を depth 引数で
   チェック済み（`tests/conv.rhm` の `ABS_CONV` テストで固定）。

## 7. 参照したソフトウェア

この実装を作る際に参照したもの。「設計を参考にした」ものと、
「このチャットで実際にソースコード／ドキュメントを読んだ」ものは性質が違うので分けて書く。

### このチャットで実際にソースコード・ドキュメントを開いて読んだもの

- **Rhombus（言語本体）**
  - ドキュメント一式: `/Users/tani/Documents/rhombus/rhombus/rhombus/scribblings/`
    以下の多数のファイル。特に頻繁に参照したもの:
    `reference/module.scrbl`（サブモジュールの合流・`~lang`/`~splice`/`~early`/`~late`
    の意味論）、`meta/defn-macro.scrbl`（`defn.macro`/`defn.sequence_macro`）、
    `meta/macro-more.scrbl`、`meta/expr-macro.scrbl`（`expr_meta.Parsed` など）、
    `meta/bind-macro.scrbl`、`meta/annotation-macro.scrbl`、`meta/lang.scrbl`、
    `meta/rhombus-meta.scrbl`、`reference/import.scrbl`（`ModulePath`/`ModulePath.maybe`）、
    `reference/check.scrbl`、`reference/box.scrbl`（`Box`/`.value`/`:=`）、
    `reference/symbol.scrbl`、`reference/equatable.scrbl`、`reference/eval.scrbl`
    （`Evaluator.module_is_declared` など）、`reference/syntax-class.scrbl`、
    `guide/module-basics.scrbl`。
  - 実装ソース: `/Applications/Racket v9.3/share/pkgs/rhombus-lib/rhombus/private/amalgam/`
    以下。特に `check.rhm`（`check` フォームの実装 — `theorem`/`proof:` の
    「後続節を任意で取り込む」設計の比較対象にした）、`defn-macro.rkt`、
    `sequence_meta.rhm`、`sequence-help.rkt`、`guard.rhm`、`closeable.rhm`。
  - Rhombus/HOL の `use_theory` を通常の `import` に統合する設計と、
    宣言形式を実マクロに再実装できるかの検討（本セッションの後半）は、
    上記のドキュメント・ソースを実際に `grep`/`Read` し、かつ実機で
    コンパイル・実行して確かめながら進めた。
- **Racket（Rhombus の実行基盤）** — `lib("racket/base.rkt")` 経由で
  `raise-syntax-error` などを直接呼んでいる（`driver.rhm`）。処理系自体は
  `/Applications/Racket v9.3/` にインストールされたものを実行確認に使い続けた
  （バージョン固定: v9.3）。

### 設計の参考にした（このチャットでソースは見ていない、既存の公表された設計として）

- **HOL Light** — カーネルの十個の基本推論規則、locally nameless の項表現、
  等式変換（`conv.rhm` は `equal.ml` の設計を踏襲）、型の表現
  （型変数と型構成子の適用の 2 構成子）。コードコメントに散在して明記済み
  （`kernel.rhm`、`conv.rhm`、`htype.rhm`、`printer.rhm` など）。
- **HOL4** — 論理定数の定義のしかたと、3 つの公理（ETA・SELECT・BOOL_CASES）の
  選び方（HOL Light 式の `INFINITY_AX` を経由しない構成）。`bool.rhm` に明記済み。
- **ACL2** — Waterfall（簡約・デストラクタ除去・一般化・帰納法の固定パイプライン）
  の設計、置換可能な書き換え規則を発振させないための項順序（`order.rhm`）、
  規則データベースが新しい規則を優先する順序（`ruledb.rhm`）。
  複数のファイルのコメントに明記済み。
- **QuickCheck**（の系譜のプロパティベーステスト全般） — `check_property` /
  `qc.rhm` の設計（生成・収縮・反例の最小化）は QuickCheck の系譜の標準的な
  仕組みを踏襲しているが、具体的な実装（Haskell 版・その他言語版いずれも）の
  ソースコードを本セッションで直接参照したことはない。
