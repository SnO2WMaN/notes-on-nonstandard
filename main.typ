#import "template.typ": *

#show: project.with(
  title: "超準モデルなどに関するノート",
  authors: ("SnO2WMaN",),
)

#let LangArith = $cal(L)_upright(A)$

#let Model(M) = $frak(#M)$
#let StandardModel = $frak(N)$
#let NonstandardModel = $frak(M)$

#let numeral(t) = $overline(#t)$
#let isomorphic = $tilde.equiv$
#let notIsomorphic = $tilde.equiv.not$

#let IOpenArithmetic = $bold(upright("IOpen"))$
#let IDeltaZeroArithmetic = $bold(upright("I"Δ_0))$
#let PeanoArithmetic = $bold(upright("PA"))$

= 本文

#notation[
  全体を通して，以下とする．
  - $LangArith$ を算術の言語とする．
  - モデル $Model(M)$ とその領域 $|Model(M)|$ を同一視することにする．
  - $T$ を $LangArith$ における一階述語論理の理論とする．
  - 通常の自然数全体の集合を $omega$ とする．
  - $StandardModel$ は算術の標準モデルとする．
]

== 最小値原理

#proposition[最小値原理][
  空でない自然数の部分集合には必ず最小値が存在する．
]

#let LNP(G) = $upright("LNP")(#G)$

#definition[
  $phi(x)$ を $LangArith$-論理式とする．次の論理式は $phi$ に対する最小値原理という．
  $
    exists x. phi(x) -> exists x.[phi(x) and forall y < x. not phi(y)]
  $

  論理式のクラス $Gamma$ に対し，$Gamma$ のすべての論理式に対する最小値原理の集合を $LNP(Gamma)$ と書く．
]

$PeanoArithmetic$ では全ての算術的な論理式に対して最小値原理が成り立つ．

#theorem[
  $PeanoArithmetic vdash LNP(LangArith)$．
]<thm:PA_lnp>


#remark[
  - $#IDeltaZeroArithmetic + LNP(LangArith) vdash PeanoArithmetic$．
  - $IOpenArithmetic vdash LNP(upright("Open"))$．
]

== 超準モデルの基本的な性質

#theorem[
  $T$ が $StandardModel$ をモデルに持つなら，可算濃度の超準モデルを持つ．
]<thm:construct_nonstandard_model>

#proof[
  定数記号 $c$ を新しく $LangArith$ に加えて $LangArith'$ として拡張する．
  任意の $i in omega$ に対し，公理 ${numeral(i) < c | i in omega}$ を $T$ に加えた公理系 $T'$ とする．

  $T'$ が無矛盾である，すなわちモデルを持つことを示す．
  #struct[
    $T'$ の任意の部分集合 $S$ とする．
    このとき，適当な $n in omega$ が存在し，$S subset.eq T union {numeral(i) < c | i <= n}$ で抑えられる．
    $c$ を $n + 1$ として解釈すれば $StandardModel$ は $T union {numeral(i) < c | i <= n}$ のモデルになるので，
    $S$ もモデルを持つ．
    コンパクト性定理より，$T'$ もモデルを持つ．
  ]

  Löwenheim–Skolemの定理より $T'$ は可算無限モデル $Model(M)$ を持つ．
  $T subset.eq T'$ より $Model(M)$ は $T$ のモデルでもある．
  $Model(M)$ は $LangArith'$ 上の構造であるので，$c$ の $Model(M)$ 上の解釈 $c^Model(M)$ がある．
  $Model(M) vDash T'$ より任意の $i in omega$ に対して $(numeral(i))^Model(M) < c^Model(M)$ が成り立つので，
  $StandardModel notIsomorphic Model(M)$，すなわち $Model(M)$ は超準モデルである．
]

#let initSeg = $attach(subset.eq, br: upright("e"))$

#definition[
  $Model(M')$ は $Model(M)$ の部分モデルとする．
  任意の $a in Model(M), b in Model(M) without Model(M')$ に対して $Model(M) vDash a < b$ が成り立つとき，
  $Model(M')$ は $Model(M)$ の始切片 あるいは $Model(M)$ は $Model(M')$ の終拡大といい，$Model(M') initSeg Model(M)$ と書く．
]

次のことは明らか．

#proposition[
  $PeanoArithmetic$ の任意の超準モデル $Model(M)$ に対して $StandardModel initSeg Model(M)$．
]<prop:any_nonstandard_initSeg>

#lemma[菊池8.3.9][
  $Model(M') initSeg Model(M)$ とし，$Delta_0$-論理式 $phi(arrow(x))$，$arrow(a) in Model(M')$ とする．
  このとき，$Model(M') vDash phi(arrow(a)) <==> Model(M) vDash phi(arrow(a))$．
]<lem:equiv_initSeg_delta0>
#proof[
  $phi$ の論理式の構成に関する帰納法．
]

#lemma[菊池8.3.10][@lem:equiv_initSeg_delta0 は$Sigma_1$-論理式でも成り立つ．]<lem:equiv_initSeg_sigma1>

#corollary[
  $T$ は $Pi_1$-公理化可能な理論とする．
  $Model(M) vDash T$ で $Model(M') initSeg Model(M')$ ならば $Model(M') vDash T$．
]

@lem:equiv_initSeg_sigma1 から $PeanoArithmetic$ の $Sigma_1$-完全性が成り立つ．

#theorem[$PeanoArithmetic$ の $Sigma_1$-完全性][
  $phi$ は $Sigma_1$-文とする．
  $StandardModel vDash phi$ ならば $PeanoArithmetic vdash phi$．
]<thm:model_D1>

#proof[
  @thm:construct_nonstandard_model から超準モデル $Model(M)$ が構成出来て，@prop:any_nonstandard_initSeg から $StandardModel initSeg Model(M)$ になる．
  仮定より $StandardModel vDash phi$ なので，これは @lem:equiv_initSeg_sigma1 の条件を満たすので $Model(M) vDash phi$．
  完全性定理より $PeanoArithmetic vdash phi$．
]

#theorem[Overspill][
  $Model(M)$ は $PeanoArithmetic$ の超準モデルとする．
  $Model(M') initSeg Model(M)$ とし，$phi(arrow(x), y)$ は $LangArith$-論理式，$arrow(b) in Model(M)$ とする．
  このとき，任意の $a in Model(M')$ に対して $Model(M) vDash phi(a, arrow(b))$ ならば，
  ある $c in Model(M) without Model(M')$ が存在し，$Model(M) vDash forall x < c. phi(x, arrow(b))$．
]<thm:overspill>

#proof[
  任意の $Model(M)$ の元 $a$ で $Model(M) vDash phi(a, arrow(b))$ なら $Model(M) without Model(M')$ の元を適当に取れば良い．
  そうでないとする．すなわち，$Model(M) vDash not phi(a, arrow(b))$ となる $Model(M)$ の元 $a$ が存在すると仮定する．
  最小値原理より，そのようなものの中で最小である $c$ が存在する．

  前提より $c in Model(M')$ とすると $Model(M) vDash phi(c, arrow(b))$ となっておかしいので，この $c$ は $Model(M')$ の元ではない．
  また，$c$ の最小性より $Model(M) vDash forall x < c. not phi(x, arrow(b))$ が成り立つ．
]

#remark[
  大雑把に言うと，数学的帰納法によって正当化可能な事実を，超準モデル上の適当な無限大元の存在性に還元できるということを意味する．
]

#remark[
  同様に，$IDeltaZeroArithmetic$ では $Delta_0$-論理式に対するoverspillが成り立ち，$IOpenArithmetic$ では開論理式に対するoverspillが成り立つ．
]

ある意味逆方向も成り立つ．

#theorem[Underspill(?)][
  $Model(M)$ は $PeanoArithmetic$ の超準モデルとする．
  $Model(M') initSeg Model(M)$ とし，$phi(arrow(x), y)$ は $LangArith$-論理式，$arrow(b) in Model(M)$ とする．
  このとき，任意の $a in Model(M) without Model(M')$ で $Model(M) vDash phi(a, arrow(b))$ ならば，
  ある $c in Model(M')$ が存在して $Model(M) vDash forall x >= c. phi(x, arrow(b))$．
]

#theorem[
  $Model(M)$ は $PeanoArithmetic$ の超準モデルとし，$Model(M') initSeg Model(M)$ とする．
  $Model(M')$ は $Model(M)$ 上でいかなる $LangArith$-論理式でも定義することは出来ない．
  すなわち，任意の $LangArith$-論理式 $phi(x, arrow(y))$ と任意の $arrow(b) in Model(M)$ に対して $Model(M') != {a in Model(M) | Model(M) vDash phi(a, arrow(b))}$．
]

#remark[
  特に $Model(M')$ を $StandardModel$ とすれば，
  $StandardModel$ は $PeanoArithmetic$ の超準モデルの中では算術の言語でいかなる方法でも定義することが出来ない，ということを意味する．
  同様に，$IDeltaZeroArithmetic$ の超準モデルの中では $StandardModel$ は $Delta_0$-定義可能ではなく，
  $IOpenArithmetic$ の超準モデルの中では $StandardModel$ を開論理式で定義することが出来ない．
]
