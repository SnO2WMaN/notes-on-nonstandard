#import "template.typ": *

#show: project.with(
  title: "算術の超準モデルなどに関するノート",
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

#let Nat = $NN$

= はじめに

算術の超準モデルの性質，およびTennenbaumの定理(@thm:Tennenbaum)についてのメモ．

= 本文

#notation[
  全体を通して，以下とする．
  - $LangArith$ を算術の言語とする．
  - モデル $Model(M)$ とその領域 $|Model(M)|$ を同一視することにする．
  - $T$ を $LangArith$ における一階述語論理の理論とする．
  - 通常の自然数全体の集合を $Nat$ とする．
  - $StandardModel$ は算術の標準モデルとする．
  - 自然数 $n$ とその数項 $numeral(n)$ は適当に同一視する．
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
  任意の $i in Nat$ に対し，公理 ${i < c | i in Nat}$ を $T$ に加えた公理系 $T'$ とする．

  $T'$ が無矛盾である，すなわちモデルを持つことを示す．
  #struct[
    $T'$ の任意の部分集合 $S$ とする．
    このとき，適当な $n in Nat$ が存在し，$S subset.eq T union {i < c | i <= n}$ で抑えられる．
    $c$ を $n + 1$ として解釈すれば $StandardModel$ は $T union {i < c | i <= n}$ のモデルになるので，
    $S$ もモデルを持つ．
    コンパクト性定理より，$T'$ もモデルを持つ．
  ]

  Löwenheim–Skolemの定理より $T'$ は可算無限モデル $Model(M)$ を持つ．
  $T subset.eq T'$ より $Model(M)$ は $T$ のモデルでもある．
  $Model(M)$ は $LangArith'$ 上の構造であるので，$c$ の $Model(M)$ 上の解釈 $c^Model(M)$ がある．
  $Model(M) vDash T'$ より任意の $i in Nat$ に対して $(i)^Model(M) < c^Model(M)$ が成り立つので，
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

次の定理は適当な性質を満たす超準元の存在を示すためによく使う．

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
  $Model(M')$ を $StandardModel$ として大雑把に直感を述べると，$PeanoArithmetic$ で数学的帰納法によって正当化可能な事実を，超準モデル上の適当な超準元の存在性に還元できるということを意味する．
]

#remark[
  同様に，$IDeltaZeroArithmetic$ では $Delta_0$-論理式に対するoverspillが成り立ち，$IOpenArithmetic$ では開論理式に対するoverspillが成り立つ．
] <rem:overspill_weaker>

ある意味逆方向も成り立つ．

#theorem[Underspill(?)][
  $Model(M)$ は $PeanoArithmetic$ の超準モデルとする．
  $Model(M') initSeg Model(M)$ とし，$phi(arrow(x), y)$ は $LangArith$-論理式，$arrow(b) in Model(M)$ とする．
  このとき，任意の $a in Model(M) without Model(M')$ で $Model(M) vDash phi(a, arrow(b))$ ならば，
  ある $c in Model(M')$ が存在して $Model(M) vDash forall x >= c. phi(x, arrow(b))$．
]

Overspillから次のことが一般に成り立つ（証明不明）．

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

== Tennenbaumの定理

#definition[
  再帰的可算集合 $A, B$ が再帰的分離不能とは，次を満たすこととする．
  1. $A sect B = emptyset$．
  2. $A subset.eq C$ かつ $C sect B = emptyset$ となる再帰的な $C$ は存在しない．
  特に2の $C$ を分離集合という．
]

#let recPlus = $plus.circle$
#let recTimes = $times.circle$
#let recLE = $triangle.l$

#definition[
  $LangArith$ の可算モデル $Model(M)$ が $angle.l NN; n_0, n_1; recPlus, recTimes; recLE angle.r$ と同型であるとき，$Model(M)$ は再帰的という．
  ここで $n_0, n_1 in NN$ であり，$recPlus, recTimes$ は再帰的な関数，$recLE$ は再帰的な関係である．
]

次は自明である．

#proposition[
  $StandardModel$ は再帰的である．
]

#theorem[Tennenbaumの定理][
  $PeanoArithmetic$ の超準モデルは再帰的ではない．
] <thm:Tennenbaum>

#proof[
  再帰的な超準モデル $Model(M)$ が存在するとして矛盾を導く．証明は次の大きく2ステップに分かれる．

  #enum[
    超準モデル $Model(M)$ 上では，再帰的分離不能な再帰的可算集合の分離集合とその補集合を $Model(M)$ の超準元としてエンコードできる．
  ][
    もし $Model(M)$ が再帰的なら，再帰的な $recPlus, recTimes$ によってその超準元のコードらから元の集合へのデコードができて，これらは再帰的可算になる．
    よって，再帰的な分離集合が存在することとなり，これは再帰的分離不能としたことと矛盾する．
  ]

  今 $A, B$ を再帰的可算集合として再帰的分離不能であるとする．
  表現定理より $A, B$ に対して $Delta_0$-論理式 $alpha(x), beta(x)$ が存在して以下を満たす．
  $
    n in A &<==> StandardModel vDash exists s. alpha(n, s) \
    n in B &<==> StandardModel vDash exists s. beta(n, s)
  $

  $Delta_0$ 論理式 $phi(u)$ を次のように定義する．
  $
    phi(u) equiv (forall x, s_1, s_2 < u). [beta(x, s_2) -> not alpha(x, s_1)]
  $

  このとき，$A sect B = emptyset$ なので任意の $n in omega$ に対して $StandardModel vDash not phi(n)$ が成り立つ．
  Overspill(@thm:overspill)より，$Model(M)$ の超準元 $a$ が存在して $Model(M) vDash phi(a)$．

  $C := {n in omega | Model(M) vDash exists s <= a. alpha(n, s)}$ と定めると，これは $A, B$ の分離集合になっている．
  #struct[
    $A subset.eq C$ を見る．
    $n in A$ とすると，$StandardModel vDash exists s. alpha(n, s)$ なので，
    適当な $m in omega$ が存在して $Model(M) vDash alpha(n, s)$ となる．
    $StandardModel initSeg Model(M)$ かつ $alpha(x)$ が $Delta_0$-論理式なので@lem:equiv_initSeg_delta0 より $Model(M) vDash alpha(n, s)$ となる．
    $a$ は $Model(M)$ の超準元なので $Model(M) vDash m < a$ であるから，$Model(M) vDash exists s <= a. alpha(n, s)$ が成り立つ．
    よって $n in C$ であり，$A subset.eq C$．
  ]
  #struct[
    $B sect C = emptyset$ を見る．
    $n in B$ とすると，$Model(M) vDash phi(a)$ であるから，$n in.not A$．$A subset.eq C$ だから $n in.not C$ であり，よって $B sect C = emptyset$．
  ]

  $C$ が再帰的であることと，$C$ とその補集合 $dash(C)$ が再帰的可算であることは同値である#footnote[菊池，補題5.4.8などを参考．]．
  $C, dash(C)$ をそれぞれ $Model(M)$ の超準元 $e, dash(e)$ にエンコードする．
  #struct[
    まずアイデアを説明する．

    $p(n)$ は0から始めて $n$ 番目の素数とする．
    $C$ の要素を小さい順 $c_0, c_1,...$ に列挙する．
    今，$n$ 番目までの有限個の $c_n$ までなら $e_n = product_n p(c_n)$ とすれば，
    $e_n$ が $p(m)$ で割り切れるかどうかで $m in C$ を判定できる．
    これを $n -> infinity$ に飛ばして $e$ を作れば，無限大の値を持つが $Model(M)$ の上では適切に $C$ の要素かを判定できる．

    事実として，これらの論理式は $Delta_0$ である．簡単のために意図的に表記を濫用している．
    - 「$n$ 番目の素数は $m$ である」を表現する論理式 $quote.double.l p(n) = m quote.double.r$．
    - 「$y$ は $x$ で割り切れる」を表現する論理式 $quote.double.l x|y quote.double.r$．
    - 「$x$ は $C$ に含まれる」を表現する論理式 $quote.double.l x in C quote.double.r$．これは $exists s <= a. alpha(x, s)$ とすれば $A subset.eq C$ なのでよい．

    これらの論理式を用いてこのアイデアを形式化したものが $psi(k)$ であり，定義より $psi(k)$ は $Delta_0$-論理式である．
    $
      psi(k) <==> exists e <= a. forall n <= k. exists m <= a. [p(n) = m and [m|e <-> c in C]]
    $


    任意の $n in omega$ に対して $StandardModel vDash psi(n)$ が成り立つので，@lem:equiv_initSeg_delta0 より $Model(M) vDash psi(a)$ が成り立つ．
    よってOverspillより $Model(M)$ の超準元 $b$ が存在して $Model(M) vDash psi(b)$ が成り立つ．
    $psi(b)$ の形から，さらに $Model(M)$ の超準元 $e$ が存在して，
    $Model(M) vDash forall n <= b. exists m <= a. [p(n) = m and [m|e <-> c in C]]$ が成り立つ．

    この $e$ はアイデアを実現している．すなわち，任意の $n in omega$ に対して，$p(n)$ で $e$ が割り切れるかどうかで $n in C$ を判定できる．
  ]

  #struct[
    逆に $not exists s <= a. alpha(a, s)$ とすれば「$x$ は $C$ に含まれない」を表現する論理式となるので，
    これを使って同様にやれば超準元 $dash(e)$ も作れる．
  ]

  逆に $e, dash(e)$ から $C, dash(C)$ をデコードする．
  #struct[
    $Model(M)$ は再帰的なので，$angle.l NN; n_0, n_1; recPlus, recTimes; recLE angle.r$ と同型である．
    この同型写像を $f : Model(M) -> NN$ とする．

    デコードを構成する前に，$recTimes$ について次のことに注意しておく．
    #struct[
      $m recTimes n$ は
      $f(k) = n$ を満たす $k in Model(M)$ について，$overbrace(m recPlus m recPlus dots.c recPlus m, k)$ を意味する．
      すなわち，直接 $overbrace(m recPlus m recPlus dots.c recPlus m, n)$ を意味しない．
    ]

    よって，元の $recTimes$ を使わずに，$recPlus$ から新しい演算 $recTimes' : Nat times Nat -> Nat$ を以下のように定め，$recPlus,recTimes'$ から，すなわち実質的に $recPlus$ のみでデコードを行う．
    $
      m recTimes' 0 &= n_0 \
      m recTimes' (n + 1) &= (m recTimes' n) recPlus m
    $
    $recPlus$ が再帰的なので $recTimes'$ も 再帰的である．

    自然数の集合 $tilde(C)$ を以下のように定めると，これは明らかに再帰的可算である．
    $
      tilde(C) := {n in omega | StandardModel vDash exists t. [t recTimes' n = f(e)]}
    $

    任意の $t in Model(M), n in omega$ について，
    この $recTimes'$ は任意の $k,l in Model(M), n in omega$ に対し以下を満たすことに注意する．
    $
      Model(M) vDash k dot n = l <==> StandardModel vDash f(k) recTimes' n = f(l)
    $

    $l = e$ に固定すれば，
    $
      Model(M) vDash t dot n = e
      &<==> StandardModel vDash f(t) recTimes' n = f(e)
    $

    $tilde(C)$ の定義を考えれば，
    $
      Model(M) vDash n|e
      &<==> n in tilde(C)
    $

    更に $n$ として $m$ 番目の素数 $p(m)$ を取れば，$e$ の定義より，$Model(M) vDash p(m)|e <==> p(m) in tilde(C) <==> m in C$．
    したがって，$C$ は再帰的可算である．
  ]
  #struct[
    同様の議論で，$dash(C)$ も再帰的可算である．
  ]

  したがって，$C, dash(C)$ が再帰的可算であるので $C$ は再帰的であり，これは再帰的分離不能としたことと矛盾する．
  よって $Model(M)$ は再帰的ではない．
]

証明を踏まえると，より強めて，次のことが言える．

#proposition[
  和のみが再帰的な $PeanoArithmetic$ の超準モデルは存在しない．
]

適当にエンコーディングを変更すれば，次のことも言える．

#proposition[
  積のみが再帰的な $PeanoArithmetic$ の超準モデルは存在しない．
]

#remark[
  @rem:overspill_weaker でも述べたように，Overspillは $Delta_0$-論理式については $PeanoArithmetic$ より弱く $IDeltaZeroArithmetic$ でも成り立つ．したがって，この証明は $IDeltaZeroArithmetic$ が再帰的な超準モデルを持たないことの証明にもそのまま使える．
]

#remark[
  一方，$IOpenArithmetic$ は再帰的な超準モデルを持つ．
  より詳細に言えば，ある代数的構造が $IOpenArithmetic$ のモデルになる再帰的な条件が知られていて，これはShepherdsonの定理として知られている（菊池 8.3.19）．
  大雑把に考えれば，どのように頑張っても $IOpenArithmetic$ では超越的な方法を超えず計算可能な方法でしか事実を証明出来ないということを意味し，
  その意味で $IOpenArithmetic$ は非常に弱く，
  例えば $IOpenArithmetic$ では「素数は無限に存在する」などの素数に関する性質はほとんど証明できない．
]

#remark[
  @thm:Tennenbaum の証明の中核は，再帰的可算だが再帰的分離不能な集合の存在である．
  このような集合から直接に第一不完全性定理を導くことが出来る（菊池7.3.20，7.3.21参照）．
  このような観点から，Tennenbaumの定理とは第1不完全性定理のモデル的な書き直しであるとも言える．
]

例えばある命題が $PeanoArithmetic$ や $IDeltaZeroArithmetic$ から証明可能でないことを示すには，その命題を成り立たせないモデルの存在を示せばよい．
しかし $PeanoArithmetic$ や $IDeltaZeroArithmetic$ の超準モデルは再帰的にはなりえないので，そのようなモデルを構成することは非常に難しい．
