#import "@preview/cetz:0.3.4"
#import "@preview/theoretic:0.4.0"
#import "@preview/dashy-todo:0.1.3": todo
#import theoretic.presets.basic: * // this will automatically load predefined styled environments
#show ref: theoretic.show-ref      // this is necessary for references to theorems to work

#import "lib.typ": *

#set document(title: [Infinite Dyck Paths Algebra for Unbounded Interval Temporal Logic])
#set page(numbering: "1")
#set par(justify: true)

// Multi-letter math operators (Typst has no LaTeX-style \operatorname macros).
#let supp = math.op("supp")
#let colim = math.op("colim")
#let Int = math.op("Int")

#title()

#set quote(block: true)


= Introduction

#quote(attribution: [Ferrari])[
  Instead of considering a finite total order, one can consider either an infinite (but discrete) total order or a more general partial order.
  In the former case, the combinatorial structure that is involved could be some notion of infinite Dyck path, that is, a Dyck path having infinite length.
  There are at least two different ways to formalize this suggestion: either working in the *set of all Dyck paths* (of any length), which is naturally partially ordered, and can be probably interpreted as some kind of infinitary limit object for the family of Dyck lattices;
  or introducing *Dyck paths having infinite support*, i.e., Dyck paths unbounded on the right which do not have a suffix consisting of the concatenation of an infinite number of peaks lying on the x-axis.
]

Therefore, we denote:

- *Model 1:* the set of all Dyck paths;
- *Model 2:* the set of Dyck paths with infinite support.

Both models live inside the same picture. Read an infinite word over $Sigma = \{u, d\}^omega$ as a lattice path and compare it to the bottom element
$bot = (u d)^omega$, the infinite concatenation of peaks lying on the axis: the two models are exactly the two ways a path can behave against $bot$ in the long
run.

#let bot-word = "ud" * 8
#let P-fin = "uuuddd" + "ud" * 4 + "ud"
#let P-inf = "uudd" + "uuuddd" + "uuuudd"

#figure(
  grid(
    columns: 2,
    column-gutter: 1.2em,
    row-gutter: 0.7em,
    align: center + bottom,

    dyck-diagram(n: 16, height: 4, unit: 0.42cm, x-ticks: 4, x-label: [$n$], y-label: [$h$], {
      dyck-path(bot-word, color: cmute, offset: -0.08)
      dyck-path(P-fin, color: cI, fill: auto, dots: true)
    }),
    dyck-diagram(n: 16, height: 4, unit: 0.42cm, x-ticks: 4, x-label: [$n$], y-label: [$h$], {
      dyck-path(bot-word, color: cmute, offset: -0.08)
      dyck-path(P-inf, color: cII, fill: auto, dots: true)
    }),
  ),
) <fig:two-models>


= Ambient definitions

For a path $P = p_0 p_1 p_2 dots$, we define the function $h_P (n)$ that returns the height of $P$ after its first $n$ steps.

$
  h_P (0) = 0, wide h_P (n) = |{i < n | p_i = u}| - |{i < n | p_i = d}|.
$

$
  cal(D)_omega = \{ P = (p_i)_(i in NN) in \{u, d\}^omega mid(|) forall n in NN, h_P (n) >= 0 \}
$

#definition("geometric order")[
  For $P, Q in cal(D)_omega$ set
  $
    P <= Q quad arrow.l.r.double quad forall n in NN, h_P (n) <= h_Q (n),
  $
  and say that $P$ lies _weakly below_ $Q$. We call $<=$ the _geometric order_,
  since it compares the two drawings pointwise. It restricts to each $D_n$, and
  $(D_n, <=)$ is the Dyck lattice of order $n$ of @Ferrari2015DyckAI.
]

We import the vocabulary of @Ferrari2015DyckAI about specific Dyck paths, transposed to infinite
words. A _return_ of a path $P$ is an index $n > 0$ with $P$ crossing the $x$ axis i.e. $h_P (n) = 0$;
a _peak_ is a pair of consecutive steps $p_n p_(n+1) = u d$, and a _hill_ is a peak at height
$0$, i.e. one with $h_P (n) = 0$. A _pyramid_ is a block $u^k d^k$ ($k >= 1$)
starting and ending on the axis, so a hill is the pyramid with $k = 1$. Finally,
a _factor_ of $P$ is a block of consecutive steps running between two
consecutive returns (or from the origin to the first return); a hill is also
called a _trivial factor_. In the finite case every Dyck path is the
juxtaposition of its factors; here the same holds for the prefix of $P$ up to
its last return, and a path with infinitely many returns is the juxtaposition of
infinitely many factors. The atom $pi_i$ are the path
whose factors are all hills except for a single pyramid $u u d d$.

#definition("limit path")[
  In this language, we denote $bot$ as the unique path all of whose factors are hills.
  $
    bot = (u d)^omega, wide h_bot (n) =
    cases(
      0 & "if " n = 0 mod 2,
      1 & "if " n = 1 mod 2,
    ).
  $
]

// (2) two variants of supp, with the translation between them

The _support_ of a path measures how far it strays from the floor $bot$: it
collects the times at which $P$ does not sit exactly where $bot$ does. Since
$bot$ is nothing but hills, this amounts to recording where $P$ does something
other than a hill: a path of finite support is one whose factors are hills from
some point on — a finite Dyck path followed by an infinite run of hills —
whereas a path of infinite support keeps producing nontrivial factors
arbitrarily late. This is precisely the line separating Model 1 from Model 2.

$
  supp(P) = \{ n in NN mid(|) h_P (n) != h_bot (n) \}, wide supp_"at" (P) = \{ i >= 1 mid(|) h_P (2i) > 0 \}.
$

The second variant samples only the even times, and there $bot$ is on the axis:
since paths never go below $0$, "differing from $bot$" and "being strictly
above the axis" say the same thing. The next two lemmas show that this sampling
loses nothing, so we may use whichever variant is convenient.

#lemma[
  $supp_"at" (P) = \{ i mid(|) 2i in supp(P) \}$.
]


#lemma[
  $abs(supp(P)) < infinity <=> abs(supp_"at" (P)) < infinity$.
]

#lemma[
  $i in supp_"at" (P) <=> pi_i <= P$, where
  $pi_i = (u d)^(i-1) u u d d (u d)^omega$.
]

// (2'') the interval representation: down-sets, not antichains

Ferrari represents a path of $D_n$ by an antichain of intervals of $[n-1]$,
namely the orders of the atoms lying below each join-irreducible in its
decomposition @Ferrari2015DyckAI. We keep the intervals, but not the antichain.

#definition("interval representation")[
  Let $Int$ denote the set of finite nonempty intervals $I = [a, b]$ of
  $NN_(>= 1)$, ordered by inclusion. For $I = [a, b] in Int$ put
  $
    J_I = (u d)^(a-1) u^(b-a+2) d^(b-a+2) (u d)^omega,
  $
  the path all of whose factors are hills except for a single pyramid, and set
  $
    hat(F)_P = \{ I in Int mid(|) J_I <= P \}.
  $
]

Each $J_I$ is join-irreducible in $cal(D)_omega$, and $J_([i, i]) = pi_i$; hence
$supp_"at" (P) = \{ i mid(|) [i, i] in hat(F)_P \}$: the support records exactly
the singletons of $hat(F)_P$, and forgets every wider interval.

#lemma[
  $J_I <= J_(I')$ if and only if $I subset.eq I'$. In particular $hat(F)_P$ is a
  down-set of $Int$.
]

// #remark[
//   In the finite case a down-set of intervals is determined by its maximal
//   elements, and Ferrari works with that antichain throughout. Over
//   $cal(D)_omega$ the antichain is no longer available. For $P = top = u^omega$
//   every join-irreducible satisfies $J_I <= P$, so $hat(F)_P = Int$, a down-set
//   with no maximal element whatsoever: the associated antichain is empty, which
//   is the representation of $bot$ and not of $top$. This is the failure of
//   directed sups, $or.big_n u^n d^n (u d)^omega = u^omega$, seen from the
//   representation side, and it is why we carry the whole down-set.
// ]

#example[
  Knowing $supp_"at" (P)$ is not enough to know $P$. Both paths below have
  $supp_"at" = \{1, 2\}$, yet
  #text(fill: cII)[$u u d u d d (u d)^omega$] $<$
  #text(fill: cI)[$u u u d d d (u d)^omega$].

  #figure(
    grid(
      columns: 2,
      column-gutter: 1.6em,
      row-gutter: 0.5em,
      align: center,
      dyck-diagram(n: 10, height: 3, unit: 0.42cm, x-ticks: 2, y-ticks: none, {
        dyck-path("ud" * 5, color: cmute, offset: -0.08)
        dyck-path("uuuddd" + "ud" * 2, color: cI, fill: auto, dots: true)
      }),
      dyck-diagram(n: 10, height: 3, unit: 0.42cm, x-ticks: 2, y-ticks: none, {
        dyck-path("ud" * 5, color: cmute, offset: -0.08)
        dyck-path("uududd" + "ud" * 2, color: cII, fill: auto, dots: true)
      }),

      text(fill: cI)[$u u u d d d (u d)^omega$], text(fill: cII)[$u u d u d d (u d)^omega$],
    ),
  )

  The order is exactly what the picture shows: at every abscissa the
  #text(fill: cII)[right] path sits weakly below the #text(fill: cI)[left] one,
  and that pointwise comparison of heights is all that $<=$ means.

  The two are nevertheless different paths. The #text(fill: cI)[left] one is a
  single pyramid, hence join-irreducible with atom-interval $[1, 2]$, while the
  #text(fill: cII)[right] one is $pi_1 or pi_2$; what separates them is the
  down-set,
  #text(fill: cI)[$hat(F) = \{[1,1], [2,2], [1,2]\}$] against
  #text(fill: cII)[$hat(F) = \{[1,1], [2,2]\}$], of which $supp_"at" (P)$
  retains only the singletons. So $supp_"at" (P)$ tells us whether $P$ has
  finite support, but not which path $P$ is; only $hat(F)_P$ does that.
]

// (3) lattice structure of the ambient object, stated once

#lemma[
  Pointwise $min$ and $sup$ of height functions of paths in
  $cal(D)_omega$ are height functions of paths in $cal(D)_omega$;
  hence $(cal(D)_omega, <=)$ is a complete lattice with
  $bot = (u d)^omega$, $top = u^omega$, and binary meets distribute
  over arbitrary joins, so $cal(D)_omega$ is a complete Heyting
  algebra.
]

== Dyck paths lattice

Each $(D_n, <=)$ is a finite distributive lattice. The @fig-d4 illustrate the lattice for $n = 4$. The bottom is the path of four hills $bot_4$, the top the single pyramid $top_4$, and an edge joins two paths when one covers the other in the geometric order.

#figure(
  placement: top,
  dyck-hasse(
    d4-nodes,
    d4-edges,
    unit: 1.5cm,
    xgap: 1.32,
    ygap: 0.72,
    glyph-w: 0.86,
    glyph-h: 0.32,
    pad: 0.05,
    notes: (
      "udududud": $bot_4 = (u d)^4$,
      "uuuudddd": $top_4 = u^4 d^4$,
    ),
  ),
  caption: [The Dyck lattice $D_4$, drawn in the geometric order.],
) <fig-d4>

These finite lattices are the stages of a single tower.
To pass from one stage to the next we leave the path alone and append a hill at the right end by the inclusion function $iota$ defined below.
The @fig-iota draws the case $iota_3$.


$
  iota_n : D_n -> D_(n+1), wide iota_n (P) = P u d.
$

#figure(
  placement: top,
  dyck-hasse-map(
    d3-nodes,
    d3-edges,
    d4-nodes-mirror,
    d4-edges,
    (
      ("ududud", "udududud"),
      ("uuddud", "uuddudud"),
      ("uduudd", "uduuddud"),
      ("uududd", "uududdud"),
      ("uuuddd", "uuudddud"),
    ),
    highlight: ("udududud", "uduuddud", "uuddudud", "uududdud", "uuudddud"),
    routes: (
      "uduudd": ((-4.60, 0.62), (-4.55, 0.28), (-0.90, 0.28), (-0.35, 0.64)),
    ),
    titles: ($D_3$, $D_4$),
    map-label: $iota_3$,
    map-label-on: "uuuddd",
  ),
  caption: [
    The case $iota_3 : D_3 arrow.r.hook D_4$.
  ],
) <fig-iota>


Appending a hill is also the extension that fixes the floor, sending
$bot_n = (u d)^n$ to $bot_(n+1)$, which keeps the whole tower compatible with
the reference path against which support is measured. In the interval
representation the map does nothing at all: the intervals representing $P$ are
unchanged and only the ambient index set grows from $[n-1]$ to $[n]$, the new
atom $pi_n$ failing to lie below $P u d$ because $P u d$ has returned to the
axis at abscissa $2n$. Appending hills lets a path of one stage be compared with a path of any later
one, and two paths should count as equal when the tower eventually makes them so.

#definition("eventual equality", label: <def-eventual-equality>)[
  For $n <= k$ let $iota_(n,k) : D_n -> D_k$ denote the composite
  $iota_(k-1) compose dots.c compose iota_n$, with $iota_(n,n) = "id"$; that is,
  $iota_(n,k) (P) = P (u d)^(k-n)$. On the disjoint union
  $
    product.co_(n in NN) D_n = \{ (n, P) mid(|) n in NN, P in D_n \}
  $
  define
  $
    (n, P) tilde.op (m, Q) quad arrow.l.r.double quad
    exists k >= max(n, m) : iota_(n,k) (P) = iota_(m,k) (Q).
  $
] <def:equiv-class>

The relation $tilde.op$ is obviously an equivalence relation.
Its classes are what let paths of different lengths be compared at all: $P in
D_n$ and $Q in D_m$ with $n != m$.


#todo(position: "inline")[intro $D_omega$ lattice and figure @fig-omega]

#figure(
  placement: bottom,
  omega-sketch(),
  caption: [
    The two strata of $cal(D)_omega$, and the tower $D_1 subset D_2 subset
    dots.c D_omega$.
  ],
) <fig-omega>

= Model 1

We restate that Model 1 corresponds to the set of all Dyck paths (of any
length), which is naturally partially ordered, and can probably be interpreted
as some kind of infinitary limit object for the family of Dyck lattices
@ferrari2004latticeslatticepaths @ferrari2009latticespathsrepresentationtheory @baril2025latticedyckpathsclose.

#lemma[
  $iota_n$ is injective.
]


#lemma(label: <lem-iota>)[
  $iota_n$ is an order-embedding preserving function.
]

The infinitary limit object $cal(D)_colim$ for the family of Dyck lattices, denoted $limits(colim) D_n$, is the colimit of the chain $D_0 ->_iota D_1 ->_iota D_2 -> dots.c$ along the maps $iota_n$: the smallest object in
which every stage sits compatibly.
Therefore, the $cal(D)_colim$ is simply the increasing union of the tower quotiented by $tilde.op$.

#definition($"Direct limit of" D_n$)[
  Writing $[(n, P)]$ for the $tilde.op$-class of $(n, P)$, put
  $
    cal(D)_colim = (product.co_(n in NN) D_n) \/ tilde.op,
    wide
    c_n : D_n -> cal(D)_colim, quad c_n (P) = [(n, P)],
  $
  and equip $cal(D)_colim$ with
  $
    [(n,P)] <= [(m,Q)] quad arrow.l.r.double quad
    exists k >= max(n, m) : iota_(n,k) (P) <=_(D_k) iota_(m,k) (Q),
  $
  $
    [(n,P)] or [(m,Q)] = [(k, iota_(n,k) (P) or_(D_k) iota_(m,k) (Q))],
  $
  and
  $
    [(n,P)] and [(m,Q)] = [(k, iota_(n,k) (P) and_(D_k) iota_(m,k) (Q))]
  $
  for any $k >= max(n, m)$, and $bot = [(0, epsilon)]$ with $epsilon$ the empty
  path.
]

An element of $cal(D)_colim$ is thus a finite Dyck path together with the
convention that the flat ground to its right does not count. Letting that ground
run forever is exactly a subset of $cal(D)_omega$.

$
  j : cal(D)_colim arrow.hook cal(D)_omega wide j([(n,P)]) = P (u d)^omega.
$


#proposition(label: <prop-colim-image>)[
  $j$ is an order-embedding, and
  $j(cal(D)_colim) = \{ P in cal(D)_omega mid(|)
  abs(supp(P)) < infinity \}$.
]

== Algebraic representation

Model 1 has a second possible description, it is an initial algebra.
Recall that an algebra for an endofunctor $F$ is just a map $F(X) -> X$ and a coalgebra is a map $X -> F(X)$;
neither carries the associativity that an algebra over a monad, or a coalgebra over a comonad,
would supply. Least and greatest fixpoints of $F$ are written $mu F$ and $nu F$ respectively.

#definition("initial algebra")[
  An _$F$-algebra_ is a pair $(X, alpha)$ with $alpha : F(X) -> X$, and a
  morphism of $F$-algebras $(X, alpha) -> (Y, beta)$ is a map $f : X -> Y$ with
  $f compose alpha = beta compose F(f)$. An algebra $(mu F, "in")$ is _initial_
  when for every $F$-algebra $(X, alpha)$ there is exactly one such $f$, that is
  a unique
  $
    "fold"(alpha) : mu F -> X
    quad "with" quad
    "fold"(alpha) compose "in" = alpha compose F("fold"(alpha)).
  $
  #todo(position: "inline")[cite]
  // It is unique up to isomorphism, and by Lambek's lemma
  // $"in" : F(mu F) -> mu F$ is itself an isomorphism, so $mu F$ is a fixpoint of
  // $F$ and it is the least one.
]

Recall finite Dyck words are constructed with the grammar $S ::= epsilon | u S d S$ generates, and that grammar is a signature functor.

#definition("Dyck initial algebra")[
  Let $F : "Set" -> "Set"$ be
  $
    F(X) = 1 + X times X,
  $
  with constructors $epsilon$ (i.e. $emptyset$) for the terminal object $1$ and $u (-) d (-)$ for the
  product $X times X$, the latter reading a pair $(A, B)$ as the word
  $u A d B$.
]


#proposition(label: <prop-mu-F>)[
  $F$ is finitary, so its initial algebra exists and is computed by the initial
  chain $emptyset -> F(emptyset) -> F^2 (emptyset) -> dots.c$, which converges
  at $omega$:
  $
    mu F = union.big_(k in NN) F^k (emptyset),
  $
  with $"in" : F(mu F) -> mu F$ the pair of constructors. Its elements are the finite Dyck words before any quotient.
]

Let $sigma : F(NN) -> NN$ be the $F$-algebra $sigma(ast) = 0$ and $sigma(a, b) = a + b + 1$, and set
$
  ell := "fold"(sigma) : mu F -> NN,
  quad ell(epsilon) = 0,
  quad ell(u A d B) = ell(A) + ell(B) + 1,
$
the unique map counting the uses of the constructor $u (-) d (-)$, i.e. the semilength.

#proposition[
  The fibres of $ell$ are the strata of the tower: $ell^(-1)(n)$ is exactly the
  carrier of $D_n$, so that
  $
    mu F = product.co_(n in NN) ell^(-1)(n) tilde.equiv product.co_(n in NN) D_n,
  $
  and $abs(ell^(-1)(n)) = C_n$:
  $
    1, 1, 2, 5, 14, 42, 132, dots
  $
  the Catalan numbers.
]

#figure(
  placement: top,
  table(
    columns: 4,
    align: (center + horizon, left, left, center + horizon),
    inset: (x: 0.8em, y: 0.5em),
    stroke: none,
    table.hline(),
    table.header([$n$], [terms of $mu F$], [word], [count]),
    table.hline(stroke: 0.5pt),
    table.cell(rowspan: 1)[$0$], [$epsilon$], [$epsilon$], table.cell(rowspan: 1)[$C_0 = 1$],
    table.hline(stroke: 0.3pt + luma(80%)),
    table.cell(rowspan: 1)[$1$], [$u thin epsilon thin d thin epsilon$], [$u d$], table.cell(rowspan: 1)[$C_1 = 1$],
    table.hline(stroke: 0.3pt + luma(80%)),
    table.cell(rowspan: 2)[$2$],
    [$u thin epsilon thin d thin (u thin epsilon thin d thin epsilon)$],
    [$u d u d$],
    table.cell(rowspan: 2)[$C_2 = 2$],
    [$u thin (u thin epsilon thin d thin epsilon) thin d thin epsilon$], [$u u d d$],
    table.hline(stroke: 0.3pt + luma(80%)),
    table.cell(rowspan: 5)[$3$],
    [$u thin epsilon thin d thin (u thin epsilon thin d thin (u thin epsilon thin d thin epsilon))$],
    [$u d u d u d$],
    table.cell(rowspan: 5)[$C_3 = 5$],
    [$u thin epsilon thin d thin (u thin (u thin epsilon thin d thin epsilon) thin d thin epsilon)$], [$u d u u d d$],
    [$u thin (u thin epsilon thin d thin epsilon) thin d thin (u thin epsilon thin d thin epsilon)$], [$u u d d u d$],
    [$u thin (u thin epsilon thin d thin (u thin epsilon thin d thin epsilon)) thin d thin epsilon$], [$u u d u d d$],
    [$u thin (u thin (u thin epsilon thin d thin epsilon) thin d thin epsilon) thin d thin epsilon$], [$u u u d d d$],
    table.hline(),
  ),
  caption: [
    The correspondance of $mu F$ and Catalan number $C_n = frac(1, n+1) binom(2n, n)$
  ],
) <fig-mu-strata>


#todo(position: "inline")[define $D_omega$ by the quotienting of $mu F$]

= Model 2

$
  cal(D)_(infinity"-supp") = \{ P in cal(D)_omega mid(|) abs(supp(P)) = infinity \},
  wide
  cal(D)_omega = j(cal(D)_colim) union.sq cal(D)_(infinity"-supp").
$

// (8) record that Model 2 is a stratum, not a subalgebra

#proposition[
  $cal(D)_(infinity"-supp")$ is an up-set of $cal(D)_omega$, closed
  under arbitrary joins, but closed under neither binary meets
  (interleaved combs: $P, Q$ with pyramids at odd resp. even slots
  have $P and Q = bot$) nor pseudonegation; dually,
  $j(cal(D)_colim)$ is closed under $or, and, bot$ but not under
  $tilde$, $arrow.squiggly$, or directed sups
  ($or.big_n u^n d^n (u d)^omega = u^omega$).
]

// (9) optional refinement, if you want the conservative reading
$
  R(P) = \{ i >= 1 | h_P (2i) = 0 \},
  wide
  cal(D)_(infinity"-supp") = underbrace(\{ abs(R(P)) = infinity \}, "recurrent") union.sq underbrace(\{ abs(R(P)) < infinity \}, "transient").
$

= Unbounded Interval Temporal Logics



$
  cal(D)_"fs" := \{ P in cal(D)_omega mid(|) abs(supp(P)) < infinity \},
  wide
  cal(D)_"is" := \{ P in cal(D)_omega mid(|) abs(supp(P)) = infinity \}.
$

$
  cal(D)_omega = cal(D)_"fs" union.sq cal(D)_"is".
$


== Logic of Model 1


$
  cal(D)_1 := limits(colim)_n D_n
  tilde.equiv cal(D)_"fs" = \{ P in cal(D)_omega mid(|) abs(supp(P)) < infinity \}.
$

$
  bot = (u d)^omega in cal(D)_1, wide top in.not cal(D)_1.
$

$
  P, Q in cal(D)_1 quad => quad P and Q in cal(D)_1, wide P or Q in cal(D)_1.
$

$
  h_(P and Q) (n) = min(h_P (n), h_Q (n)), wide h_(P or Q) (n) = max(h_P (n), h_Q (n)).
$

$
  supp(P and Q) = supp(P) inter supp(Q), wide supp(P or Q) = supp(P) union supp(Q).
$

$
  cal(D)_1 = "distributive lattice with bottom, without top".
$

$
  not exists top quad => quad not exists " global Heyting implication".
$

$
  cal(L)_1 = \{ bot, and, or \}.
$


== Logic of Model 2

$
  cal(D)_2 := cal(D)_"is" = \{ P in cal(D)_omega mid(|) abs(supp(P)) = infinity \}.
$

$
  (u d)^omega in.not cal(D)_2, wide top = u^omega in cal(D)_2.
$

$
  P, Q in cal(D)_2 quad => quad P or Q in cal(D)_2.
$

$
  supp(P or Q) = supp(P) union supp(Q),
  wide
  abs(supp(P)) = infinity quad => quad abs(supp(P or Q)) = infinity.
$

$
  P, Q in cal(D)_2 quad arrow.r.double.not quad P and Q in cal(D)_2.
$

$
  supp(P and Q) = supp(P) inter supp(Q),
  wide
  abs(supp(P)) = abs(supp(Q)) = infinity
  quad arrow.r.double.not quad abs(supp(P) inter supp(Q)) = infinity.
$

$
  bot in.not cal(D)_2, wide and " is not closed".
$

$
  cal(D)_2 = "join-semilattice with top", wide cal(L)_2 = \{ top, or \}.
$

$
  not exists bot, wide not exists " global " and, wide
  not exists " global " arrow.r, wide not exists " global negation".
$


== Completion

$
  cal(D)_omega = cal(D)_"fs" union.sq cal(D)_"is",
  wide
  cal(D)_1 arrow.r cal(D)_omega arrow.l cal(D)_2.
$

$
  cal(D)_1 tilde.equiv cal(D)_"fs" subset.eq cal(D)_omega,
  wide
  cal(D)_2 = cal(D)_"is" subset.eq cal(D)_omega.
$

$
  bot = (u d)^omega, wide top = u^omega.
$

$
  h_(sup_(i in I) P_i) (n) = sup_(i in I) h_(P_i) (n),
  wide
  h_(inf_(i in I) P_i) (n) = inf_(i in I) h_(P_i) (n).
$

$
  P and (sup_(i in I) Q_i) = sup_(i in I) (P and Q_i).
$

$
  cal(D)_omega = "frame" = "complete Heyting algebra".
$

$
  P arrow.r Q = sup \{ R in cal(D)_omega mid(|) P and R <= Q \},
  wide
  not P = P arrow.r bot.
$

$
  cal(L)_omega = \{ bot, top, and, or, arrow.r, not \}
  + \{ sup_(i in I), inf_(i in I) \}.
$

$
  "Idl"(cal(D)_1) tilde.equiv cal(D)_omega.
$


== Final overview


#bibliography("refs.bib")
