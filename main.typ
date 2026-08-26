#import "@preview/cetz:0.3.4"
#import "@preview/theoretic:0.4.0"
#import theoretic.presets.basic: * // this will automatically load predefined styled environments
#show ref: theoretic.show-ref      // this is necessary for references to theorems to work

#import "lib.typ": *

#set document(title: [Dyck Paths with Infinite Support and Unbounded Temporal Logic])
#set page(numbering: "1")
#set par(justify: true)

// Multi-letter math operators (Typst has no LaTeX-style \operatorname macros).
#let supp = math.op("supp")
#let colim = math.op("colim")

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
  )
) <fig:two-models>

= Formalising Model 1 and 2

== Ambient definitions

For a path $P = p_0 p_1 p_2 dots$, we define the function $h_P (n)$ that returns the height of $P$ after its first $n$ steps.

$
  h_P (0) = 0, wide h_P (n) = \#{i < n | p_i = u} - \#{i < n | p_i = d}.
$

$
  cal(D)_omega = \{ P = (p_i)_(i in NN) in \{u, d\}^omega mid(|) forall n in NN, h_P (n) >= 0 \}
$

$
  P <= Q quad arrow.l.r.double quad forall n in NN, h_P (n) <= h_Q (n).
$

$
  bot = (u d)^omega, wide h_bot (n) =
  cases(
    0 & "if " n = 0 mod 2,
    1 & "if " n = 1 mod 2,
  ).
$

We import the local vocabulary of @Ferrari2015DyckAI, transposed to infinite
words. A _return_ of $P$ is an index $n > 0$ with $h_P (n) = 0$; a _peak_ is a
pair of consecutive steps $p_n p_(n+1) = u d$, and a _hill_ is a peak at height
$0$, i.e. one with $h_P (n) = 0$. A _pyramid_ is a block $u^k d^k$ ($k >= 1$)
starting and ending on the axis, so a hill is the pyramid with $k = 1$. Finally,
a _factor_ of $P$ is a block of consecutive steps running between two
consecutive returns (or from the origin to the first return); a hill is also
called a _trivial factor_. In the finite case every Dyck path is the
juxtaposition of its factors; here the same holds for the prefix of $P$ up to
its last return, and a path with infinitely many returns is the juxtaposition of
infinitely many factors. In this language $bot = (u d)^omega$ is the unique path
all of whose factors are hills, and the atom $pi_i$ introduced below is the path
whose factors are all hills except for a single pyramid $u u d d$.

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
above the axis" say the same thing. The next lemma shows that this sampling
loses nothing, so we may use whichever variant is convenient.

#lemma[
  $supp_"at" (P) = \{ i mid(|) 2i in supp(P) \}$, and
  $abs(supp(P)) < infinity <=> abs(supp_"at" (P)) < infinity$.
]
#proof[
  The first identity is immediate from $h_bot (2i) = 0$ and $h_P >= 0$.
  For the second, suppose $h_P (2i) = 0$ for all $i >= m$. Between two
  consecutive even times at height $0$ there are exactly two steps, and
  nonnegativity forces them to be $u$ then $d$ --- a hill --- so
  $h_P (2i+1) = 1 = h_bot (2i+1)$ there as well. Hence $supp(P) subset.eq
  [0, 2m]$ is finite. The converse follows from the first identity, which
  embeds $supp_"at" (P)$ into $supp(P)$ via $i |-> 2i$.
]

// (2') the reason to keep supp_at: it is the atom spectrum
#lemma[
  $i in supp_"at" (P) <=> pi_i <= P$, where
  $pi_i = (u d)^(i-1) u u d d (u d)^omega$.
]

#example[
  The atom spectrum does not determine the path. Both paths below have
  $supp_"at" = \{1, 2\}$, yet $u u d u d d (u d)^omega < u u u d d d (u d)^omega$.

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
      text(fill: cI)[$u u u d d d (u d)^omega$],
      text(fill: cII)[$u u d u d d (u d)^omega$],
    )
  )

  In Ferrari's terms the left path is one pyramid, hence join-irreducible with
  atom-interval $[1, 2]$, while the right one is $pi_1 or pi_2$: the invariant
  that separates them is the antichain of intervals, $\{[1,2]\}$ against
  $\{[1], [2]\}$, of which $supp_"at" (P)$ retains only the union. So
  $supp_"at"$ is a finiteness test, not a representation.
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

== Model 1

$
  iota_n : D_n -> D_(n+1), wide iota_n (P) = P u d.
$

// (4) well-definedness obligations, stated before the colimit

#lemma[
  $iota_n$ is an order-embedding preserving $or$, $and$, and $bot$;
  it preserves neither $top$ nor $tilde$ nor $arrow.squiggly$.
]

$
  cal(D)_colim = limits(colim)_n D_n,
  wide
  (n,P) tilde.op (m,Q) quad arrow.l.r.double quad exists k >= n,m : P (u d)^(k-n) = Q (u d)^(k-m),
$

$
  [(n,P)] <= [(m,Q)] quad arrow.l.r.double quad exists k >= n,m : P (u d)^(k-n) <=_(D_k) Q (u d)^(k-m).
$

$
  j : cal(D)_colim arrow.r.hook cal(D)_omega, wide j([(n,P)]) = P (u d)^omega.
$

// (6) the image characterization is a proposition with a proof,
//     not a displayed equation

#proposition[
  $j$ is an order-embedding, and
  $j(cal(D)_colim) = \{ P in cal(D)_omega mid(|)
  abs(supp(P)) < infinity \}$.
]
#proof[
  ($subset.eq$) $j([(n,P)])$ agrees with $h_bot$ from abscissa $2n$
  on. ($supset.eq$) If $h_P = h_bot$ from $N$ on, then from $N$ on
  the letters of $P$ alternate $u d$, so $P = p (u d)^omega$ with
  $p$ a finite Dyck word.
]

== Model 2

// (7) do not restate D_omega here — it was defined in the Setup

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


=  Unbounded Interval Temporal Logics

$
  cal(D)_omega := \{ P in \{u, d\}^omega mid(|) forall n in NN, h_P (n) >= 0 \},
  wide
  bot := (u d)^omega.
$

$
  supp(P) := \{ n in NN mid(|) h_P (n) != h_bot (n) \}.
$

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
  D_0 arrow.r D_1 arrow.r D_2 arrow.r dots.c, wide iota_n (P) = P u d.
$

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

#table(
  columns: 4,
  align: center,
  inset: 7pt,

  [*Property*], [*Model 1*], [*Model 2*], [*Completion*],

  [*Space*], [$cal(D)_1 = limits("colim")_n D_n$], [$cal(D)_2 = cal(D)_"is"$], [$cal(D)_omega$],

  [*Support*], [$abs(supp(P)) < infinity$], [$abs(supp(P)) = infinity$], [$abs(supp(P)) <= infinity$],

  [*Bottom*], [$(u d)^omega$], [$not exists$], [$(u d)^omega$],

  [*Top*], [$not exists$], [$u^omega$], [$u^omega$],

  [*$and$*], [$checkmark$], [$times$], [$checkmark$],

  [*$or$*], [$checkmark$], [$checkmark$], [$checkmark$],

  [*$arrow.r$*], [$times$], [$times$], [$checkmark$],

  [*$not$*], [$times$], [$times$], [$checkmark$],

  [*Arbitrary meets*], [$times$], [$times$], [$checkmark$],

  [*Arbitrary joins*], [$times$], [$"nonempty"$], [$checkmark$],

  [*Algebra*],
  [$"DL + bottom"$],
  [$"JSL + top"$],
  [$"complete Heyt / frame"$],

  [*Logic*], [$bot, and, or$], [$top, or$], [$bot, top, and, or, arrow.r, not$],

  [*Relation*],
  [$cal(D)_1 tilde.equiv cal(D)_"fs" subset.eq cal(D)_omega$],
  [$cal(D)_2 = cal(D)_"is" subset.eq cal(D)_omega$],
  [$cal(D)_omega = cal(D)_"fs" union.sq cal(D)_"is"$],
)

#bibliography("refs.bib")
