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
  Instead of considering a finite total order, one can consider either an infinite (but discrete) total order or a more general partial order. In the former case, the combinatorial structure that is involved could be some notion of infinite Dyck path, that is, a Dyck path having infinite length. There are at least two different ways to formalize this suggestion: either working in the set of all Dyck paths (of any length), which is naturally partially ordered, and can be probably interpreted as some kind of infinitary limit object for the family of Dyck lattices; or introducing Dyck paths having infinite support, i.e., Dyck paths unbounded on the right which do not have a suffix consisting of the concatenation of an infinite number of peaks lying on the x-axis.
]

Both formalisations live inside the same picture. Read an infinite word over
$\{u, d\}$ as a lattice path and compare it to the bottom element
$bot = (u d)^omega$, the infinite concatenation of peaks lying on the axis: the
two models are exactly the two ways a path can behave against $bot$ in the long
run.

#let bot-word = "ud" * 8
#let P-fin = "uuuddd" + "ud" * 4 + "u"
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
      dyck-annotate(P-fin, 3, [$supp(P)$], color: cI, dir: (-0.5, 1.0), anchor: "south")
    }),
    dyck-diagram(n: 16, height: 4, unit: 0.42cm, x-ticks: 4, x-label: [$n$], y-label: [$h$], {
      dyck-path(bot-word, color: cmute, offset: -0.08)
      dyck-path(P-inf, color: cII, fill: auto, dots: true)
      dyck-annotate(
        P-inf,
        8,
        [$supp(P)$ unbounded],
        color: cII,
        dir: (-3.0, 2.0),
        anchor: "west",
        leader: false,
        dot: false,
      )
    }),

    text(0.92em)[Model 1: $P (u d)^omega$, $abs(supp(P)) < infinity$], text(0.92em)[Model 2: $abs(supp(P)) = infinity$],
  ),
  caption: [
    The two shapes of infinite Dyck path, drawn against $bot = (u d)^omega$ (grey).
    On the left the path merges with $bot$ and stays there, so it is a finite Dyck
    path padded with peaks; on the right its excursions above $bot$ never stop.
  ],
) <fig:two-models>

= Model 1 and 2

== Setup  // (1) define the ambient object once, before both models

$
  h_P (0) = 0,
  wide
  h_P (n)
  =
  \#{i < n : p_i = u}
  -
  \#{i < n : p_i = d}.
$

$
  cal(D)_omega
  =
  lr(
    \{
    P = p_0 p_1 p_2 dots.c in \{u, d\}^omega
    mid(|)
    forall n in NN, h_P (n) >= 0
    \}
  ).
$

$
  P <= Q
  quad arrow.l.r.double quad
  forall n in NN,
  h_P (n) <= h_Q (n).
$

$
  bot = (u d)^omega,
  wide
  h_bot (n)
  =
  cases(
    0 & "if " n = 0 mod 2,
    1 & "if " n = 1 mod 2,
  ).
$

// (2) two variants of supp, with the translation between them

$
  supp(P)
  =
  \{ n in NN mid(|) h_P (n) != h_bot (n) \},
  wide
  supp_"at" (P)
  =
  \{ i >= 1 mid(|) h_P (2i) > 0 \}.
$

#lemma[
  $supp_"at" (P) = \{ i mid(|) 2i in supp(P) \}$, and
  $abs(supp(P)) < infinity <=> abs(supp_"at" (P)) < infinity$.
]
#proof[
  If $h_P (2i) = 0$ for all $i >= m$, then each excursion between
  consecutive returns at distance $2$ is a hill, so $h_P (2i+1) = 1
  = h_bot (2i+1)$ there as well; hence finiteness of $supp_"at"$
  gives finiteness of $supp$. The converse is immediate.
]

// (2') the reason to keep supp_at: it is the atom spectrum
#lemma[
  $i in supp_"at" (P) <=> pi_i <= P$, where
  $pi_i = (u d)^(i-1) u u d d (u d)^omega$.
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
  iota_n : D_n -> D_(n+1),
  wide
  iota_n (P) = P u d.
$

// (4) well-definedness obligations, stated before the colimit

#lemma[
  $iota_n$ is an order-embedding preserving $or$, $and$, and $bot$;
  it preserves neither $top$ nor $tilde$ nor $arrow.squiggly$.
]

$
  cal(D)_colim
  =
  limits(colim)_n D_n,
  wide
  (n,P) tilde.op (m,Q)
  quad arrow.l.r.double quad
  exists k >= n,m :
  P (u d)^(k-n) = Q (u d)^(k-m),
$

// (5) name the category of the colimit explicitly
// "colimit in the category of bounded-below distributive lattices
//  and embeddings; NOT a colimit of Heyting algebras"

$
  [(n,P)] <= [(m,Q)]
  quad arrow.l.r.double quad
  exists k >= n,m :
  P (u d)^(k-n)
  <=_(D_k)
  Q (u d)^(k-m).
$

$
  j :
  cal(D)_colim
  arrow.r.hook
  cal(D)_omega,
  wide
  j([(n,P)])
  =
  P (u d)^omega.
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
  cal(D)_(infinity"-supp")
  =
  \{ P in cal(D)_omega mid(|) abs(supp(P)) = infinity \},
  wide
  cal(D)_omega
  =
  j(cal(D)_colim)
  union.sq
  cal(D)_(infinity"-supp").
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
  R(P) = \{ i >= 1 mid(|) h_P (2i) = 0 \},
  wide
  cal(D)_(infinity"-supp")
  =
  underbrace(\{ abs(R(P)) = infinity \}, "recurrent")
  union.sq
  underbrace(\{ abs(R(P)) < infinity \}, "transient").
$


= Logic

$
  cal(D)_omega
  :=
  lr(
    {
      P in {u,d}^omega
      mid(|)
      forall n in NN, h_P(n) >= 0
    }
  ).
$

$
  bot := (u d)^omega.
$

$
  supp(P)
  :=
  lr(
    {
      n in NN
      mid(|)
      h_P(n) != h_bot(n)
    }
  ).
$

$
  cal(D)_"fs"
  :=
  lr(
    {
      P in cal(D)_omega
      mid(|)
      abs(supp(P)) < infinity
    }
  ).
$

$
  cal(D)_"is"
  :=
  lr(
    {
      P in cal(D)_omega
      mid(|)
      abs(supp(P)) = infinity
    }
  ).
$

$
  cal(D)_omega
  =
  cal(D)_"fs"
  union.sq
  cal(D)_"is".
$


== Logic of Model 1

$
  D_0
  arrow.r
  D_1
  arrow.r
  D_2
  arrow.r
  dots.c,
  wide
  iota_n(P) = P u d.
$

$
  cal(D)_1
  :=
  limits("colim")_n D_n.
$

$
  cal(D)_1
  tilde.equiv
  cal(D)_"fs"
  =
  lr(
    {
      P in cal(D)_omega
      mid(|)
      abs(supp(P)) < infinity
    }
  ).
$

$
  bot = (u d)^omega
  in cal(D)_1.
$

$
  top in.not cal(D)_1.
$

$
  P,Q in cal(D)_1
  quad => quad
  P and Q in cal(D)_1,
  wide
  P or Q in cal(D)_1.
$

$
  h_(P and Q)(n)
  =
  min(h_P(n), h_Q(n)).
$

$
  h_(P or Q)(n)
  =
  max(h_P(n), h_Q(n)).
$

$
  supp(P and Q)
  =
  supp(P) inter supp(Q).
$

$
  supp(P or Q)
  =
  supp(P) union supp(Q).
$

$
  cal(D)_1
  =
  "distributive lattice with bottom, without top".
$

$
  not exists top
  quad => quad
  not exists " global Heyting implication".
$

$
  cal(L)_1
  =
  lr(
    {
      bot,
      and,
      or
    }
  ).
$


== Logic of Model 2

$
  cal(D)_2
  :=
  cal(D)_"is"
  =
  lr(
    {
      P in cal(D)_omega
      mid(|)
      abs(supp(P)) = infinity
    }
  ).
$

$
  (u d)^omega
  in.not
  cal(D)_2.
$

$
  top
  =
  u^omega
  in
  cal(D)_2.
$

$
  P,Q in cal(D)_2
  quad => quad
  P or Q in cal(D)_2.
$

$
  supp(P or Q)
  =
  supp(P) union supp(Q).
$

$
  abs(supp(P)) = infinity
  quad => quad
  abs(supp(P or Q)) = infinity.
$

$
  P,Q in cal(D)_2
  quad not=> quad
  P and Q in cal(D)_2.
$

$
  supp(P and Q)
  =
  supp(P) inter supp(Q).
$

$
  abs(supp(P)) = infinity,
  quad
  abs(supp(Q)) = infinity
  quad not=> quad
  abs(supp(P) inter supp(Q)) = infinity.
$

$
  bot in.not cal(D)_2,
  wide
  and " is not closed".
$

$
  cal(D)_2
  =
  "join-semilattice with top".
$

$
  cal(L)_2
  =
  lr(
    {
      top,
      or
    }
  ).
$

$
  not exists bot,
  wide
  not exists " global " and,
  wide
  not exists " global " arrow.r,
  wide
  not exists " global negation".
$


== Completion

$
  cal(D)_omega
  =
  cal(D)_"fs"
  union.sq
  cal(D)_"is".
$

$
  cal(D)_1
  arrow.r
  cal(D)_omega
  arrow.l
  cal(D)_2.
$

$
  cal(D)_1
  tilde.equiv
  cal(D)_"fs"
  subset.eq
  cal(D)_omega.
$

$
  cal(D)_2
  =
  cal(D)_"is"
  subset.eq
  cal(D)_omega.
$

$
  bot
  =
  (u d)^omega.
$

$
  top
  =
  u^omega.
$

$
  h_(sup_(i in I) P_i)(n)
  =
  sup_(i in I) h_(P_i)(n).
$

$
  h_(inf_(i in I) P_i)(n)
  =
  inf_(i in I) h_(P_i)(n).
$

$
  P and lr(sup_(i in I) Q_i)
  =
  sup_(i in I) lr(P and Q_i).
$

$
  cal(D)_omega
  =
  "frame"
  =
  "complete Heyting algebra".
$

$
  P arrow.r Q
  =
  sup
  lr(
    {
      R in cal(D)_omega
      mid(|)
      P and R <= Q
    }
  ).
$

$
  not P
  =
  P arrow.r bot.
$

$
  cal(L)_omega
  =
  lr(
    {
      bot,
      top,
      and,
      or,
      arrow.r,
      not
    }
  ).
$

$
  cal(L)_omega
  +
  lr(
    {
      sup_(i in I),
      inf_(i in I)
    }
  ).
$

$
  "Idl"(cal(D)_1)
  tilde.equiv
  cal(D)_omega.
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
  [$"distributive lattice + bottom"$],
  [$"join-semilattice + top"$],
  [$"complete Heyting algebra / frame"$],

  [*Logic*], [$bot, and, or$], [$top, or$], [$bot, top, and, or, arrow.r, not$],

  [*Relation*],
  [$cal(D)_1 tilde.equiv cal(D)_"fs" subset.eq cal(D)_omega$],
  [$cal(D)_2 = cal(D)_"is" subset.eq cal(D)_omega$],
  [$cal(D)_omega = cal(D)_"fs" union.sq cal(D)_"is"$],
)

#bibliography("refs.bib")
