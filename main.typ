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

== Three readings of a Dyck path

In this work we explore the duality between an interval temporal logic, Dyck paths, and prime filters.
An interval temporal logic is characterized by the fact that the truth of a
statement depends on the time interval it is evaluated on (rather than the time instant) @halpern1991propositional.
Dyck paths enter as the geometric representation of such intervals sharing some algebraic properties with logic of subintervals @Ferrari2015DyckAI.
The analysis of the finite Dyck lattices in @Ferrari2015DyckAI rests on one
observation: a finite Dyck path $P$ can be read in three ways.

- A path, an element of the lattice of Dyck paths ordered by geometric
  inclusion;
- a down-set named $hat(F)_P$ of intervals of the underlying time line;
- an antichain of intervals written $A_P$, namely the maximal elements of that down-set.

These are three names for one object.
Write $D_n$ for the Dyck paths of semilength $n$ ordered by geometric
inclusion $P <= Q$ when $P$ lies weakly below $Q$ @Ferrari2015DyckAI[§ 2]. This is a finite
distributive lattice, so by Birkhoff's representation theorem @davey2002introduction it is the lattice
of down-sets of its join-irreducible elements, and those are transposed in Dyck algebra where
join-irreducible is a path all of whose factors are hills except for a single
pyramid $u^k d^k$ with $k >= 2$, and it is determined by the interval of atoms
lying below it. Writing $Int([n-1])$ for the intervals $[i, j]$,
$1 <= i <= j <= n-1$, of the chain $[n-1]$ ordered by inclusion, this reads
$
  D_n tilde.equiv cal(O)(Int([n-1])),
$
the lattice of down-sets of $Int([n-1])$.

#figure(
  kind: image,
  placement: bottom,
  stack(
    dir: ttb,
    spacing: 1em,
    interval-triangle(),
    table(
      columns: 3,
      align: (left + horizon, center + horizon, left + horizon),
      inset: (x: 0.8em, y: 0.45em),
      stroke: none,
      table.hline(),
      table.header([reading], [$P = u u u d u d d d$], [read off from]),
      table.hline(stroke: 0.5pt),
      [the path $P$],
      dyck-mini("uuududdd", hmax: 4, step: 0.17, hunit: 0.17, marks: ((3, cI), (5, cII))),
      [the peaks above the axis at abscissas
        #text(fill: cI)[$3$] and #text(fill: cII)[$5$]],
      table.hline(stroke: 0.3pt + luma(80%)),
      [the antichain $A_P$],
      [$\{ #text(fill: cI)[$[1,2]$], #text(fill: cII)[$[2,3]$] \}$],
      [one maximal interval per peak of $P$ above the axis],
      table.hline(stroke: 0.3pt + luma(80%)),
      [the down-set $hat(F)_P$],
      [$Int([3]) without \{[1,3]\}$],
      [the down-closure of $A_P$],
      table.hline(),
    ),
  ),
  caption: [The three readings of $P = u u u d u d d d in D_4$.],
) <fig:triangle>

// We write $hat(F)_P subset.eq Int([n-1])$ for the down-set of $P$ and $A_P$ for its antichain of maximal elements.

// / Path $arrow.r$ down-set: the interval $[i,j]$ lies below $P$ exactly when the
//   pyramid of height $j - i + 2$ planted at slot $i$ fits underneath it,
//   $
//     [i,j] in hat(F)_P quad <==> quad h_P (i + j) >= j - i + 2.
//   $
// / Down-set $arrow.r$ path: the path is read back column by column, its height at
//   $x$ being one more than the length of the longest interval of $hat(F)_P$
//   centred there, and $h_bot (x)$ when no interval is.
// / Down-set $arrow.l.r$ antichain: $A_P$ is the set of maximal elements of
//   $hat(F)_P$, and $hat(F)_P$ is the down-closure of $A_P$. The intervals of
//   $A_P$ are pairwise incomparable, but they may well overlap.
// / Path $arrow.r$ antichain: the maximal intervals are visible in the drawing.
//   Each peak of $P$ at abscissa $x$ and height $k >= 2$ contributes
//   $
//     [(x - k) / 2 + 1, (x + k) / 2 - 1],
//   $
//   a hill contributing nothing.
// / Antichain $arrow.r$ path: $P = or.big_([i,j] in A_P) J_([i,j])$, where
//   $J_([i,j])$ is the join-irreducible whose pyramid spans $[i,j]$. The join
//   superposes intervals without fusing them: two overlapping maximal intervals
//   produce two peaks separated by a saddle, not one taller pyramid.

#example[
  Take $n = 4$, so the time line is the chain $[3] = \{1, 2, 3\}$ and $Int([3])$
  has the six elements $[1,1], [2,2], [3,3], [1,2], [2,3], [1,3]$. For
  $P = u u u d u d d d$, with height profile $0, 1, 2, 3, 2, 3, 2, 1, 0$, the
  test $h_P (i + j) >= j - i + 2$ runs over those six:

  #align(center, table(
    columns: 6,
    stroke: none,
    inset: (x: 0.5em, y: 0.28em),
    align: (right, left, right, left, right, left),
    [$[1,1]$], [$h_P (2) = 2 >= 2$], [$[2,2]$], [$h_P (4) = 2 >= 2$], [$[3,3]$], [$h_P (6) = 2 >= 2$],
    [$[1,2]$], [$h_P (3) = 3 >= 3$], [$[2,3]$], [$h_P (5) = 3 >= 3$], [$[1,3]$], [$h_P (4) = 2 gt.eq.not 4$],
  ))

  So $hat(F)_P$ is everything but $[1,3]$, and its maximal elements are
  $A_P = \{[1,2], [2,3]\}$ --- the same answer the peak rule gives at a glance.
  Running the computation over all of $D_4$ labels each of its fourteen paths
  with an antichain of intervals of $[3]$:

  #let mini = w => dyck-mini(w, hmax: 4, step: 0.17, hunit: 0.17)
  #align(center, table(
    columns: 4,
    stroke: none,
    align: (center + horizon, left + horizon, center + horizon, left + horizon),
    inset: (x: 0.7em, y: 0.3em),
    mini("udududud"), [$emptyset$], mini("uudududd"), [$\{[1,1], [2,2], [3,3]\}$],
    mini("uuddudud"), [$\{[1,1]\}$], mini("uuudddud"), [$\{[1,2]\}$],
    mini("uduuddud"), [$\{[2,2]\}$], mini("uduuuddd"), [$\{[2,3]\}$],
    mini("ududuudd"), [$\{[3,3]\}$], mini("uuuddudd"), [$\{[1,2], [3,3]\}$],
    mini("uududdud"), [$\{[1,1], [2,2]\}$], mini("uuduuddd"), [$\{[1,1], [2,3]\}$],
    mini("uudduudd"), [$\{[1,1], [3,3]\}$], mini("uuududdd"), [$\{[1,2], [2,3]\}$],
    mini("uduududd"), [$\{[2,2], [3,3]\}$], mini("uuuudddd"), [$\{[1,3]\}$],
  ))

  Reading the two columns against @fig-d4: the empty antichain is $bot_4$, the
  single interval $[1,3]$ spanning the whole chain is $top_4$, and the number of
  intervals in $A_P$ is the number of nontrivial peaks of $P$.
]

== From a bounded time line to an unbounded one

Everything above is finite with the chain $[n-1]$: the intervals are the time
spans of a bounded history, and the lattice they generate is bounded with them.
The suggestion this paper follows is to let that chain run off to the right and
keep the triangle standing, or as much of it as will stand. An unbounded Dyck
path is still to be read as a down-set of intervals of the time line
$NN_(>= 1)$, hence as a hereditary proposition about an unbounded future, and
the question becomes which connectives such paths support once no last stage
closes them off. The passage between a path and its down-set survives intact;
the antichain of maximal intervals does not always, since a down-set of an
infinite poset may have no maximal elements at all, and we will keep the
intervals but not the antichain.

What holds the triangle up is a representation theorem, and it is worth saying
on which scale ours sits. Birkhoff's theorem is a statement about finite
distributive lattices. Its general form for bounded distributive lattices is
Priestley duality, which trades the finite poset of join-irreducibles for an
ordered topological space; beside it stands the topology-free representation of
the down-set lattice $cal(O)(P)$ of an arbitrary poset $P$ by its completely
join-irreducible elements, the principal down-sets @davey2002introduction. We
will not need the strength of Priestley duality and do not use it, but our work
follows this spectrum: the stages $D_n$ are Birkhoff's case, and the ambient
object in which we place their limit remains the down-set lattice of a poset,
the finite intervals of $NN_(>= 1)$, where the correspondence between the poset
and the completely join-irreducible elements --- now the paths made of a single
pyramid --- survives unchanged.

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

Only half of the finite condition survives here, and it is worth saying which
half and why. A finite Dyck word is asked two things: that no prefix dip below
the axis, and that the last step land back on it. The second speaks about the
last step, and an infinite word has none, so $cal(D)_omega$ keeps the first
alone. This is not an arbitrary weakening: it is what the finite notion becomes
in the limit. A finite word $w$ with no negative prefix is exactly a _prefix_ of a finite
Dyck word, since appending $d^(h_w (abs(w)))$ closes it off; the definition
above therefore reads
$
  cal(D)_omega = \{ P in \{u, d\}^omega mid(|) forall n in NN, quad
  p_0 dots.c p_(n-1) "is a prefix of a finite Dyck word" \},
$
the infinite branches of the tree of Dyck prefixes. Read the other way round,
the paths of finite support --- Model 1 seen inside $cal(D)_omega$ --- are dense
in it: truncating $P$ at time $n$ and closing it off with
$d^(h_P (n)) (u d)^omega$ gives a path of finite support agreeing with $P$ up to
$n$. Every infinite path is thus approximated by genuine finite Dyck paths, one
prefix at a time, and nothing beyond that approximation has been let in.

#remark(number: auto, label: <rem-no-return>)[
  An infinite Dyck path need not return to the axis. Returning is a feature of
  the finite case, forced there by the balance condition, and it lapses together
  with it: the descents a prefix owes are not missing from the path, only
  postponed, and postponement may go on forever. The extreme case is
  $top = u^omega$, which never comes back at all, although each of its prefixes
  $u^n$ is settled by the honest Dyck path $u^n d^n$; a milder one is
  $u^k (d u)^omega$, which oscillates between heights $k - 1$ and $k$ and never
  descends further.

  Demanding infinitely many returns instead is possible, but costly. That set is
  not closed under joins --- @prop-top-chain writes $u^omega$ as the supremum of
  the chain $u^k d^k (u d)^omega$, every member of which returns infinitely
  often --- so it is no complete lattice, and Model 2 would lose the top that is
  the only constant of its logic. The return is a condition on the tail of a
  path, and the tail is exactly what an unbounded time line declines to fix.
]

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
infinitely many factors; a path with no return at all, $top = u^omega$ being the
extreme case, has no factors. The atom $pi_i$ are the path
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

#remark(number: auto, label: <rem-grammar>)[
  The grammar is what makes $top = u^omega$ look illegal: no derivation from
  $S ::= epsilon | u S d S$ produces it. What is true is that no derivation
  _terminates_ on it, and that is a statement about $mu$, not about the rules.
  Read as a least fixpoint the grammar gives $mu F$, the words reached in
  finitely many productions, and $u^omega$ is not one of them. Read as a
  greatest fixpoint it gives $nu F$, the possibly infinite trees, where a
  derivation may run forever provided every single step is a legitimate
  production; and there $u^omega$ is the word of the unique tree $T$ with
  $T = u T d T$. Expanding the left argument forever emits $u$ after $u$, and the
  $d$ that each production promises sits behind an infinite word, so it is never
  reached: every rule is obeyed at every step, only the end of the derivation is
  missing. Flattening $nu F$ to words yields the finite Dyck words together with
  all of $cal(D)_omega$. The flattening is not injective --- at a node whose left
  argument is infinite, the $d$ and the right argument are unreachable and hence
  invisible in the word --- which is why $cal(D)_omega$ is made of words and not
  of trees.
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

We restate that model 2 correspond to Dyck paths with infinite support, i.e., Dyck paths unbounded on the right which do not have a suffix consisting of the concatenation of an infinite number of peaks lying on the x-axis ($...u d^omega$).

$
  cal(D)_(infinity) = \{ P in cal(D)_omega mid(|) abs(supp(P)) = infinity \}
$


// #lemma(label: <lem-supp-mono>)[
//   $bot <= P$ for every $P in cal(D)_omega$, and
//   $
//     P <= Q quad => quad supp(P) subset.eq supp(Q).
//   $
//   Hence $cal(D)_infinity$ is an up-set of $cal(D)_omega$.
// ]

// Since $h_P (n) >= 0$ and $h_P (n) equiv n mod 2$, every odd $n$ has
// $h_P (n) >= 1 = h_bot (n)$; so $supp(P) = \{ n mid(|) h_P (n) > h_bot (n) \}$,
// which $h_P <= h_Q$ transports pointwise.

#definition("top path")[
  $
    top = u^omega, wide h_top (n) = n, wide
    supp(top) = NN_(>= 2), wide supp_"at" (top) = NN_(>= 1).
  $
]

$
  top in cal(D)_infinity, wide forall P in cal(D)_infinity, quad P <= top.
$

After its first step $top$ never meets the axis again: it has no return, hence
no factor, and the grammar of finite Dyck words does not generate it. It is a
Dyck path all the same, in the sense fixed by @rem-no-return --- every prefix
$u^n$ is a prefix of the Dyck path $u^n d^n$, and the descents it owes are
postponed rather than dropped --- and @rem-grammar says the same on the side of
the grammar, where $top$ is the word of the tree $T = u T d T$ of $nu F$.

#proposition(label: <prop-top-chain>)[
  $top$ is the supremum of an increasing chain taken in stratum of Model 1:
  $
    top
    = or.big_(k in NN) underbrace(u^k d^k (u d)^omega, in cal(D)_"fs")
    = or.big_(k >= 2) underbrace(u^k (d u)^omega, in cal(D)_infinity)
    = u^omega
  $
  both because the $k$-th term has $h(n) = n$ as soon as $k >= n$.
]

The left chain lies in Model 1 and its supremum does not, which is exactly why
$cal(D)_1$ has no top; the right chain shows that $top$ is already a join of
paths of infinite support, so Model 2 does not need Model 1 to name it.

== Join

#proposition[
  For $I != emptyset$ and $P_i in cal(D)_infinity$,
  $
    h_(or.big_(i in I) P_i) (n) = sup_(i in I) h_(P_i) (n),
    wide
    supp(or.big_(i in I) P_i) = union.big_(i in I) supp(P_i),
  $
  hence $or.big_(i in I) P_i in cal(D)_infinity$; in the binary case
  $
    h_(P or Q) (n) = max(h_P (n), h_Q (n)),
    wide
    supp(P or Q) = supp(P) union supp(Q).
  $
]

$
  (cal(D)_infinity, <=, or.big, top) = "complete join-semilattice with top".
$

== Failure of meets

#lemma(label: <lem-empty-supp>)[
  $supp_"at" (P) = emptyset quad <==> quad P = bot$.
]

If $h_P (2i) = h_P (2i + 2) = 0$ then $h_P (2i + 1) = 1$, so $h_P = h_bot$.

#example[
  Split the atoms $pi_i$ into the odd and the even ones:
  $
    O = (u u d d)^omega = or.big_(i "odd") pi_i,
    wide
    E = u d (u u d d)^omega = or.big_(i "even") pi_i,
  $
  $
    supp_"at" (O) = \{1, 3, 5, dots\},
    wide
    supp_"at" (E) = \{2, 4, 6, dots\},
    wide
    O, E in cal(D)_infinity.
  $
  Their height functions interleave, and the pointwise minimum collapses onto
  the floor:
  $
            h_O & = 0, 1, 2, 1, 0, 1, 2, 1, 0, dots \
            h_E & = 0, 1, 0, 1, 2, 1, 0, 1, 2, dots \
    h_(O and E) & = 0, 1, 0, 1, 0, 1, 0, 1, 0, dots = h_bot
  $
  $
    supp_"at" (O and E) = supp_"at" (O) inter supp_"at" (E) = emptyset
    quad => quad
    O and E = bot in.not cal(D)_infinity.
  $
]

#proposition[
  $O$ and $E$ have no lower bound at all in $cal(D)_infinity$:
  $
    R <= O, quad R <= E quad => quad R <= bot quad => quad
    R = bot in.not cal(D)_infinity.
  $
]

#proposition[
  $and$ is a partial operation on $cal(D)_infinity$:
  $
    supp(P and Q) = supp(P) inter supp(Q),
    wide
    P and Q in cal(D)_infinity quad <==> quad abs(supp(P) inter supp(Q)) = infinity.
  $
]

$
  bot in.not cal(D)_infinity, wide cal(D)_infinity "is not a meet-semilattice".
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

Nor does $cal(D)_1$ keep the implication $arrow.r$ and negation $not$ of
$cal(D)_omega$ (Completion below): for $P, Q in cal(D)_1$, every $J_I$ with $I$
beyond $supp(P)$ has $J_I and P = bot <= Q$, hence $J_I <= P arrow.r Q$; so

$
  P, Q in cal(D)_1 quad => quad abs(supp(P arrow.r Q)) = abs(supp(not P)) = infinity,
  wide not bot = top in.not cal(D)_1.
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
  cal(D)_2 = "join-semilattice with top", wide cal(L)_2 = \{ top, or, arrow.r \}.
$

$
  not exists bot, wide not exists " global " and, wide
  not exists " global negation": quad not top = bot in.not cal(D)_2.
$

The implication of $cal(D)_omega$, however, restricts to $cal(D)_2$: $Q <= P
arrow.r Q$, and $cal(D)_2$ is an up-set of $cal(D)_omega$ since $supp$ is
monotone, so

$
  P, Q in cal(D)_2 quad => quad P arrow.r Q in cal(D)_2.
$

It is not the residual of the partial meet of $cal(D)_2$: $O arrow.r E = not O =
E$, while no $R in cal(D)_2$ has $O and R in cal(D)_2$ below $E$, as $O and R <=
O and E = bot$. The adjunction $P and R <= Q <==> R <= P arrow.r Q$ is
available in $cal(D)_omega$ only.


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

== Final overview


#bibliography("refs.bib")
