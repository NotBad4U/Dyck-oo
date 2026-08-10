#set document(title: [Dyck Paths with Infinite Support and Unbounded Temporal Logic])
#set page(numbering: "1")
#set par(justify: true)

#title()

#import "@preview/cetz:0.3.4"
#import "lib.typ": *

#let fig-title(t, sub) = [
  #text(weight: 600, size: 11pt)[#t] \
  #text(fill: cgray, size: 9pt)[#sub]
]

#set figure(gap: 0.8em)
#set figure.caption(position: bottom)
#show figure.caption: set align(left)
#show figure: set align(left)
#show figure: set block(above: 1.6em, below: 1.2em)


= Introduction

This work extends Ferrari's @Ferrari2015DyckAI correspondence between Dyck lattices, Heyting algebras, and interval temporal logic from finite to infinite discrete time. Ferrari sketched two candidate notions of infinite Dyck path; I make both precise — one as the completion of the family of finite Dyck lattices, the other as the space of paths with infinite support — and compare their algebraic behavior. The main observation is an asymmetry: the first construction yields a complete Heyting algebra outright, while the second loses the bottom element and closure under meets. I study the resulting structures and the temporal logics they support, and formulate the associated open problems.


#let cI = rgb("#0F6E56")
#let cII = rgb("#534AB7")
#let cpath = rgb("#2C2C2A")
#let cmute = rgb("#9C9A93")
#let caxis = rgb("#B4B2A9")

#let dx = 0.16
#let dy = 0.16

// word over {u,d} -> polyline points, starting from (x0, y0)
#let dyck(word, x0: 0.0, y0: 0.0, dx: dx, dy: dy) = {
  let pts = ((x0, y0),)
  let x = x0
  let y = y0
  for c in word.clusters() {
    x += dx
    y += if c == "u" { dy } else { -dy }
    pts.push((x, y))
  }
  pts
}

#align(center, figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    let w = 20
    let gap = 4.6
    let sol = (thickness: 1.3pt, join: "round")
    let dsh = (thickness: 1.3pt, dash: "dashed")

    // ---- glyph 1 : finite content, then flat peaks forever -------------
    let o1 = 0.0
    line((o1 - 0.1, 0), (o1 + w * dx + 0.3, 0), stroke: 0.4pt + caxis)
    line(..dyck("uuuddd", x0: o1), stroke: (paint: cpath, ..sol))
    line(..dyck("udududud", x0: o1 + 6 * dx), stroke: (paint: cmute, ..sol))
    line(..dyck("udud", x0: o1 + 14 * dx), stroke: (paint: cmute, ..dsh))
    content((o1 + w * dx + 0.26, 0.13), text(fill: cmute, size: 9pt)[$dots.c$])

    // ---- glyph 2 : excursions recurring forever ------------------------
    let o2 = gap
    line((o2 - 0.1, 0), (o2 + w * dx + 0.3, 0), stroke: 0.4pt + caxis)
    line(..dyck("uuddud" + "uuuddd" + "ud", x0: o2), stroke: (paint: cpath, ..sol))
    line(..dyck("uudd", x0: o2 + 14 * dx), stroke: (paint: cpath, ..dsh))
    content((o2 + w * dx + 0.26, 0.20), text(fill: cpath, size: 9pt)[$dots.c$])

    // ---- glyph 3 : finite rebounds, then unbounded ascent --------------
    let o3 = 2 * gap
    line((o3 - 0.1, 0), (o3 + w * dx + 0.3, 0), stroke: 0.4pt + caxis)
    line(..dyck("uuddud" + "uuuuuu", x0: o3), stroke: (paint: cpath, ..sol))
    line(..dyck("uuu", x0: o3 + 12 * dx, y0: 6 * dy), stroke: (paint: cpath, ..dsh))
    content((o3 + 16 * dx + 0.20, 9.6 * dy), text(fill: cpath, size: 9pt)[$dots.c$])

    // ---- brackets ------------------------------------------------------
    let y1 = -0.50
    let y2 = -1.00
    let l1 = o1 - 0.1
    let r1 = o2 + w * dx + 0.3
    let l2 = o2 - 0.1
    let r2 = o3 + w * dx + 0.3

    line((l1, y1), (r1, y1), stroke: 1pt + cI)
    line((l1, y1), (l1, y1 + 0.11), stroke: 1pt + cI)
    line((r1, y1), (r1, y1 + 0.11), stroke: 1pt + cI)
    content(((l1 + r1) / 2, y1 - 0.20), text(fill: cI, weight: 600)[Model I])

    line((l2, y2), (r2, y2), stroke: 1pt + cII)
    line((l2, y2), (l2, y2 + 0.11), stroke: 1pt + cII)
    line((r2, y2), (r2, y2 + 0.11), stroke: 1pt + cII)
    content(((l2 + r2) / 2, y2 - 0.20), text(fill: cII, weight: 600)[Model II])
  }),
  caption: [Three kinds of infinite path: finite content followed by flat peaks
    forever; excursions recurring without end; finitely many rebounds, then
    unbounded ascent.],
))


#let dx = 0.22
#let dy = 0.20

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    let gui = (paint: caxis, thickness: 0.4pt, dash: "dotted")
    let yT = -0.85 // time line
    let yI = -1.05 // interval bars, top edge
    let hI = 0.12 // bar thickness
    let W = 26 // steps drawn

    // ---------------- the path ----------------------------------------
    line((-0.1, 0), (W * dx + 0.3, 0), stroke: 0.4pt + caxis)
    line(..dyck("uudd" + "ud" + "uuuddd" + "ud" + "uudd", x0: 0.0, dx: dx, dy: dy), stroke: solid(ctealD))
    line(..dyck("uduudd", x0: 18 * dx, dx: dx, dy: dy), stroke: dashed(ctealD))
    content((W * dx + 0.28, 0.22), text(fill: ctealD, size: 9pt)[$dots.c$])

    // ---------------- guides from excursion feet to intervals ---------
    for x in (0, 4, 6, 12, 14, 18, 20, 24) {
      line((x * dx, 0.02), (x * dx, yI - hI - 0.06), stroke: gui)
    }

    // ---------------- the time line -----------------------------------
    line((-0.1, yT), (W * dx + 0.4, yT), stroke: 0.5pt + cgray, mark: (end: ">", scale: 0.6))
    for k in range(0, 14) {
      line((2 * k * dx, yT), (2 * k * dx, yT - 0.06), stroke: 0.4pt + cgray)
    }
    content((-0.28, yT), text(size: 9pt, fill: cgray)[$omega$])

    // ---------------- the antichain of intervals ----------------------
    let bar(a, b, alpha) = {
      rect((a * dx, yI), (b * dx, yI - hI), fill: cteal.transparentize(alpha), stroke: none, radius: 0.03)
    }
    bar(0, 4, 0%)
    bar(6, 12, 0%)
    bar(14, 18, 0%)
    bar(20, 24, 55%) // continuing, fainter

    content((2 * dx, yI - 0.34), text(fill: ctealD, size: 9pt)[$I_1$])
    content((9 * dx, yI - 0.34), text(fill: ctealD, size: 9pt)[$I_2$])
    content((16 * dx, yI - 0.34), text(fill: ctealD, size: 9pt)[$I_3$])
    content((W * dx + 0.28, yI - 0.06), text(fill: cteal, size: 9pt)[$dots.c$])

    // ---------------- down-closure hint under I_2 ---------------------
    let ySub = yI - 0.60
    rect((6.6 * dx, ySub), (11.4 * dx, ySub - 0.08), fill: cgray.transparentize(45%), stroke: none, radius: 0.03)
    rect((7.4 * dx, ySub - 0.20), (10.2 * dx, ySub - 0.28), fill: cgray.transparentize(60%), stroke: none, radius: 0.03)
    rect((8.4 * dx, ySub - 0.40), (9.4 * dx, ySub - 0.48), fill: cgray.transparentize(72%), stroke: none, radius: 0.03)
    content((13.9 * dx, ySub - 0.24), text(fill: cgray, size: 8.5pt)[subintervals of $I_2$])
  }),
  caption: [Each excursion of the path occupies a stretch of time; the stretches
    form an antichain $I_1, I_2, I_3, dots$ of intervals of $omega$, and the
    element of the algebra is its down-closure. Flat peaks occupy no stretch.],
)


#let s = 0.075          // step size of the little path glyphs
#let hw = 4 * s         // half-width of a glyph (words have 8 steps)

#figure(
  align(center, cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // ---- node centres -------------------------------------------------
    let nBot = (0.0, 0.0)
    let nA1 = (-0.95, 1.15)
    let nA2 = (0.95, 1.15)
    let nA3 = (2.55, 1.15)
    let nJoin = (0.0, 2.30)
    let nPyr = (0.0, 3.45)
    let nTop = (0.0, 4.60)

    // ---- edges (drawn first; glyph backgrounds cover the crossings) ----
    let edge(a, b, col: cgray, dash: none) = {
      line(a, b, stroke: (paint: col, thickness: 0.6pt, dash: dash))
    }
    edge(nBot, nA1)
    edge(nBot, nA2)
    edge(nBot, nA3, col: caxis, dash: "dotted")
    edge(nA1, nJoin)
    edge(nA2, nJoin)
    edge(nA3, nJoin, col: caxis, dash: "dotted")
    edge(nJoin, nPyr)
    edge(nPyr, nTop, col: cpurpD, dash: "dashed")

    // ---- node drawing --------------------------------------------------
    // lx nudges a label sideways off the edge that runs beneath its node;
    // the label also carries a white frame, so whatever it still crosses is
    // masked rather than overprinted.
    let node(pos, word, lab, col: cteal, dash: none, lx: 0.0) = {
      let (px, py) = pos
      rect((px - hw - 0.10, py - 0.09), (px + hw + 0.10, py + 3.4 * s + 0.07), fill: white, stroke: none)
      line((px - hw, py), (px + hw, py), stroke: 0.3pt + caxis)
      line(..dyck(word, x0: px - hw, y0: py, dx: s, dy: s), stroke: (
        paint: col,
        thickness: 1.1pt,
        join: "round",
        dash: dash,
      ))
      content(
        (px + lx, py - 0.32),
        text(size: 7.5pt, fill: cgray, lab),
        frame: "rect",
        fill: white,
        stroke: none,
        padding: (top: 0.18, rest: 0.05),
      )
    }

    node(nBot, "udududud", $emptyset$, col: cred)
    node(nA1, "uuddudud", $\{[1,1]\}$, lx: -0.30)
    node(nA2, "uduudd" + "ud", $\{[2,2]\}$, lx: 0.30)
    node(nA3, "ududuudd", $\{[3,3]\}$, col: cteal.lighten(45%))
    node(nJoin, "uududdud", $\{[1,1], [2,2]\}$)
    node(nPyr, "uuudddud", $\{[1,2]\}$)
    node(nTop, "uuuuuuuu", $\{[1, infinity)\}$, col: cpurp, dash: "dashed")

    // ---- annotations ---------------------------------------------------
    content((nA3.at(0) + 0.80, nA3.at(1) + 0.05), text(size: 9pt, fill: caxis)[$dots.c$])
    content((nTop.at(0) + 1.60, nTop.at(1) + 0.14), text(size: 8pt, fill: cpurpD)[limit, not a path])
    content((nBot.at(0) - 1.55, nBot.at(1) + 0.08), text(size: 8pt, fill: credD)[$bot = (u d)^omega$])

    // ---- symmetric invisible bounds so the spine (x = 0) sits at the
    //      centre of the block; the drawing itself overhangs to the right
    rect((-3.6, 0), (3.6, 0), stroke: none)
  })),
  caption: [A fragment of the infinite Dyck lattice, in the style of Ferrari's
    Figure 3. Each node carries a path and, beneath it, the antichain of time
    intervals it determines. The two atoms occupy the instants $1$ and $2$
    separately; their join keeps them separate, and only one step higher do they
    merge into the single interval $[1,2]$. Upward the atoms never run out, and
    the ascending chain of pyramids converges to a ray that no path realises.],
)



= Dyck paths with infinite support

#figure(
  caption: fig-title[Generic admissible path — support under the excursions][
    bands mark positions of height $>= 2$ excursions; hills contribute nothing;
    supp infinite $checkmark$],
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    // excursion, hill, excursion, hill, excursion, dashed tail
    let w-solid = "uudd" + "ud" + "uuuddd" + "ud" + "uudd" // 18 steps
    band(0, 4, cteal)
    band(6, 12, cteal)
    band(14, 18, cteal)
    band(18.4, 21, cteal, alpha: 40%) // tail, fainter
    axis(21)
    line(..dyck-points(w-solid), stroke: solid(cteal))
    line(..dyck-points("uud", x0: 18 * 0.32), stroke: dashed(cteal))
    ell(21, 0.55, cteal)
    content((0.32 * 5, 1.05), text(size: 8.5pt, fill: cgray)[hill: no support])
    line((0.32 * 5, 0.35), (0.32 * 5, 0.85), stroke: 0.4pt + caxis)
    content((0.32 * 13, 1.05), text(size: 8.5pt, fill: cgray)[hill])
    line((0.32 * 13, 0.35), (0.32 * 13, 0.85), stroke: 0.4pt + caxis)
  }),
) <fig:generic>


#figure(
  caption: fig-title[The infinite hill $(u d)^omega$ — never leaves the floor][
    geometrically busy, logically empty: the path *is* the floor;
    supp $= emptyset$, this element is $bot$ #text(fill: credD)[$crossmark$]],
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    axis(21)
    line(..dyck-points("ud" * 8), stroke: solid(cred)) // 16 steps
    line(..dyck-points("udud", x0: 16 * 0.32), stroke: dashed(cred))
    ell(20.5, 0.30, cred)
  }),
) <fig:infinite-hill>


#figure(
  caption: fig-title[Join of all atoms $u u (d u)^omega$ — punctual truth everywhere][
    one step above the floor: height $2$ cleared at every position;
    supp $= omega$, admissible $checkmark$],
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    band(2, 18, cpurp)
    band(18.4, 21, cpurp, alpha: 40%)
    axis(21)
    line(..dyck-points("uu" + "du" * 8), stroke: solid(cpurp)) // 18 steps, ends at height 2
    line(..dyck-points("dud", x0: 18 * 0.32, y0: 2 * 0.32), stroke: dashed(cpurp))
    ell(21, 0.60, cpurp)
  }),
) <fig:join-of-atoms>


#figure(
  caption: fig-title[$D$ (teal): excursions over even positions — $E$ (amber): over odd
    positions][both supports infinite $checkmark checkmark$ — but disjoint:
    the bands interleave and never overlap],
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    // D = (uudd udud)^omega : excursion then hills.  E = (udud uudd)^omega : hills then excursion.
    // Period 8 so the two excursion spans tile the axis without overlapping.
    for k in range(3) { band(8 * k, 8 * k + 4, cteal) } // D bands
    for k in range(3) {
      // E bands, offset row
      rect((0.32 * (8 * k + 4), -0.26), (0.32 * (8 * k + 8), -0.38), fill: camber, stroke: none, radius: 0.04)
    }
    axis(25)
    line(..dyck-points("uuddudud" * 3), stroke: solid(cteal))
    line(..dyck-points("ududuudd" * 3), stroke: solid(camber))
    line(..dyck-points("uu", x0: 24 * 0.32), stroke: dashed(cteal))
    line(..dyck-points("ud", x0: 24 * 0.32), stroke: dashed(camber))
    ell(25.4, 0.45, cteal)
  }),
) <fig:disjoint-supports>

// =====================================================================
#figure(
  caption: fig-title[$D and E$ = pointwise minimum][
    the min is on the floor wherever *either* path is — with interleaved
    supports, that is everywhere: $D inter E = (u d)^omega = bot$
    #text(fill: credD)[$crossmark$] — the meet of two admissible paths lands
    exactly on the banned element],
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    axis(25)
    line(..dyck-points("ud" * 12), stroke: solid(cred))
    line(..dyck-points("ud", x0: 24 * 0.32), stroke: dashed(cred))
    ell(25.4, 0.30, cred)
  }),
) <fig:meet-is-bottom>



= The two models, informally

Ferrari's theory relates three things: Dyck paths of a fixed finite length, the
Heyting algebras they form under the natural order, and a logic whose worlds are
the intervals of a finite line of time. He observes that one may try to replay
this over an infinite discrete line of time, and proposes two candidate notions
of infinite Dyck path. We call the resulting constructions Model I and Model II.

== Model I: paths that always come back.

One starts with nothing infinite at all,
only the collection of _all_ finite Dyck paths, ordered so that a path sits below
another when it stays weakly underneath it. Passing from one length to the next
means padding a path with a small flat peak on the right, and such padding adds
no information, so paths differing only by padding are treated as the same
object. This ordered collection is then completed, in the sense that every
increasing family of paths is given a limit. The completion introduces genuinely
infinite objects, and they turn out to have a uniform shape: they are paths that
rise and fall forever, returning to the ground line infinitely often, each
individual rise and fall being of finite extent. Alongside these there appear a
few boundary objects that no path realises directly — the limits of paths that
climb higher and higher — which the completion is obliged to supply and which
behave as ideal points rather than as paths.

== Model II: paths that stay busy forever.

The second construction takes infinite paths as the primitive notion instead of manufacturing them. An infinite path here is simply a path that never ends. Two decisions distinguish it from the first construction.
First, the line of time is enlarged so that unbounded stretches of time — everything from some instant onward — count as legitimate worlds at which a statement may be evaluated; this is what makes it possible to say "from this moment on, forever".
Second, one refuses those paths that do
something interesting only for a while and then subside into an endless run of
small flat peaks. Such a path is an impostor: the flat peaks carry no content, so
the path holds exactly the information of the finite path preceding them, dressed
up as an infinite object. Ruling them out is what "infinite support" means: the
interesting behaviour must keep recurring, no matter how far to the right one
looks.

*Where they differ.* The first construction excludes nothing and adds ideal
points; the second excludes a whole family of paths and adds real ones. Adding is
harmless, removing is not. The path with no content at all — flat peaks
throughout — is the least element of the first model, and its removal is
precisely what the second model demands. A structure deprived of its least
element cannot combine statements conjunctively without risk: two paths may each
remain busy forever and yet be busy in places that never coincide, so that
everything they hold in common evaporates. This is the central asymmetry between
the two.

= Algebraic interpretation

Write $"Int"_b (omega)$ for the bounded intervals of $omega$ ordered by
inclusion, $"Int"_infinity (omega)$ for the same enlarged by the rays
$[a, infinity)$, and for a down-set $D$ put
$ "supp"(D) = { x in omega : [x,x] in D }. $

== Model I

The algebra is the full down-set algebra
$ cal(H)^"reb" = cal(O)("Int"_b (omega)), $
with $and = inter$, $or = union$ at arbitrary arity, $bot = emptyset$,
$top = "Int"_b (omega)$, and
$
  D arrow.squiggly E = { I : forall J subset.eq I, thick J in D => J in E }, quad
  not D = D arrow.squiggly bot.
$
This is a complete Heyting algebra. Its compact elements are the finite Dyck
paths; the remaining elements of finite-interval type are the infinitely
rebounding paths; the ray-type elements are non-compact suprema realised by no
path. Coinductively, the paths are the inhabitants of $nu X . (D_"fin" times X)$
where $D_"fin" = mu Y . (1 + Y times Y)$ generates the finite excursions.

== Model II
The carrier is the sub-collection of the enlarged down-set algebra
consisting of the elements of unbounded support:
$
  cal(H)^"sup" = { D in cal(O)("Int"_infinity (omega)) :
    "supp"(D) "unbounded in" omega }.
$
It is closed under arbitrary nonempty joins, and under relative
pseudocomplementation, since
$ "supp"(D -> E) = (omega without "supp"(D)) union "supp"(E) supset.eq "supp"(E). $
It has no least element and no minimal elements, and meets are only partial: the
infimum of $D$ and $E$ exists exactly when $"supp"(D) inter "supp"(E)$ is
unbounded, and then coincides with $D inter E$. Pseudocomplementation is
unavailable, requiring a bottom that has been removed. Coinductively the carrier
is a proper subset of $nu X . (D_"fin" times X + X)$, cut out by the condition
that nontrivial content be emitted cofinally often.

= The logic of unbounded intervals

Both models interpret a propositional language whose worlds are stretches of
time and whose implication quantifies over sub-stretches. Everything they share
--- the line of time, the valuation schema, the connectives that use the
interval order --- is fixed first, so that each model can afterwards be given by
its own two decisions: which stretches of time count as worlds, and which
propositions are admitted.

== Common ground

=== Time states and intervals

Let $T = omega = {t_0, t_1, t_2, dots}$ be an infinite discrete linearly ordered
set, $t_0 < t_1 < t_2 < dots.c$, whose elements are called _time states_. Write
$ [t_i, t_j] = { t | t_i <= t <= t_j }, quad i <= j < omega $
for a _bounded_ interval and $[t_i, infinity) = { t | t >= t_i }$ for a _ray_,
and put
$
  "Int"_b (T) = { [t_i, t_j] : i <= j < omega }, quad
  "Int"_infinity (T) = "Int"_b (T) union { [t_i, infinity) : i in omega },
$
both partially ordered by inclusion. This is the first decision: Model I
evaluates over $"Int"_b (T)$ alone, so that rays are _not_ intervals of $T$
there; Model II evaluates over $"Int"_infinity (T)$.

=== Valuation

Fix a set $W$ of worlds --- $"Int"_b (T)$ or $"Int"_infinity (T)$ --- ordered by
inclusion, and a propositional language $cal(L)$. A valuation is a map
$ v : cal(L) --> 2^W : phi mapsto v_phi : W --> {0, 1}, $

and we write $phi(I)$ for $v_phi (I)$. A proposition $phi$ is _valid_ when
$phi(I) = 1$ for every $I in W$. On whichever of the connectives $cal(L)$
contains, the clauses are pointwise:

- $(phi or psi)(I) = 1$ whenever $phi(I) = 1$ or $psi(I) = 1$;
- $(or.big_k phi_k)(I) = 1$ whenever $phi_k (I) = 1$ for some $k$;
- $(phi and psi)(I) = 1$ whenever $phi(I) = 1$ and $psi(I) = 1$;
  $psi(I) = 1$.

Infinitary disjunction is present in both models, and it is not a convenience:
over an infinite time domain an antichain of intervals may be infinite, so
finite disjunction no longer suffices for the normal forms below.

=== The order-sensitive connectives

So far the partial order of $W$ plays no role. The connectives that use it are

- $(square phi)(I) = 1$ when $phi(J) = 1$ for all $J subset.eq I$;
- $(lozenge phi)(I) = 1$ when $phi(J) = 1$ for some $J subset.eq I$;
- $(phi arrow.squiggly psi)(I) = 1$ when, for all $J subset.eq I$, if
  $phi(J) = 1$ then $psi(J) = 1$;
- $(tilde.op phi)(I) = 1$ when $phi(J) = 0$ for all $J subset.eq I$.

In every clause $J$ ranges over the worlds below $I$, so the same four
definitions read differently in the two models: over $"Int"_infinity (T)$ the
quantifier reaches sub-rays as well as bounded subintervals. Note that
$tilde.op phi$ is $phi arrow.squiggly bot$ and so presupposes a falsum; it is
available in Model I only.

=== The hereditary fragment

Put
$ Theta(W) = { phi | phi -> square phi "is valid" }, $
so that $phi in Theta(W)$ exactly when truth of $phi$ at a world carries to
every world below it. As in the finite case, $Theta(W)$ is closed under $and$
and $or$ --- and, by the same argument, under arbitrary $or.big$ --- but not
under $not$ nor under $->$; witnesses are recorded in Model I, whose punctual
atoms make them easy to write down. Replacing $not$ and $->$ by $tilde.op$ and
$arrow.squiggly$ is what repairs this. Both models work inside a hereditary
fragment, and which one is the second decision.

== Model I --- infinite rebound

Worlds are the bounded stretches of time, $W = "Int"_b (T)$, and no proposition
is excluded. Since no world witnesses the unbounded future, no "henceforth"
operator is available here.

=== Propositions

The set $"ITL"_omega$ is defined recursively:

- $bot, top in "ITL"_omega$; and $epsilon_i in "ITL"_omega$ for every
  $i in omega$ (the propositional variables);
- if $phi, psi in "ITL"_omega$, then
  $phi or psi, thick phi and psi, thick phi -> psi, thick not phi in
  "ITL"_omega$;
- if ${phi_k}_(k in K) subset.eq "ITL"_omega$, then
  $or.big_(k in K) phi_k in "ITL"_omega$.

In grammar form,
$
  phi ::= epsilon_i | bot | top | phi and phi | phi or phi | or.big_k phi_k
  | phi -> phi, quad "with" quad not phi := phi -> bot
$
--- the full intuitionistic signature, the infinitary join apart. The atoms are
_punctual_,
$ epsilon_i (I) = 1 quad <==> quad I = [t_i, t_i] = {t_i}, $
and the remaining clauses are those fixed above, read over $"Int"_b (T)$.

=== The hereditary fragment

Put
$
  Theta_omega = Theta("Int"_b (T)) inter "ITL"_omega
  = { phi in "ITL"_omega | phi -> square phi "is valid" },
$
so that $phi in Theta_omega$ exactly when truth of $phi$ on an interval carries
to all of its subintervals. The failures of closure announced above are
witnessed here: $phi = epsilon_i or epsilon_(i+1)$ is hereditary while $not phi$
is not, and $(phi, psi) = (epsilon_1 or epsilon_2, thick epsilon_2)$ is a
hereditary pair whose implication is not. Both counterexamples are local and
transfer verbatim from the finite case, and both are repaired by passing to
$tilde.op$ and $arrow.squiggly$. Writing
$overline(phi) = tilde.op tilde.op phi$ and
$epsilon_I = or.big_(i in I) epsilon_i$, one has as before
$overline(epsilon_I)(J) = 1$ if and only if $J subset.eq I$.

=== Quotient and normal form

The quotient $[Theta_omega] = Theta_omega \/ arrow.l.r.double$, equipped with
$and, or, tilde.op, arrow.squiggly$, is a *complete* Heyting algebra, isomorphic
to $cal(O)("Int"_b (omega))$. Ferrari's Lemma 3.7 becomes: for every
$phi in Theta_omega$ there is a unique antichain ${I_alpha}$ of _generalized_
intervals --- bounded intervals together with at most one ray $[t_i, infinity)$ ---
such that
$ phi arrow.l.r.double or.big_alpha overline(epsilon_(I_alpha)). $
The ray case is unavoidable and is the one genuine break with the finite
statement: when the intervals on which $phi$ holds form an ascending chain with
no maximal member, no bounded interval represents the join, and
$epsilon_([t_i, infinity)) = or.big_(j >= i) epsilon_j$ is needed. Rays occur
here as _disjunctions_, never as evaluation points.

== Model II --- infinite support

Worlds now include the unbounded stretches, $W = "Int"_infinity (T)$, so
propositions are evaluated at rays as well as at bounded intervals and
"henceforth" becomes meaningful. Against that, only the propositions of
unbounded support are admitted, and the fragment so cut out is not closed under
all the connectives.

=== Propositions

We take as primitive the _hereditary interval atoms_ $pi_I$, one for each
$I in "Int"_infinity (T)$, and close under disjunction and $arrow.squiggly$:
$ phi ::= pi_I | top | phi or phi | or.big_k phi_k | phi arrow.squiggly phi. $
Neither $bot$ nor $and$ occurs, for the reason recorded under _Closure_ below;
the trade is exact --- one gains a temporal modality and loses a constant
together with a connective. Taking $pi_I$ primitive, rather than defining it as
$tilde.op tilde.op epsilon_I$, is deliberate: $tilde.op$ requires $bot$, which
is absent here. The atoms are not punctual but hereditary by construction,
$ pi_I (J) = 1 quad <==> quad J subset.eq I, $
and here $J$ ranges over sub-rays of $I$ as well as over bounded subintervals.

=== Henceforth

Set $G_i := pi_([t_i, infinity))$, read _we are at or after instant $i$_, so that
$
  G_i (I) = 1 quad <==> quad I subset.eq [t_i, infinity) quad <==>
  quad min I >= t_i .
$
It is hereditary, hence lies in $Theta$, and it is the modality that the
enlarged interval structure makes meaningful: in Model I no evaluation point is
a ray, so the corresponding proposition exists but is witnessed by no world.

=== The admissible fragment

For $phi in Theta("Int"_infinity (T))$ put
$
  "supp"(phi) = { i in omega : phi([t_i, t_i]) = 1 }, quad
  Theta^"sup" = { phi in Theta | "supp"(phi) "unbounded in" omega }.
$
Every $phi in Theta^"sup"$ is equivalent to $or.big_alpha pi_(I_alpha)$ for a
unique antichain of generalized intervals with $union.big_alpha I_alpha$
unbounded --- the propositional form of _the path has infinite support_, excluding
exactly the paths $v(u d)^omega$.

=== Closure

$Theta^"sup"$ is closed under $or$ and under arbitrary $or.big$, since
$"supp"(phi or psi) supset.eq "supp"(phi)$; and under $arrow.squiggly$ whenever
the consequent is admissible, since
$
  "supp"(phi arrow.squiggly psi) =
  (omega without "supp"(phi)) union "supp"(psi).
$
It is *not* closed under $and$: taking $phi$ with support the even instants and
$psi$ with support the odd ones, both are admissible while
$"supp"(phi and psi) = emptyset$. Moreover $bot in.not Theta^"sup"$, so
$tilde.op$ is undefined. This is why the signature above omits both.

== The operators at a glance

#let lbl(x) = text(weight: 600, size: 9pt, x)
#let note(x) = text(fill: cgray, size: 8.5pt, style: "italic", x)
#let yes = align(center, text(fill: cteal, weight: 700)[$checkmark$])
#let no = align(center, text(fill: cgray)[---])

#table(
  columns: (5.2em, 1fr, 2.6em, 2.6em),
  stroke: (x, y) => (
    top: if y == 0 { 0.8pt } else { 0.3pt + cgray.lighten(50%) },
    bottom: 0.3pt + cgray.lighten(50%),
    rest: none,
  ),
  inset: (x: 7pt, y: 5.5pt),
  align: (left + horizon, left + horizon, center + horizon, center + horizon),

  lbl[Syntax],
  lbl[Semantics --- $phi(I) = 1$ when],
  align(center, text(fill: cteal, weight: 700)[I]),
  align(center, text(fill: cpurp, weight: 700)[II]),

  $epsilon_i$, [$I = [t_i, t_i]$ #note[--- punctual atom]], yes, no,
  $pi_I$, [$J subset.eq I$ #note[--- hereditary atom, one per $I in W$]], no, yes,
  $bot$, [never], yes, no,
  $top$, [always], yes, yes,
  $phi and psi$, [$phi(I) = 1$ and $psi(I) = 1$], yes, no,
  $phi or psi$, [$phi(I) = 1$ or $psi(I) = 1$], yes, yes,
  $or.big_k phi_k$, [$phi_k (I) = 1$ for some $k$], yes, yes,
  $not phi$, [$phi(I) = 0$ #note[--- i.e. $phi -> bot$]], yes, no,
  $phi -> psi$, [if $phi(I) = 1$ then $psi(I) = 1$], yes, no,
  $tilde.op phi$,
  [$phi(J) = 0$ for all $J subset.eq I$ #note[--- i.e.
      $phi arrow.squiggly bot$]],
  yes,
  no,

  $phi arrow.squiggly psi$, [for all $J subset.eq I$: if $phi(J) = 1$ then $psi(J) = 1$], yes, yes,
  $square phi$, [$phi(J) = 1$ for all $J subset.eq I$], yes, yes,
  $lozenge phi$, [$phi(J) = 1$ for some $J subset.eq I$], yes, yes,
  $G_i$,
  [$I subset.eq [t_i, infinity)$, i.e. $min I >= t_i$
    #note[--- abbreviates $pi_([t_i, infinity))$]],
  no,
  yes,
)

#note[$I$ and $J$ range over the worlds: $W = "Int"_b (T)$ in Model I, so $J$
  runs over bounded subintervals only; $W = "Int"_infinity (T)$ in Model II, so
  $J$ runs over sub-rays as well. The clauses themselves are unchanged --- only
  the quantifier domain differs.]

#v(0.6em)
#block(inset: (left: 0.4em))[
  #text(size: 9.5pt, style: "italic")[Three departures from the finite
    presentation, in order of severity: infinitary disjunction becomes necessary
    in both models; the normal form requires rays as generalized intervals in both;
    and only in Model II does the carrier fail to be closed under the connectives,
    which forces a reduced signature rather than merely a longer list of clauses.]
]

= Combinatorial properties of unbounded Dyck paths



#bibliography("refs.bib")

#pagebreak()

= Appendix: Model I and Model II at a glance

#let hI(x) = text(fill: cteal, weight: 700, x)
#let hII(x) = text(fill: cpurp, weight: 700, x)
// lbl and note are defined with the side-by-side table above

#v(0.6em)

#table(
  columns: (7em, 1fr, 1fr),
  stroke: (x, y) => (
    top: if y == 0 { 0.8pt } else { 0.3pt + cgray.lighten(50%) },
    bottom: 0.3pt + cgray.lighten(50%),
    rest: none,
  ),
  inset: 8pt,
  align: (left + top, left + top, left + top),

  // ------------------------------------------------ header
  [],
  [#text(fill: cteal, weight: 700, size: 10.5pt)[Model I — infinite rebound]],
  [#text(fill: cpurp, weight: 700, size: 10.5pt)[Model II — infinite support]],

  // ------------------------------------------------ 1. description
  lbl[Description],
  [Completion of the family of finite Dyck lattices. Start from all finite paths
    ordered by padding, adjoin limits. Nothing is excluded; the infinite objects
    appear as limits and are paths that return to the ground line forever.
    #note[Complete Heyting algebra, obtained for free.]],
  [Infinite paths taken as primitive, over a time line enlarged by unbounded
    stretches. Paths that eventually go quiet are refused: the interesting
    behaviour must recur forever.
    #note[Gains a temporal modality, loses bottom and meet.]],

  // ------------------------------------------------ 2. syntax
  lbl[Syntax],
  [$phi ::= p | #hI[$bot$] | top | #hI[$phi and phi$] | phi or phi | phi -> phi$
    #v(0.3em)
    #note[full intuitionistic; #hI[$bot$] and #hI[$and$] present, so $not phi :=
      phi -> bot$ is available. No henceforth: every world is a bounded stretch, so
      the modality would be inert.]],
  [$phi ::= p | top | phi or phi | phi -> phi | #hII[$G_i$] quad (i in omega)$
    #v(0.3em)
    #note[positive fragment; $bot$ and $and$ absent because the carrier is not
      closed under them. #hII[$G_i$] reads _at or after instant $i$_ — meaningful
      only because rays are worlds.]],

  // ------------------------------------------------ 3. grammar
  lbl[Dyck grammar],
  [$E ::= u thin D thin d$, #h(0.4em) $D$ a finite Dyck word
    #v(0.3em)
    $w = E_0 E_1 E_2 dots.c$
    #v(0.3em)
    #note[an $omega$-product of finite excursions, no side condition. $E_i = u d$
      is allowed at every stage, so $v(u d)^omega$ — and $(u d)^omega$ itself — are
      legal words.]],
  [$w = E_0 E_1 E_2 dots.c$ with $E_i eq.not u d$ for infinitely many $i$
    #v(0.3em)
    #h(1em) or #h(0.6em) $w = E_0 dots.c E_m dot.c u^omega$
    #v(0.3em)
    #note[a fairness condition, not expressible by finite lookahead: the syntactic
      face of the carrier being a proper coinductive subset.]],

  // ------------------------------------------------ 4. (co)fixpoints
  lbl[Functor
    #linebreak()
    (co)fixpoints],
  [$D = mu Y . (1 + Y times Y)$ #note[(finite excursions)]
    #v(0.3em)
    $Delta_"I" = nu X . (D times X)$
    #v(0.3em)
    #note[the full final coalgebra — emit a finite excursion, rebound, repeat.
      Algebra: $cal(H)^"reb" = cal(O)("Int"_b (omega))$, a frame.]],
  [$D = mu Y . (1 + Y times Y)$
    #v(0.3em)
    $Delta_"II" subset.neq nu X . (D times X + X)$
    #v(0.3em)
    #note[the summand $+X$ is the unmatched up-step, whence rays; the carrier is
      the fair part only. Algebra: $cal(H)^"sup" = { D : "supp"(D) "unbounded" }$,
      not a sublattice.]],

  // ------------------------------------------------ 5. accepted / rejected
  lbl[Paths accepted
    #linebreak()
    and rejected],
  [*Accepted:* every path returning to the axis infinitely often — including
    $v(u d)^omega$ and $(u d)^omega$ itself, which is the bottom element.
    #v(0.3em)
    *Rejected:* none.
    #v(0.3em)
    *Absent as paths:* the infinite ascents. $u^omega$ and $v dot.c u^omega$ exist
    in the algebra only as non-compact limits of chains of finite paths.],
  [*Accepted:* rebound paths whose excursions recur cofinally, and the
    ray-bearing paths $v dot.c u^omega$ including $u^omega = top$.
    #v(0.3em)
    *Rejected:* every $v(u d)^omega$ — finite content dressed as an infinite
    object — and with them the bottom element.
    #v(0.3em)
    *Consequence:* no minimal elements, meets only partial.],
)

#v(0.8em)
#note[The two carriers overlap: the cofinally-nontrivial rebound paths belong to
  both. What is proper to Model I is the eventually-quiet stratum; what is proper
  to Model II is the ray stratum as genuine paths. Adding limits costs nothing;
  removing paths costs $bot$, $and$ and $not$.]
