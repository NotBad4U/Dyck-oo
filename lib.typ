#import "@preview/cetz:0.3.4"

// ---------- palette ----------
#let cteal = rgb("#1D9E75")
#let ctealD = rgb("#0F6E56")
#let camber = rgb("#EF9F27")
#let camberD = rgb("#B26E0A")
#let cred = rgb("#E24B4A")
#let credD = rgb("#A32D2D")
#let cpurp = rgb("#7F77DD")
#let cpurpD = rgb("#534AB7")
#let cgray = rgb("#5F5E5A")
#let caxis = rgb("#888780")
#let cI = rgb("#0F6E56")
#let cII = rgb("#534AB7")
#let cpath = rgb("#2C2C2A")
#let cmute = rgb("#9C9A93")
#let caxis = rgb("#B4B2A9")

#let dyck-points(word, x0: 0.0, y0: 0.0, dx: 0.32, dy: 0.32) = {
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

// ============================================================
//  Dyck path diagrams
// ============================================================
//
// A Dyck word is a string over {u, d}, e.g. "uuddudud".
//
// Usage:
//
//   #dyck-diagram(n: 8, height: 3, {
//     dyck-path("udududud", color: cmute, dots: true)
//     dyck-path("uuddudud", color: cteal, fill: auto, marks: true)
//   })
//
// `dyck-diagram` draws the grid + axes and sets up the coordinate
// system (one unit = one step); `dyck-path` draws inside it, so any
// number of paths (and annotations) can share one diagram.

/// Number of steps of `word`.
#let dyck-len(word) = word.clusters().len()

/// Height profile (h(0), h(1), ..., h(n)) of `word`.
#let dyck-heights(word, y0: 0) = {
  let hs = (y0,)
  let y = y0
  for c in word.clusters() {
    y += if c == "u" { 1 } else { -1 }
    hs.push(y)
  }
  hs
}

/// Smallest grid covering every given word, as `(n: .., height: ..)`.
/// Spread it into the diagram: `#dyck-diagram(..dyck-extent(p, q), { .. })`.
#let dyck-extent(..words, pad: 0) = {
  let ws = words.pos()
  if ws.len() == 0 { return (n: 8, height: 4) }
  (
    n: calc.max(..ws.map(dyck-len)) + pad,
    height: calc.max(1, ..ws.map(w => calc.max(..dyck-heights(w)))) + pad,
  )
}

/// Lattice point reached after `i` steps of `word`, in diagram coordinates.
/// Handy to anchor your own `cetz` drawings onto a path.
#let dyck-at(word, i, start: (0, 0)) = {
  let hs = dyck-heights(word, y0: start.at(1))
  assert(i >= 0 and i < hs.len(), message: "step " + str(i) + " is outside the word")
  (start.at(0) + i, hs.at(i))
}

/// Grid, axes and ticks for Dyck paths. `body` is a `cetz` code block:
/// put `dyck-path(..)` / `dyck-annotate(..)` calls (or raw `cetz.draw`
/// calls) in it.
///
/// - n: width of the grid, in steps.
/// - height: height of the grid; `auto` = `ceil(n / 2)`.
/// - unit: length of one step on the page.
/// - x-ticks, y-ticks: label every k-th tick, or `none` for no labels.
#let dyck-diagram(
  body,
  n: 8,
  height: auto,
  unit: 0.5cm,
  grid: true,
  grid-step: 1,
  grid-stroke: auto,
  axes: true,
  axis-stroke: auto,
  x-ticks: 1,
  y-ticks: 1,
  tick-color: auto,
  tick-size: 0.75em,
  x-label: none,
  y-label: none,
  padding: 0.7,
) = {
  import cetz.draw: content, grid as grid-lines, line

  let h = if height == auto { calc.ceil(n / 2) } else { height }
  let gstroke = if grid-stroke == auto { 0.4pt + rgb("#E9E7E0") } else { grid-stroke }
  let astroke = if axis-stroke == auto { 0.6pt + caxis } else { axis-stroke }
  let tcolor = if tick-color == auto { cmute } else { tick-color }
  let tick = 0.14

  cetz.canvas(length: unit, {
    if grid {
      grid-lines((0, 0), (n, h), step: grid-step, stroke: gstroke)
    }

    if axes {
      let arrow = (end: ">", scale: 0.32, fill: astroke.paint, stroke: astroke)
      line((0, 0), (n + padding, 0), stroke: astroke, mark: arrow)
      line((0, 0), (0, h + padding), stroke: astroke, mark: arrow)
    }

    if x-ticks != none {
      for i in range(0, n + 1, step: x-ticks) {
        line((i, 0), (i, -tick), stroke: astroke)
        content((i, -tick - 0.08), text(tick-size, fill: tcolor)[#i], anchor: "north")
      }
    }
    if y-ticks != none {
      for j in range(1, h + 1, step: y-ticks) {
        line((0, j), (-tick, j), stroke: astroke)
        content((-tick - 0.08, j), text(tick-size, fill: tcolor)[#j], anchor: "east")
      }
    }

    if x-label != none {
      content((n + padding, -tick - 0.45), text(tick-size, fill: tcolor, x-label), anchor: "north-east")
    }
    if y-label != none {
      content((-tick - 0.1, h + padding), text(tick-size, fill: tcolor, y-label), anchor: "south-east")
    }

    body
  })
}

/// One Dyck path, drawn inside a `dyck-diagram`.
///
/// - color: colour of the stroke (and of marks, dots and `fill: auto`).
/// - stroke: full stroke override; `auto` derives it from `color`.
/// - start: lattice point the path starts from.
/// - offset: vertical nudge, to keep overlapping paths distinguishable.
/// - marks: draw a dot at every lattice point.
/// - fill: shade the area under the path (`auto` = `color`, faded).
/// - dots: append a `⋯` to suggest an infinite continuation.
/// - label: content placed just after the end of the path.
#let dyck-path(
  word,
  color: cpath,
  stroke: auto,
  start: (0, 0),
  offset: 0,
  marks: false,
  mark-size: 0.075,
  fill: none,
  dots: false,
  label: none,
  label-size: 0.85em,
) = {
  import cetz.draw: circle, content, line

  let (x0, y0) = start
  let pts = dyck-points(word, x0: x0, y0: y0 + offset, dx: 1, dy: 1)
  let pstroke = if stroke == auto { 1.1pt + color } else { stroke }
  let (xe, ye) = pts.last()
  let drawable = pts.len() >= 2

  if fill != none and drawable {
    let f = if fill == auto { color.transparentize(88%) } else { fill }
    line(..pts, (xe, y0), (x0, y0), close: true, stroke: none, fill: f)
  }

  if drawable { line(..pts, stroke: pstroke) }

  if marks {
    for p in pts { circle(p, radius: mark-size, fill: color, stroke: none) }
  }

  let cursor = xe
  if dots {
    content((cursor + 0.3, ye), text(fill: color)[#sym.dots.c], anchor: "west")
    cursor += 0.95
  }
  if label != none {
    content((cursor + 0.35, ye), text(label-size, fill: color, label), anchor: "west")
  }
}

/// Callout attached to step `i` of `word`, for annotating a path.
/// `dir` is where the label sits relative to the lattice point.
#let dyck-annotate(
  word,
  i,
  body,
  start: (0, 0),
  offset: 0,
  color: cgray,
  dir: (0.6, 0.8),
  dot: true,
  dot-size: 0.09,
  leader: true,
  anchor: auto,
  size: 0.8em,
) = {
  import cetz.draw: circle, content, line

  let (px, py) = dyck-at(word, i, start: start)
  let p = (px, py + offset)
  let q = (px + dir.at(0), py + offset + dir.at(1))

  if dot { circle(p, radius: dot-size, fill: color, stroke: none) }
  if leader { line(p, q, stroke: 0.5pt + color.transparentize(35%)) }
  content(
    q,
    text(size, fill: color, body),
    anchor: if anchor != auto { anchor } else if dir.at(0) >= 0 { "west" } else { "east" },
  )
}

// ============================================================
//  Hasse diagrams whose nodes are Dyck paths
// ============================================================

/// A miniature Dyck path, drawn as a node glyph rather than in a grid.
/// `at` is the centre of the glyph and `w`/`h` its bounding box. `hmax` is the
/// height that fills the box: pass the same value to every glyph of a diagram
/// so that heights stay comparable across nodes (`auto` = this word's own
/// maximum, which rescales each glyph independently).
#let dyck-glyph(
  word,
  at: (0, 0),
  w: 0.8,
  h: 0.3,
  hmax: auto,
  color: cpath,
  thickness: 0.6pt,
  base: true,
) = {
  import cetz.draw: line

  let n = dyck-len(word)
  let hs = dyck-heights(word)
  let mx = if hmax == auto { calc.max(..hs) } else { hmax }
  let dx = w / n
  let dy = if mx == 0 { 0.0 } else { h / mx }
  let (cx, cy) = at
  let x0 = cx - w / 2
  let y0 = cy - h / 2

  if base {
    line((x0, y0), (x0 + w, y0), stroke: (paint: cmute, thickness: 0.4pt, dash: "dotted"))
  }
  line(..hs.enumerate().map(((i, hv)) => (x0 + i * dx, y0 + hv * dy)), stroke: thickness + color)
}

/// Hasse diagram of a lattice of Dyck paths.
///
/// - nodes: `((word, x, y), ..)`, one entry per element; `y` is the rank.
/// - edges: `((lower-word, upper-word), ..)`, one entry per covering pair.
/// - highlight: words to draw in `highlight-color` instead of `color`.
#let dyck-hasse(
  nodes,
  edges,
  unit: 1cm,
  xgap: 1.2,
  ygap: 0.8,
  glyph-w: 0.82,
  glyph-h: 0.3,
  pad: 0.08,
  color: cpath,
  edge-color: auto,
  highlight: (),
  highlight-color: cteal,
  notes: (:),
  note-size: 0.8em,
  note-color: cgray,
  note-dir: "east",
) = {
  import cetz.draw: content, line, rect

  let ecol = if edge-color == auto { cmute } else { edge-color }
  // one height scale for every glyph, so that "lies below" stays readable
  let hmax = calc.max(..nodes.map(((w, x, y)) => calc.max(..dyck-heights(w))))
  let centre = (x, y) => (x * xgap, y * ygap)
  let coord = (:)
  for (w, x, y) in nodes { coord.insert(w, centre(x, y)) }

  cetz.canvas(length: unit, {
    for (a, b) in edges {
      line(coord.at(a), coord.at(b), stroke: 0.5pt + ecol)
    }
    for (w, x, y) in nodes {
      let (cx, cy) = centre(x, y)
      rect(
        (cx - glyph-w / 2 - pad, cy - glyph-h / 2 - pad),
        (cx + glyph-w / 2 + pad, cy + glyph-h / 2 + pad),
        fill: white,
        stroke: none,
      )
      dyck-glyph(
        w,
        at: (cx, cy),
        w: glyph-w,
        h: glyph-h,
        hmax: hmax,
        color: if w in highlight { highlight-color } else { color },
      )
      if w in notes {
        let off = glyph-w / 2 + pad + 0.12
        content(
          (cx + (if note-dir == "east" { off } else { -off }), cy),
          text(note-size, fill: note-color, notes.at(w)),
          anchor: if note-dir == "east" { "west" } else { "east" },
        )
      }
    }
  })
}

// ---------- the Dyck lattice D_4, laid out by rank ----------
// 14 elements, 21 covering pairs; the layout minimises crossings (2 remain).

#let d4-nodes = (
  ("udududud", 0, 0),
  ("ududuudd", -1, 1),
  ("uduuddud", 0, 1),
  ("uuddudud", 1, 1),
  ("uduududd", -1, 2),
  ("uudduudd", 0, 2),
  ("uududdud", 1, 2),
  ("uduuuddd", -1, 3),
  ("uudududd", 0, 3),
  ("uuudddud", 1, 3),
  ("uuduuddd", -0.5, 4),
  ("uuuddudd", 0.5, 4),
  ("uuududdd", 0, 5),
  ("uuuudddd", 0, 6),
)

#let d4-edges = (
  ("udududud", "uuddudud"),
  ("udududud", "uduuddud"),
  ("udududud", "ududuudd"),
  ("ududuudd", "uudduudd"),
  ("ududuudd", "uduududd"),
  ("uduuddud", "uududdud"),
  ("uduuddud", "uduududd"),
  ("uuddudud", "uududdud"),
  ("uuddudud", "uudduudd"),
  ("uduududd", "uudududd"),
  ("uduududd", "uduuuddd"),
  ("uudduudd", "uudududd"),
  ("uududdud", "uuudddud"),
  ("uududdud", "uudududd"),
  ("uduuuddd", "uuduuddd"),
  ("uudududd", "uuuddudd"),
  ("uudududd", "uuduuddd"),
  ("uuudddud", "uuuddudd"),
  ("uuduuddd", "uuududdd"),
  ("uuuddudd", "uuududdd"),
  ("uuududdd", "uuuudddd"),
)

// ---------- schematic of the ambient lattice ----------

/// Sketch of `D_ω` as two strata — finite support below, infinite support
/// above — with the tower `D_1 ⊂ D_2 ⊂ ...` climbing inside the lower one and
/// the join of its tops escaping to `⊤`.
#let omega-sketch(unit: 0.9cm) = {
  import cetz.draw: bezier, circle, content, line, merge-path

  let hw = 2.5 // half-width of the lens
  let ym = 3.3 // height of the finite/infinite divide
  let yt = 6.6 // top vertex

  let wavy = range(0, 49).map(i => {
    let t = i / 48
    (-hw + 2 * hw * t, ym + 0.16 * calc.sin(t * 4 * calc.pi))
  })

  cetz.canvas(length: unit, {
    merge-path(
      {
        bezier((0, 0), (-hw, ym), (-1.9, 0.5))
        line(..wavy)
        bezier((hw, ym), (0, 0), (1.9, 0.5))
      },
      close: true,
      fill: cI.transparentize(92%),
      stroke: 0.6pt + cI.transparentize(45%),
    )
    merge-path(
      {
        bezier((-hw, ym), (0, yt), (-1.9, yt - 0.5))
        bezier((0, yt), (hw, ym), (1.9, yt - 0.5))
        line(..wavy.rev())
      },
      close: true,
      fill: cII.transparentize(92%),
      stroke: 0.6pt + cII.transparentize(45%),
    )
    line(..wavy, stroke: (paint: cgray, thickness: 0.6pt, dash: "dashed"))

    let tops = ((0.55, 0.95), (0.95, 1.60), (1.30, 2.15), (1.60, 2.62))
    for (w, y) in tops {
      merge-path(
        {
          bezier((0, 0), (0, y), (-w, y * 0.42))
          bezier((0, y), (0, 0), (w, y * 0.42))
        },
        close: true,
        stroke: 0.5pt + cI.transparentize(30%),
      )
      circle((0, y), radius: 0.05, fill: cI, stroke: none)
    }
    circle((0, 0), radius: 0.075, fill: cpath, stroke: none)
    circle((0, yt), radius: 0.075, fill: cpath, stroke: none)

    line(
      (0, 2.62),
      (0, yt - 0.12),
      stroke: (paint: cII, thickness: 0.7pt, dash: "dotted"),
      mark: (end: ">", scale: 0.3, fill: cII, stroke: cII),
    )

    content((0, -0.3), text(0.8em, fill: cgray)[$bot = (u d)^omega$], anchor: "north")
    content((0, yt + 0.16), text(0.8em, fill: cgray)[$top = u^omega$], anchor: "south")
    content((-0.16, 0.95), text(0.72em, fill: cI)[$D_1$], anchor: "east")
    content((-0.16, 1.60), text(0.72em, fill: cI)[$D_2$], anchor: "east")
    content((-0.16, 2.15), text(0.72em, fill: cI)[$dots.v$], anchor: "east")
    content((-0.16, 2.62), text(0.72em, fill: cI)[$D_n$], anchor: "east")
    content((0.58, 4.15), text(0.72em, fill: cII)[$or.big_n u^n d^n (u d)^omega = top$], anchor: "west")

    line((1.75, 1.5), (2.9, 1.5), stroke: 0.4pt + cmute)
    content((3.0, 1.5), text(0.8em, fill: cI)[$cal(D)_"fs"$], anchor: "west")
    content((3.0, 1.12), text(0.68em, fill: cmute)[finite support, a down-set], anchor: "west")
    line((1.55, 5.2), (2.9, 5.2), stroke: 0.4pt + cmute)
    content((3.0, 5.2), text(0.8em, fill: cII)[$cal(D)_"is"$], anchor: "west")
    content((3.0, 4.82), text(0.68em, fill: cmute)[infinite support, an up-set], anchor: "west")
  })
}

// ---------- the Dyck lattice D_3 ----------

#let d3-nodes = (
  ("ududud", 0, 0),
  ("uduudd", -0.5, 1),
  ("uuddud", 0.5, 1),
  ("uududd", 0, 2),
  ("uuuddd", 0, 3),
)

#let d3-edges = (
  ("ududud", "uduudd"),
  ("ududud", "uuddud"),
  ("uduudd", "uududd"),
  ("uuddud", "uududd"),
  ("uududd", "uuuddd"),
)

// D_4 laid out so that the image of iota_3 -- the principal down-set below
// u^3 d^3 u d -- occupies the left of each rank, letting the arrows come in
// horizontally. Same lattice as `d4-nodes`, mirrored.
#let d4-nodes-mirror = d4-nodes.map(((w, x, y)) => (w, -x, y))

/// Two Dyck lattices side by side with an order-embedding drawn between them.
///
/// - map: `((source-word, target-word), ..)`, one arrow each.
/// - routes: `(source-word: (start, ctrl1, ctrl2, end), ..)` draws that arrow as
///   an explicit cubic Bezier through the four given points, instead of a
///   straight segment, for targets a straight arrow would run through. Anchor
///   `start` and `end` on the glyph edges so the arrow visibly leaves its
///   source and reaches its target.
/// - highlight: words drawn in `highlight-color` (use it for the image).
#let dyck-hasse-map(
  src-nodes,
  src-edges,
  dst-nodes,
  dst-edges,
  map,
  unit: 1.25cm,
  src-origin: (-4.0, 0),
  dst-origin: (0, 0),
  src-xgap: 1.15,
  dst-xgap: 1.36,
  ygap: 0.96,
  step: 0.108,
  hunit: 0.10,
  pad: 0.07,
  color: cpath,
  edge-color: auto,
  arrow-color: auto,
  highlight: (),
  highlight-color: cteal,
  routes: (:),
  titles: (none, none),
  title-dy: 0.75,
  map-label: none,
  map-label-on: none,
) = {
  import cetz.draw: bezier, content, line, rect

  let ecol = if edge-color == auto { cmute } else { edge-color }
  let acol = if arrow-color == auto { cteal } else { arrow-color }
  let all-words = (src-nodes + dst-nodes).map(((w, x, y)) => w)
  let hmax = calc.max(..all-words.map(w => calc.max(..dyck-heights(w))))
  let gh = hunit * hmax
  let hw = w => step * dyck-len(w) / 2

  let locate = (nodes, origin, xg) => {
    let d = (:)
    for (w, x, y) in nodes {
      d.insert(w, (origin.at(0) + x * xg, origin.at(1) + y * ygap))
    }
    d
  }
  let ca = locate(src-nodes, src-origin, src-xgap)
  let cb = locate(dst-nodes, dst-origin, dst-xgap)

  cetz.canvas(length: unit, {
    // covering relations of both lattices
    for (nodes, edges, c) in ((src-nodes, src-edges, ca), (dst-nodes, dst-edges, cb)) {
      for (a, b) in edges { line(c.at(a), c.at(b), stroke: 0.5pt + ecol) }
    }
    // the embedding
    let tip = (end: ">", scale: 0.3, fill: acol, stroke: acol)
    for (s, t) in map {
      let (ax, ay) = ca.at(s)
      let (bx, by) = cb.at(t)
      if s in routes {
        let (p, c1, c2, q) = routes.at(s)
        bezier(p, q, c1, c2, stroke: 0.6pt + acol, mark: tip)
      } else {
        let p = (ax + hw(s) + pad + 0.05, ay)
        let q = (bx - hw(t) - pad - 0.05, by)
        line(p, q, stroke: 0.6pt + acol, mark: tip)
      }
    }
    // nodes, masking whatever passes behind them
    for (nodes, c) in ((src-nodes, ca), (dst-nodes, cb)) {
      for (w, x, y) in nodes {
        let (cx, cy) = c.at(w)
        rect(
          (cx - hw(w) - pad, cy - gh / 2 - pad),
          (cx + hw(w) + pad, cy + gh / 2 + pad),
          fill: white,
          stroke: none,
        )
        dyck-glyph(
          w,
          at: (cx, cy),
          w: step * dyck-len(w),
          h: gh,
          hmax: hmax,
          color: if w in highlight { highlight-color } else { color },
        )
      }
    }
    if map-label != none and map-label-on != none {
      let (ax, ay) = ca.at(map-label-on)
      let (bx, by) = cb.at(map.find(((s2, t2)) => s2 == map-label-on).at(1))
      content(
        ((ax + hw(map-label-on) + bx - hw(map.find(((s2, t2)) => s2 == map-label-on).at(1))) / 2, ay + 0.16),
        text(0.85em, fill: acol, map-label),
        anchor: "south",
      )
    }
    let (ta, tb) = titles
    if ta != none {
      content((src-origin.at(0), -title-dy), text(0.9em, fill: cgray, ta), anchor: "north")
    }
    if tb != none {
      content((dst-origin.at(0), -title-dy), text(0.9em, fill: cgray, tb), anchor: "north")
    }
  })
}

/// A single miniature Dyck path as standalone content, for a table cell or a
/// run of text. `hmax` fixes the height scale; pass the same value to every
/// call in a group so the pictures stay comparable.
#let dyck-mini(word, unit: 1cm, step: 0.11, hunit: 0.11, hmax: auto, color: cpath) = {
  import cetz.draw: line, circle
  let n = dyck-len(word)
  let m = if hmax == auto { calc.max(1, ..dyck-heights(word)) } else { hmax }
  cetz.canvas(length: unit, {
    if n == 0 {
      circle((0, 0), radius: 0.035, fill: color, stroke: none)
    } else {
      dyck-glyph(
        word,
        at: (step * n / 2, hunit * m / 2),
        w: step * n,
        h: hunit * m,
        hmax: m,
        color: color,
        base: false,
      )
    }
  })
}

/// The first-return decomposition w = u A d B, drawn on u^3 d^3 u d.
/// `A` sits one unit up between the opening u and the closing d; `B` follows
/// the first return.
#let first-return-figure(unit: 0.62cm) = {
  import cetz.draw: line, circle, content
  cetz.canvas(length: unit, {
    line((0, 0), (1, 1), stroke: 1.4pt + camberD)
    line((5, 1), (6, 0), stroke: 1.4pt + camberD)
    dyck-path("uudd", start: (1, 1), color: cI, fill: auto)
    dyck-path("ud", start: (6, 0), color: cII, fill: auto)
    line((-0.3, 0), (8.9, 0), stroke: 0.6pt + caxis)
    line((6, -0.3), (6, 1.15), stroke: (paint: cmute, thickness: 0.5pt, dash: "dashed"))
    circle((6, 0), radius: 0.1, fill: camberD, stroke: none)
    circle((0, 0), radius: 0.1, fill: camberD, stroke: none)
    content((3, 1.62), text(0.8em, fill: cI)[$A$], anchor: "south")
    content((7, 1.18), text(0.8em, fill: cII)[$B$], anchor: "south")
    content((0.30, 0.66), text(0.78em, fill: camberD)[$u$], anchor: "east")
    content((5.30, 0.66), text(0.78em, fill: camberD)[$d$], anchor: "east")
    content((6, -0.5), text(0.72em, fill: cmute)[first return], anchor: "north")
  })
}
