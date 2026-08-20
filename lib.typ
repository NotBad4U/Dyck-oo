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
  import cetz.draw: line, grid as grid-lines, content

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
  import cetz.draw: line, circle, content

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
  import cetz.draw: line, circle, content

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
