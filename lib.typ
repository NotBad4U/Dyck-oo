#import "@preview/cetz:0.3.4"

// ---------- palette ----------
#let cteal   = rgb("#1D9E75")
#let ctealD  = rgb("#0F6E56")
#let camber  = rgb("#EF9F27")
#let camberD = rgb("#B26E0A")
#let cred    = rgb("#E24B4A")
#let credD   = rgb("#A32D2D")
#let cpurp   = rgb("#7F77DD")
#let cpurpD  = rgb("#534AB7")
#let cgray   = rgb("#5F5E5A")
#let caxis   = rgb("#888780")

// ---------- helpers ----------
// Turn a word over {u,d} into a list of CeTZ points.
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

#let solid(col)  = (paint: col, thickness: 1.6pt, join: "round")
#let dashed(col) = (paint: col, thickness: 1.6pt, dash: "dashed")

// A support band on the axis from abscissa a to b (in path units).
#let band(a, b, col, dx: 0.32, alpha: 100%) = {
  import cetz.draw: *
  rect((a * dx, -0.10), (b * dx, -0.22),
       fill: col.transparentize(100% - alpha), stroke: none, radius: 0.04)
}

#let axis(len, dx: 0.32) = {
  import cetz.draw: *
  line((-0.15, 0), (len * dx + 0.55, 0),
       stroke: 0.5pt + caxis, mark: (end: ">", scale: 0.7))
}

#let ell(x, y, col, dx: 0.32) = {
  import cetz.draw: *
  content((x * dx + 0.35, y), text(fill: col, size: 12pt)[$dots.c$])
}
