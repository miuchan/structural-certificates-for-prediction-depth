// The plotted example fixes i = 0, T = 4 and v = 1 in both panels.
// At backward step k the initial control site is j(k) = (3 - k)u + k.
#let control-panel(u) = {
  let grid-ink = luma(80%)
  let trace-ink = rgb("275665")
  let x(k) = 32pt + 29pt * k
  let y(j) = 76pt - 15pt * j
  let site(k) = (3 - k) * u + k
  let draw-line(from, to, stroke) = place(top + left, line(start: from, end: to, stroke: stroke))
  let label-at(x, y, body) = place(top + left, dx: x - 8pt, dy: y - 6pt,
    box(width: 16pt, height: 12pt, align(center + horizon, body)),
  )
  let heading = if u == 1 { $u = v = 1$ } else { $u = 0, v = 1$ }

  block(width: 148pt, height: 96pt)[
    #set text(size: 9pt)
    #place(top + center, text(size: 10pt, heading))
    #for k in range(4) {
      draw-line((x(k), y(3)), (x(k), y(0)), 0.45pt + grid-ink)
      label-at(x(k), y(0) + 10pt, $#k$)
    }
    #for j in range(4) {
      draw-line((x(0), y(j)), (x(3), y(j)), 0.45pt + grid-ink)
      label-at(x(0) - 10pt, y(j), $#j$)
    }
    #draw-line((x(0), y(site(0))), (x(3), y(site(3))), 1pt + trace-ink)
    #for k in range(4) {
      place(top + left, dx: x(k) - 2.5pt, dy: y(site(k)) - 2.5pt,
        circle(radius: 2.5pt, fill: trace-ink, stroke: none),
      )
    }
    #label-at(x(0) - 12pt, y(3) - 11pt, $j(k)$)
    #label-at(x(3) + 11pt, y(0) + 10pt, $k$)
  ]
}

#let transported-control-figure(caption: none, alt: none, supplement: auto) = figure(
  grid(columns: (auto, auto), gutter: 20pt, control-panel(1), control-panel(0)),
  kind: image,
  caption: caption,
  alt: alt,
  supplement: supplement,
)
