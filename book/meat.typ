#let repo = "https://github.com/poyea/meat"
#let rev = sys.inputs.at("rev", default: "main")
#let strict = sys.inputs.at("strict", default: "false") == "true"
#import sys.inputs.at("manifest", default: "/.lake/build/lean.typ"): decls

#let given = math.class("relation", sym.bar.v)

#let stmt-counter = counter("meat-statement")

#let statuses = (
  proved: (glyph: "●", word: "proved", color: rgb("#2e7d32")),
  sorry: (glyph: "◐", word: "sorry", color: rgb("#e65100")),
  informal: (glyph: "○", word: "not in Lean", color: rgb("#616161")),
  open: (glyph: "◇", word: "open", color: rgb("#6a1b9a")),
  missing: (glyph: "✗", word: "missing in Lean", color: rgb("#c62828")),
)

#let source-url(file, from: none, to: none) = {
  let url = repo + "/blob/" + rev + "/" + file
  if from != none { url += "#L" + str(from) + "-L" + str(to) }
  url
}

#let badge(status) = {
  let s = statuses.at(status)
  text(size: 8.5pt, fill: s.color)[#s.glyph #s.word]
}

#let entry-status(kind, name) = {
  let e = decls.at(name, default: none)
  if e == none {
    if strict { panic("Lean declaration not found: " + name) }
    "missing"
  } else if kind == "Open problem" {
    if strict and e.kind == "theorem" {
      panic("An open problem must be a Prop definition, not a theorem: " + name)
    }
    "open"
  } else if e.sorry {
    "sorry"
  } else {
    "proved"
  }
}

#let worst(states) = {
  for s in ("missing", "sorry", "open", "proved") {
    if s in states { return s }
  }
  "informal"
}

#let lean-source(e, mode) = {
  let all = read("/" + e.file).split("\n")
  if e.endLine > all.len() {
    panic("The manifest is out of date for " + e.file + ". Run `lake exe manifest` again.")
  }
  let lines = all.slice(e.line - 1, e.endLine)
  let src = lines.map(l => l.trim("\r", at: end)).join("\n")
  if mode == "statement" or (mode == auto and e.kind == "theorem") {
    let i = src.position(":=")
    if i != none { src = src.slice(0, i).trim(at: end) }
  }
  src
}

#let lean-code(e, mode) = block(
  width: 100%,
  breakable: false,
  fill: luma(247),
  stroke: (left: 1.5pt + luma(200)),
  inset: (x: 8pt, y: 6pt),
  {
    show raw.where(block: false): set text(size: 8pt)
    grid(
      columns: (1fr, auto),
      raw(e.name),
      link(source-url(e.file, from: e.line, to: e.endLine), raw(e.file + ":" + str(e.line))),
    )
    v(-2pt)
    raw(lean-source(e, mode), lang: "lean", block: true)
  },
)

#let statement-number(loc) = {
  str(counter(heading).at(loc).first()) + "." + str(stmt-counter.at(loc).first())
}

#let uses-line(deps) = if deps.len() > 0 {
  context {
    let stmts = query(<meat-statement>)
    let seen = (:)
    for d in deps {
      let hit = stmts.find(m => d in m.value.names)
      if hit == none {
        seen.insert(d, (key: (1000000, 0, d), body: raw(d)))
      } else {
        let loc = hit.location()
        let num = statement-number(loc)
        let key = (counter(heading).at(loc).first(), stmt-counter.at(loc).first(), "")
        seen.insert(num, (key: key, body: link(loc)[#hit.value.kind #num]))
      }
    }
    let refs = seen.values().sorted(key: r => r.key).map(r => r.body)
    block(above: 0.6em, text(size: 9pt)[_Uses:_ #refs.join(", ")])
  }
}

#let generated(names) = {
  let shown = names.filter(n => n in decls and decls.at(n).statement != none)
  for (i, n) in shown.enumerate() {
    let e = decls.at(n)
    if strict and e.unmapped.len() > 0 {
      panic("No Typst form for " + e.unmapped.join(", ") + " in " + n)
    }
    let tag = if shown.len() > 1 [(#(i + 1)) ]
    let hyps = if e.hyps.len() > 0 [Assume #e.hyps.join([, ]). ]
    block(above: 0.7em, below: 0.7em, emph[#tag#hyps])
    math.equation(block: true, e.statement.body)
  }
}

#let statement(kind, lean: none, uses: (), code: auto, ..args) = {
  let pos = args.pos()
  let title = if type(pos.first()) == str { pos.remove(0) } else { none }
  let body = pos.at(0)
  let proof = pos.at(1, default: none)
  let names = if lean == none { () } else if type(lean) == str { (lean,) } else { lean }
  let status = if names.len() == 0 { "informal" } else {
    worst(names.map(n => entry-status(kind, n)))
  }
  let deps = names
    .map(n => decls.at(n, default: (deps: ())).deps)
    .flatten()
    .filter(d => d not in names)
  deps = (deps + uses).dedup()

  stmt-counter.step()
  [#metadata((kind: kind, title: title, names: names, status: status)) <meat-statement>]
  block(width: 100%, breakable: true, above: 1.4em, below: 1.4em, {
    context grid(
      columns: (1fr, auto),
      column-gutter: 1em,
      [*#kind #statement-number(here())*#if title != none [ (#title)]],
      badge(status),
    )
    v(-0.3em)
    if body == [] { generated(names) } else if kind == "Definition" { body } else { emph(body) }
    uses-line(deps)
    if code != none {
      for n in names {
        if n in decls { lean-code(decls.at(n), code) }
      }
    }
    if proof != none {
      block(above: 0.8em)[_Proof sketch._ #proof #h(1fr) $square$]
    }
  })
}

#let definition = statement.with("Definition")
#let theorem = statement.with("Theorem")
#let lemma = statement.with("Lemma")
#let proposition = statement.with("Proposition")
#let corollary = statement.with("Corollary")
#let open-problem = statement.with("Open problem")

#let source(module) = {
  let file = module.replace(".", "/") + ".lean"
  show raw: set text(size: 8.5pt)
  block(above: 0.4em, below: 1em, link(source-url(file), raw(file)))
}

#let progress() = context {
  let chapters = query(heading.where(level: 1)).filter(h => h.numbering != none)
  let stmts = query(<meat-statement>)
  let order = ("proved", "sorry", "informal", "open", "missing")
  let count(ch, s) = stmts
    .filter(m => counter(heading).at(m.location()).first() == ch and m.value.status == s)
    .len()
  table(
    columns: (1fr,) + order.map(_ => auto),
    align: (left,) + order.map(_ => center),
    stroke: none,
    table.hline(),
    [*Chapter*], ..order.map(s => badge(s)),
    table.hline(stroke: 0.5pt),
    ..chapters.enumerate().map(((i, h)) => {
      (link(h.location(), h.body),) + order.map(s => {
        let n = count(i + 1, s)
        if n == 0 [] else [#n]
      })
    }).flatten(),
    table.hline(),
  )
}

#let coverage(internal: ()) = {
  heading(numbering: none)[Lean coverage]
  [Each declaration in the Lean library must be in a statement of this book.]
  context {
    let referenced = query(<meat-statement>).map(m => m.value.names).flatten()
    let left = decls.keys().filter(n => n not in referenced and n not in internal).sorted()
    // The first layout pass sees no statements yet, so only a populated pass may fail the build.
    if strict and referenced.len() > 0 and left.len() > 0 {
      panic("Lean declarations missing from the book: " + left.join(", "))
    }
    if left.len() == 0 [
      All #decls.len() declarations are in the book.
    ] else [
      These #left.len() declarations are not in the book:
      #list(..left.map(n => {
        let e = decls.at(n)
        link(source-url(e.file, from: e.line, to: e.endLine), raw(n))
      }))
    ]
  }
}

#let book(title: none, subtitle: none, body) = {
  set document(title: title)
  set page(paper: "a4", margin: (x: 2.4cm, y: 2.5cm))
  set text(font: "New Computer Modern", size: 10.5pt)
  set par(justify: true)
  set raw(syntaxes: "lean4.sublime-syntax")
  show raw: set text(font: "DejaVu Sans Mono")
  show raw.where(block: true): set text(size: 7.2pt)
  show raw.where(block: false): set text(size: 9pt)
  show link: set text(fill: rgb("#1a4f8b"))
  set heading(numbering: "1.1")
  show heading: set block(above: 1.6em, below: 0.9em)
  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    stmt-counter.update(0)
    set text(size: 18pt)
    v(1.5cm)
    it
  }

  page(numbering: none, align(center + horizon, {
    text(size: 30pt, weight: "bold", title)
    v(0.6em)
    text(size: 14pt, subtitle)
    v(2em)
    text(size: 10pt, link("https://github.com/poyea"))
  }))

  set page(
    header: text(size: 9pt)[
      #smallcaps[_#title Notes by #link("https://github.com/poyea")[\@poyea]_]
      #h(1fr)
      #emph(datetime.today().display())
      #h(1fr)
      #emph(link(repo)[poyea/meat])
    ],
    footer: context align(right, text(size: 9pt, counter(page).display("1"))),
  )
  counter(page).update(1)
  heading(numbering: none, outlined: false)[Contents]
  outline(title: none, depth: 2)

  heading(numbering: none)[How to use this book]
  [
    Each definition and each theorem identifies the Lean declaration that it describes.
    Each one also shows the source of that declaration.
    The build calculates the status of each statement from the Lean code:
  ]
  list(
    [#badge("proved"): the Lean declaration exists, and no declaration that it uses contains `sorry`.],
    [#badge("sorry"): the statement is in Lean, but its proof or a proof that it uses is `sorry`.],
    [#badge("informal"): the statement is only in this book.],
    [#badge("open"): the statement is an open problem. Lean states it as a `Prop`, not as a theorem.],
    [#badge("missing"): the book identifies a Lean declaration that does not exist.],
  )
  [
    The _Uses_ line shows the statements that this statement uses in Lean.
    Lean generates the statements of most theorems.
    For these theorems, the statement in this book is the statement that Lean checks.
  ]
  v(1em)
  progress()

  body
}
