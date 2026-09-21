# F. Is Shalen's 1984 route a better way to the 3-dimensional PL approximation theorem, given this tree?

*Consultation prompt, self-contained. Answer in English or Chinese.*

**Where to look.** Repository (private; reachable through the owner's GitHub account)
**https://github.com/liao9yuan/differential-geometry-dev**, branch **`moise-integration`**
(https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration). Lean paths are
relative to `DifferentialGeometry/Topology/PiecewiseLinear/`. Context: your answers A, A2, D, E
(`consult/*-answer-digest.md`).

## Why we ask

The end point is Moise 36.1 / the PL approximation theorem for homeomorphisms between PL
3-manifolds (`PLApproximationManifold 3`), from which triangulation and the Hauptvermutung
follow. On 2026-09-12 the project chose Moise's §30–36 (pseudo-cells, canonical configurations)
over **P. B. Shalen, "A 'piecewise-linear' method for triangulating 3-manifolds", Adv. Math. 52
(1984) 34–80**, for one reason only, recorded in `PHASE3_APPROXIMATION_PLAN.md` §0.2: Moise's full
text was on the machine and Shalen's paper was not. The owner's original roadmap was organised
along Shalen's lines (covering towers, Nielsen, controlled alignment, Heegaard structure). In
your answer A (Q5) you verified only the bibliographic identification of Shalen's paper. Nobody
has evaluated the route mathematically. Meanwhile the Moise route has proved expensive exactly
where Moise is tersest.

**Where the Moise route stands** (details in `LANES_CODEX_20260920.md`):

* *Loop-theorem side.* `GeneralPositionInDoubleBufferedStatement ∧ DescentStepOrientableStatement
  ∧ OrientableCoverReductionStatement → Moise252 → Moise304 → Moise305Tame` is proved
  (`LoopTheorem/CoverReductionOrientable.lean`). Open: the relative general-position producer;
  the descent step — boundary branches (a marked PL tube round a touching seam), the disjoint
  two-circle closed case, the orientable exclusion of the one-circle case; done: the nested
  two-circle case, the cut-and-paste producers, the complexity induction, the tower.
* *§34–35 side.* `Moise352Open 3 → Moise352 3 → PLApproximationManifold 3` is proved, including
  the non-compact inward push. Open: everything in §34 — the producers P0–P8 (controlled frame,
  joint graph selection needing a *controlled* 35.1, torus generator transfer, face balls,
  protected compression and bigon slide, locally finite normalization, exterior face disks,
  tetrahedron and vertex recognition) and the terminal labelled PL-cell assembly — plus 35.1
  itself (`Moise351`), and upstream `Moise331`, `Moise341`. Built so far for it: corrected 30.8
  (`Moise308Nested`), link connectivity, the marked-circle sector lemma, a uniform ball-family
  extension lemma, a source cut diagram, labelled normalization, tolerance control, chart-local
  34.1, and older layers for 30.4 (spherical shells), toroidal shells, degree-one Hurewicz,
  solid-torus neighbourhoods of trivalent graphs.

## Questions

**Q1. What does Shalen's proof actually consist of?** Please give its dependency graph at the
level of named theorems: what is proved, in what order, and from which standard inputs. We
believe (from memory, unverified — correct us) that it uses the loop theorem / Dehn's lemma via
towers, an algebraic recognition of handlebodies, Nielsen's theorem that automorphisms of a free
group are realised by homeomorphisms of a handlebody, Heegaard-type decompositions, and a
controlled ("aligned") version of these to get approximation rather than mere existence. Which
of these are genuinely needed, and in what generality (compact only? orientable only? with
boundary?) Does it prove the *approximation* theorem with a continuous positive error function
on a non-compact manifold, or a compact/weaker statement from which ours must still be derived?

**Q2. What would it replace, and what would it not?** Specifically:
(a) Is Lemma 2 of the loop theorem (our whole loop-theorem side) still needed? We expect yes.
(b) Does it avoid Moise's §30–33 (30.4–30.8, pseudo-cells, canonical configurations, 33.1) and
§34's P3–P8 (face balls, compressions, bigon slides, recognition of tetrahedra and vertex
neighbourhoods)? These are the most expensive open items we have.
(c) Does it still need a regular-neighbourhood-of-the-1-skeleton step like Moise 35.1, and a
controlled one?
(d) Which of the tree's existing assets listed above would be reused, and which would be
abandoned?

**Q3. What new theory would the tree need that it does not have?** For each item say whether it
exists in Mathlib (we believe Nielsen's generation theorem for `Aut (FreeGroup)` and any theory of
handlebodies or Heegaard splittings do not), how large a formalisation it is, and whether it has
the same "terse source" risk that hurt us in Moise (steps the paper treats as evident: general
position, push-offs, isotopy extension, regular neighbourhood uniqueness, control estimates).
Please be concrete about **regular neighbourhood uniqueness** and **isotopy extension**: the tree
has derived neighbourhoods and several extension lemmas but *no* uniqueness theorem for regular
neighbourhoods and no ambient isotopy extension theorem; does Shalen's argument need them?

**Q4. Honest comparison.** Given the assets and the open lists above, rank: (i) finish Moise
§34–35 as planned; (ii) switch the §34–35 side to Shalen, keeping the loop-theorem side;
(iii) Bing 1959 (which you called "the alternative most worth a separate full audit");
(iv) a hybrid — e.g. Shalen's handlebody argument for the neighbourhood of the 1-skeleton (in
place of 35.1 and P1–P2) feeding Moise's cell-by-cell extension, or the reverse. For each give
the number and nature of the chapter-scale pieces still to be built, and the single most likely
place for a statement-level surprise. A recommendation with its uncertainty is wanted, not a
survey.

**Q5. If the answer is "switch" or "hybrid":** state the first three theorems to formalise, in
Lean-facing form, each with a non-degenerate instance on which all its hypotheses hold
simultaneously, so that we do not repeat the vacuity problems recorded in
`consult/D-answer-digest.md`.
