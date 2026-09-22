# AL. Design consult — a producer for `Moise341` (34.1) without circularity, and the supplier of the §34 face balls

*请用中文回答；Lean 标识符与公式保持原样。这是整体结构设计，不是逐叶审查：请给出一个完整、自洽的方案（精确的数学陈述 + Lean 接口形状 + 证明梗概），篇幅可到 2500 字；先给结论。*

**Where.** https://github.com/liao9yuan/differential-geometry-dev, branch `moise-integration`
(snapshot `93051952`), `DifferentialGeometry/Topology/PiecewiseLinear/`. Ledger `FREE_INPUTS.md`;
digests `consult/A-section34-lemma-list.md` (§0 citation census, §2 Lemmas 1–4), `consult/T-…`,
`consult/AH/AJ-…` (P2–P5 reviews).

## 1. The dependency problem (found by the lead's inventory, 2026-09-21)

Named proposition `Moise341` (`MoiseChain.lean:99`): a PL 3-ball `C ⊆ ℝ³`, an embedding `h` of
`C`, `ε > 0` ⟹ a PL homeomorphism `f` on `C` with `dist (f x) (h x) < ε`. **It has no producer.**

Its consumers, all skeletons on the goal path:
* `Skeleton/ControlledGraphNeighborhood.lean` (controlled 35.1): the vertex approximation
  `Moise341.exists_section34VertexApproximation` (proved from `h341`) and the piercing package
  leaf. This matches the book: 35.1 (p. 249) uses 34.1 to produce `f_v : C''_v → M₂`.
* `Skeleton/Section34Normalization.lean` (P2–P5): the face-ball leaf
  `exists_section34FaceBalls (h341 : Moise341) (hU) (hh) (hcut) (hctrl) (hgraph) : ∃ fbl fblBd,
  Section34FaceBallInvariants …` — the worker used 34.1 for "approximation and general position"
  of the `C_σ`. **The book does not:** Lemma 3 (p. 240) takes small 3-cell neighbourhoods `C₁ ⊆ Int C₂`
  of `σ` with a spherical shell between them and gets a polyhedral 3-cell from **30.5** (the tame
  version), then adjusts to general position; Lemma 4 uses Lemma 2 (30.8). The A side of the ledger
  delivers exactly `Moise305Tame` (`TameNestedCells.lean:27`, PROVED from `Moise304`):
  `C₁ ⊆ interior C₂` topological 3-cells, `closure (C₂ \ C₁)` a spherical shell, `frontier C₂`
  bicollared ⟹ a PL ball `C` with `C₁ ⊆ interior C ⊆ C ⊆ interior C₂`. Ledger row B1.e ("how A's
  output enters P3/P4") is still "not stated in Lean".

The only route to `Moise341` in the tree is circular:
`Moise341 ⇐ Moise352 3 ⇐ Moise352Open 3` (`Moise352OfOpen.lean:40`, inward push proved)
`⇐ Section34CellDiagram` (terminal skeleton) `⇐ Section34NormalFamilyStatement` (P2–P5)
`⇐ ControlledGraphNeighborhoodStatement` (controlled 35.1) `⇐ Moise341`.

In the book the order is 33.1 → **34.1 (§34 on a compact ball, Lemmas 1–11 + the seven-stage
extension)** → 35.1 → 35.2. So 34.1 needs its own producer from `Moise331`, `Moise305Tame`,
`moise308Nested` and the §34 machinery, and the P2–P5 face-ball leaf must consume `Moise305Tame`,
not `Moise341`.

## 2. What exists

* The open-source §34 pipeline, all skeletons, all leaf statements frozen by review:
  P0 `Section34ControlStatement` (a locally finite triangulation of an open `U ⊆ M₁` in some
  `ℝ^N`, carriers `Section34CarrierControl`); controlled 35.1
  `ControlledGraphNeighborhoodStatement` (from `𝒦`, carriers: `Section34CutFrame U 𝒦 𝒦' src srcBd`
  and `Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁`); P2–P5 `Section34NormalFamilyStatement`
  (face balls, Operations 1–2, terminal family, `Section34Trace`); terminal
  `Section34CellDiagram` (P6–P8). All predicates live in `Section34Frame.lean` and take `U : Set M₁`
  with `𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U` (the realisation `map` is a bijection onto `U`);
  openness of `U` enters only through explicit hypotheses `hU : IsOpen U` in some leaves (P3, P4,
  the P0 leaves) and through `Section34Exterior` (Lemma 5(7) in manifold form: the "unbounded
  component" is replaced by "the component reaches the frontier of the carrier `H t`").
* `Moise331` (33.1; skeleton `Section33Approximation`, 12 frozen leaves) gives `N`, `f₁` on the
  derived neighbourhood of the 1-skeleton of a finite graph in `ℝ³`.
* `moise308Nested` PROVED (30.8 in nested-torus form); `Moise305Tame` PROVED from `Moise304`.

## 3. Questions

1. **Producer of `Moise341`.** Which of these do you recommend, and give the precise
   interface for it:
   (a) a *compact-ball instance* of the open pipeline: triangulate the PL ball `C` by a finite `K`
   (`IsCombinatorialManifoldWithBoundary 3 K`), set `M₁ = M₂ = ℝ³`, `U := C` (compact, **not
   open**), and reuse the P1–P8 leaf statements verbatim after generalising their `U` — say
   exactly which hypotheses (`IsOpen U`, `Section34Exterior`'s carrier-frontier reading, the
   locally-finite-in-`h '' U` clauses, invariance of domain uses) break for a compact `U` with
   boundary and how to restate them so both instances are covered by ONE set of leaves (the
   skeleton protocol forbids skeletons importing each other, so shared leaves must be shared
   *statements*, hoisted as named propositions into real modules);
   (b) a separate compact-ball skeleton `Skeleton/Section34Compact.lean` with its own leaves
   (Lemma 1 from `Moise331` with the four incidence clauses [ASSERTED], Lemma 2 from
   `moise308Nested`, Lemma 3 from `Moise305Tame`, Lemmas 5–11, the seven-stage extension with the
   cyclic-order gap of stage 2 and the splitting-disk stage), duplicating P2–P8's content in the
   finite setting where "unbounded component of `ℝ³ − …`" is literal;
   (c) an *inward-push* argument that derives 34.1 from the open case restricted to `Int C` **without**
   passing through `Moise352Open`'s proof — e.g. approximate `h` on a collar-shrunk copy and extend
   over the collar — and say why this does not need 35.1 (which needs 34.1).
   For the option you recommend: the statement of each new leaf in tree vocabulary, which frozen
   leaves are reused unchanged, and the assembly order.

2. **P3's supplier.** Restate `exists_section34FaceBalls` with `(h305 : Moise305Tame)` (and
   whatever A-side data it needs) in place of `h341`: what does the leaf need to *produce* the
   spherical-shell pair `C₁ ⊆ Int C₂` around `h '' (Bd σ)` (= `h '' simplexRim 𝒦 s`) inside the
   carrier, and is `IsBicollared (frontier C₂)` obtainable there (source-side shells transported by
   the embedding `h`, or a PL shell in the chart)? Note `h` is a topological embedding, not PL. Also:
   is the *general position* part of Lemma 3 ("minor adjustment") a separate obligation once the
   ball comes from 30.5 — which leaf owns it?

3. **Does controlled 35.1 need the full `Moise341`?** It uses 34.1 inside one chart of `M₂` for a
   ball `Cc w ⊆ U` with `h '' Cc w` in a chart. Is the chart-local special case
   (`Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart`, `ChartLocalApproximation.lean:42`)
   all that is ever consumed, so that the producer of 1 may be stated for `ℝ³` only (as `Moise341`
   is), with the chart transport already proved? Confirm there is no hidden second consumer needing
   34.1 in a general PL 3-manifold.

4. **Ledger accounting.** Which named propositions on the whole route still lack producers after
   your design (`Moise264`, `Moise307`, `Moise303`, `Moise286`, `Moise267`, `Moise341`), and for each
   whether it is a genuine book theorem to be proved (with the book section) or reducible to a
   proved tree result (name it).

**Fixture** for 1–2: `C` = a tetrahedron, `h = g ∘ ψ` with `g` a small non-zero PL shear and `ψ`
non-PL supported in the interior, `ε` smaller than the shear.
