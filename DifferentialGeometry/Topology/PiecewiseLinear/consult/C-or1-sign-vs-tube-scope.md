# C-or1 — marked sign route vs. tube route: scope decision (2026-09-21)

Read-only scoping of ledger item A2.3.b. Paths relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.

## 0. Bottom line

**Keep the tube route.** The sign argument is the same argument as the tube argument (both say: the
normal circle of `Γ` has orientation-reversing monodromy), and here it is *strictly more expensive*:
it duplicates the one genuinely hard obligation of the tube leaf (the marked link trace at every
face of `Γ`) **and** must build from scratch the orientation bridge — an oriented link circle of an
edge, transported through branch vertices — which the tube route already owns as proved code.
Answer to D: both routes need the same bridge; only the tube route has it. §5 gives two cheapenings.

## 1. What `IsOrientable` is here, and what chart-level orientation facts exist

`IsOrientable n K := Nonempty (CoherentOrientation n K)` (`Orientation.lean:434`), where
`CoherentOrientation` (:424) is a `LinearOrder E` on vertices, a `sign : Finset E → ℤ` that is `±1`
on every `n`-simplex, and coherence `orientedBoundary vertexOrder K n sign t = 0` (:258) at every
`(n−1)`-face with `≠ 1` cofaces. Moise 23.14; purely combinatorial.

* **Restriction/transport, proved.** `IsOrientable.of_le` (:3153), `.boundary` (:3105),
  `.barycentricSubdivision` (:5447), `.subdivision` (:8252), `.of_isSubdivision` (:8454),
  `.double` (:5185), `.of_isGlueIso` (:1148), `.of_isPLHomeomorphOn_subset`
  (`MobiusEmbedding.lean:19`), `.of_space_subset` (:37, **equal dimension only**),
  `isOrientable_derivedNeighborhood_of_isSubdivision` (`…TubeCarrier.lean:135`).
* **Local orientation data, combinatorial, proved.** `isOrientable_faceStarComplex`
  (`Orientation.lean:8586`), `localOrientationSign` (`OrientationCocycle.lean:23`),
  `localSubdivisionOrientationSign` (:153) and `_pair_cancel` (:319),
  `affineSimplexOrientationSign` (`AffineOrientation.lean:107`), the ℤ/2 cocycle
  `orientationCocycle` (:110) with `orientationCocycle_isCoboundary_iff` (:431),
  `isOrientable_iff_forall_walkMonodromy_eq_zero` (`PolygonNeighborhoodOrientation.lean:48`), and
  the orientation double cover `isOrientable_coveringComplex_orientationCocycle`
  (`CoveringOrientation.lean:871`).
* **The only bridge to a geometric orientation statement** is the Möbius chain:
  `not_isOrientable_mobiusComplex` (`MobiusBand.lean:333`) →
  `not_isPLHomeomorphOn_mobiusComplex_of_isOrientable` (`MobiusEmbedding.lean:46`) →
  `isPLCirclePositive_of_isOrientable_cylindricalDiagram` (:56) →
  `IsCylindricalDiagram.boundary_isPLCirclePositive_of_bottom_eq_top`
  (`CylindricalMonodromy.lean:78`), landing in `IsPLCirclePositive`
  (`CircleAnnulusOrientation.lean:208`) — exactly "the cross-section circle is oriented and the
  monodromy preserves it". `not_closedBranchCase1` (`ClosedBranchOrientability.lean:289`) consumes
  `IsOrientable 3 M` only through that chain.

**Absent everywhere in the tree:** any statement that a chart transition (of
`combinatorialChartedSpace` or of any atlas) is orientation preserving; any notion of
orientation-preserving PL homeomorphism of open subsets of `ℝ³`; any use of Mathlib's
`Orientation`/`positiveOrientation` in the PL tree; any coupling between `IsOrientable` and
`Topology/Homology/Local/*` or `Topology/LocalDegree/*` (checked file by file: no file mentioning
`IsOrientable` mentions `localHomology`, `fundamentalClass`, `LocalDegree` or
`OrientationPreserving`); any orientation of an edge link or a vertex-link sphere —
`IsOrientable.boundary` gives *orientability*, not a chosen class.

The marked charts are arbitrary `OpenPartialHomeomorph M (ℝ × ℝ × ℝ)`: the frozen
`IsMarkedCrossingChartAt` (`LoopTheorem/ClosedBranchCaseOneTransport.lean:59`) has **no** PL,
atlas-membership or orientation clause (the design dropped `IsPiecewiseAffineOn e` as ill typed
over a charted `M`). Its producer (`…MarkedChart.lean:663`) does build `e` from an atlas chart
composed with a `LinearEquiv` and a sign rescaling, but none of that survives into the statement,
and its docstring records that no orientation and no sheet comparison is used.

## 2. A — the cheapest rigorous `σ`, and where the sign argument breaks

The *local* step is free and correct. In a marked chart at `a`, the sheet through `a` is
`(e z).2.2 = 0` with positive ray `(e z).2.1 > 0`, the sheet through `τ a` is `(e z).2.1 = 0` with
positive ray `(e z).2.2 > 0`, the branch is `(e z).2 = 0`. The chart at `b = τ a` presents the same
ambient point with the sheets exchanged, so `e_b ∘ e_a⁻¹` preserves the flag `{branch} ⊂ {sheet}`
and the four marked half-planes while swapping `x` and `y`: flag sign `−1`, finite data, no degree
theory. The transport around `Γ` is where it breaks.

Option (i) — **chart-transition flag sign — is not usable.** (a) No bridge exists from
`IsOrientable 3 L` to any sign of a chart transition; building one means re-freezing the proved
A2.3.a statement with PL-in-coordinates clauses, or a new local-homology/degree theory for
`IsOrientable` — a new foundational layer with nothing to build on. (b) More fundamentally, the
flag sign is defined only for two charts **at the same point with the same flag**, while the
contradiction needs it transported once around `Γ`, where the flag moves; a chain of overlapping
marked charts "with collar sides and branch direction transported continuously" *is* a
trivialisation of the normal data along `Γ`, i.e. the tube.

Option (ii) — **simplicial flag sign after a common subdivision — is the cheapest rigorous one**,
and is what `consult/E-answer-digest.md` §1 actually proposes. Take `R` with `Γ` and
`ι '' (⇑D '' D.domain)` subcomplexes (`…TubeCarrier.lean:92`, proved), orient `R`
(`IsOrientable.subdivision`), and for an oriented edge `σ ⊆ Γ` orient the link circle of `σ` from
the coherent orientation of the tetrahedra containing `σ`; set `σ(a) := ±1` according to whether the
positive ray at `τ a` lies on the positive side of the line of the positive ray at `a` in that
oriented circle. Locally constant, `σ(τ a) = −σ(a)` (the rays exchange roles at one point of `Γ`),
`J` connected (`…CaseOneSource.lean:105`). This needs no cyclic order of four points, only
transversality — but it needs two new theorems (rows 9, 10) *and* still needs the marked rays
presented on the link, the tube leaf's own hard obligation. Option (iii) is the tube route.

## 3. B — inventory with sizes (S < 500, M 500–3000, L > 3000)

| # | Obligation | Sign (ii) | Tube | Exists? |
|---|---|---|---|---|
| 1 | common subdivision, `Γ` and trace subcomplexes | needed | needed | **proved** `…TubeCarrier.lean:92` |
| 2 | cyclic cell decomposition, `n ≥ 3` | — | needed | **proved** `NeighborhoodSolidTorus.lean:19` |
| 3 | trace in a cell is a cone over its link trace | needed | needed | **proved** `…TubeCarrier.lean:161`, `DerivedNeighborhoodLink.lean:306` |
| 4 | **marked link trace**: four arcs on the link, alternating, labelled `(sheet, collar side)` from the actual `ρ`; `FourArcSphere.lean:423` with real `hsep`, `hsep'`, `π (i+2) = π i + 2` | M 700–1200 | M 700–1200 | tool proved, application **open** |
| 5 | cone-pair extension per cell (`FourSpokeAbstract.lean:53`, `ConePairExtension.lean`) | — | M 400–800 | tools proved, glue open |
| 6 | cyclic gluing into one cylindrical diagram, pages kept | — | M 500–900 | open |
| 7 | four source arcs `a i`, `s i`, `φ (r i, t) = ι (⇑D (ρ (a i t, s i t)))` | S–M, weaker form | M 400–700 | open (review's "most likely surprise") |
| 8 | `cyclic`, `mapsTo`, `derived`, `branchInterior`, finiteness | — | S 250–450 | open |
| 9 | **oriented link circle of an edge** from `CoherentOrientation 3 R` | **M–L 1000–2500** | not needed | **nothing in tree** |
| 10 | **transport through a branch vertex** (link 2-sphere, two poles, four meridians, opposite conventions at the poles) | **M–L 800–2000** | not needed | **nothing in tree** |
| 11 | orientation of the normal circle + monodromy positivity | via 9+10 | **free** | **proved** `CylindricalMonodromy.lean:78` |
| 12 | final contradiction | S 250–450 | **proved** `…Transport.lean:141,168` + assembly | — |

Totals. **Sign route ≈ 2800–6000 (M–L)**, of which 1800–4500 is new orientation theory with no other
consumer. **Tube route** — the single leaf `exists_isSourceTrackedBranchTube`
(`Skeleton/ClosedBranchCaseOne.lean:166`) — **≈ 2000–3500 (M, upper half)**, all inside the marked
normalisation and gluing (`consult/C-or1-design.md`'s 1700–2600 predates `realisation`; rows 4–8
are my own re-estimate).

## 4. C — verdict and leaf list

**Tube route.** No hybrid helps: "use `SourceRayTransport` but take the monodromy contradiction
from a local orientation count" still needs rows 9–10, exactly what row 11 supplies for free. Keep
the endpoint, A2.3.a and A2.3.c unchanged; cut the remaining leaf into these orientation-free
sub-leaves, each of which must hold on the Möbius fixture of `consult/I-…-digest.md`:

1. `exists_markedLinkNormalisation_at_branchFace` — at every face of `restrict R Γ`, a PL
   homeomorphism of the link pair onto the standard four-arc/four-spoke model carrying the four
   marked arcs to the model arcs, the marking read off `ρ`. *Fixture: holds* (same local crossing).
2. `exists_markedConePairExtension_cell` — cone-pair extension of (1) over one derived
   neighbourhood cell. *Fixture: holds.*
3. `exists_markedCylindricalDiagram_of_cyclicCells` — cyclic splice of (2) into one
   `IsCylindricalDiagram` with end map `u` and `mapsTo u (range r) (range r)` from the page
   permutation. *Fixture: holds*, end map the reflection `(0 1)(2 3)`.
4. `exists_sourceArcs_of_markedCylindricalDiagram` — the four continuous `a i`, `s i` over one
   circuit, realisation identity, alternating pairing. *Fixture: holds*, `a 0 = a 2 = [t]`,
   `a 1 = a 3 = [t+1]`, signs `(+,+,−,−)`.
5. bookkeeping: `cyclic`, `derived`, `branchInterior`, finiteness.

`hor` is still used only in the assembly, through `isOrientable_derivedNeighborhood_of_isSubdivision`
and inside `not_closedBranchCase1`. **Most uncertain leaf: (1)** — `hsep`, `hsep'` of
`FourArcSphere.lean:423` at a *vertex* of `Γ`, where alternation of the four marked arcs on the
link 2-sphere must be derived from transversality, together with `π (i + 2) = π i + 2`.

## 5. Two cheapenings of the frozen leaf (owner's call)
The assembly (`Skeleton/ClosedBranchCaseOne.lean:184`) reads `htube.derived`, `.cyclic`,
`.isPLBall`, `.isManifold`, `.isCylindrical`, `.isEndMap`, `.seam`, `.mapsTo`, `.realisation` — and
**never `trace`, never `branchInterior`**.
* **`trace` can be weakened to `t = 0` or dropped.** `mapsTo` is an explicit field, so a producer
  that builds `u` as the page permutation proves it directly; dropping `trace` removes the
  obligation to show that nothing else enters the interior levels. Review I's two counterexamples
  are excluded by `derived` and `realisation`, not by `trace`, so that repair survives. Weakening a
  clause of the leaf's *conclusion* cannot break an assembly that never reads it.
* **`branchInterior` is likewise unconsumed**; keep it as an honesty guard (it follows from the
  derived-neighbourhood presentation) but spend nothing extra on it.

Neither change touches the endpoint, A2.3.a, or `…CaseOneTransport.lean`. If taken, re-freeze the
leaf and re-check it on the Möbius fixture before work starts.
