# Digest — second external review of the two §34 skeletons (snapshot `99f3e3a9a2f7`)

Verification marks (owner's rule, 2026-09-21): **[V]** = checked by the lead against the Lean
source; **[–]** = not independently verified.

Corrections to our text: `LocallyFinitePLPieceIn ℝ³ 3 M U` asks that **all of `U` be realised in
`ℝ³`** — it is not a triangulation of an arbitrary PL 3-manifold **[V]** (`PolyhedralGraph.lean:43`:
`complex` lives in the ambient `E`, `BijOn map complex.space Y`, `IsEmbedding`; with `E = ℝ³` and
`U = S³` invariance of domain makes `|𝒦|` open, non-empty and compact in `ℝ³`). This is the defect
the lead had already recorded in `E3_ASSEMBLY_DESIGN_20260920.md` ("forces `U` to embed in ℝ³") and
failed to catch when the workers re-introduced it. `ControlledGraphNeighborhoodStatement` supplies
only P1, conditional on `Moise341`; it is not a producer of `Section34NormalPlus`. `NormalPlus`
forgot `IsSubdivision 𝒦'.complex 𝒦.complex` and the equality of the two realisation maps.

## `Skeleton/Section34Terminal.lean`
| Leaf | Verdict | Reason |
|---|---|---|
| `exists_section34NormalFamily` | **FALSE [V]** | realisation ambient fixed to `ℝ³` excludes `U = S³` (`h` the antipodal map, `η ≡ 1`) |
| `exists_section34FaceDisks` | **OK [–]** | with *all* cut/trace clauses the cyclic seam structure excludes "tangent once" |
| `exists_section34ResidualBalls` | **FALSE [–]** | `H t` may have holes: the carrier containing the boundary need not contain the ball it bounds |
| `section34TargetRecognition` | **FIX** | separate the source-side exact-flags recognition from target recognition; its first conjunct ("all are PL cells") is already an input |

* **Realisation.** Separate realisation dimension from manifold dimension: a fixed larger ambient
  (Moise §7: `2n+1 = 7`) or a parameter; `ChartedSpace`, `plGroupoid`, `IsPLCellOn` stay
  3-dimensional; `H`, `cr` and the `Finset` indices follow. The shared frame keeps
  `IsCombinatorialManifold 3 𝒦.complex ∧ IsSubdivision 𝒦'.complex 𝒦.complex ∧ 𝒦'.map = 𝒦.map`.
  P0–P5 should be cut into control triangulation, P1, initial face balls, protected operations,
  normalization.
* **P6 is fine without a transversality field [–].** From the source boundary decompositions and
  exact intersections, `∂d_σ = ⋃_v a_{vσ}`, `∂a_{vσ} = {p_{σe}}`: a finite simple cycle with at
  least three seams; `∂T_σ` is cut by the `γ_e` into cyclically arranged annuli. A PL circle meeting
  **every** seam exactly once cannot be tangent at one: the mod-2 intersection numbers with the
  seams agree; all tangent would keep it in the closure of one annulus, which touches only two
  seams. So all crossings are transverse and the circle is essential in `T_σ`. An innermost disk
  on `∂C_σ` with interior in `N''` would lie in `T_σ` (non-incident vertex balls are excluded),
  contradicting essentiality — so it is exterior. **Lemma 5(7) is not needed for P6**; it serves P7.
* **Exterior / P7.** The component test is right for a **closed PL 3-ball** `H`
  (`O ⊆ Int H` ⇒ `∂H ⊆ H \ O` connected ⇒ a unique outer component), wrong for an open set or a
  closed set with holes (a component touching an *inner* boundary passes). Counterexample [–]:
  standard cut and translate `g`; `q ∈ Int R_t⁰ \ O_t`, `p ∉ S_t`, a compactly supported PL
  homeomorphism `a` off the graph neighbourhood moving `p` to `g⁻¹ q`, `h = g ∘ a`, `f₁ = g`;
  `H_t = B \ Int B_q` for a small closed PL ball `B_q ∋ q` avoiding `h(S_t) ∪ O_t`. All inputs hold,
  but `R_t = R_t⁰ ∋ q ∉ H_t`. **Repair:** add
  `∀ t : Section34SimplexIndex 𝒦 4, IsPLCellOn 3 (H t.1) (frontier (H t.1))`; keep
  `O_t ⊆ interior (H t.1)` and the marker clause.
* **Mixed flags are read correctly [–].** Under a genuine subdivision with common realisation,
  `↑s ⊆ convexHull ℝ ↑t` is the geometric incidence; the three boundary formulas of `ResidualPlus`
  are indexed correctly. For a subdivision vertex inside an old edge, `∂X_{tv}` is a quadrilateral
  (two `a` + two `I`), for an old vertex three + three; `∂I_{te}` is still two marked points.
  Degree 2 comes from the subdivision of the graph, not from the last two seam incidences.
* **P8 split.** First a source-side bridge `src m ⊆ src l ↔ m ≤_cut l`, `≤_cut` the reflexive
  transitive closure of the codimension-one incidences
  (`∂C_v = ⋃_{e∋v} D_e ∪ ⋃_{t∋v} X_{tv}`, `∂Q_t = ⋃_{σ<t} d_σ ∪ ⋃_{v∈t} X_{tv}`, `∂D_e = ⋃_{t>e} I_{te}`,
  `∂d_σ = ⋃_{v∈σ} a_{vσ}`, `∂X_{tv}`, `∂a_{vσ} = ⋃ p_{σe}`, `∂I_{te} = ⋃ p_{σe}`), proved on the source
  cut; then the target recognition. Incident-pair subtypes are not by themselves the face-poset
  bridge. Target cell-ness is read off the inputs, not a geometric obligation.

## `Skeleton/ControlledGraphNeighborhood.lean`
| Leaf / endpoint | Verdict | Reason |
|---|---|---|
| `exists_section34CutFrame` | **OK [–]** | for a given `𝒦` one can subdivide the graph and choose a standard cut meeting `W`, `ψ` and carrier separation |
| `Moise341.exists_section34VertexApproximation` | **FIX [V]** | the output has no approximation or protected-core clause (read: only `IsPLHomeomorphInto`, image `⊆ Q w`, PL cell) — satisfiable by shrinking `C_v` into a small tetrahedron of `interior (Q v)`; `Moise341` not even needed |
| `exists_section34EdgeMatching` | **FIX** | the real piercing, annulus, circle removal and overlap deletion are all hidden here; the input `G` carries none of the certificates |
| `section34MeridianAndNeighborhood` | **FALSE [V]** | covering `h(Γ)` by the total image does not give label-wise marker, rim or generator clauses: periodic cut, `Q_v = ℝ³`, `f₁ = G_v = id`, `h x = x + a` with `a` a large period — every hypothesis of the leaf as written holds (it does not receive `hQsmall`, `hQsep`), yet `h v ∉ C_v` |
| `ControlledGraphNeighborhoodStatement` | **FIX** | quantifier order right; the global `ℝ³` realisation must go |

* `IsOpen (h '' U)` need not be assumed: `Section34CarrierControl` gives
  `h '' U = ⋃_α interior (H α)` because the `S_α` cover `U`. Invariance of domain is used when the
  carriers are *produced*.
* **Vertex and edge stages pass preparation certificates, not an arbitrary `G`.** First produce
  enlarged/pierced cells `C_v''`, annular buffers and error bounds `ε_v`, fixed **before** the maps;
  then the chart-local `Moise341`: `∃ f_v` PL embedding with `dist (f_v x) (h x) < ε_v` on `C_v''`;
  the bounds yield conditions (2)–(7) of pp. 249–250, general position (8) by a small perturbation.
  Split the edge leaf into: preparation + approximation transfer · protected disk/annulus circle
  removal (for an infinite family: label-wise finite descent with locally finite supports, not a
  minimisation of a possibly infinite total count) · ball recognition after overlap deletion + PL
  matching. **The exact meet `G_v(C_v ∩ C_w) = G_v C_v ∩ G_w C_w` stays** (it excludes new
  cross-cell coincidences; `EqOn` alone does not); the final `G'` need not preserve the initial
  approximations — conditions (2)–(8) and their protection data are what is kept.
* **Meridian leaf.** Marker and rim containment go back into the **joint producer's output**; the
  generator consumer takes a genuine nested-torus certificate: `J_σ` a spine of `S_{1σ}`,
  `S_{1σ} ⊆ Int T_σ`, `T_σ ⊆ Int S_{2σ}`, `S_{1σ}, S_{2σ}` solid tori, `T_σ` a PL solid torus,
  `closure (S_{2σ} \ S_{1σ})` a toroidal shell ⇒ `CarriesFundamentalGroupOnto J_σ T_σ`
  (`Moise308Nested` is the proved tool). Moise's Lemma 2 (p. 240) says `f₁` *can be chosen* with the
  property, not that every `f₁` with a total-image neighbourhood has it. The
  `FundamentalGroup.map`-surjective-at-every-base-point formulation is right.

**Missing obligations:** realisation of general manifolds; closed PL ball carriers; the source
flags bridge; marker and nested-torus certificates kept through approximation and operations.
**Fixture:** fine periodic cut with degree-2 vertices inserted in old edges, all eight label
kinds; `h = g ∘ ψ`, `g` a non-zero PL translation, `ψ` non-PL supported in one residual cell and
fixing `N`; `f₁ = g`. **Most likely surprise:** handing a property the producer "can jointly choose"
to a universal consumer that only sees the final sets and an arbitrary map.
