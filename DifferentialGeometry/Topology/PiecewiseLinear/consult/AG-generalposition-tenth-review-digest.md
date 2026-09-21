# Digest — tenth external review of the A1 skeleton (snapshot `44a987ac`, the six leaves of design Y)

Marks: **[V]** checked by the lead against the Lean text.

| Leaf | Verdict | Ruling |
|---|---|---|
| `exists_commonWallComplex` | **OK** | a common subdivision of the given double yields the certificate; `wallSides` must come from the face incidence of a closed 3-manifold, not from `dimLe + memCell` |
| `wallProductBlock_transport` | **OK** | both proof obligations follow from the fields |
| `hasStableCrossingBlocks_of_wallProductBlocks` | **OK** | chart change + finite subcover over the compact double point set; boundary blocks give neighbourhoods relative to `C`; no `Z' ⊆ C` |
| `wallProductBlocks_stable_on_fixedSubdivision` | **OK as stated** | `hlinear` repairs the base interpolation; the conclusion promises no correspondence of wall labels between old and new blocks |
| `exists_wallGenericVertexMap` | **FIX [V]** → repaired | `hVec` puts the active region in the chart only; `chartAffine` says nothing there |
| `wallProductBlocks_of_wallGenericity` | **OK** | receives `hgcont`, `hgfiber` of the new map; `hWE` puts the double points in the certified layer; accumulation on both sides suffices, no quantitative angle |

* **Two readings corrected.** In the abstract certificate a continuous bijection `ρ` is not
  automatically a homeomorphism; for the compact double it is. "The same `Q`, `ρ`" is not "the same
  wall label block by block".
* **Certificate.** Sufficient and producible. `wallSides`: `isCombinatorialManifold_double_succ_succ`
  gives a closed double; every triangle of a closed 3-manifold has exactly two tetrahedra, stable
  under subdivision; a wall of `BdM` still has two, exactly one in `Cf` — the present `boundarySides`
  is right. `C`, `Bd` are given subcomplexes, so **the cover hypothesis is not needed by this leaf**
  (the cover belongs to the global assembly) — **removed [V]** (the assembly's `hVcover` block went
  with it). `chartAtlas` gives PL compatibility, `chartC/chartBd` the half-space reading; neither
  replaces the other. `dimLe` follows from `memCell`, `layerSubset` from surjectivity, `memCell`,
  `starLayer`; kept for convenience.
* **The one repair [V].** The generic leaf had `V ⊆ (ecf i₀).source` only, while `chartAffine` covers
  cells wholly inside `Eb' i₀`. Interface counter-model: all `Eb, Eb'` empty and `ρ` composed with a PL
  self-homeomorphism preserving `(C, Bd)` but non-affine inside `V` — `starLayer/chartAffine` idle, a
  non-empty active region allowed. Refutes "the certificate supplies affine wall data on the
  active region", not the density statement. Added `hVE : closure V ⊆ interior (Eb i₀)`; the assembly
  had it (`hVEint`). With the fixed finite mesh and `hlinear` the perturbation is shrunk until the
  interpolated image stays in the layer; then `starLayer` reaches `chartAffine`.
* **Same-wall tracking.** `HasWallProductBlocks` already quantifies a finite block family; the
  stability conclusion re-quantifies it without relating old and new witnesses. The present
  consumer needs existence only. A consumer using "the old type (ii) wall is kept" would need named
  witnesses, a refinement relation and equal wall labels (sheets and box may be re-chosen).
* **Transport obligations.** `hspan` needs a *nonempty* relatively open wall piece (three affinely
  independent points span the wall plane). `A` of `chartAffine` is inverted only after restriction
  to `affineSpan ℝ ↑c` (injective by chart injectivity and surjectivity of `ρ`; both sides of
  dimension three) — never on the whole ambient `Ea`.
* The five counterexamples of review AB are all excluded (genuine certificate; `hlinear`; purity and
  surjectivity; `IsFreeDoubleGerm`; `hgfiber` + `hgcont`).

**Owed:** the face incidence of the closed double as a derived lemma, not a hypothesis.
**Fixture:** AB's `γ × [−1,1]` in a double cube with a genuine common subdivision and a small non-zero
perturbation of the free vertices. **Likely surprise:** the chart-representation estimate when the
fixed-mesh perturbation crosses the target wall — a piecewise affine transition is not globally
affine, and the difference before/after a moving fold need not have a small Lipschitz constant.

**State:** lead re-check on lease d — 14 diagnostics, all `declaration uses 'sorry'`. All fourteen
leaves of `Skeleton/GeneralPositionInDouble.lean` are frozen.
