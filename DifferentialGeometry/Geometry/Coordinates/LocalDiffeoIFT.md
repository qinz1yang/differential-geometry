# LocalDiffeoIFT.lean — manifold forward inverse function theorem

## Goal
Invertible differential ⟹ local diffeomorphism (Mathlib has only the reverse,
`IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv`).  Reusable brick for B1 `lbl403` `hloc`
(and future C∞ uses).  General layer, imports ONLY Mathlib (no Step A/B/C).

## State — 2026-07-07: **DONE, whole file sorry-free, axiom-clean** (+ ∞ IFT + injectivity toolbox, same day)
Full `lake build` green (2356 jobs).  All theorems `#print axioms = [propext, Classical.choice,
Quot.sound]` (NO `sorryAx`).  The core `isLocalDiffeomorphAt_of_contMDiffOn` is PROVED via the trans
route (`n ≠ ∞`).  B1's `hloc` gap (`StepB1Producers.hlocOn_of_chartNeumann`, finite order) closed too.

### Round 2 additions (same day, all sorry-free/axiom-clean)
- **`isLocalDiffeomorphAt_of_contMDiffOn'`** (strong core): conclusion additionally exposes
  `Φ.source ⊆ U` (the construction's `S ⊆ U` was already there; now public).  Weak form = corollary.
- **`contMDiffOn_isLocalDiffeomorphOn_infty`** — the **`n = ∞` forward IFT**: `C^∞` on open `U` +
  invertible chart-derivative at *every* point of `U` ⟹ `IsLocalDiffeomorphOn ∞`.  Route =
  **inverse-uniqueness upgrade**: take the order-1 realizing `Φ` (strong core, `source ⊆ U`); for
  every finite `k` and every `y ∈ Φ.target`, the order-`max 1 k` local diffeo `Ψ` at `z := Φ.symm y`
  agrees with `Φ` near `z` (both `= f`), so on the open set
  `W := Φ.target ∩ (Ψ.target ∩ Ψ.symm ⁻¹' Φ.source)` the two inverses coincide (`Φ` injective on its
  source, both preimages land there) ⟹ `Φ.symm` is `C^k` at `y` by congr ⟹ `contMDiffOn_infty` ⟹
  rebuild the `PartialDiffeomorph` at `∞` on the same `PartialEquiv`.  KEY trick: `Φ.toFun := f`
  directly in the core makes `EqOn` transfer `rfl`-cheap.  GOTCHA: `rw [h1]` where `h1 : y = Ψ (…y…)`
  rewrites ALL `y`-occurrences (incl. inside the RHS) — state `h1 : Ψ (…) = y` and `calc` instead.
- **`norm_sub_le_of_fderiv_near_id`** + **`injOn_of_fderiv_near_id`** — Neumann antilipschitz
  (`‖id − dG‖ ≤ ε` on convex `s` ⟹ `(1−ε)‖x−y‖ ≤ ‖Gx−Gy‖`, MVT on `z ↦ z − G z`) and `InjOn` for
  `ε < 1`.  MVT = `Convex.norm_image_sub_le_of_norm_fderiv_le` (dot on `hs`; plain name doesn't
  resolve).  `fderiv (fun w => w − G w)` via `(hasFDerivAt_id z).sub …|>.fderiv` (a `fderiv_fun_sub`
  rewrite mismatches the lambda shape).
- **`injOn_of_writtenInExtChart`** — manifold `InjOn` from chart `InjOn` (set-theoretic transfer
  through the chart round-trip; NO metric distortion input; the target-side hypothesis turned out
  unnecessary).
- **LEInfty discovery**: `[IsManifold I ∞ M]` gives `IsManifold I ((k:ℕ):WithTop ℕ∞) M` and order-`1`
  instances FOR FREE (`ENat.LEInfty` instances + the derived `IsManifold` instance) — no `haveI`
  needed when applying finite-order lemmas under an `∞` hypothesis.

## ⚠ MATH CORRECTION to the planner's spec (n = ∞)
The planner's (i) — `ContMDiffAt` + invertible chart-derivative ⟹ `IsLocalDiffeomorphAt`, "general
order" — is **FALSE for n = ∞**.  `IsLocalDiffeomorphAt I J n f x` needs a `PartialDiffeomorph Φ`
with `f = Φ` on an *open* source, so `f` must be `C^n` on a neighborhood.  For finite `n` this is
free (`contMDiffAt_iff_contMDiffOn_nhds`, which itself requires `n ≠ ∞`), but a `C^∞`-at-a-point map
need NOT be `C^∞` nearby, hence need not be a local diffeo.  Restructured accordingly:
- **core `isLocalDiffeomorphAt_of_contMDiffOn`** — hypothesis is `ContMDiffOn I J n f U` on an open
  `U ∋ x`, `n ≠ ∞`.  **PROVED.**
- **(ii) `contMDiffOn_isLocalDiffeomorphOn`** — general finite `n`, from the core pointwise.  PROVED.
- **(i) `contMDiffAt_isLocalDiffeomorphAt`** — takes `hn' : n ≠ ∞`; upgrades `ContMDiffAt` to
  `ContMDiffOn` on a nbhd then applies the core.  This is B1's shape (order 1).  PROVED.
- **`n ≠ ∞` is also on the core** now (not just (i)): the inverse-smoothness step needs it (below).
- **Neumann `isInvertible_of_norm_id_sub_lt`** — `‖id − T‖ < 1 ⟹ T.IsInvertible`, via
  `Units.oneSub` + `ContinuousLinearEquiv.ofUnit`.  GREEN, axiom-clean.  (B1's entry shape `dF ≈ id`.)

Hypothesis shape (per `StepBInputs.md`): invertibility on the CHART-LEVEL
`(fderiv ℝ (writtenInExtChartAt I J x f) (extChartAt I x x)).IsInvertible` (genuine `E ≃L F`), NOT
`mfderiv` — dodges the `TangentSpace 𝓘(ℝ,E) = E` defeq wall.

## Core construction roadmap (the remaining sorry — all cited lemmas VERIFIED present)
`c := extChartAt I x`, `d := extChartAt J (f x)`, `a := c x`, `G := writtenInExtChartAt I J x f`.
1. `G` is `ContDiffAt ℝ n` at `a`: `(contMDiffAt_iff.mp (hf.contMDiffAt (hU.mem_nhds hxU))).2` +
   `ModelWithCorners.Boundaryless.range_eq_univ` + `contDiffWithinAt_univ`.
2. `⟨G', hG'eq⟩ := hinv` (`G' : E ≃L F`, `↑G' = fderiv ℝ G a`); `HasFDerivAt G ↑G' a` via
   `hG.differentiableAt hn |>.hasFDerivAt` + `rw [hG'eq]`.
3. `Ψ := hG.toOpenPartialHomeomorph G hG'fderiv hn0` (normed IFT, `hn0 : n ≠ 0` from `hn`):
   `OpenPartialHomeomorph E F`, `⇑Ψ = G` (`toOpenPartialHomeomorph_coe`), `a ∈ Ψ.source`,
   `G a ∈ Ψ.target`, `Ψ.symm` `ContDiffAt` at `G a` (`to_localInverse`); extract `ContDiffOn` on
   open subsets (shrink `Ψ.source`/`Ψ.target`).
4. `Φ : PartialDiffeomorph I J M N n` — MANUAL fields (mirror
   `Geometry/Exponential/LocalDiffeomorphism.lean:493` `expMapPartialDiffeomorph`, but chart BOTH
   sides): `toFun := f`, `invFun := ↑c.symm ∘ Ψ.symm ∘ ↑d`,
   `source := c.source ∩ c⁻¹'Ψ.source ∩ f⁻¹'d.source ∩ U` (open, `x ∈`), `target := f '' source`.
   On source, `f = ↑d.symm ∘ Ψ ∘ ↑c` (chart round-trips + `Ψ = G`).  `contMDiffOn_toFun` from
   `hf.mono`; `contMDiffOn_invFun` from `contMDiffOn_extChartAt_symm`/`_extChartAt` + `Ψ.symm`
   smoothness.  **Hard field = `open_target`** (image of open under the local homeo) — mirror the
   template's `niceTarget_eq_source_inter_preimage` + `isOpen_extChartAt_preimage'`.
5. `⟨Φ, hxΦ_source, eqOn⟩` gives `IsLocalDiffeomorphAt`.

Estimate ~120–150 lines; the `open_target` step is the only genuinely delicate one (needed a bespoke
lemma even in the one-sided expMap template).  De-risked: every other lemma is confirmed present.

## REFINED ROUTE (2026-07-06 investigation) — trans-in-the-`OpenPartialHomeomorph`-world + `n ≠ ∞`
Full API now confirmed; `open_target` becomes FREE via `OpenPartialHomeomorph.trans`.
- **`chartAt` IS an `OpenPartialHomeomorph`** here (`ChartedSpace.atlas : Set (OpenPartialHomeomorph
  M H)`).  `extChartAt` packages directly as `OpenPartialHomeomorph M E` for boundaryless:
  `{ extChartAt I x with open_source := isOpen_extChartAt_source x, open_target :=
  isOpen_extChartAt_target x, continuousOn_toFun := continuousOn_extChartAt x, continuousOn_invFun :=
  continuousOn_extChartAt_symm x }`.  (`isOpen_extChartAt_target` needs `[I.Boundaryless]` ✓.)
- `Ψ := hG.toOpenPartialHomeomorph … : OpenPartialHomeomorph E F` (IFT).
- `Θ := (cO.trans Ψ).trans dO.symm : OpenPartialHomeomorph M N` — source/target OPEN for free.
  `coe_trans : ⇑(e.trans e') = e' ∘ e`, `coe_trans_symm : ⇑(e.trans e').symm = e.symm ∘ e'.symm`,
  `trans_apply`, `restrOpen`/`restrOpen_source` (`= e.source ∩ s`).  `Homeomorph.toOpenPartialHomeomorph`
  and `ModelWithCorners.toHomeomorph [Boundaryless] : H ≃ₜ E` also available if charting via `chartAt`.
- **`n ≠ ∞` REQUIRED (add to core + (ii); (i) already has it).**  The inverse
  `g = ↑c.symm ∘ Ψ.symm ∘ ↑d` is `ContMDiffAt (f x)` (charts `ContMDiffAt` + `Ψ.symm` `ContDiffAt (G
  a₀)` via `OpenPartialHomeomorph.contDiffAt_symm` at the single point `G a₀`, using `hG`/`hG'fderiv`).
  Then `contMDiffAt_iff_contMDiffOn_nhds` (needs `n ≠ ∞`) lifts it to `ContMDiffOn` a nbhd `W ∋ f x`.
  For `n = ∞` this path fails — one would instead prove `fderiv G` invertible on a *neighborhood*
  (openness of invertibles + `fderiv` continuity) and apply `contDiffAt_symm` pointwise (harder,
  deferred).  B1 uses finite order, so `n ≠ ∞` is the honest restriction.
- **Double restriction:** restrict `Θ.source` to `∩ U` (forward smooth via `hf.mono` + `ContMDiffOn.congr`)
  AND `Θ.target` to `∩ W` (inverse smooth); then `Φ := ⟨Θ''.toPartialEquiv, Θ''.open_source,
  Θ''.open_target, fwd, inv⟩ : PartialDiffeomorph`, `⟨Φ, x∈source, EqOn f Φ source⟩`.
- **DONE 2026-07-07.**  The actual proof (≈130 lines) used a simpler assembly than "double
  restriction": build `Θ := (cO.trans Ψ).trans dO.symm` (open source/target free), then take
  `Φ.toFun := f` DIRECTLY (not `Θ`), `Φ.invFun := Θ.symm`, `Φ.source := S` an open nbhd of `x` inside
  `Θ.source ∩ U ∩ f⁻¹'(chart src) ∩ Θ⁻¹'W` (`W` = the inverse-smooth nbhd from
  `contMDiffAt_iff_contMDiffOn_nhds`), `Φ.target := f '' S`.  Then `EqOn f Φ` is `rfl` (toFun = f),
  `open_target` = `f''S = Θ''S` (`Set.image_congr hEqS`) open via `Θ.isOpen_image_of_subset_source`,
  `contMDiffOn_toFun = hf.mono`, `contMDiffOn_invFun = hΘsymmW.mono`, and the `map_/left_/right_inv`
  fields from `hEqS : f = Θ on S` + `Θ.left_inv`.  KEY lemma facts: `hEq` (charts round-trip:
  `Θ z = f z` when `z ∈ chart src ∧ f z ∈ chart src`, via `trans_apply` + `PartialEquiv.left_inv`);
  inverse `ContMDiffAt (f x)` = `contMDiffAt_extChartAt` ∘ `(contMDiffAt_iff_contDiffAt.mpr` of
  `Ψ.contDiffAt_symm` at the single point `G a₀`) ∘ `contMDiffOn_extChartAt_symm.contMDiffAt`.
  GOTCHAS: use `OpenPartialHomeomorph.continuousOn` (coe-based) not `.continuousOn_toFun` (so the
  point is `⇑Θ x`, matching `hΘx`, for the `Θ⁻¹'W` nbhd `rw [hΘx]`); `∞ = ↑(⊤:ℕ∞) ≠ ω = ⊤` so
  `le_top`/`IsManifold.of_le le_top` targets `ω` (wrong) — use explicit `((n:ℕ∞):WithTop ℕ∞) ≤ ∞`.

## Key Mathlib API confirmed present
`contMDiffAt_iff` (chart-rep ContDiffWithinAt), `ModelWithCorners.Boundaryless.range_eq_univ`,
`ContinuousLinearMap.IsInvertible` (`∃ A : E ≃L F, ↑A = f`), `ContDiffAt.toOpenPartialHomeomorph`
+ `_coe`/`mem_..source`/`image_mem_..target`/`to_localInverse`, `contMDiffAt_iff_contMDiffOn_nhds`
(needs `n ≠ ∞`), `contMDiffOn_extChartAt`/`_symm`, `Units.oneSub`, `ContinuousLinearEquiv.ofUnit`.
NO Mathlib manifold IFT exists (only the reverse `mfderivToContinuousLinearEquiv`).

## 2026-07-14: canonical Neumann extraction

The proof of `isInvertible_of_norm_id_sub_lt` now delegates to
`ContinuousLinearMap.invertible_of_id_sub` in
`Analysis/Calculus/CLMNeumann.lean`.  Its public statement is unchanged, so the
manifold-IFT API remains stable while the reusable Banach-space theorem now
lives at the lower calculus layer.  Focused verification passes; the file's
pre-existing unused-section-variable warnings are unchanged.
