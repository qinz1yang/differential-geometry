import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1ApproxIso
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveraging
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringSeq
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergenceComp
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergenceDeriv
import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoIFT
import DifferentialGeometry.Analysis.Calculus.PiDeriv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step B1 (`lbl397`) — producer lemmas for `stepB1_glue`

`stepB1_glue` (in `StepB1ApproxIso.lean`, sorry-free) consumes, per `(k, ℓ)`:
`hloc` (`IsLocalDiffeomorphOn F U`), `hinj` (`InjOn F U`), `hbase` (`F O_k = O_ℓ`), and the
forward/reverse `PreApproxIsoDataOn`.  This file collects the *producers* of those inputs from the
C-track engines, and pins the honest inputs each still needs.

## Honest status of the four producers (audited this session)
The planner's premise "engines all ready, no new analysis" does **not** hold; each producer bottoms
out in real analysis or missing API (survey 2026-07-05):

- **(a) `lbl404` — averaged map is `C^p`-close to `id`.**  The chart-level single-composition engine
  `StepBApproxIso.comp_cInf_id_on` (green) gives `C^p → id` for one transition composition, and
  `StepCAveraging.eq_of_all_eq` (green) gives the `C⁰` diagonal identity of the center average.  But
  the *averaged* map `G^β_{kℓ;r} = chart_ℓ ∘ centerAverageOn ∘ chart_k⁻¹` is the center of mass of
  `A(r)` near-identity summands; bounding `‖∇^p(G^β − id)‖` requires the Faà-di-Bruno composition of
  the **threaded cm-derivative bound** (`‖∇^j(chart∘cm)‖ ≤ C̃ j` for `j ≤ p+1`).
  `StepCDerivBounds.cmChartDerivLe2` proves only the honest order-two part; the arbitrary-order
  theorem still needs order-`p` regularity and a recursive numerical majorant.  Combining it
  with the summand `C^p→id` smallness is genuine multi-lemma analysis, not
  transcription.  Remaining frontier.

- **(b) `lbl403` — local diffeomorphism + injectivity: CLOSED 2026-07-07.**  `hloc`: the manifold
  forward IFT is built (`Geometry/Coordinates/LocalDiffeoIFT.lean`, incl. the `n = ∞` version via the
  inverse-uniqueness upgrade); the producer in `stepB1_glue`'s exact shape is
  `hlocOn_of_chartNeumann_infty` below (`C^∞` + chart-level Neumann `‖id − dG‖ < 1` at every point ⟹
  `IsLocalDiffeomorphOn ∞`).  `hinj`: manifold-level via `stepB1_hlocHinj`/`injOn_of_dist_le`
  (displacement bound), chart-level via `Coordinates.injOn_of_fderiv_near_id` (Neumann antilipschitz,
  MVT).  The remaining (b)-side work is only *estimate production* — the Neumann bound itself from
  the C-track `C¹`-closeness — which is part of (a).

- **(c) `lbl402` — forward/reverse `PreApproxIsoDataOn`.**  Consumes (a)'s `C^p` output +
  `ApproxIsometryCompHigher.comp_cov_le`/`comp_cov_accum` (green) + the pullback-metric-tensor
  construction.  Blocked on (a).

- **(d) basepoint `F O_k = O_ℓ`.**  Book L1676–78: the `χ`-cutoff makes only the `α = 0` weight live
  at `O_k`, so `F O_k = cm{F^0_{kℓ}(O_k)} = F^0_{kℓ}(O_k) = O_ℓ`.  Route = `centerAverage.activeFill`
  + `eq_of_all_eq`, but needs the POU concentration fact `φ_k^α(O_k) = δ_{α0}` and
  `F^0_{kℓ}(O_k) = O_ℓ`.  **MISSING POU PRODUCER** — no such fact exists in `StepCAveragePOU`
  (off-limits to edit); it must be added there before (d) can close.

## Honest assembly boundary
The former `stepB1_approxIso` incorrectly exposed a theorem from `X + P` alone.  It has been
replaced by `StepB1RawInput` plus the conditional consumer `stepB1_of_raw`; Step D likewise consumes
that package explicitly through `directed_of_b1`.  The package records the raw comparison map,
local diffeomorphism/injectivity/basepoint data, and two-sided `PreApproxIsoDataOn`, not the final
`BookApproxIsoPartialData` conclusion.

The genuine B/C theorem remains 0% until this file constructs `StepB1RawInput` from the conditional
endpoint's C-track data (`NetLimitData`, `PackingBound`, `ExpInverseDerivBoundInput`, the POU,
overlaps, and the derivative bounds).  The checked `_of_raw` assembly must not be reported as that
producer theorem.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff BigOperators Topology

/-- **Injectivity from a below-bounded displacement.**  If `dist x y ≤ K · dist (F x) (F y)` on `s`,
then `F` is injective on `s` (`F x = F y` forces `dist x y ≤ 0`, hence `x = y`).  This is the
`lbl403` injectivity half: the `C¹` closeness of the comparison map gives such a bound (bi-Lipschitz
below with constant near `1`), so `InjOn` is free once the closeness estimate is available. -/
theorem injOn_of_dist_le {M : Type*} [MetricSpace M] {N : Type*} [PseudoMetricSpace N]
    {F : M → N} {s : Set M} {K : Real}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ K * dist (F x) (F y)) : Set.InjOn F s := by
  intro x hx y hy hFxy
  have hle : dist x y ≤ K * dist (F x) (F y) := h x hx y hy
  rw [hFxy, dist_self, mul_zero] at hle
  exact dist_le_zero.mp hle

section CloseIdEngine

variable {E' P Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- **`lbl404` C¹ diagonal engine.**  For a two-slot map `Φ` (the chart center of mass in
`(weights, points)`), if the *diagonal* composite `y ↦ Φ (u y, w y)` is the identity near `x`
(`eq_of_all_eq` through the charts) and the targets `v` are `C¹`-close to the diagonal `w`, then the
averaged map `y ↦ Φ (u y, v y)` has derivative close to `id`:
`‖dG − id‖ ≤ ‖DΦᵥ − DΦ_w‖·max ‖Du‖ ‖Dv‖ + ‖DΦ_w‖·‖Dv − Dw‖`.

The chain rule pins `DΦ_w ∘ (Du, Dw) = id` (differentiating the diagonal identity), and
`dG − id = (DΦᵥ − DΦ_w)∘(Du, Dv) + DΦ_w∘(0, Dv − Dw)`.  The caller instantiates `LΦ` with the
`C²`-Lipschitz bound times `‖v x − w x‖` (the `C⁰` closeness) — this is what the Neumann producers
(`hlocOn_of_chartNeumann…`, `injOn_of_fderiv_near_id`) consume for `lbl403`. -/
theorem fderiv_pair_sub_id_le {Φ : P × Q → E'} {u : E' → P} {v w : E' → Q} {x : E'}
    {DΦv DΦw : P × Q →L[ℝ] E'} {Du : E' →L[ℝ] P} {Dv Dw : E' →L[ℝ] Q}
    {LΦ BΦ Bu Bv δ' : ℝ}
    (hΦv : HasFDerivAt Φ DΦv (u x, v x)) (hΦw : HasFDerivAt Φ DΦw (u x, w x))
    (hu : HasFDerivAt u Du x) (hv : HasFDerivAt v Dv x) (hw : HasFDerivAt w Dw x)
    (hdiag : (fun y => Φ (u y, w y)) =ᶠ[nhds x] fun y => y)
    (hLip : ‖DΦv - DΦw‖ ≤ LΦ) (hBΦ : ‖DΦw‖ ≤ BΦ)
    (hBu : ‖Du‖ ≤ Bu) (hBv : ‖Dv‖ ≤ Bv) (hδ' : ‖Dv - Dw‖ ≤ δ') :
    ‖fderiv ℝ (fun y => Φ (u y, v y)) x - ContinuousLinearMap.id ℝ E'‖
      ≤ LΦ * max Bu Bv + BΦ * δ' := by
  -- chain rules for the averaged and diagonal composites
  have hG : HasFDerivAt (fun y => Φ (u y, v y)) (DΦv.comp (Du.prod Dv)) x :=
    hΦv.comp x (hu.prodMk hv)
  have hW : HasFDerivAt (fun y => Φ (u y, w y)) (DΦw.comp (Du.prod Dw)) x :=
    hΦw.comp x (hu.prodMk hw)
  -- differentiating the diagonal identity pins the `w`-composite derivative to `id`
  have hkey : DΦw.comp (Du.prod Dw) = ContinuousLinearMap.id ℝ E' := by
    have h1 : fderiv ℝ (fun y => Φ (u y, w y)) x = fderiv ℝ (fun y : E' => y) x :=
      Filter.EventuallyEq.fderiv_eq hdiag
    rw [hW.fderiv] at h1
    rw [h1, fderiv_id']
  -- the difference splits into the two error terms
  have hsplit : DΦv.comp (Du.prod Dv) - ContinuousLinearMap.id ℝ E'
      = (DΦv - DΦw).comp (Du.prod Dv)
        + DΦw.comp ((0 : E' →L[ℝ] P).prod (Dv - Dw)) := by
    rw [← hkey]
    ext ξ
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.zero_apply]
    have hpt : (((0 : P), Dv ξ - Dw ξ) : P × Q) = (Du ξ, Dv ξ) - (Du ξ, Dw ξ) := by
      simp [Prod.mk_sub_mk]
    rw [hpt, map_sub]
    abel
  rw [hG.fderiv, hsplit]
  have hLΦ0 : 0 ≤ LΦ := le_trans (norm_nonneg _) hLip
  have hBΦ0 : 0 ≤ BΦ := le_trans (norm_nonneg _) hBΦ
  have h1 : ‖(DΦv - DΦw).comp (Du.prod Dv)‖ ≤ LΦ * max Bu Bv := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) (mul_le_mul hLip ?_ (norm_nonneg _) hLΦ0)
    rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
    exact max_le_max hBu hBv
  have h2 : ‖DΦw.comp ((0 : E' →L[ℝ] P).prod (Dv - Dw))‖ ≤ BΦ * δ' := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) (mul_le_mul hBΦ ?_ (norm_nonneg _) hBΦ0)
    rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
    simp only [norm_zero]
    rw [max_eq_right (norm_nonneg _)]
    exact hδ'
  exact le_trans (norm_add_le _ _) (by linarith)

/-- **`lbl404` C⁰ diagonal engine.**  Order-`0` companion of `fderiv_pair_sub_id_le`: if the
diagonal value is the point itself (`Φ (u x, w x) = x`, from `eq_of_all_eq` through the charts) and
the slot map `q ↦ Φ (u x, q)` has derivative bounded by `B` along the segment from `w x` to `v x`,
then `‖Φ (u x, v x) − x‖ ≤ B·‖v x − w x‖` — the averaged map is `C⁰`-close to the identity.  Mean
value inequality on the segment. -/
theorem norm_pair_sub_self_le {Φ : P × Q → E'} {u : E' → P} {v w : E' → Q} {x : E'} {B : ℝ}
    (hdiag : Φ (u x, w x) = x)
    (hdiff : ∀ q ∈ segment ℝ (w x) (v x), DifferentiableAt ℝ (fun q' => Φ (u x, q')) q)
    (hbd : ∀ q ∈ segment ℝ (w x) (v x), ‖fderiv ℝ (fun q' => Φ (u x, q')) q‖ ≤ B) :
    ‖Φ (u x, v x) - x‖ ≤ B * ‖v x - w x‖ := by
  have hseg : Convex ℝ (segment ℝ (w x) (v x)) := convex_segment _ _
  have hmvt : ‖Φ (u x, v x) - Φ (u x, w x)‖ ≤ B * ‖v x - w x‖ :=
    hseg.norm_image_sub_le_of_norm_fderiv_le hdiff hbd
      (left_mem_segment ℝ (w x) (v x)) (right_mem_segment ℝ (w x) (v x))
  rwa [hdiag] at hmvt


/-- **`lbl404` abstract endpoint — the averaged map converges to the identity in `C^∞` on
compacts.**  If the weights `u k → u∞` and the targets `v k → v∞` converge in
`MapCInfConvOnCompacts U`, all factors are `C^∞`, the pairs land in the domain `V` of the fixed
`C^∞` two-slot map `Φ` (the chart center of mass), and the *limit diagonal identity*
`Φ (u∞ y, v∞ y) = y` holds on `U` (from `chartCm_diag`, when `v∞` is the diagonal configuration),
then `y ↦ Φ (u k y, v k y) → id` in `MapCInfConvOnCompacts U`.  Composition of the delivered
Faà-di-Bruno engine `MapCInfConvOnCompacts.comp` with `mapCInfConv_prodMk`/`mapCInfConv_const` and
the `congr` transfer — the convergence route needs NO quantitative derivative-difference bounds. -/
theorem averagedCInf_id {U : Set E'} {V : Set (P × Q)} (hU : IsOpen U) (hV : IsOpen V)
    [ProperSpace (P × Q)]
    {u : ℕ → E' → P} {uinf : E' → P} {v : ℕ → E' → Q} {vinf : E' → Q} {Φ : P × Q → E'}
    (hu : MapCInfConvOnCompacts U u uinf) (hv : MapCInfConvOnCompacts U v vinf)
    (huc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U)
    (hvc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) vinf U)
    (hΦc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Φ V)
    (hmapk : ∀ k, Set.MapsTo (fun y => (u k y, v k y)) U V)
    (hmap : Set.MapsTo (fun y => (uinf y, vinf y)) U V)
    (hdiag : ∀ y ∈ U, Φ (uinf y, vinf y) = y) :
    MapCInfConvOnCompacts U (fun k y => Φ (u k y, v k y)) (fun y => y) := by
  have hpair := mapCInfConv_prodMk hU hu hv huc huinfc hvc hvinfc
  have hpairc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun y => (u k y, v k y)) U :=
    fun k => (huc k).prodMk (hvc k)
  have hpairinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun y => (uinf y, vinf y)) U :=
    huinfc.prodMk hvinfc
  have hcomp := MapCInfConvOnCompacts.comp hU hV hpair
    (mapCInfConv_const (U := V) Φ) hpairc hpairinfc (fun _ => hΦc) hΦc hmap hmapk
  exact hcomp.congr hU (fun _ => Set.eqOn_refl _ _) (fun y hy => (hdiag y hy).symm)


/-- **The normalized weight family** `w_i := num_i / Σ_j num_j` — the reusable abstraction of the
book's POU weight quotient (`lbl400`, chapter4.tex L1633–59): the `χ∘J⋅ψ∘J` products are the
`num` data, and every property the averaging consumes (sum `1`, nonnegativity, smoothness,
`C^∞` convergence, basepoint concentration) follows from `num`-level facts. -/
noncomputable def normWeights {ι : Type*} [Fintype ι] (num : ι → E' → ℝ) (i : ι) (z : E') : ℝ :=
  num i z / ∑ j, num j z

/-- The normalized weights sum to `1` wherever the denominator is nonzero. -/
theorem normWeights_sum {ι : Type*} [Fintype ι] {num : ι → E' → ℝ} {z : E'}
    (hne : (∑ j, num j z) ≠ 0) : ∑ i, normWeights num i z = 1 := by
  simp only [normWeights, ← Finset.sum_div]
  exact div_self hne

/-- The normalized weights are nonnegative for nonnegative numerators. -/
theorem normWeights_nonneg {ι : Type*} [Fintype ι] {num : ι → E' → ℝ} {z : E'}
    (hnn : ∀ j, 0 ≤ num j z) (i : ι) : 0 ≤ normWeights num i z :=
  div_nonneg (hnn i) (Finset.sum_nonneg fun j _ => hnn j)

/-- A nonnegative normalized family with nonzero denominator has a positive slot. -/
theorem normWeights_pos {ι : Type*} [Fintype ι] {num : ι → E' → ℝ} {z : E'}
    (hnn : ∀ j, 0 ≤ num j z) (hne : (∑ j, num j z) ≠ 0) :
    ∃ i, 0 < normWeights num i z := by
  have hsum : ∑ i, normWeights num i z = 1 := normWeights_sum hne
  have hpos : 0 < ∑ i, normWeights num i z := by rw [hsum]; exact zero_lt_one
  simpa only [Finset.mem_univ, true_and] using
    (Finset.sum_pos_iff_of_nonneg
      (fun i (_hi : i ∈ Finset.univ) => normWeights_nonneg hnn i)).mp hpos

/-- A nonzero normalized weight can only occur in a nonzero numerator slot. -/
theorem num_ne_of_weight_ne {ι : Type*} [Fintype ι] {num : ι → E' → ℝ} {i : ι} {z : E'}
    (hweight : normWeights num i z ≠ 0) : num i z ≠ 0 := by
  intro hnum
  apply hweight
  simp [normWeights, hnum]

/-- **Basepoint concentration**: if all numerators except slot `i0` vanish at `z` (the `χ`-cutoff
at the basepoint) and the live one is nonzero, the weights are the Kronecker `δ_{i0}` there —
feeding `centerOfMass_delta` for the `F(O_k) = O_ℓ` basepoint identity. -/
theorem normWeights_delta {ι : Type*} [Fintype ι] {num : ι → E' → ℝ} {z : E'} (i0 : ι)
    (hzero : ∀ j, j ≠ i0 → num j z = 0) (hne : num i0 z ≠ 0) :
    normWeights num i0 z = 1 ∧ ∀ j, j ≠ i0 → normWeights num j z = 0 := by
  have hsum : ∑ j, num j z = num i0 z :=
    Finset.sum_eq_single i0 (fun b _ hb => hzero b hb)
      (fun h => absurd (Finset.mem_univ i0) h)
  refine ⟨?_, fun j hj => ?_⟩
  · simp [normWeights, hsum, div_self hne]
  · simp [normWeights, hzero j hj]

/-- Smoothness of the normalized weights (nonvanishing denominator). -/
theorem normWeights_contDiffOn {ι : Type*} [Fintype ι] {U : Set E'} {num : ι → E' → ℝ}
    (hnum : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (num i) U)
    (hne : ∀ z ∈ U, (∑ j, num j z) ≠ 0) (i : ι) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞) (normWeights num i) U :=
  (hnum i).div (ContDiffOn.sum fun j _ => hnum j) hne

/-- Nonnegative numerators with nonvanishing sum and controlled active support
produce exactly the pointwise weight data consumed by the Step-C average. -/
theorem normWeights_data {ι : Type} [Fintype ι] {s : Set E'} {U : ι → Set E'}
    {num : ι → E' → ℝ}
    (hnn : ∀ z ∈ s, ∀ i, 0 ≤ num i z)
    (hne : ∀ z ∈ s, (∑ j, num j z) ≠ 0)
    (hactive : ∀ z ∈ s, ∀ i, num i z ≠ 0 → z ∈ U i) :
    centerAverage.WeightDataOn s U (fun z i => normWeights num i z) where
  nonneg z hz i := normWeights_nonneg (hnn z hz) i
  pos z hz := normWeights_pos (hnn z hz) (hne z hz)
  sum_one z hz := normWeights_sum (hne z hz)
  active_mem z hz i hi := hactive z hz i (num_ne_of_weight_ne hi)

/-- **Pointwise products preserve `C^∞` convergence on compacts** — quotient-formula machinery
for the book's POU weights (`φ^α = χ∘J⋅ψ^α∘J / (…)`): pair the factors (`mapCInfConv_prodMk`)
and postcompose the globally-`C^∞` multiplication via the delivered `comp` engine. -/
theorem mapCInfConv_mul {U : Set E'} (hU : IsOpen U)
    {u v : ℕ → E' → ℝ} {uinf vinf : E' → ℝ}
    (hu : MapCInfConvOnCompacts U u uinf) (hv : MapCInfConvOnCompacts U v vinf)
    (huc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U)
    (hvc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) vinf U) :
    MapCInfConvOnCompacts U (fun k y => u k y * v k y) (fun y => uinf y * vinf y) := by
  have hpair := mapCInfConv_prodMk hU hu hv huc huinfc hvc hvinfc
  have hmulc : ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun q : ℝ × ℝ => q.1 * q.2) Set.univ :=
    contDiff_mul.contDiffOn
  have hcomp := MapCInfConvOnCompacts.comp hU isOpen_univ hpair
    (mapCInfConv_const (U := (Set.univ : Set (ℝ × ℝ))) (fun q : ℝ × ℝ => q.1 * q.2))
    (fun k => (huc k).prodMk (hvc k)) (huinfc.prodMk hvinfc)
    (fun _ => hmulc) hmulc (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)
  exact hcomp

/-- **Reciprocals of uniformly-bounded-below families preserve `C^∞` convergence** — the
denominator step of the POU weight quotient: postcompose `Inv.inv` (which is `C^∞` away from `0`,
`contDiffOn_inv`) on the open half-line `Ioi δ` that the uniform lower bound corrals the values
into. -/
theorem mapCInfConv_inv {U : Set E'} (hU : IsOpen U)
    {u : ℕ → E' → ℝ} {uinf : E' → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hu : MapCInfConvOnCompacts U u uinf)
    (huc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U)
    (hlow : ∀ k, ∀ y ∈ U, δ < u k y) (hlowinf : ∀ y ∈ U, δ < uinf y) :
    MapCInfConvOnCompacts U (fun k y => (u k y)⁻¹) (fun y => (uinf y)⁻¹) := by
  have hinvc : ContDiffOn ℝ (∞ : WithTop ℕ∞) (Inv.inv : ℝ → ℝ) (Set.Ioi δ) :=
    ContDiffOn.mono (contDiffOn_inv ℝ)
      (fun t ht => Set.mem_compl_singleton_iff.mpr (ne_of_gt (lt_trans hδ ht)))
  have hcomp := MapCInfConvOnCompacts.comp hU isOpen_Ioi hu
    (mapCInfConv_const (U := Set.Ioi δ) (Inv.inv : ℝ → ℝ))
    huc huinfc (fun _ => hinvc) hinvc
    (fun y hy => hlowinf y hy) (fun k y hy => hlow k y hy)
  exact hcomp

/-- **`C^∞` convergence of the normalized weights** — the full `lbl400` weight-quotient
convergence: per-slot numerator convergence + a uniform positive lower bound on the denominators
gives `normWeights (num k) i → normWeights numinf i` in `MapCInfConvOnCompacts U`.
Assembly: the denominators converge (`mapCInfConv_pi` + the summation CLM via `mapCInfConv_clm`),
their reciprocals converge (`mapCInfConv_inv`, corralled by the lower bound), and the quotient is
numerator times reciprocal (`mapCInfConv_mul` + `congr` on `div_eq_mul_inv`). -/
theorem normWeightsConv {ι : Type*} [Fintype ι] {U : Set E'} (hU : IsOpen U)
    {num : ℕ → ι → E' → ℝ} {numinf : ι → E' → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hconv : ∀ i, MapCInfConvOnCompacts U (fun k => num k i) (numinf i))
    (hc : ∀ k i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (num k i) U)
    (hcinf : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (numinf i) U)
    (hlow : ∀ k, ∀ z ∈ U, δ < ∑ j, num k j z)
    (hlowinf : ∀ z ∈ U, δ < ∑ j, numinf j z) (i : ι) :
    MapCInfConvOnCompacts U (fun k => normWeights (num k) i) (normWeights numinf i) := by
  -- the pi-family and the summation CLM give denominator convergence
  have hpi := mapCInfConv_pi hU hconv (fun i k => hc k i) hcinf
  set Lsum : (ι → ℝ) →L[ℝ] ℝ := ∑ j : ι, ContinuousLinearMap.proj j with hLsum
  have hpic : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun y (j : ι) => num k j y) U :=
    fun k => contDiffOn_pi.mpr fun j => hc k j
  have hpiinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun y (j : ι) => numinf j y) U :=
    contDiffOn_pi.mpr fun j => hcinf j
  have hsum0 := mapCInfConv_clm hU Lsum hpi hpic hpiinfc
  have hLapp : ∀ v : ι → ℝ, Lsum v = ∑ j, v j := by
    intro v
    rw [hLsum, ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => ContinuousLinearMap.proj_apply j v
  have hsum : MapCInfConvOnCompacts U (fun k y => ∑ j, num k j y)
      (fun y => ∑ j, numinf j y) := by
    refine hsum0.congr hU (fun k y _ => ?_) (fun y _ => ?_) <;> rw [hLapp]
  -- denominator smoothness and reciprocal convergence
  have hsumc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun y => ∑ j, num k j y) U :=
    fun k => ContDiffOn.sum fun j _ => hc k j
  have hsuminfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun y => ∑ j, numinf j y) U :=
    ContDiffOn.sum fun j _ => hcinf j
  have hinv := mapCInfConv_inv hU hδ hsum hsumc hsuminfc hlow hlowinf
  have hinvc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun y => (∑ j, num k j y)⁻¹) U :=
    fun k => (hsumc k).inv (fun z hz => ne_of_gt (lt_trans hδ (hlow k z hz)))
  have hinvinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun y => (∑ j, numinf j y)⁻¹) U :=
    hsuminfc.inv (fun z hz => ne_of_gt (lt_trans hδ (hlowinf z hz)))
  -- quotient = numerator × reciprocal
  have hmul := mapCInfConv_mul hU (hconv i) hinv (fun k => hc k i) (hcinf i) hinvc hinvinfc
  refine hmul.congr hU (fun k y _ => ?_) (fun y _ => ?_) <;>
    simp [normWeights, div_eq_mul_inv]

/-- **The book's weight numerators** (`lbl400`, chapter4.tex L1633–59): slot `i0` (the base
slot `α = 0`) is the bare bump readout `ψ_{i0} ∘ J_{i0}`, every other slot carries the `χ`-cutoff
factor `χ∘J_{i0} ⋅ ψ_i∘J_i`.  Feeding these to `normWeights` reproduces the book's POU weights;
the four lemmas below discharge every `normWeights` input except the covering positivity (the
denominator lower bound — the one honest geometric input). -/
noncomputable def bumpNum {ι : Type*} [DecidableEq ι] (χ : E' → ℝ) (ψ : ι → E' → ℝ)
    (J : ι → E' → E') (i0 : ι) (i : ι) (z : E') : ℝ :=
  if i = i0 then ψ i0 (J i0 z) else χ (J i0 z) * ψ i (J i z)

theorem bumpNum_nonneg {ι : Type*} [DecidableEq ι] {χ : E' → ℝ} {ψ : ι → E' → ℝ}
    {J : ι → E' → E'} {i0 : ι} (hχ : ∀ t, 0 ≤ χ t) (hψ : ∀ i t, 0 ≤ ψ i t) (i : ι) (z : E') :
    0 ≤ bumpNum χ ψ J i0 i z := by
  by_cases h : i = i0 <;> simp [bumpNum, h]
  · exact hψ i0 _
  · exact mul_nonneg (hχ _) (hψ i _)

/-- The book's explicit bump quotient supplies the pointwise weight package
once denominator positivity and bump-support membership are known. -/
theorem bumpWeights_data {ι : Type} [DecidableEq ι] [Fintype ι]
    {s : Set E'} {U : ι → Set E'} {χ : E' → ℝ} {ψ : ι → E' → ℝ}
    {J : ι → E' → E'} {i0 : ι}
    (hχ : ∀ t, 0 ≤ χ t) (hψ : ∀ i t, 0 ≤ ψ i t)
    (hne : ∀ z ∈ s, (∑ j, bumpNum χ ψ J i0 j z) ≠ 0)
    (hactive : ∀ z ∈ s, ∀ i, bumpNum χ ψ J i0 i z ≠ 0 → z ∈ U i) :
    centerAverage.WeightDataOn s U
      (fun z i => normWeights (bumpNum χ ψ J i0) i z) :=
  normWeights_data (fun z _hz i => bumpNum_nonneg hχ hψ i z) hne hactive

/-- **Basepoint kill**: where the cutoff vanishes (`χ (J_{i0} x₀) = 0`, the book's `O_k`), every
non-base numerator vanishes and the base one is the bare bump value — combined with
`normWeights_delta` and `centerOfMass_delta` this is the full weight side of `F(O_k) = O_ℓ`. -/
theorem bumpNum_delta {ι : Type*} [DecidableEq ι] {χ : E' → ℝ} {ψ : ι → E' → ℝ}
    {J : ι → E' → E'} {i0 : ι} {x₀ : E'} (hχ0 : χ (J i0 x₀) = 0) :
    (∀ j, j ≠ i0 → bumpNum χ ψ J i0 j x₀ = 0) ∧
      bumpNum χ ψ J i0 i0 x₀ = ψ i0 (J i0 x₀) := by
  refine ⟨fun j hj => ?_, by simp [bumpNum]⟩
  simp [bumpNum, hj, hχ0]

/-- **Alternative basepoint kill by separated bump supports.**  If every non-base `ψ_j` readout
vanishes at the basepoint, the non-base numerators vanish independently of `χ`.  This is useful
for separation-based variants, but it is not the mechanism used in MSM135: there `χ` is chosen
to vanish near the origin, so `bumpNum_delta` is the book-facing `lbl400` route. -/
theorem bumpNum_delta' {ι : Type*} [DecidableEq ι] {χ : E' → ℝ} {ψ : ι → E' → ℝ}
    {J : ι → E' → E'} {i0 : ι} {x₀ : E'} (hψ0 : ∀ j, j ≠ i0 → ψ j (J j x₀) = 0) :
    (∀ j, j ≠ i0 → bumpNum χ ψ J i0 j x₀ = 0) ∧
      bumpNum χ ψ J i0 i0 x₀ = ψ i0 (J i0 x₀) := by
  refine ⟨fun j hj => ?_, by simp [bumpNum]⟩
  simp [bumpNum, hj, hψ0 j hj]

theorem bumpNum_contDiffOn {ι : Type*} [DecidableEq ι] {U : Set E'} {χ : E' → ℝ}
    {ψ : ι → E' → ℝ} {J : ι → E' → E'} {i0 : ι}
    (hχ : ContDiff ℝ (∞ : WithTop ℕ∞) χ) (hψ : ∀ i, ContDiff ℝ (∞ : WithTop ℕ∞) (ψ i))
    (hJ : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (J i) U) (i : ι) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞) (bumpNum χ ψ J i0 i) U := by
  by_cases h : i = i0
  · subst h
    exact ContDiffOn.congr ((hψ i).comp_contDiffOn (hJ i)) (fun z _ => by simp [bumpNum])
  · have h1 : ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun z => χ (J i0 z)) U :=
      hχ.comp_contDiffOn (hJ i0)
    have h2 : ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun z => ψ i (J i z)) U :=
      (hψ i).comp_contDiffOn (hJ i)
    exact ContDiffOn.congr (h1.mul h2) (fun z _ => by simp [bumpNum, h])

/-- **Numerator convergence**: the cutoff/bump factors are fixed (`k`-independent) globally-`C^∞`
maps, so their readouts along the converging transition families converge (`comp` with a constant
outer family on `univ`), and the products converge (`mapCInfConv_mul`).  Feeding
`normWeightsConv` with these numerators gives the full convergence of the book's POU weights. -/
theorem bumpNumConv {ι : Type*} [DecidableEq ι] [ProperSpace E'] {U : Set E'} (hU : IsOpen U)
    {χ : E' → ℝ} {ψ : ι → E' → ℝ} {J : ι → ℕ → E' → E'} {Jinf : ι → E' → E'} {i0 : ι}
    (hχ : ContDiff ℝ (∞ : WithTop ℕ∞) χ) (hψ : ∀ i, ContDiff ℝ (∞ : WithTop ℕ∞) (ψ i))
    (hJ : ∀ i, MapCInfConvOnCompacts U (J i) (Jinf i))
    (hJc : ∀ i k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (J i k) U)
    (hJinfc : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (Jinf i) U) (i : ι) :
    MapCInfConvOnCompacts U (fun k => bumpNum χ ψ (fun j => J j k) i0 i)
      (bumpNum χ ψ Jinf i0 i) := by
  have hread : ∀ (g : E' → ℝ), ContDiff ℝ (∞ : WithTop ℕ∞) g → ∀ j : ι,
      MapCInfConvOnCompacts U (fun k z => g (J j k z)) (fun z => g (Jinf j z)) := by
    intro g hg j
    exact MapCInfConvOnCompacts.comp hU isOpen_univ (hJ j)
      (mapCInfConv_const (U := (Set.univ : Set E')) g) (hJc j) (hJinfc j)
      (fun _ => hg.contDiffOn) hg.contDiffOn
      (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)
  by_cases h : i = i0
  · subst h
    have := hread (ψ i) (hψ i) i
    refine this.congr hU (fun k z _ => ?_) (fun z _ => ?_) <;> simp [bumpNum]
  · have h1 := hread χ hχ i0
    have h2 := hread (ψ i) (hψ i) i
    have hmul := mapCInfConv_mul hU h1 h2
      (fun k => hχ.comp_contDiffOn (hJc i0 k)) (hχ.comp_contDiffOn (hJinfc i0))
      (fun k => (hψ i).comp_contDiffOn (hJc i k)) ((hψ i).comp_contDiffOn (hJinfc i))
    refine hmul.congr hU (fun k z _ => ?_) (fun z _ => ?_) <;> simp [bumpNum, h]

/-- **ψ-kill in `ContDiffBump` language**: if the basepoint's non-base chart images have norm at
least the bump's outer radius (the `lbl383` ball-separation fact), the ψ-readouts vanish and the
weights concentrate (`bumpNum_delta'` + `zero_of_le_dist`).  The geometric residue is EXACTLY the
norm lower bound `hfar`. -/
theorem bumpNumDeltaOfNorm {ι : Type*} [DecidableEq ι] [HasContDiffBump E'] {χ : E' → ℝ}
    (f : ι → ContDiffBump (0 : E')) {J : ι → E' → E'} {i0 : ι} {x₀ : E'}
    (hfar : ∀ j, j ≠ i0 → (f j).rOut ≤ ‖J j x₀‖) :
    (∀ j, j ≠ i0 → bumpNum χ (fun i => ⇑(f i)) J i0 j x₀ = 0) ∧
      bumpNum χ (fun i => ⇑(f i)) J i0 i0 x₀ = f i0 (J i0 x₀) :=
  bumpNum_delta' (fun j hj => (f j).zero_of_le_dist
    (by rw [dist_zero_right]; exact hfar j hj))

/-- **Single-numerator lower bound in `ContDiffBump` language**: if `z`'s own-slot chart image is
inside the bump's inner ball (`z` is covered by its ball — `lbl383`), the ψ-factor is `1`, so the
numerator is `1` (base slot) or exactly the cutoff value `χ(J_{i0} z)` (other slots).  With
`bumpNum_sum_low` this reduces the covering positivity to: every `z ∈ U` has a slot with
`‖J_j z‖ ≤ rIn`, and on non-base slots `δ ≤ χ(J_{i0} z)`. -/
theorem bumpNumLowOfMem {ι : Type*} [DecidableEq ι] [HasContDiffBump E'] {χ : E' → ℝ}
    (f : ι → ContDiffBump (0 : E')) {J : ι → E' → E'} {i0 : ι} {z : E'} {j : ι} {δ : ℝ}
    (hmem : ‖J j z‖ ≤ (f j).rIn)
    (hχδ : j ≠ i0 → δ ≤ χ (J i0 z)) (hδ1 : j = i0 → δ ≤ 1) :
    δ ≤ bumpNum χ (fun i => ⇑(f i)) J i0 j z := by
  have hone : f j (J j z) = 1 :=
    (f j).one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right]; exact hmem)
  by_cases h : j = i0
  · subst h
    simpa [bumpNum, hone] using hδ1 rfl
  · simpa [bumpNum, h, hone] using hχδ h

/-- **Covering positivity, reduced**: the denominator lower bound (`normWeightsConv.hlow`) follows
from a SINGLE numerator being bounded below (all numerators are nonnegative) — so the honest
geometric input shrinks to "every `z ∈ U` lies in some ball where its own numerator is `≥ δ`"
(the book's covering statement for `lbl383`'s balls). -/
theorem bumpNum_sum_low {ι : Type*} [DecidableEq ι] [Fintype ι] {χ : E' → ℝ} {ψ : ι → E' → ℝ}
    {J : ι → E' → E'} {i0 : ι} (hχ : ∀ t, 0 ≤ χ t) (hψ : ∀ i t, 0 ≤ ψ i t)
    {z : E'} {δ : ℝ} (h : ∃ j, δ ≤ bumpNum χ ψ J i0 j z) :
    δ ≤ ∑ j, bumpNum χ ψ J i0 j z := by
  obtain ⟨j, hj⟩ := h
  exact le_trans hj (Finset.single_le_sum
    (fun j' _ => bumpNum_nonneg hχ hψ j' z) (Finset.mem_univ j))

/-- **Book cutoff denominator bound.**  Suppose the ordinary inner bump balls
cover `z`.  If the base cutoff is `1`, any covering slot contributes numerator
`1`; if it is not `1`, it suffices that `z` lies in the base slot's inner bump
ball, whose uncut numerator is `1`.  Thus the modified numerator sum remains at
least `1` after the basepoint cutoff. -/
theorem bumpNum_sum_one {ι : Type*} [DecidableEq ι] [Fintype ι]
    [HasContDiffBump E'] {χ : E' → ℝ} (f : ι → ContDiffBump (0 : E'))
    {J : ι → E' → E'} {i0 : ι} {z : E'}
    (hχ : ∀ t, 0 ≤ χ t)
    (hcover : ∃ j, ‖J j z‖ ≤ (f j).rIn)
    (hbase : χ (J i0 z) ≠ 1 → ‖J i0 z‖ ≤ (f i0).rIn) :
    1 ≤ ∑ j, bumpNum χ (fun i => ⇑(f i)) J i0 j z := by
  apply bumpNum_sum_low hχ (fun i t => (f i).nonneg)
  by_cases hχ1 : χ (J i0 z) = 1
  · obtain ⟨j, hj⟩ := hcover
    refine ⟨j, bumpNumLowOfMem f hj ?_ ?_⟩
    · intro _hj
      rw [hχ1]
    · intro _hj
      exact le_rfl
  · refine ⟨i0, bumpNumLowOfMem f (hbase hχ1) ?_ ?_⟩
    · intro hi
      exact (hi rfl).elim
    · intro _hi
      exact le_rfl

/-- **The complete weights-slot producer** — the `hw` input of `averagedTargets₂` from the fully
concrete weight pipeline: `w_k := normWeights (bumpNum χ ψ (J · k) i0)` with fixed `ContDiffBump`
data `χ`/`ψ` and the (source-side, `k`-only) transition families `J`.  Chains `bumpNumConv` →
`normWeightsConv` and reindexes (`comp_tendsto_atTop`) into the two-index diagonal form.  The only
geometric input left is the covering lower bound `hlow` (reduced by `bumpNum_sum_low`). -/
theorem weightsSlot {ι : Type*} [DecidableEq ι] [Fintype ι] [ProperSpace E']
    {U : Set E'} (hU : IsOpen U)
    {χ : E' → ℝ} {ψ : ι → E' → ℝ} {J : ι → ℕ → E' → E'} {Jinf : ι → E' → E'} {i0 : ι}
    {δ : ℝ} (hδ : 0 < δ)
    (hχ : ContDiff ℝ (∞ : WithTop ℕ∞) χ) (hψ : ∀ i, ContDiff ℝ (∞ : WithTop ℕ∞) (ψ i))
    (hJ : ∀ i, MapCInfConvOnCompacts U (J i) (Jinf i))
    (hJc : ∀ i k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (J i k) U)
    (hJinfc : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (Jinf i) U)
    (hlow : ∀ k, ∀ z ∈ U, δ < ∑ j, bumpNum χ ψ (fun j' => J j' k) i0 j z)
    (hlowinf : ∀ z ∈ U, δ < ∑ j, bumpNum χ ψ Jinf i0 j z) (i : ι)
    (kn ln : ℕ → ℕ) (hkn : Filter.Tendsto kn Filter.atTop Filter.atTop)
    (_hln : Filter.Tendsto ln Filter.atTop Filter.atTop) :
    MapCInfConvOnCompacts U
      (fun n => normWeights (bumpNum χ ψ (fun j => J j (kn n)) i0) i)
      (normWeights (bumpNum χ ψ Jinf i0) i) := by
  have hsingle : MapCInfConvOnCompacts U
      (fun k => normWeights (bumpNum χ ψ (fun j => J j k) i0) i)
      (normWeights (bumpNum χ ψ Jinf i0) i) := by
    refine normWeightsConv hU hδ (fun j => bumpNumConv hU hχ hψ hJ hJc hJinfc j)
      (fun k j => bumpNum_contDiffOn hχ hψ (fun j' => hJc j' k) j)
      (fun j => bumpNum_contDiffOn hχ hψ hJinfc j) hlow hlowinf i
  exact hsingle.comp_tendsto_atTop hkn

/-- **Bilinear pullback perturbation (the `lbl402` `C⁰` core)** — for a bilinear form `B` (a
metric readout) and a near-identity `A` (= `dG`):
`|B(Av, Aw) − B(v, w)| ≤ ‖B‖·‖A − id‖·(1 + ‖A‖)·‖v‖‖w‖`, by splitting the difference through
the two slots.  Feeding `A := dG` with the Neumann bound and `B := ` the chart metric gives the
`c0_small` slot of `PreApproxIsoDataOn` for the pullback error `G^*h − h`. -/
theorem bilinPerturb {B : E' →L[ℝ] E' →L[ℝ] ℝ} {A : E' →L[ℝ] E'} (v w : E') :
    |B (A v) (A w) - B v w|
      ≤ ‖B‖ * ‖A - ContinuousLinearMap.id ℝ E'‖ * (1 + ‖A‖) * (‖v‖ * ‖w‖) := by
  have hsplit : B (A v) (A w) - B v w
      = B ((A - ContinuousLinearMap.id ℝ E') v) (A w)
        + B v ((A - ContinuousLinearMap.id ℝ E') w) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_id', id_eq, map_sub,
      ContinuousLinearMap.sub_apply]
    abel
  rw [hsplit]
  have h1 : |B ((A - ContinuousLinearMap.id ℝ E') v) (A w)|
      ≤ ‖B‖ * (‖A - ContinuousLinearMap.id ℝ E'‖ * ‖v‖) * (‖A‖ * ‖w‖) := by
    calc |B ((A - ContinuousLinearMap.id ℝ E') v) (A w)|
        ≤ ‖B‖ * ‖(A - ContinuousLinearMap.id ℝ E') v‖ * ‖A w‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm₂ B _ _
      _ ≤ ‖B‖ * (‖A - ContinuousLinearMap.id ℝ E'‖ * ‖v‖) * (‖A‖ * ‖w‖) := by
          gcongr
          · exact ContinuousLinearMap.le_opNorm _ v
          · exact ContinuousLinearMap.le_opNorm A w
  have h2 : |B v ((A - ContinuousLinearMap.id ℝ E') w)|
      ≤ ‖B‖ * ‖v‖ * (‖A - ContinuousLinearMap.id ℝ E'‖ * ‖w‖) := by
    calc |B v ((A - ContinuousLinearMap.id ℝ E') w)|
        ≤ ‖B‖ * ‖v‖ * ‖(A - ContinuousLinearMap.id ℝ E') w‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm₂ B _ _
      _ ≤ ‖B‖ * ‖v‖ * (‖A - ContinuousLinearMap.id ℝ E'‖ * ‖w‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ w
  calc |B ((A - ContinuousLinearMap.id ℝ E') v) (A w)
        + B v ((A - ContinuousLinearMap.id ℝ E') w)|
      ≤ |B ((A - ContinuousLinearMap.id ℝ E') v) (A w)|
        + |B v ((A - ContinuousLinearMap.id ℝ E') w)| := abs_add_le _ _
    _ ≤ ‖B‖ * (‖A - ContinuousLinearMap.id ℝ E'‖ * ‖v‖) * (‖A‖ * ‖w‖)
        + ‖B‖ * ‖v‖ * (‖A - ContinuousLinearMap.id ℝ E'‖ * ‖w‖) := add_le_add h1 h2
    _ = ‖B‖ * ‖A - ContinuousLinearMap.id ℝ E'‖ * (1 + ‖A‖) * (‖v‖ * ‖w‖) := by ring

/-- **Pullback error against a different base metric (the `lbl402` `c0_small` chart form)** —
triangulating `bilinPerturb` through the target form: for the pulled-back quadratic readout
against a possibly different base form,
`|B₁(Av, Av) − B₀(v, v)| ≤ (‖B₁‖·‖A−id‖·(1+‖A‖) + ‖B₁ − B₀‖)·‖v‖²`.
Instantiating `B₁ := ` the target metric's chart form at the image point, `B₀ := ` the source
metric's chart form, `A := dG` (Neumann-small), and the `lbl394`/`lbl395` `h ≈ δ ≈ g` equivalence
for `‖B₁ − B₀‖` produces the pointwise `PreApproxIsoDataOn.c0_small` bound. -/
theorem quadPerturbTri {B₀ B₁ : E' →L[ℝ] E' →L[ℝ] ℝ} {A : E' →L[ℝ] E'} (v : E') :
    |B₁ (A v) (A v) - B₀ v v|
      ≤ (‖B₁‖ * ‖A - ContinuousLinearMap.id ℝ E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) * (‖v‖ * ‖v‖) := by
  have h1 := bilinPerturb (B := B₁) (A := A) v v
  have h2 : |B₁ v v - B₀ v v| ≤ ‖B₁ - B₀‖ * (‖v‖ * ‖v‖) := by
    have : B₁ v v - B₀ v v = (B₁ - B₀) v v := by
      simp [ContinuousLinearMap.sub_apply]
    rw [this, ← Real.norm_eq_abs]
    calc ‖(B₁ - B₀) v v‖ ≤ ‖B₁ - B₀‖ * ‖v‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm₂ _ v v
      _ = ‖B₁ - B₀‖ * (‖v‖ * ‖v‖) := by ring
  calc |B₁ (A v) (A v) - B₀ v v|
      = |(B₁ (A v) (A v) - B₁ v v) + (B₁ v v - B₀ v v)| := by ring_nf
    _ ≤ |B₁ (A v) (A v) - B₁ v v| + |B₁ v v - B₀ v v| := abs_add_le _ _
    _ ≤ ‖B₁‖ * ‖A - ContinuousLinearMap.id ℝ E'‖ * (1 + ‖A‖) * (‖v‖ * ‖v‖)
        + ‖B₁ - B₀‖ * (‖v‖ * ‖v‖) := add_le_add h1 h2
    _ = (‖B₁‖ * ‖A - ContinuousLinearMap.id ℝ E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) * (‖v‖ * ‖v‖) := by
        ring

/-- **Two-slot version of `quadPerturbTri`** — the shape the orthonormal-component bound of the
pullback error takes (`A(bᵢ, bⱼ)` has independent slots):
`|B₁(Av, Aw) − B₀(v, w)| ≤ (‖B₁‖·‖A−id‖·(1+‖A‖) + ‖B₁−B₀‖)·‖v‖‖w‖`. -/
theorem bilinPerturbTri {B₀ B₁ : E' →L[ℝ] E' →L[ℝ] ℝ} {A : E' →L[ℝ] E'} (v w : E') :
    |B₁ (A v) (A w) - B₀ v w|
      ≤ (‖B₁‖ * ‖A - ContinuousLinearMap.id ℝ E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) * (‖v‖ * ‖w‖) := by
  have h1 := bilinPerturb (B := B₁) (A := A) v w
  have h2 : |B₁ v w - B₀ v w| ≤ ‖B₁ - B₀‖ * (‖v‖ * ‖w‖) := by
    have hsub : B₁ v w - B₀ v w = (B₁ - B₀) v w := by
      simp [ContinuousLinearMap.sub_apply]
    rw [hsub, ← Real.norm_eq_abs]
    calc ‖(B₁ - B₀) v w‖ ≤ ‖B₁ - B₀‖ * ‖v‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm₂ _ v w
      _ = ‖B₁ - B₀‖ * (‖v‖ * ‖w‖) := by ring
  calc |B₁ (A v) (A w) - B₀ v w|
      = |(B₁ (A v) (A w) - B₁ v w) + (B₁ v w - B₀ v w)| := by ring_nf
    _ ≤ |B₁ (A v) (A w) - B₁ v w| + |B₁ v w - B₀ v w| := abs_add_le _ _
    _ ≤ ‖B₁‖ * ‖A - ContinuousLinearMap.id ℝ E'‖ * (1 + ‖A‖) * (‖v‖ * ‖w‖)
        + ‖B₁ - B₀‖ * (‖v‖ * ‖w‖) := add_le_add h1 h2
    _ = (‖B₁‖ * ‖A - ContinuousLinearMap.id ℝ E'‖ * (1 + ‖A‖) + ‖B₁ - B₀‖) * (‖v‖ * ‖w‖) := by
        ring

/-- **`quadPerturbTri`, Neumann-concretized**: under `‖A − id‖ ≤ ε` the pullback coefficient is
`ε(2 + ε)`, so `|B₁(Av,Av) − B₀(v,v)| ≤ (‖B₁‖·ε·(2+ε) + ‖B₁−B₀‖)·‖v‖²` — the shape the
`lbl402` `(ε, 0)` bound takes with the book's `ε < 1` (coefficient `≤ 3ε`). -/
theorem quadPerturbNeumann {B₀ B₁ : E' →L[ℝ] E' →L[ℝ] ℝ} {A : E' →L[ℝ] E'} {ε : ℝ}
    (hA : ‖A - ContinuousLinearMap.id ℝ E'‖ ≤ ε) (v : E') :
    |B₁ (A v) (A v) - B₀ v v|
      ≤ (‖B₁‖ * ε * (2 + ε) + ‖B₁ - B₀‖) * (‖v‖ * ‖v‖) := by
  refine (quadPerturbTri v).trans ?_
  have hAle : ‖A‖ ≤ 1 + ε := by
    calc ‖A‖ = ‖ContinuousLinearMap.id ℝ E' + (A - ContinuousLinearMap.id ℝ E')‖ := by
          congr 1; abel
      _ ≤ ‖ContinuousLinearMap.id ℝ E'‖ + ‖A - ContinuousLinearMap.id ℝ E'‖ := norm_add_le _ _
      _ ≤ 1 + ε := add_le_add ContinuousLinearMap.norm_id_le hA
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hA
  have hcoef : ‖B₁‖ * ‖A - ContinuousLinearMap.id ℝ E'‖ * (1 + ‖A‖)
      ≤ ‖B₁‖ * ε * (2 + ε) := by
    have h2 : (1 : ℝ) + ‖A‖ ≤ 2 + ε := by linarith [hAle]
    gcongr
  gcongr

/-- **Order-`1` convergence → Neumann bound** — the formal `lbl404 → lbl403` interface: the
`r = 1` clause of `mapDerivNorm` closeness-to-identity is exactly the Neumann hypothesis
`‖id − dG‖ ≤ ε` that `hlocOn_of_chartNeumann…`/`injOn_of_fderiv_near_id` consume. -/
theorem neumannOfDerivNorm {G : E' → E'} {x : E'} {ε : ℝ}
    (hG : DifferentiableAt ℝ G x)
    (h : mapDerivNorm 1 G (fun y => y) x ≤ ε) :
    ‖ContinuousLinearMap.id ℝ E' - fderiv ℝ G x‖ ≤ ε := by
  simp only [mapDerivNorm] at h
  rw [norm_iteratedFDeriv_one] at h
  have hsub : fderiv ℝ (fun y => G y - y) x
      = fderiv ℝ G x - ContinuousLinearMap.id ℝ E' := by
    have h1 : HasFDerivAt (fun y => G y - y)
        (fderiv ℝ G x - ContinuousLinearMap.id ℝ E') x :=
      hG.hasFDerivAt.sub (hasFDerivAt_id x)
    exact h1.fderiv
  rw [hsub, norm_sub_rev] at h
  exact h

/-- **Diagonal convergence of a two-index composition to the identity** — the producer of the
`hu`/`hv` slots of `averagedCInf_id₂`: single-index `C^∞` convergences `B_k → B∞` (source side)
and `A_ℓ → A∞` (target side) with `A∞ ∘ B∞ = id` on `U` give, for every pair of `→ ∞`
reindexings, single-index convergence of the reindexed composition to the identity
(`comp_tendsto_atTop` + the delivered `MapCInfConvOnCompacts.comp` + `congr`).  Instantiating
`B`/`A` with the per-slot `normalTransition` families (whose convergence is
`StepCTransitionRefine`'s output) produces the targets-slot hypothesis of the two-index
`lbl404` endpoint. -/
theorem compDiagConvId {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [ProperSpace F']
    {U : Set E'} {V : Set F'} (hU : IsOpen U) (hV : IsOpen V)
    {B : ℕ → E' → F'} {Binf : E' → F'} {A : ℕ → F' → E'} {Ainf : F' → E'}
    (hB : MapCInfConvOnCompacts U B Binf) (hA : MapCInfConvOnCompacts V A Ainf)
    (hBc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Binf U)
    (hAc : ∀ l, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A l) V)
    (hAinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V) (hmapk : ∀ k, Set.MapsTo (B k) U V)
    (hid : ∀ y ∈ U, Ainf (Binf y) = y)
    (kn ln : ℕ → ℕ) (hkn : Filter.Tendsto kn Filter.atTop Filter.atTop)
    (hln : Filter.Tendsto ln Filter.atTop Filter.atTop) :
    MapCInfConvOnCompacts U (fun n y => A (ln n) (B (kn n) y)) (fun y => y) := by
  have hB' : MapCInfConvOnCompacts U (fun n => B (kn n)) Binf :=
    hB.comp_tendsto_atTop hkn
  have hA' : MapCInfConvOnCompacts V (fun n => A (ln n)) Ainf :=
    hA.comp_tendsto_atTop hln
  have hcomp := MapCInfConvOnCompacts.comp hU hV hB' hA'
    (fun n => hBc (kn n)) hBinfc (fun n => hAc (ln n)) hAinfc hmap (fun n => hmapk (kn n))
  exact hcomp.congr hU (fun _ => Set.eqOn_refl _ _) (fun y hy => (hid y hy).symm)

/-- **Targets-tuple diagonal convergence — the concrete `hv` producer for `averagedCInf_id₂`.**
Per slot `i`, the target is the composite `A_i^ℓ ∘ B_i^k` of the two normal-transition families
(`StepCTransitionRefine`'s output shape: source-side convergence on `U`, target-side on `V i`,
limits mutually inverse); `compDiagConvId` gives each slot's reindexed convergence to `id`, and
`mapCInfConv_pi` packages the slots into the `(ι → E')`-valued points-tuple converging to the
diagonal `fun y _ => y` — exactly the `hv` slot of the two-index `lbl404` endpoint (with
`vinf := diagonal`), for every pair of `→ ∞` reindexings. -/
theorem targetsDiagConv {ι : Type*} [Fintype ι] {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [ProperSpace F']
    {U : Set E'} {V : ι → Set F'} (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    {B : ι → ℕ → E' → F'} {Binf : ι → E' → F'} {A : ι → ℕ → F' → E'} {Ainf : ι → F' → E'}
    (hB : ∀ i, MapCInfConvOnCompacts U (B i) (Binf i))
    (hA : ∀ i, MapCInfConvOnCompacts (V i) (A i) (Ainf i))
    (hBc : ∀ i k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (B i k) U)
    (hBinfc : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (Binf i) U)
    (hAc : ∀ i l, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A i l) (V i))
    (hAinfc : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (Ainf i) (V i))
    (hmap : ∀ i, Set.MapsTo (Binf i) U (V i)) (hmapk : ∀ i k, Set.MapsTo (B i k) U (V i))
    (hid : ∀ i, ∀ y ∈ U, Ainf i (Binf i y) = y)
    (kn ln : ℕ → ℕ) (hkn : Filter.Tendsto kn Filter.atTop Filter.atTop)
    (hln : Filter.Tendsto ln Filter.atTop Filter.atTop) :
    MapCInfConvOnCompacts U (fun n y (i : ι) => A i (ln n) (B i (kn n) y))
      (fun y (_ : ι) => y) := by
  have hslot : ∀ i, MapCInfConvOnCompacts U (fun n y => A i (ln n) (B i (kn n) y))
      (fun y => y) := fun i =>
    compDiagConvId hU (hV i) (hB i) (hA i) (hBc i) (hBinfc i) (hAc i) (hAinfc i)
      (hmap i) (hmapk i) (hid i) kn ln hkn hln
  have hslotc : ∀ i n, ContDiffOn ℝ (∞ : WithTop ℕ∞)
      (fun y => A i (ln n) (B i (kn n) y)) U := fun i n =>
    (hAc i (ln n)).comp (hBc i (kn n)) (hmapk i (kn n))
  exact mapCInfConv_pi hU hslot hslotc (fun _ => contDiffOn_id)

/-- **`lbl404` two-index endpoint — the averaged map is `(ε, p)`-close to the identity for `k, ℓ`
large INDEPENDENTLY.**  The `lbl397`-facing form of `averagedCInf_id`: weights/targets are
two-index families (`k` = source member, `ℓ` = target member), their convergence supplied in
diagonal form (every pair of `→ ∞` reindexings converges single-index — producible from the
delivered engines via `MapCInfConvOnCompacts.comp_tendsto_atTop`), and the conclusion is the
book's two-index threshold.  Proof = the `comp_cInf_id_on` contradiction/diagonalization: bad
indices `k_N, ℓ_N ≥ N` would give reindexed sequences still tending to infinity, contradicting
the single-index `averagedCInf_id` on the diagonal family. -/
theorem averagedCInf_id₂ {U : Set E'} {V : Set (P × Q)} (hU : IsOpen U) (hV : IsOpen V)
    [ProperSpace (P × Q)]
    {u : ℕ → ℕ → E' → P} {uinf : E' → P} {v : ℕ → ℕ → E' → Q} {vinf : E' → Q} {Φ : P × Q → E'}
    (hu : ∀ kn ln : ℕ → ℕ, Filter.Tendsto kn Filter.atTop Filter.atTop →
      Filter.Tendsto ln Filter.atTop Filter.atTop →
      MapCInfConvOnCompacts U (fun n => u (kn n) (ln n)) uinf)
    (hv : ∀ kn ln : ℕ → ℕ, Filter.Tendsto kn Filter.atTop Filter.atTop →
      Filter.Tendsto ln Filter.atTop Filter.atTop →
      MapCInfConvOnCompacts U (fun n => v (kn n) (ln n)) vinf)
    (huc : ∀ k l, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k l) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U)
    (hvc : ∀ k l, ContDiffOn ℝ (∞ : WithTop ℕ∞) (v k l) U)
    (hvinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) vinf U)
    (hΦc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Φ V)
    (hmapk : ∀ k l, Set.MapsTo (fun y => (u k l y, v k l y)) U V)
    (hmap : Set.MapsTo (fun y => (uinf y, vinf y)) U V)
    (hdiag : ∀ y ∈ U, Φ (uinf y, vinf y) = y)
    {K : Set E'} (hK : IsCompact K) (hKU : K ⊆ U) (p : ℕ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ r ≤ p, ∀ x ∈ K,
      mapDerivNorm r (fun y => Φ (u k l y, v k l y)) (fun y => y) x ≤ ε := by
  classical
  intro ε hε
  by_contra hbad
  push Not at hbad
  choose k hk hbad using hbad
  choose l hl hbad using hbad
  choose r hr hbad using hbad
  choose x hx hbad using hbad
  have hk_tendsto : Filter.Tendsto k Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hk Filter.tendsto_id
  have hl_tendsto : Filter.Tendsto l Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hl Filter.tendsto_id
  have hconv : MapCInfConvOnCompacts U
      (fun n y => Φ (u (k n) (l n) y, v (k n) (l n) y)) (fun y => y) :=
    averagedCInf_id hU hV (hu k l hk_tendsto hl_tendsto) (hv k l hk_tendsto hl_tendsto)
      (fun n => huc (k n) (l n)) huinfc (fun n => hvc (k n) (l n)) hvinfc hΦc
      (fun n => hmapk (k n) (l n)) hmap hdiag
  obtain ⟨N, hN⟩ := hconv K hK hKU p ε hε
  exact not_lt_of_ge (hN N le_rfl (r N) (hr N) (x N) (hx N)) (hbad N)

/-- **`lbl404` semi-concrete two-index endpoint** — targets instantiated as the per-slot
transition composites (`targetsDiagConv`'s hypotheses = `StepCTransitionRefine`'s output shape),
weights left as atomic honest inputs (diagonal-form convergence + smoothness — the shape the
still-unbuilt POU layer must produce), the outer map `Φ` and the diagonal identity threaded (from
`chartCm_contDiffOn` / `diagEventuallyEqId`).  Conclusion = the book's `lbl397` two-index
threshold for the averaged comparison map.  After this, closing `lbl404` is *pure data*: the
concrete `normalTransition` families and the concrete POU weights. -/
theorem averagedTargets₂ {ι : Type*} [Fintype ι] {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [ProperSpace F']
    {U : Set E'} {V : ι → Set F'} {W : Set (P × (ι → E'))}
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hW : IsOpen W)
    [ProperSpace (P × (ι → E'))]
    {w : ℕ → ℕ → E' → P} {winf : E' → P}
    {B : ι → ℕ → E' → F'} {Binf : ι → E' → F'} {A : ι → ℕ → F' → E'} {Ainf : ι → F' → E'}
    {Φ : P × (ι → E') → E'}
    (hw : ∀ kn ln : ℕ → ℕ, Filter.Tendsto kn Filter.atTop Filter.atTop →
      Filter.Tendsto ln Filter.atTop Filter.atTop →
      MapCInfConvOnCompacts U (fun n => w (kn n) (ln n)) winf)
    (hwc : ∀ k l, ContDiffOn ℝ (∞ : WithTop ℕ∞) (w k l) U)
    (hwinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) winf U)
    (hB : ∀ i, MapCInfConvOnCompacts U (B i) (Binf i))
    (hA : ∀ i, MapCInfConvOnCompacts (V i) (A i) (Ainf i))
    (hBc : ∀ i k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (B i k) U)
    (hBinfc : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (Binf i) U)
    (hAc : ∀ i l, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A i l) (V i))
    (hAinfc : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (Ainf i) (V i))
    (hmapBV : ∀ i, Set.MapsTo (Binf i) U (V i)) (hmapBVk : ∀ i k, Set.MapsTo (B i k) U (V i))
    (hid : ∀ i, ∀ y ∈ U, Ainf i (Binf i y) = y)
    (hΦc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Φ W)
    (hmapk : ∀ k l, Set.MapsTo
      (fun y => (w k l y, fun i : ι => A i l (B i k y))) U W)
    (hmap : Set.MapsTo (fun y => (winf y, fun _ : ι => y)) U W)
    (hdiag : ∀ y ∈ U, Φ (winf y, fun _ : ι => y) = y)
    {K : Set E'} (hK : IsCompact K) (hKU : K ⊆ U) (p : ℕ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ r ≤ p, ∀ x ∈ K,
      mapDerivNorm r (fun y => Φ (w k l y, fun i : ι => A i l (B i k y)))
        (fun y => y) x ≤ ε :=
  averagedCInf_id₂ (v := fun k l y (i : ι) => A i l (B i k y))
    (vinf := fun y (_ : ι) => y) hU hW hw
    (fun kn ln hkn hln => targetsDiagConv hU hV hB hA hBc hBinfc hAc hAinfc
      hmapBV hmapBVk hid kn ln hkn hln)
    hwc hwinfc
    (fun k l => contDiffOn_pi.mpr fun i => (hAc i l).comp (hBc i k) (hmapBVk i k))
    (contDiffOn_pi.mpr fun _ => contDiffOn_id)
    hΦc hmapk hmap hdiag hK hKU p

end CloseIdEngine

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [MetricSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [PseudoMetricSpace N]

/-- **`lbl403` reduction — `hloc ∧ hinj` for `stepB1_glue`.**  The local-diffeomorphism input `hloc`
is carried as the honest `lbl403` datum (the manifold inverse function theorem applied to the
Neumann-invertible `dF ≈ id`; the minimal missing bridge — see the module docstring).  The
injectivity `hinj` is then *derived* from the `C¹`-closeness displacement bound `hdisp` via
`injOn_of_dist_le`.  So the only genuine `lbl403` frontier is `hloc`. -/
theorem stepB1_hlocHinj {F : M → N} {U : Set M} {K : Real}
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hdisp : ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ K * dist (F x) (F y)) :
    IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U ∧ Set.InjOn F U :=
  ⟨hloc, injOn_of_dist_le hdisp⟩

/-- **`lbl403` `hloc` producer (finite order) — from `dF ≈ id` at the chart level.**  For finite
`n ≥ 1`, `C^n`-ness on the open ball `U` plus the Neumann bound `‖id − dG‖ < 1` on the chart-level
derivative `G = writtenInExtChartAt` (i.e. `dF ≈ id` below the conjugate scale) gives a `C^n` local
diffeomorphism on `U`, via the manifold forward IFT (`Coordinates.contMDiffOn_isLocalDiffeomorphOn`
+ the Neumann convenience `isInvertible_of_norm_id_sub_lt`).  This is the actual entry shape of
`lbl403`.  Note `n ≠ ∞` is required by the IFT; `stepB1_hlocHinj` above takes `∞`, whose plug-in
awaits the (deferred) `n = ∞` forward IFT. -/
theorem hlocOn_of_chartNeumann {F : M → N} {U : Set M} (n : ℕ) (hn : 1 ≤ n) (hU : IsOpen U)
    (hf : ContMDiffOn I I (n : ℕ∞) F U)
    (hneu : ∀ y ∈ U, ‖ContinuousLinearMap.id ℝ E -
        fderiv ℝ (writtenInExtChartAt I I y F) (extChartAt I y y)‖ < 1) :
    IsLocalDiffeomorphOn I I (n : ℕ∞) F U := by
  have hle : ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hne : ((n : ℕ∞) : WithTop ℕ∞) ≠ ∞ := by exact_mod_cast (ENat.coe_ne_top n)
  haveI : IsManifold I ((n : ℕ∞) : WithTop ℕ∞) M := IsManifold.of_le hle
  haveI : IsManifold I ((n : ℕ∞) : WithTop ℕ∞) N := IsManifold.of_le hle
  exact Coordinates.contMDiffOn_isLocalDiffeomorphOn (by exact_mod_cast hn) hne hU hf
    (fun y hy => Coordinates.isInvertible_of_norm_id_sub_lt (hneu y hy))

/-- **Fixed-chart differentiability.**  If `F` is `C^∞` on `U ⊆` (chart source at `x₀`) and maps `U`
into the chart source at `F x₀`, its fixed-chart representative `writtenInExtChartAt I I x₀ F` is
differentiable at every point of the chart image of `U` — the input `injOn_of_fderiv_near_id`
needs.  Compose chart-inverse, `F`, chart through `contMDiffAt`, then `contMDiffAt_iff_contDiffAt`. -/
theorem chartRep_differentiableAt {F : M → N} {U : Set M} (x₀ : M)
    (hU : IsOpen U) (hUsub : U ⊆ (extChartAt I x₀).source)
    (hf : ContMDiffOn I I (∞ : WithTop ℕ∞) F U)
    (hFsub : ∀ y ∈ U, F y ∈ (extChartAt I (F x₀)).source) :
    ∀ z ∈ (extChartAt I x₀) '' U,
      DifferentiableAt ℝ (writtenInExtChartAt I I x₀ F) z := by
  rintro z ⟨y, hy, rfl⟩
  have hyz : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    PartialEquiv.left_inv _ (hUsub hy)
  -- the three factors, as `ContMDiffAt` at the chained points
  have h1 : ContMDiffAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) ((extChartAt I x₀).symm)
      (extChartAt I x₀ y) :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds ((extChartAt I x₀).map_source (hUsub hy)))
  have h2 : ContMDiffAt I I (∞ : WithTop ℕ∞) F ((extChartAt I x₀).symm (extChartAt I x₀ y)) := by
    rw [hyz]; exact hf.contMDiffAt (hU.mem_nhds hy)
  have h3 : ContMDiffAt I 𝓘(ℝ, E) (∞ : WithTop ℕ∞) (extChartAt I (F x₀))
      (F ((extChartAt I x₀).symm (extChartAt I x₀ y))) := by
    rw [hyz]
    exact (contMDiffOn_extChartAt (I := I) (x := F x₀) (n := (∞ : WithTop ℕ∞))).contMDiffAt
      ((chartAt H (F x₀)).open_source.mem_nhds
        (extChartAt_source (I := I) (F x₀) ▸ hFsub y hy))
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : WithTop ℕ∞)
      (writtenInExtChartAt I I x₀ F) (extChartAt I x₀ y) :=
    (h3.comp _ h2).comp _ h1
  have hcd : ContDiffAt ℝ (∞ : WithTop ℕ∞) (writtenInExtChartAt I I x₀ F)
      (extChartAt I x₀ y) := contMDiffAt_iff_contDiffAt.mp hcomp
  exact hcd.differentiableAt (by exact_mod_cast (by simp : (⊤ : ℕ∞) ≠ 0))

/-- **`lbl403` `hloc` producer at `∞` — `stepB1_glue`'s exact entry shape.**  `C^∞`-ness on the
open ball `U` plus the Neumann bound `‖id − dG‖ < 1` at every point (i.e. `dF ≈ id` below the
conjugate scale) gives a `C^∞` local diffeomorphism on `U`, via the `n = ∞` manifold forward IFT
(`Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty`, the inverse-uniqueness upgrade).  Feeds
`stepB1_hlocHinj`/`stepB1_glue` verbatim: with the displacement bound `hdisp` this discharges BOTH
`hloc` and `hinj`. -/
theorem hlocOn_of_chartNeumann_infty {F : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I I (∞ : WithTop ℕ∞) F U)
    (hneu : ∀ y ∈ U, ‖ContinuousLinearMap.id ℝ E -
        fderiv ℝ (writtenInExtChartAt I I y F) (extChartAt I y y)‖ < 1) :
    IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U :=
  Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty hU hf
    (fun y hy => Coordinates.isInvertible_of_norm_id_sub_lt (hneu y hy))

/-- **`lbl403` complete `(hloc, hinj)` producer — `stepB1_glue`'s exact pair from chart-Neumann
data.**  Given `C^∞`-ness on `U` (inside the `x₀`-chart, mapping into the `F x₀`-chart), the
per-point own-chart Neumann bound (for `hloc`, via the `n = ∞` forward IFT) and the fixed-chart
Neumann bound `≤ ε < 1` on the convex chart image (for `hinj`, via the antilipschitz +
chart-transfer), produce both inputs of `stepB1_glue`/`stepB1_hlocHinj` at once. -/
theorem hlocHinj_of_chartNeumann {F : M → N} {U : Set M} (x₀ : M) {ε : ℝ} (hε : ε < 1)
    (hU : IsOpen U) (hUsub : U ⊆ (extChartAt I x₀).source)
    (hconv : Convex ℝ ((extChartAt I x₀) '' U))
    (hf : ContMDiffOn I I (∞ : WithTop ℕ∞) F U)
    (hFsub : ∀ y ∈ U, F y ∈ (extChartAt I (F x₀)).source)
    (hneu : ∀ y ∈ U, ‖ContinuousLinearMap.id ℝ E -
        fderiv ℝ (writtenInExtChartAt I I y F) (extChartAt I y y)‖ < 1)
    (hneu₀ : ∀ z ∈ (extChartAt I x₀) '' U, ‖ContinuousLinearMap.id ℝ E -
        fderiv ℝ (writtenInExtChartAt I I x₀ F) z‖ ≤ ε) :
    IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U ∧ Set.InjOn F U := by
  refine ⟨hlocOn_of_chartNeumann_infty hU hf hneu, ?_⟩
  refine Coordinates.injOn_of_writtenInExtChart (I := I) (J := I) x₀ hUsub ?_
  exact Coordinates.injOn_of_fderiv_near_id hconv hε
    (chartRep_differentiableAt x₀ hU hUsub hf hFsub) hneu₀

section CmDiag

open DifferentialGeometry.Geometry.Riemannian

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [T2Space M'] [T2Space (TangentBundle I M')] [SigmaCompactSpace M']
  [ConnectedSpace M'] [T3Space M']

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`lbl404` diagonal identity, manifold level.**  The center of mass of an all-equal
configuration is that point: all summand distances vanish, so `centerOfMass.dist_le` at `ε = 0`
pins the center.  (Single-configuration form of `centerAverage.eq_of_all_eq`.) -/
theorem centerOfMass_diag (g : SmoothRiemannianMetric I M') {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M') (join : M' → M' → ℝ → M') (p : M') (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) (q : M') (hall : ∀ i, pts i = q) :
    centerOfMass (I := I) g μ pts join p r h = q := by
  letI : RiemannianBundle (fun x : M' => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M' => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M' := HopfRinow.riemMetricSpace (I := I) (M := M')
  have hnear : ∀ i : ι, dist q (pts i) ≤ (0 : ℝ) := fun i => by rw [hall i, dist_self]
  have hd := centerOfMass.dist_le (I := I) (g := g) (μ := μ) (pts := pts) (join := join)
    (p := p) (r := r) h le_rfl hnear
  rw [mul_zero] at hd
  exact dist_le_zero.mp hd

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`lbl404` diagonal identity, chart level** — the `hdiag` input of `fderiv_pair_sub_id_le` at
one configuration: the chart center of mass of the all-equal configuration `(μ, z, …, z)` is `z`
itself (`centerOfMass_diag` + the normal-chart right inverse). -/
theorem chartCm_diag (g : SmoothRiemannianMetric I M') {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (join : M' → M' → ℝ → M') (p : M') (r : ℝ) (z : E)
    (hz : z ∈ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (h : CenterInput (I := I) g μ
      (fun _ : ι => (NormalCoordinates.normalChartAt (I := I) g p).symm z) join p r) :
    NormalCoordinates.normalChartAt (I := I) g p
      (centerOfMass (I := I) g μ
        (fun _ : ι => (NormalCoordinates.normalChartAt (I := I) g p).symm z) join p r h) = z := by
  rw [centerOfMass_diag (I := I) g μ _ join p r h
    ((NormalCoordinates.normalChartAt (I := I) g p).symm z) (fun _ => rfl)]
  exact NormalCoordinates.normalChartAt_right_inv (I := I) g p hz

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`lbl400` basepoint core — δ-weights pin the center.**  If every weight except slot `i0`
vanishes, the center of mass IS the `i0`-th target: the center energy at `pts i0` is `0` (the
self-distance kills the live summand, the dead weights kill the rest), it is nonnegative
everywhere, and the uniqueness clause pins the minimizer.  This is the cm-side of the book's
basepoint identity `F_{kℓ;r}(O_k) = O_ℓ` (chapter4.tex L1676–78); the remaining `(d)` gap is
ONLY the POU weight concentration `φ_k^α(O_k) = δ_{α0}` (a `StepCAveragePOU` fact). -/
theorem centerOfMass_delta (g : SmoothRiemannianMetric I M') {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M') (join : M' → M' → ℝ → M') (p : M') (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) (i0 : ι)
    (hdead : ∀ i, i ≠ i0 → μ i = 0) :
    centerOfMass (I := I) g μ pts join p r h = pts i0 := by
  letI : RiemannianBundle (fun x : M' => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M' => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M' := HopfRinow.riemMetricSpace (I := I) (M := M')
  have hzero : CenterOfMass.centerEnergy (I := I) g μ pts (pts i0) = 0 := by
    simp only [CenterOfMass.centerEnergy]
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    rcases eq_or_ne i i0 with rfl | hne
    · rw [Manifold.riemannianEDist_self]
      simp
    · rw [hdead i hne, zero_mul]
  have hmin : ∀ z : M', CenterOfMass.centerEnergy (I := I) g μ pts (pts i0)
      ≤ CenterOfMass.centerEnergy (I := I) g μ pts z := by
    intro z
    rw [hzero]
    simp only [CenterOfMass.centerEnergy]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (h.μ_nonneg i) (by positivity)
  exact ((centerOfMass.unique (I := I) (g := g) (μ := μ) (pts := pts) (join := join)
    (p := p) (r := r) h) (pts i0) hmin).symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`lbl404` `hdiag` producer — the diagonal composite is eventually the identity.**  Any total
map `G` that agrees on an open `V ∋ x` with the chart center of mass of the all-equal (diagonal)
configuration is `=ᶠ[𝓝 x]` the identity (`chartCm_diag` pointwise).  This is exactly the `hdiag`
input of `fderiv_pair_sub_id_le`; the wiring session supplies `hagree` for its concrete total
averaged map (e.g. `centerAverageOn` with default). -/
theorem diagEventuallyEqId (g : SmoothRiemannianMetric I M') {ι : Type} [Fintype ι]
    (μfun : E → ι → ℝ) (join : M' → M' → ℝ → M') (p : M') (r : ℝ)
    {x : E} {V : Set E} (hV : IsOpen V) (hxV : x ∈ V)
    (hVtgt : V ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (H : ∀ z ∈ V, CenterInput (I := I) g (μfun z)
      (fun _ : ι => (NormalCoordinates.normalChartAt (I := I) g p).symm z) join p r)
    {G : E → E}
    (hagree : ∀ z, ∀ hz : z ∈ V,
      G z = NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g (μfun z)
          (fun _ : ι => (NormalCoordinates.normalChartAt (I := I) g p).symm z) join p r
          (H z hz))) :
    G =ᶠ[nhds x] fun y => y := by
  filter_upwards [hV.mem_nhds hxV] with z hz
  rw [hagree z hz, chartCm_diag (I := I) g (μfun z) join p r z (hVtgt hz) (H z hz)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The full basepoint chain, welded** (`F(O_k) = O_ℓ`, book L1676–78): bump-separation at the
basepoint (`hfar`, the `lbl383` norm bounds) kills the non-base numerators
(`bumpNumDeltaOfNorm`), own-slot membership makes the base numerator `1` (`hmem0`), so the
normalized weights are the Kronecker `δ_{i0}` (`normWeights_delta`) and the center of mass is the
base target (`centerOfMass_delta`).  Every hypothesis is either concrete bump/transition data or
a pinned `lbl383` norm bound. -/
theorem cmDeltaOfBump {ι : Type} [DecidableEq ι] [Fintype ι] [HasContDiffBump E]
    (g : SmoothRiemannianMetric I M') {χ : E → ℝ} (f : ι → ContDiffBump (0 : E))
    {J : ι → E → E} {i0 : ι} {x₀ : E}
    (pts : ι → M') (join : M' → M' → ℝ → M') (p : M') (r : ℝ)
    (hfar : ∀ j, j ≠ i0 → (f j).rOut ≤ ‖J j x₀‖)
    (hmem0 : ‖J i0 x₀‖ ≤ (f i0).rIn)
    (H : CenterInput (I := I) g
      (fun i => normWeights (bumpNum χ (fun i' => ⇑(f i')) J i0) i x₀) pts join p r) :
    centerOfMass (I := I) g
      (fun i => normWeights (bumpNum χ (fun i' => ⇑(f i')) J i0) i x₀) pts join p r H
      = pts i0 := by
  obtain ⟨hkill, hbase⟩ := bumpNumDeltaOfNorm (χ := χ) f (J := J) hfar
  have hone : f i0 (J i0 x₀) = 1 :=
    (f i0).one_of_mem_closedBall
      (by rw [Metric.mem_closedBall, dist_zero_right]; exact hmem0)
  have hne : bumpNum χ (fun i' => ⇑(f i')) J i0 i0 x₀ ≠ 0 := by
    rw [hbase, hone]; exact one_ne_zero
  obtain ⟨hw1, hw0⟩ := normWeights_delta (num := bumpNum χ (fun i' => ⇑(f i')) J i0)
    (z := x₀) i0 hkill hne
  exact centerOfMass_delta (I := I) g _ pts join p r H i0 (fun j hj => hw0 j hj)

/-- **Orthonormal collapse of the `(0,2)` fiber norm (the tensor-norm bridge, atom 1).**  In a
`g`-orthonormal basis the four-fold coordinate formula `normSq0S_two_eq_coord` collapses to the
plain sum of squared components: `‖A‖²_g = Σᵢⱼ A(bᵢ, bⱼ)²`.  This is the seam between
`metricTensorErrorNorm` (the `PreApproxIsoDataOn.c0_small` quantity) and the per-component chart
bounds produced by `quadPerturbNeumann`/`bilinPerturb`. -/
theorem normSq0S_ortho {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M') (x : M')
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j : Idx, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (A : Tensor0SBundle.Tensor0SSpace 2 I x) :
    Tensor0SBundle.normSq0S (I := I) g x 2 A
      = ∑ i : Idx, ∑ j : Idx,
          (A (fun a : Fin 2 => if a = 0 then basis i else basis j)) ^ 2 := by
  classical
  have hδ : Tensor0SBundle.MetricInverseInBasis (I := I) g x basis
      (fun i j => if i = j then (1 : ℝ) else 0) := by
    intro i j
    constructor
    · rw [Finset.sum_eq_single i]
      · simp [hON i j]
      · intro k _ hk
        simp [Ne.symm hk]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · rw [Finset.sum_eq_single j]
      · simp [hON i j]
      · intro k _ hk
        simp [hON i k, hk]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
  rw [Tensor0SBundle.normSq0S_two_eq_coord (I := I) g x basis _ hδ]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- **Tensor-norm bridge, atom 2: per-component bounds give the fiber-norm bound.**  If every
orthonormal component of a `(0,2)` tensor is `≤ c`, then `√(normSq0S A) ≤ card·c` — combined with
`normSq0S_ortho` and the `quadPerturbNeumann` per-component chart bound this converts the chart
`C⁰` estimate into the `metricTensorErrorNorm ≤ ε`-shaped `PreApproxIsoDataOn.c0_small` slot. -/
theorem sqrtNormSq_le_of_comp {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M') (x : M')
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j : Idx, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (A : Tensor0SBundle.Tensor0SSpace 2 I x) {c : ℝ} (hc : 0 ≤ c)
    (hcomp : ∀ i j : Idx,
      |A (fun a : Fin 2 => if a = 0 then basis i else basis j)| ≤ c) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 A) ≤ (Fintype.card Idx : ℝ) * c := by
  rw [normSq0S_ortho (I := I) g x basis hON A]
  have hsum : ∑ i : Idx, ∑ j : Idx,
      (A (fun a : Fin 2 => if a = 0 then basis i else basis j)) ^ 2
        ≤ ((Fintype.card Idx : ℝ) * c) ^ 2 := by
    calc ∑ i : Idx, ∑ j : Idx,
        (A (fun a : Fin 2 => if a = 0 then basis i else basis j)) ^ 2
        ≤ ∑ _i : Idx, ∑ _j : Idx, c ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have h := hcomp i j
          have habs : (A (fun a : Fin 2 => if a = 0 then basis i else basis j)) ^ 2
              = |A (fun a : Fin 2 => if a = 0 then basis i else basis j)| ^ 2 := (sq_abs _).symm
          rw [habs]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (Fintype.card Idx : ℝ) ^ 2 * c ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ]
          ring
      _ = ((Fintype.card Idx : ℝ) * c) ^ 2 := by ring
  calc Real.sqrt (∑ i : Idx, ∑ j : Idx,
      (A (fun a : Fin 2 => if a = 0 then basis i else basis j)) ^ 2)
      ≤ Real.sqrt (((Fintype.card Idx : ℝ) * c) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = (Fintype.card Idx : ℝ) * c := by
        rw [Real.sqrt_sq (by positivity)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Center-point derivative identification (seam β, atom 1).**  In normal coordinates centered
at `y` and `F y`, the manifold derivative of `F` at `y` IS the flat `fderiv` of the chart
representative `G := chart_{F y} ∘ F ∘ chart_y⁻¹` at `0` — both chart derivatives are the identity
at their centers (`mfderiv_normalChartAt_self` / `_symm_zero`), so no distortion enters.  This is
why the book's `lbl402` estimates can be read pointwise in normal coordinates. -/
theorem mfderivNormalCenter
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] [T2Space (TangentBundle I N')] [SigmaCompactSpace N']
    [ConnectedSpace N'] [T3Space N']
    (gk : SmoothRiemannianMetric I M') (gn : SmoothRiemannianMetric I N')
    (F : M' → N') (y : M')
    (hG : DifferentiableAt ℝ
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E))
    (hev : F =ᶠ[nhds y] fun q =>
      (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm
        (NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm
            (NormalCoordinates.normalChartAt (I := I) gk y q))))) :
    mfderiv I I F y = fderiv ℝ
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E) := by
  classical
  -- center values of the two charts
  have hcy : NormalCoordinates.normalChartAt (I := I) gk y y = 0 := by
    have h0 := (NormalCoordinates.expMapDiffeo (I := I) gk y).toPartialEquiv.left_inv
      (NormalCoordinates.zero_mem_expMapDiffeo_source (I := I) gk y)
    rw [NormalCoordinates.expMapDiffeo_zero] at h0
    exact h0
  have hdFy : NormalCoordinates.normalChartAt (I := I) gn (F y) (F y) = 0 := by
    have h0 := (NormalCoordinates.expMapDiffeo (I := I) gn (F y)).toPartialEquiv.left_inv
      (NormalCoordinates.zero_mem_expMapDiffeo_source (I := I) gn (F y))
    rw [NormalCoordinates.expMapDiffeo_zero] at h0
    exact h0
  have hcsymm0 : (NormalCoordinates.normalChartAt (I := I) gk y).symm (0 : E) = y := by
    show NormalCoordinates.expMapDiffeo (I := I) gk y (0 : E) = y
    exact NormalCoordinates.expMapDiffeo_zero (I := I) gk y
  -- differentiability of the three factors
  have hysrc : y ∈ (NormalCoordinates.normalChartAt (I := I) gk y).source :=
    NormalCoordinates.p_mem_expMapDiffeo_target (I := I) gk y
  have hcm : MDifferentiableAt I 𝓘(ℝ, E)
      (NormalCoordinates.normalChartAt (I := I) gk y) y :=
    (NormalCoordinates.normalChartAt (I := I) gk y).mdifferentiableAt one_ne_zero hysrc
  have hGm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
      (NormalCoordinates.normalChartAt (I := I) gk y y) := by
    rw [hcy]
    exact hG.mdifferentiableAt
  have hGc_m : MDifferentiableAt I 𝓘(ℝ, E)
      (fun q => (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
          (NormalCoordinates.normalChartAt (I := I) gk y q)) y :=
    hGm.comp y hcm
  have h0tgt : (0 : E) ∈ (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm.source := by
    show (0 : E) ∈ (NormalCoordinates.expMapDiffeo (I := I) gn (F y)).source
    exact NormalCoordinates.zero_mem_expMapDiffeo_source (I := I) gn (F y)
  have hdsymm_m : MDifferentiableAt 𝓘(ℝ, E) I
      ((NormalCoordinates.normalChartAt (I := I) gn (F y)).symm)
      ((fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
          (NormalCoordinates.normalChartAt (I := I) gk y y)) := by
    have hval : (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
          (NormalCoordinates.normalChartAt (I := I) gk y y) = 0 := by
      simp only [hcy, hcsymm0, hdFy]
    rw [hval]
    exact (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm.mdifferentiableAt
      one_ne_zero h0tgt
  -- assemble
  rw [Filter.EventuallyEq.mfderiv_eq hev]
  have hsplit := mfderiv_comp (I := I) (I' := 𝓘(ℝ, E)) (I'' := I) y hdsymm_m hGc_m
  rw [show (fun q => (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm
        (NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm
            (NormalCoordinates.normalChartAt (I := I) gk y q)))))
      = ((NormalCoordinates.normalChartAt (I := I) gn (F y)).symm : E → N')
        ∘ (fun q => (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
            (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
              (NormalCoordinates.normalChartAt (I := I) gk y q)) from rfl, hsplit]
  have hinner := mfderiv_comp (I := I) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E)) y hGm hcm
  rw [show (fun q => (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
          (NormalCoordinates.normalChartAt (I := I) gk y q))
      = ((fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
        ∘ (NormalCoordinates.normalChartAt (I := I) gk y : M' → E)) from rfl] at hsplit ⊢
  rw [hinner] at hsplit ⊢
  have hd0 : (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
      (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
        (NormalCoordinates.normalChartAt (I := I) gk y y) = 0 := by
    simp only [hcy, hcsymm0, hdFy]
  rw [hd0, NormalCoordinates.mfderiv_normalChartAt_symm_zero (I := I) gn (F y),
    NormalCoordinates.mfderiv_normalChartAt_self (I := I) gk y]
  have hmodel : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
      (NormalCoordinates.normalChartAt (I := I) gk y y)
      = fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E) := by
    rw [hcy]
    exact mfderiv_eq_fderiv
  rw [hmodel]
  ext v
  rfl

/-- **Pointwise pullback-error component bound (seam β, the c0 assembly at one point).**  The
`(0,2)` error tensor `Φ^*h − g` evaluated on a tangent pair `(v, w)` at `y` is controlled by the
chart-Neumann bound `ε` on `dG` and the pointwise metric-closeness `η`:
`|(Φ^*h − g)(v,w)| ≤ (‖h_{Fy}‖·ε·(2+ε) + η)·‖v‖‖w‖`.  Chains `pullback_apply` →
`mfderivNormalCenter` (no distortion at normal-chart centers) → `bilinPerturb` + triangle.  The
metric closeness enters POINTWISE (`hB`, scalar level) — the operator-norm mixed difference of the
two fiber forms is type-theoretically awkward across the `TangentSpace` aliases.  Feeding
`(v, w) := ` a `gk`-orthonormal pair (`exists_gOrthonormalBasis`) and `sqrtNormSq_le_of_comp`/`normSq0S_ortho`
turns this into the `metricTensorErrorNorm` bound of `PreApproxIsoDataOn.c0_small`. -/
theorem pullbackErrComp
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] [T2Space (TangentBundle I N')] [SigmaCompactSpace N']
    [ConnectedSpace N'] [T3Space N']
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M'] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N']
    (gk : SmoothRiemannianMetric I M') (gn : SmoothRiemannianMetric I N')
    {F : M' → N'} {y : M'}
    (hpb : PullbackMetricTensorData (I := I) F gn)
    (hG : DifferentiableAt ℝ
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E))
    (hev : F =ᶠ[nhds y] fun q =>
      (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm
        (NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm
            (NormalCoordinates.normalChartAt (I := I) gk y q)))))
    {ε η : ℝ}
    (hA : ‖fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E)
      - ContinuousLinearMap.id ℝ E‖ ≤ ε)
    (hB : ∀ v' w' : E, |gn.inner (F y) v' w' - gk.inner y v' w'| ≤ η * (‖v'‖ * ‖w'‖))
    (v w : TangentSpace I y) :
    |(hpb.pullback y - Tensor0SBundle.metricTensorField (I := I) gk y)
        (fun a : Fin 2 => if a = 0 then v else w)|
      ≤ ((‖gn.inner (F y)‖ * ε * (2 + ε)) + η) * (‖v‖ * ‖w‖) := by
  have hsub : (hpb.pullback y - Tensor0SBundle.metricTensorField (I := I) gk y)
      (fun a : Fin 2 => if a = 0 then v else w)
      = hpb.pullback y (fun a : Fin 2 => if a = 0 then v else w)
        - Tensor0SBundle.metricTensorField (I := I) gk y
            (fun a : Fin 2 => if a = 0 then v else w) := rfl
  have hpba := hpb.pullback_apply y (fun a : Fin 2 => if a = 0 then v else w)
  norm_num at hpba
  set A := fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
    (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E) with hAdef
  have hmv : mfderiv I I F y v = A v :=
    DFunLike.congr_fun (mfderivNormalCenter (I := I) gk gn F y hG hev) v
  have hmw : mfderiv I I F y w = A w :=
    DFunLike.congr_fun (mfderivNormalCenter (I := I) gk gn F y hG hev) w
  rw [hsub, hpba, hmv, hmw, Tensor0SBundle.metricTensorField_apply]
  norm_num
  -- goal: |gn.inner (F y) (A v) (A w) - gk.inner y v w| ≤ (‖gn.inner (F y)‖ ε (2+ε) + η) ‖v‖‖w‖
  have h1 := bilinPerturb (B := gn.inner (F y)) (A := A) v w
  have h2 := hB v w
  have hAle : ‖A‖ ≤ 1 + ε := by
    calc ‖A‖ = ‖ContinuousLinearMap.id ℝ E + (A - ContinuousLinearMap.id ℝ E)‖ := by
          congr 1; abel
      _ ≤ ‖ContinuousLinearMap.id ℝ E‖ + ‖A - ContinuousLinearMap.id ℝ E‖ := norm_add_le _ _
      _ ≤ 1 + ε := add_le_add ContinuousLinearMap.norm_id_le hA
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hA
  have hcoef : ‖gn.inner (F y)‖ * ‖A - ContinuousLinearMap.id ℝ E‖ * (1 + ‖A‖)
      ≤ ‖gn.inner (F y)‖ * ε * (2 + ε) := by
    have h2' : (1 : ℝ) + ‖A‖ ≤ 2 + ε := by linarith [hAle]
    gcongr
  calc |gn.inner (F y) (A v) (A w) - gk.inner y v w|
      = |(gn.inner (F y) (A v) (A w) - gn.inner (F y) v w)
          + (gn.inner (F y) v w - gk.inner y v w)| := by ring_nf
    _ ≤ |gn.inner (F y) (A v) (A w) - gn.inner (F y) v w|
        + |gn.inner (F y) v w - gk.inner y v w| := abs_add_le _ _
    _ ≤ ‖gn.inner (F y)‖ * ‖A - ContinuousLinearMap.id ℝ E‖ * (1 + ‖A‖) * (‖v‖ * ‖w‖)
        + η * (‖v‖ * ‖w‖) := add_le_add h1 h2
    _ ≤ ‖gn.inner (F y)‖ * ε * (2 + ε) * (‖v‖ * ‖w‖) + η * (‖v‖ * ‖w‖) := by
        gcongr
    _ = ((‖gn.inner (F y)‖ * ε * (2 + ε)) + η) * (‖v‖ * ‖w‖) := by ring

/-- **`hev` producer — chart-source conditions give the round-trip agreement.**  If, near `y`,
every point stays in the `y`-chart source and its `F`-image stays in the `F y`-chart source, then
`F` agrees near `y` with its double chart round-trip — the `hev` input of
`mfderivNormalCenter`/`pullbackErrComp`, produced from openness + continuity at assembly time. -/
theorem chartRoundTrip_ev
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] [T2Space (TangentBundle I N')] [SigmaCompactSpace N']
    [ConnectedSpace N'] [T3Space N']
    (gk : SmoothRiemannianMetric I M') (gn : SmoothRiemannianMetric I N')
    {F : M' → N'} {y : M'}
    (hsrc : ∀ᶠ q in nhds y, q ∈ (NormalCoordinates.normalChartAt (I := I) gk y).source)
    (hFsrc : ∀ᶠ q in nhds y,
      F q ∈ (NormalCoordinates.normalChartAt (I := I) gn (F y)).source) :
    F =ᶠ[nhds y] fun q =>
      (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm
        (NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm
            (NormalCoordinates.normalChartAt (I := I) gk y q)))) := by
  filter_upwards [hsrc, hFsrc] with q hq hFq
  rw [show ((NormalCoordinates.normalChartAt (I := I) gk y).symm : E → M')
        ((NormalCoordinates.normalChartAt (I := I) gk y) q) = q from
      (NormalCoordinates.normalChartAt (I := I) gk y).toPartialEquiv.left_inv hq,
    show ((NormalCoordinates.normalChartAt (I := I) gn (F y)).symm : E → N')
        ((NormalCoordinates.normalChartAt (I := I) gn (F y)) (F q)) = F q from
      (NormalCoordinates.normalChartAt (I := I) gn (F y)).toPartialEquiv.left_inv hFq]

/-- **`exists_gOrthonormalBasis`, coercivity-bounded version**: below-bounded metrics give `g`-orthonormal bases
whose vectors have Euclidean norm `≤ (√cLow)⁻¹` (from `1 = g(bᵢ,bᵢ) ≥ cLow·‖bᵢ‖²`).  The
coercivity constant is the book's `λ`-equivalence input (`lbl395` family). -/
theorem exists_gON_bd (g : SmoothRiemannianMetric I M') (x : M')
    {cLow : ℝ} (hc : 0 < cLow)
    (hcoer : ∀ v : TangentSpace I x, cLow * ‖v‖ ^ 2 ≤ g.inner x v v) :
    ∃ basis : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x),
      (∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ i, ‖(basis i : TangentSpace I x)‖ ≤ (Real.sqrt cLow)⁻¹ := by
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
  refine ⟨basis, hON, fun i => ?_⟩
  have h1 : cLow * ‖(basis i : TangentSpace I x)‖ ^ 2 ≤ 1 := by
    have := hcoer (basis i)
    rw [hON i i, if_pos rfl] at this
    linarith
  have hs : Real.sqrt cLow > 0 := Real.sqrt_pos.mpr hc
  have hsq : Real.sqrt cLow * Real.sqrt cLow = cLow := Real.mul_self_sqrt (le_of_lt hc)
  rw [inv_eq_one_div, le_div_iff₀ hs]
  nlinarith [h1, hsq, norm_nonneg (basis i : TangentSpace I x),
    sq_nonneg (‖(basis i : TangentSpace I x)‖ * Real.sqrt cLow - 1)]

/-- **The `c0_small` top single-point theorem (seam β sealed).**  Under the normal-chart Neumann
bound, the pointwise metric closeness, and the coercivity of the source metric (the book's
`λ`-equivalence input), the full fiber-norm metric error of the pullback is controlled:
`metricTensorErrorNorm (Φ^*h) g y ≤ dim·(coef)·cLow⁻¹` — weld `exists_gON_bd` +
`pullbackErrComp` + `sqrtNormSq_le_of_comp`.  This is `PreApproxIsoDataOn.c0_small` at one point;
the region/two-index quantified version is the (c)-assembly wrapper. -/
theorem pullbackErrNorm
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] [T2Space (TangentBundle I N')] [SigmaCompactSpace N']
    [ConnectedSpace N'] [T3Space N']
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M'] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N']
    (gk : SmoothRiemannianMetric I M') (gn : SmoothRiemannianMetric I N')
    {F : M' → N'} {y : M'}
    (hpb : PullbackMetricTensorData (I := I) F gn)
    (hG : DifferentiableAt ℝ
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E))
    (hev : F =ᶠ[nhds y] fun q =>
      (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm
        (NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm
            (NormalCoordinates.normalChartAt (I := I) gk y q)))))
    {ε η cLow : ℝ} (hη : 0 ≤ η) (hc : 0 < cLow)
    (hcoer : ∀ v : TangentSpace I y, cLow * ‖v‖ ^ 2 ≤ gk.inner y v v)
    (hA : ‖fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E)
      - ContinuousLinearMap.id ℝ E‖ ≤ ε)
    (hB : ∀ v' w' : E, |gn.inner (F y) v' w' - gk.inner y v' w'| ≤ η * (‖v'‖ * ‖w'‖)) :
    metricTensorErrorNorm (I := I) hpb.pullback gk y
      ≤ (Module.finrank ℝ (TangentSpace I y) : ℝ)
        * (((‖gn.inner (F y)‖ * ε * (2 + ε)) + η)
            * ((Real.sqrt cLow)⁻¹ * (Real.sqrt cLow)⁻¹)) := by
  obtain ⟨basis, hON, hbd⟩ := exists_gON_bd (I := I) gk y hc hcoer
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hA
  have hs0 : (0 : ℝ) ≤ (Real.sqrt cLow)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hc0 : 0 ≤ (((‖gn.inner (F y)‖ * ε * (2 + ε)) + η)
      * ((Real.sqrt cLow)⁻¹ * (Real.sqrt cLow)⁻¹)) := by positivity
  have hmain : Real.sqrt (Tensor0SBundle.normSq0S (I := I) gk y 2
      (hpb.pullback y - Tensor0SBundle.metricTensorField (I := I) gk y))
      ≤ (Fintype.card (Fin (Module.finrank ℝ (TangentSpace I y))) : ℝ)
        * (((‖gn.inner (F y)‖ * ε * (2 + ε)) + η)
            * ((Real.sqrt cLow)⁻¹ * (Real.sqrt cLow)⁻¹)) := by
    refine (sqrtNormSq_le_of_comp (I := I) gk y basis hON _ hc0 ?_)
    intro i j
    have h := pullbackErrComp (I := I) gk gn hpb hG hev hA hB (basis i) (basis j)
    refine h.trans ?_
    have hbb : ‖(basis i : TangentSpace I y)‖ * ‖(basis j : TangentSpace I y)‖
        ≤ (Real.sqrt cLow)⁻¹ * (Real.sqrt cLow)⁻¹ :=
      mul_le_mul (hbd i) (hbd j) (norm_nonneg _) hs0
    have hcoefnn : 0 ≤ (‖gn.inner (F y)‖ * ε * (2 + ε)) + η := by positivity
    exact mul_le_mul_of_nonneg_left hbb hcoefnn
  simpa using hmain

/-- **General-order carrier assembly (the `PreApproxIsoDataOn` endpoint at any `p`).**  Assembles
the full pre-approximate isometry carrier from the pullback data, a smoothness-on-`K` hypothesis,
the `ε` bounds, the uniform `c0` bound (`pullbackErrNorm` over `K`), and the uniform higher-order
covariant-derivative bound `hcov` (produced by the `PullbackField.lean` pullback-invariance machinery
`covNormWith_pd_zone` + `iterCov_metric_zero`).  `preApproxIsoDataOn_zero` is the `p = 0` case where
`hcov` is vacuous. -/
def preApproxIsoDataOn_of_bounds
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    (K : Set M') (eps : ℝ) (p : ℕ) (F : M' → N')
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hpb : PullbackMetricTensorData (I := I) F h)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hsmooth : ContMDiffOn I I (∞ : WithTop ℕ∞) F K)
    (hc0 : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpb.pullback g x ≤ eps)
    (hcov : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) a hpb.pullback g g x ≤ eps) :
    PreApproxIsoDataOn (I := I) K eps p F g h where
  eps_pos := heps
  eps_lt_one := heps1
  smoothOn := hsmooth
  pullback := hpb.pullback
  pullback_apply := fun x _ v => hpb.pullback_apply x v
  c0_small := hc0
  cov_deriv_small := hcov

/-- **`p = 0` carrier assembly (the C⁰ `PreApproxIsoDataOn` endpoint).**  The `p = 0` special case
of `preApproxIsoDataOn_of_bounds`: with `p = 0` the `cov_deriv_small` obligation is vacuous
(`1 ≤ a → a ≤ 0` is impossible), so only the pullback data, smoothness on `K`, the `ε` bounds, and
the uniform `c0` bound are needed.  Welds the round-16–26 chart-perturbation chain into the Step B
carrier at order `0`. -/
def preApproxIsoDataOn_zero
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    (K : Set M') (eps : ℝ) (F : M' → N')
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hpb : PullbackMetricTensorData (I := I) F h)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hsmooth : ContMDiffOn I I (∞ : WithTop ℕ∞) F K)
    (hc0 : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpb.pullback g x ≤ eps) :
    PreApproxIsoDataOn (I := I) K eps 0 F g h :=
  preApproxIsoDataOn_of_bounds K eps 0 F g h hpb heps heps1 hsmooth hc0
    (by intro a ha ha0 x hx; omega)

/-- **Two-sided `p = 0` carrier (`lbl397` `BookApproxIsoPartialData` at order 0).**  Bundles a
forward and a reverse `preApproxIsoDataOn_zero` for a partial diffeomorphism `Φ`, on `K` and its
image `Φ '' K` respectively, into the canonical two-sided partial approximate-isometry carrier.
This is the C⁰ endpoint the Step B / `lbl397` glue consumes; the `p ≥ 1` version awaits the
higher covariant-derivative estimates. -/
def bookApproxIsoData_of_bounds
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] [SigmaCompactSpace N'] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N']
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
    (K : Set M') (eps : ℝ) (p : ℕ)
    (Φ : PartialDiffeomorph I I M' N' (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hsub : K ⊆ Φ.source)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hpbF : PullbackMetricTensorData (I := I) (Φ : M' → N') h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ : M' → N') K)
    (hc0F : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpbF.pullback g x ≤ eps)
    (hcovF : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) a hpbF.pullback g g x ≤ eps)
    (hpbR : PullbackMetricTensorData (I := I) (Φ.symm : N' → M') g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ.symm : N' → M') ((Φ : M' → N') '' K))
    (hc0R : ∀ y ∈ (Φ : M' → N') '' K,
      metricTensorErrorNorm (I := I) hpbR.pullback h y ≤ eps)
    (hcovR : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ y ∈ (Φ : M' → N') '' K,
      tensor02CovDerivNormWith (I := I) a hpbR.pullback h h y ≤ eps) :
    BookApproxIsoPartialData (I := I) K eps p Φ g h where
  source_sub := hsub
  forward := preApproxIsoDataOn_of_bounds K eps p (Φ : M' → N') g h hpbF heps heps1 hsmoothF hc0F hcovF
  reverse := preApproxIsoDataOn_of_bounds ((Φ : M' → N') '' K) eps p (Φ.symm : N' → M') h g
    hpbR heps heps1 hsmoothR hc0R hcovR

/-- **Two-sided `p = 0` carrier (`lbl397` `BookApproxIsoPartialData` at order 0).**  The `p = 0`
special case of `bookApproxIsoData_of_bounds`: bundles a forward and a reverse
`preApproxIsoDataOn_zero` for a partial diffeomorphism `Φ` (on `K` and its image `Φ '' K`).  This
is the C⁰ endpoint the Step B / `lbl397` glue consumes. -/
def bookApproxIsoData_zero
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] [SigmaCompactSpace N'] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N']
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
    (K : Set M') (eps : ℝ)
    (Φ : PartialDiffeomorph I I M' N' (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hsub : K ⊆ Φ.source)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hpbF : PullbackMetricTensorData (I := I) (Φ : M' → N') h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ : M' → N') K)
    (hc0F : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpbF.pullback g x ≤ eps)
    (hpbR : PullbackMetricTensorData (I := I) (Φ.symm : N' → M') g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ.symm : N' → M') ((Φ : M' → N') '' K))
    (hc0R : ∀ y ∈ (Φ : M' → N') '' K,
      metricTensorErrorNorm (I := I) hpbR.pullback h y ≤ eps) :
    BookApproxIsoPartialData (I := I) K eps 0 Φ g h :=
  bookApproxIsoData_of_bounds K eps 0 Φ g h hsub heps heps1 hpbF hsmoothF hc0F
    (by intro a ha ha0 x hx; omega) hpbR hsmoothR hc0R (by intro a ha ha0 y hy; omega)

end CmDiag

section StepB1Zero

open Set Bundle Manifold
open scoped Topology Manifold ContDiff

variable {M'' : Type u} [TopologicalSpace M''] [ChartedSpace H M''] [IsManifold I ∞ M'']
  [T2Space M''] [T2Space (TangentBundle I M'')] [SigmaCompactSpace M'']
  [ConnectedSpace M''] [T3Space M''] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M'']
  [MetricSpace M''] [Nonempty M'']
variable {N'' : Type u} [TopologicalSpace N''] [ChartedSpace H N''] [IsManifold I ∞ N'']
  [T2Space N''] [T2Space (TangentBundle I N'')] [SigmaCompactSpace N'']
  [ConnectedSpace N''] [T3Space N''] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N'']

/-- **MSM135 `lbl397` (B1) at order `p = 0` — the C⁰ approximate-isometry endpoint.**  From the
chart-level hypotheses that Step B actually delivers (a local diffeomorphism `F` on the open set
`U`, injective there, fixing the basepoint) together with the forward and reverse `C⁰` pullback
error bounds on the closed ball and its image, there is a partial diffeomorphism realizing `F` as
an `(ε, 0)`-approximate isometry (`BookApproxIsoPartialData`).  This welds the round-16–28
chart-perturbation / carrier chain (`preApproxIsoDataOn_zero`) onto the fully-proved `stepB1_glue`,
closing the B1 conclusion at order 0.  The `p ≥ 1` version awaits the higher covariant-derivative
estimates (`cov_deriv_small`). -/
theorem stepB1_of_bounds
    (g : SmoothRiemannianMetric I M'') (h : SmoothRiemannianMetric I N'')
    (Ok : M'') (Oℓ : N'') (r ε : ℝ) (p : ℕ) (U : Set M'')
    (hU : IsOpen U) (hOkU : Ok ∈ U) (hKU : Metric.closedBall Ok r ⊆ U)
    (F : M'' → N'')
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hinj : Set.InjOn F U) (hbase : F Ok = Oℓ)
    (heps : 0 < ε) (heps1 : ε < 1)
    (hpbF : PullbackMetricTensorData (I := I) F h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) F (Metric.closedBall Ok r))
    (hc0F : ∀ x ∈ Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbF.pullback g x ≤ ε)
    (hcovF : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ Metric.closedBall Ok r,
      tensor02CovDerivNormWith (I := I) a hpbF.pullback g g x ≤ ε)
    (hpbR : PullbackMetricTensorData (I := I) (Function.invFunOn F U) g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Function.invFunOn F U)
      (F '' Metric.closedBall Ok r))
    (hc0R : ∀ y ∈ F '' Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbR.pullback h y ≤ ε)
    (hcovR : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ y ∈ F '' Metric.closedBall Ok r,
      tensor02CovDerivNormWith (I := I) a hpbR.pullback h h y ≤ ε) :
    ∃ Phi : PartialDiffeomorph I I M'' N'' (∞ : WithTop ℕ∞),
      Metric.closedBall Ok r ⊆ Phi.source ∧
      Phi Ok = Oℓ ∧
      Nonempty (BookApproxIsoPartialData (I := I) (Metric.closedBall Ok r) ε p Phi g h) :=
  stepB1_glue g h Ok Oℓ r ε p U hU hOkU hKU F hloc hinj hbase
    (preApproxIsoDataOn_of_bounds (Metric.closedBall Ok r) ε p F g h hpbF heps heps1 hsmoothF
      hc0F hcovF)
    (preApproxIsoDataOn_of_bounds (F '' Metric.closedBall Ok r) ε p (Function.invFunOn F U) h g
      hpbR heps heps1 hsmoothR hc0R hcovR)

/-- **MSM135 `lbl397` (B1) at order `p = 0` — the C⁰ approximate-isometry endpoint.**  The `p = 0`
special case of `stepB1_of_bounds`: from a local diffeomorphism `F` on the open set `U`, injective
there, fixing the basepoint, together with the forward and reverse `C⁰` pullback error bounds on the
closed ball and its image, there is a partial diffeomorphism realizing `F` as an `(ε, 0)`-approximate
isometry.  Welds the round-16–28 chart-perturbation / carrier chain onto the fully-proved
`stepB1_glue`. -/
theorem stepB1_zero
    (g : SmoothRiemannianMetric I M'') (h : SmoothRiemannianMetric I N'')
    (Ok : M'') (Oℓ : N'') (r ε : ℝ) (U : Set M'')
    (hU : IsOpen U) (hOkU : Ok ∈ U) (hKU : Metric.closedBall Ok r ⊆ U)
    (F : M'' → N'')
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hinj : Set.InjOn F U) (hbase : F Ok = Oℓ)
    (heps : 0 < ε) (heps1 : ε < 1)
    (hpbF : PullbackMetricTensorData (I := I) F h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) F (Metric.closedBall Ok r))
    (hc0F : ∀ x ∈ Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbF.pullback g x ≤ ε)
    (hpbR : PullbackMetricTensorData (I := I) (Function.invFunOn F U) g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Function.invFunOn F U)
      (F '' Metric.closedBall Ok r))
    (hc0R : ∀ y ∈ F '' Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbR.pullback h y ≤ ε) :
    ∃ Phi : PartialDiffeomorph I I M'' N'' (∞ : WithTop ℕ∞),
      Metric.closedBall Ok r ⊆ Phi.source ∧
      Phi Ok = Oℓ ∧
      Nonempty (BookApproxIsoPartialData (I := I) (Metric.closedBall Ok r) ε 0 Phi g h) :=
  stepB1_of_bounds g h Ok Oℓ r ε 0 U hU hOkU hKU F hloc hinj hbase heps heps1
    hpbF hsmoothF hc0F (by intro a ha ha0 x hx; omega)
    hpbR hsmoothR hc0R (by intro a ha ha0 y hy; omega)

end StepB1Zero

section PathBridge

open Set Bundle Manifold
open scoped Topology Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

-- Clean `StepBInputs`-matching context: the file-level `E` carries BOTH a standalone
-- `[NormedSpace ℝ E]` and `[InnerProductSpace ℝ E]` (two `Module` paths — the D3
-- instance-diamond), while `NormalCoordMetricEquivOn`'s def-site derives `NormedSpace` from
-- the inner product only.  This section therefore uses its own variables.
variable {F : Type uE} [NormedAddCommGroup F]
variable [InnerProductSpace Real F] [FiniteDimensional Real F]
variable [NeZero (Module.finrank Real F)] [CompleteSpace F]
variable {G : Type uH} [TopologicalSpace G]
variable {J' : ModelWithCorners Real F G} [J'.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The reverse chart–metric bridge (`lbl395` upper side)** — the Riemannian distance to a
normal-coordinate image is at most `√2` times the Euclidean norm of the coordinate, along the
straight segment: `riemannianEDist x (γ 1) ≤ √2‖v‖` where `γ t := exp_x (t • v)` and the
pulled-back metric satisfies the `NormalCoordMetricEquivOn` upper bound `g ≤ 2δ` on the segment.
Contrapositive: a Riemannian distance lower bound forces a norm lower bound — EXACTLY the
`lbl383`-separation → `bumpNumDeltaOfNorm.hfar` discharge.  The two threaded atoms are the
segment's `C¹`-ness `hγ` and the velocity–enorm identification `hderiv`
(`‖γ'(t)‖ₑ = √(normalCoordMetric x (t•v) v v)` — the chain rule + the enorm convention, a pinned
mechanical fact of the exponential layer). -/
theorem edistLeOfEquivOn (Y : PointedRiemannianManifold.{u, uE, uH} (I := J')) (x : Y.M)
    {U : Set F} {v : F}
    (heq : NormalCoordMetricEquivOn (I := J') Y x U)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → t • v ∈ U)
    (γ : ℝ → Y.M)
    (hγ :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      ContMDiffOn 𝓘(ℝ, ℝ) J' 1 γ (Set.Icc (0 : ℝ) 1))
    (hend : γ 0 = x)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      letI : IsManifold J' ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
      letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
        ⟨Y.metric.toRiemannianMetric⟩
      ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ
        = ENNReal.ofReal (Real.sqrt (normalCoordMetric (I := J') Y x (t • v) v v))) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace G Y.M := Y.charted
    letI : IsManifold J' ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
      ⟨Y.metric.toRiemannianMetric⟩
    Manifold.riemannianEDist J' x (γ 1)
      ≤ ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace G Y.M := Y.charted
  letI : IsManifold J' ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
  letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have h1 : Manifold.riemannianEDist J' x (γ 1) ≤ Manifold.pathELength J' γ 0 1 :=
    Manifold.riemannianEDist_le_pathELength hγ hend rfl zero_le_one
  refine h1.trans ?_
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ ≤ ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := by
    intro t ht
    rw [hderiv t ht]
    refine ENNReal.ofReal_le_ofReal ?_
    have hub := (heq (t • v) (hseg t ht) v).2
    calc Real.sqrt (normalCoordMetric (I := J') Y x (t • v) v v)
        ≤ Real.sqrt (2 * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hub
      _ = Real.sqrt 2 * ‖v‖ := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq (norm_nonneg v)]
  calc ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt 2 * ‖v‖) :=
        MeasureTheory.setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (Real.sqrt 2 * ‖v‖) * MeasureTheory.volume (Set.Icc (0 : ℝ) 1) :=
        MeasureTheory.setLIntegral_const _ _
    _ = ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := by
        rw [Real.volume_Icc]
        norm_num

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Separation → norm lower bound** (the `(a)`-discharge conversion): a Riemannian-distance
lower bound at the segment endpoint (from `netList_separated` through `ProperMetricOn.realizes`)
combines with the reverse bridge `edistLeOfEquivOn` to force `λ/√2 ≤ ‖v‖` — the
`bumpNumDeltaOfNorm.hfar` shape once `rOut ≤ λ/√2` is arranged by the ball choice. -/
theorem normLowerOfSep (Y : PointedRiemannianManifold.{u, uE, uH} (I := J')) (x : Y.M)
    {U : Set F} {v : F}
    (heq : NormalCoordMetricEquivOn (I := J') Y x U)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → t • v ∈ U)
    (γ : ℝ → Y.M)
    (hγ :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      ContMDiffOn 𝓘(ℝ, ℝ) J' 1 γ (Set.Icc (0 : ℝ) 1))
    (hend : γ 0 = x)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      letI : IsManifold J' ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
      letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
        ⟨Y.metric.toRiemannianMetric⟩
      ‖mfderiv 𝓘(ℝ, ℝ) J' γ t 1‖ₑ
        = ENNReal.ofReal (Real.sqrt (normalCoordMetric (I := J') Y x (t • v) v v)))
    {lam : ℝ}
    (hlam :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace G Y.M := Y.charted
      letI : IsManifold J' ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
      letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
        ⟨Y.metric.toRiemannianMetric⟩
      ENNReal.ofReal lam ≤ Manifold.riemannianEDist J' x (γ 1)) :
    lam / Real.sqrt 2 ≤ ‖v‖ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace G Y.M := Y.charted
  letI : IsManifold J' ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
  letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hup := edistLeOfEquivOn (J' := J') Y x heq hseg γ hγ hend hderiv
  have hchain : ENNReal.ofReal lam ≤ ENNReal.ofReal (Real.sqrt 2 * ‖v‖) := hlam.trans hup
  have hle : lam ≤ Real.sqrt 2 * ‖v‖ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)]
  linarith [hle]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Radial-exponential specialization of `normLowerOfSep`.**  If the coordinate segment
stays in a set contained in the named exponential ball, a Riemannian separation lower bound
forces the required Euclidean coordinate separation.  The radial curve's `C¹` regularity and
velocity norm are supplied by the exponential layer, rather than threaded as caller inputs. -/
theorem normLowerOfSepExp
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := J')) (x : Y.M)
    {U : Set F} {v : F}
    (heq : NormalCoordMetricEquivOn (I := J') Y x U)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → t • v ∈ U) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace G Y.M := Y.charted
    letI : IsManifold J' ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
      ⟨Y.metric.toRiemannianMetric⟩
    U ⊆ Metric.ball (0 : F) (expRadiusGp (I := J') Y.metric x) →
    ∀ {lam : ℝ},
      ENNReal.ofReal lam ≤ Manifold.riemannianEDist J' x
        (expMap (I := J') Y.metric x
          (show TangentSpace J' x from
            NormalCoordinates.normalFrame (I := J') Y.metric x v)) →
      lam / Real.sqrt 2 ≤ ‖v‖ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace G Y.M := Y.charted
  letI : IsManifold J' ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle J' Y.M) := Y.t2TangentBundle
  letI : RiemannianBundle (fun y : Y.M => TangentSpace J' y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  intro hsub lam hlam
  have hsmall : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖t • v‖ < expRadiusGp (I := J') Y.metric x := by
    intro t ht
    simpa only [Metric.mem_ball, dist_zero_right] using hsub (hseg t ht)
  have hraw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖t • (show F from
        NormalCoordinates.normalFrame (I := J') Y.metric x v)‖ <
          expMapC2Radius (I := J') Y.metric x := by
    intro t ht
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := J') Y.metric x
    have hframe : t • (show F from
        NormalCoordinates.normalFrame (I := J') Y.metric x v) =
        (show F from
          NormalCoordinates.normalFrame (I := J') Y.metric x (t • v)) := by
      exact (map_smul
        (NormalCoordinates.normalFrame (I := J') Y.metric x) t v).symm
    rw [hframe, NormalCoordinates.normalFrame_sqrt]
    exact hsmall t ht
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) J' 1
      (fun t : ℝ => (expMap (I := J') Y.metric x
        (show TangentSpace J' x from
          t • (show F from
            NormalCoordinates.normalFrame (I := J') Y.metric x v)) : Y.M))
        (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (radialCurve_contMDiffAt2 (I := J') Y.metric x
      (show F from NormalCoordinates.normalFrame (I := J') Y.metric x v)
      t (hraw t ht)).contMDiffWithinAt.of_le
      (by norm_num)
  have hend :
      (expMap (I := J') Y.metric x
        (show TangentSpace J' x from
          (0 : ℝ) • (show F from
            NormalCoordinates.normalFrame (I := J') Y.metric x v)) : Y.M) = x := by
    rw [zero_smul]
    exact expMap_zero (I := J') Y.metric x
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, ℝ) J'
        (fun s : ℝ => (expMap (I := J') Y.metric x
          (show TangentSpace J' x from
            s • (show F from
              NormalCoordinates.normalFrame (I := J') Y.metric x v)) : Y.M)) t 1‖ₑ =
        ENNReal.ofReal (Real.sqrt (normalCoordMetric (I := J') Y x (t • v) v v)) := by
    intro t ht
    exact radialEnorm_normal (I := J') Y x v t (hsmall t ht)
  apply normLowerOfSep (J' := J') Y x heq hseg _ hcurve hend hderiv
  simpa only [one_smul] using hlam

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Concrete good-covering separation in normal coordinates.**  A nonzero live
ordered-net center sees the sequence basepoint at Euclidean normal-coordinate
distance at least `λ(0) / √2`, provided the radial segment stays in the
`NormalCoordMetricEquivOn` region inside the named exponential ball. -/
theorem seqChartNorm_ge
    {Z : PointedRiemannianSeq.{u, uE, uH} (I := J')}
    (hd : InjRadiusDecayInput (I := J') Z) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := J') (Z.obj k)) (k : Nat) {α : Nat}
    (hα : α ≠ 0) {c : (Z.obj k).M} (hc : seqCenter hd D P k α = some c)
    {U : Set F} (heq : NormalCoordMetricEquivOn (I := J') (Z.obj k) c U) :
    letI : TopologicalSpace (Z.obj k).M := (Z.obj k).topology
    letI : ChartedSpace G (Z.obj k).M := (Z.obj k).charted
    letI : IsManifold J' ∞ (Z.obj k).M := (Z.obj k).smooth
    letI : T2Space (TangentBundle J' (Z.obj k).M) := (Z.obj k).t2TangentBundle
    letI : RiemannianBundle (fun y : (Z.obj k).M => TangentSpace J' y) :=
      ⟨(Z.obj k).metric.toRiemannianMetric⟩
    (Z.obj k).basepoint ∈
        (NormalCoordinates.framedChartAt (I := J') (Z.obj k).metric c).source →
    (∀ t : Real, t ∈ Set.Icc (0 : Real) 1 →
      t • NormalCoordinates.framedChartAt (I := J') (Z.obj k).metric c
        (Z.obj k).basepoint ∈ U) →
    U ⊆ Metric.ball (0 : F) (expRadiusGp (I := J') (Z.obj k).metric c) →
    hd.lambda D 0 / Real.sqrt 2 ≤
      ‖NormalCoordinates.framedChartAt (I := J') (Z.obj k).metric c
        (Z.obj k).basepoint‖ := by
  letI : TopologicalSpace (Z.obj k).M := (Z.obj k).topology
  letI : ChartedSpace G (Z.obj k).M := (Z.obj k).charted
  letI : IsManifold J' ∞ (Z.obj k).M := (Z.obj k).smooth
  letI : T2Space (TangentBundle J' (Z.obj k).M) := (Z.obj k).t2TangentBundle
  letI : RiemannianBundle (fun y : (Z.obj k).M => TangentSpace J' y) :=
    ⟨(Z.obj k).metric.toRiemannianMetric⟩
  intro hbase hseg hsub
  have hvsrc :
      NormalCoordinates.framedChartAt (I := J') (Z.obj k).metric c
          (Z.obj k).basepoint ∈
        (NormalCoordinates.framedExpDiffeo (I := J')
          (Z.obj k).metric c).source :=
    (NormalCoordinates.framedChartAt (I := J')
      (Z.obj k).metric c).map_source hbase
  have hexp :
      (expMap (I := J') (Z.obj k).metric c
        (show TangentSpace J' c from
          NormalCoordinates.normalFrame (I := J') (Z.obj k).metric c
            (NormalCoordinates.framedChartAt (I := J')
              (Z.obj k).metric c (Z.obj k).basepoint)) : (Z.obj k).M) =
          (Z.obj k).basepoint := by
    rw [← NormalCoordinates.framedExpMap_apply]
    rw [← NormalCoordinates.framedExp_eq_expMap
      (I := J') (Z.obj k).metric c hvsrc]
    exact (NormalCoordinates.framedExpDiffeo (I := J')
      (Z.obj k).metric c).right_inv hbase
  have hsep : ENNReal.ofReal (hd.lambda D 0) ≤
      Manifold.riemannianEDist J' c (Z.obj k).basepoint := by
    have h := seqCenter_edist_ge hd hD P k hα hc
    simpa [PointedRiemannianManifold.emetricSpace] using h
  rw [← hexp] at hsep
  exact normLowerOfSepExp (J' := J') (Z.obj k) c heq hseg hsub hsep

end PathBridge

section CmInfty

open Set Bundle Manifold
open scoped Topology Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [T2Space M'] [T2Space (TangentBundle I M')] [SigmaCompactSpace M']
  [ConnectedSpace M'] [T3Space M']
variable [RiemannianBundle (fun x : M' => TangentSpace I x)]
variable [PseudoEMetricSpace M'] [IsRiemannianManifold I M'] [CompleteSpace M']

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`lbl404` input (iii) — the chart center of mass is `ContDiffOn ∞` on an open configuration
region.**  The bridge from the C2 chain (`centerOfMass_contDiffAt`, every finite order) to the
`hΦc` slot of `averagedCInf_id`: `contDiffOn_infty` + the order-`max 1 n` instance at each point.
The eight per-configuration hypotheses of the C2 endpoint are threaded `∀`-quantified over `V`,
with the anchor `z₀` pinned to the chart center itself (so `hc_cont` is continuity of the chart
center at each configuration and `hz₀'` is the defining equation at the center). -/
theorem chartCm_contDiffOn
    [IsContinuousRiemannianBundle E (fun x : M' => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M')
    (hEnorm : ∀ (x : M') (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M') {ι : Type} [Fintype ι] (join : M' → M' → ℝ → M') (r : ℝ)
    (H : ∀ params : (ι → ℝ) × (ι → E),
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i)) join p r)
    {V : Set ((ι → ℝ) × (ι → E))}
    (hchz : ∀ params₀ ∈ V, ∀ n : ℕ, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.framedChartAt (I := I) g p).symm z)
      (NormalCoordinates.framedChartAt (I := I) g p
        (centerOfMass (I := I) g params₀.1
          (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i))
          join p r (H params₀))))
    (hchξ : ∀ params₀ ∈ V, ∀ n : ℕ, ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.framedChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ params₀ ∈ V, ∀ n : ℕ, ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M' × M' => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.framedChartAt (I := I) g p).symm
        (NormalCoordinates.framedChartAt (I := I) g p
          (centerOfMass (I := I) g params₀.1
            (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i))
            join p r (H params₀))),
        (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∀ params₀ ∈ V, ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E)
        (NormalCoordinates.framedChartAt (I := I) g p
          (centerOfMass (I := I) g params₀.1
            (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i))
            join p r (H params₀))))
    (hz₀' : ∀ params₀ ∈ V,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.framedChartAt (I := I) g p
          (centerOfMass (I := I) g params₀.1
            (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i))
            join p r (H params₀))) params₀ = 0)
    (hc_solves : ∀ params₀ ∈ V, ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.framedChartAt (I := I) g p
          (centerOfMass (I := I) g params.1
            (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))
            join p r (H params))) params = 0)
    (hc_cont : ∀ params₀ ∈ V, Filter.Tendsto
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))
          join p r (H params)) : E))
      (nhds params₀)
      (nhds (NormalCoordinates.framedChartAt (I := I) g p
        (centerOfMass (I := I) g params₀.1
          (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i))
          join p r (H params₀))))) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞)
      (fun params => (NormalCoordinates.framedChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params.2 i))
          join p r (H params)) : E)) V := by
  rw [contDiffOn_infty]
  intro n params₀ hp
  have hcd := centerOfMass_contDiffAt (I := I) g hEnorm p
    (NormalCoordinates.framedChartAt (I := I) g p
      (centerOfMass (I := I) g params₀.1
        (fun i => (NormalCoordinates.framedChartAt (I := I) g p).symm (params₀.2 i))
        join p r (H params₀)))
    params₀ (max 1 n) (le_max_left 1 n) join r H
    (hchz params₀ hp (max 1 n)) (hchξ params₀ hp (max 1 n)) (hsm params₀ hp (max 1 n))
    (hinv' params₀ hp) (hz₀' params₀ hp) (hc_solves params₀ hp) (hc_cont params₀ hp)
  exact (hcd.of_le (by exact_mod_cast le_max_right 1 n)).contDiffWithinAt

end CmInfty

end HCGCompactness
end DifferentialGeometry
