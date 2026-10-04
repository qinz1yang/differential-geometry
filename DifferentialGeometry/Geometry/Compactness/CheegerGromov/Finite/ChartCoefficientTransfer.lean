import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.ChartPullback
import DifferentialGeometry.Geometry.Metric.Approximation.ChartLimits.Overlap
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Smoothing
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import DifferentialGeometry.Geometry.Metric.Pullback.CoefficientConvergence

/-!
# LFR14, metric convergence in the charts of the smooth carrier

Blueprint LFR14 (master207A.tex:25869), step 4 ("`f_{i,a}^* g_i → g` in `C^{K-1}`"), transferred
from the limit chart parametrizations `σ a` to the extended charts of the carrier `N`.

* `chartCoeff_eqOn_bilinearComp_fderiv`: in the open overlap of an extended chart with a chart
  parametrization `σ a`, the chart coefficients of `G` are the pullback of the `σ`-coefficients
  `b a` along the coordinate change `τ = σ a⁻¹ ∘ chart⁻¹` (chain rule; germ equality).
* `mapCPConvergenceOn_chartCoeff_of_limit_charts`: `C^{K-1}` convergence of the pulled-back
  coefficients in every `σ a` implies the same convergence to `chartCoeff G x` in every extended
  chart. The pieces are arbitrary compact subsets of the OPEN overlaps
  `target ∩ chart⁻¹⁻¹ (σ a.target ∩ ball x k)`; on such an overlap the coordinate change is `C^K`,
  its image has `σ`-image in the compact `closedBall x k` (common regularity tail), I-CHART
  applies, and the identities hold on the open overlap, so the global iterated derivatives are
  moved by `MapCPConvergenceOn.congr`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Chart coefficients through a chart parametrization.** If `G` has coefficients `b` in the
chart parametrization `σ` (of order `K ≥ 1`), then on every open set `U` of the target of the
extended chart at `x` on which `chart⁻¹` lands in the target of `σ`, the chart coefficients of `G`
are `τ^* b` with `τ = σ⁻¹ ∘ chart⁻¹`, provided `τ` is differentiable on `U`. -/
theorem chartCoeff_eqOn_bilinearComp_fderiv
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    {K : ℕ} (hK : 1 ≤ K) {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (σ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N K) (b : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hG : ∀ u ∈ σ.source, ∀ v w : E,
      G.inner (σ u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ u v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ u w) = b u v w)
    (x : N) {U : Set E} (hU : IsOpen U)
    (hUσ : MapsTo (extChartAt 𝓘(ℝ, E) x).symm U σ.target)
    (hτ : DifferentiableOn ℝ (σ.symm ∘ (extChartAt 𝓘(ℝ, E) x).symm) U) :
    EqOn (chartCoeff G x)
      (fun u => (b ((σ.symm ∘ (extChartAt 𝓘(ℝ, E) x).symm) u)).bilinearComp
        (fderiv ℝ (σ.symm ∘ (extChartAt 𝓘(ℝ, E) x).symm) u)
        (fderiv ℝ (σ.symm ∘ (extChartAt 𝓘(ℝ, E) x).symm) u)) U := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK
  intro u hu
  set c := (extChartAt 𝓘(ℝ, E) x).symm with hc
  set τ := σ.symm ∘ c with hτdef
  have hcu : c u ∈ σ.target := hUσ hu
  have hτu : τ u ∈ σ.source := σ.toPartialEquiv.map_target hcu
  have hστ : σ (τ u) = c u := σ.toPartialEquiv.right_inv hcu
  -- `c = σ ∘ τ` near `u`
  have hgerm : c =ᶠ[𝓝 u] σ ∘ τ := by
    filter_upwards [hU.mem_nhds hu] with y hy
    exact (σ.toPartialEquiv.right_inv (hUσ hy)).symm
  have hσd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) σ (τ u) := σ.mdifferentiableAt hK0 hτu
  have hτd : DifferentiableAt ℝ τ u := (hτ u hu).differentiableAt (hU.mem_nhds hu)
  have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c u =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ (τ u)).comp (fderiv ℝ τ u) := by
    rw [hgerm.mfderiv_eq, mfderiv_comp u hσd hτd.mdifferentiableAt, mfderiv_eq_fderiv]
    rfl
  have key : ∀ y y' : N, y = y' → ∀ v w : E, G.inner y v w = G.inner y' v w := by
    rintro y _ rfl v w
    rfl
  ext v w
  rw [chartCoeff_apply, ContinuousLinearMap.bilinearComp_apply, ← hG (τ u) hτu]
  change G.inner (c u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c u v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c u w) = _
  rw [hd]
  exact key _ _ hστ.symm _ _

/-- **Metric convergence in every extended chart (LFR14, clause (c3)).** Let `N` be proper, `σ a`
chart parametrizations of order `K ≥ 1` whose targets cover `N`, `G` a `C^{K-1}` metric with
coefficients `b a` in `σ a` (`C^{K-1}` on the sources), and `j i : N → Y i` partial
diffeomorphisms of order `K` whose sources eventually contain every compact set and whose pulled
back coefficients converge in `C^{K-1}` to `b a` on the compacts of every `σ a` source. Then on
every compact subset of the target of every extended chart at `x`, the pulled-back coefficients of
`g i` along `j i ∘ chart⁻¹` converge in `C^{K-1}` to `chartCoeff G x`. -/
theorem mapCPConvergenceOn_chartCoeff_of_limit_charts
    [FiniteDimensional ℝ E] {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace E N]
    [IsManifold 𝓘(ℝ, E) ∞ N] {K : ℕ} (hK : 1 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _))
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)] (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    {α : Type*} (σ : α → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N K)
    (hcover : ∀ y : N, ∃ a, y ∈ (σ a).target)
    (b : α → E → E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ a, ContDiffOn ℝ (K - 1 : ℕ) (b a) (σ a).source)
    (hG : ∀ a, ∀ u ∈ (σ a).source, ∀ v w : E,
      G.inner (σ a u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (σ a) u v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (σ a) u w) = b a u v w)
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ a (S : Set E), IsCompact S → S ⊆ (σ a).source →
      MapCPConvergenceOn S (K - 1)
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → Y i) ∘ σ a)) (b a))
    (x : N) {L : Set E} (hL : IsCompact L) (hLt : L ⊆ (extChartAt 𝓘(ℝ, E) x).target) :
    MapCPConvergenceOn L (K - 1)
      (fun i => pullbackMetricCoefficients (g i)
        ((j i : N → Y i) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
      (chartCoeff G x) := by
  have hKK : K - 1 + 1 = K := by omega
  have hKle : ((K : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  set c := (extChartAt 𝓘(ℝ, E) x).symm with hc
  -- the open overlaps
  let U : α × ℕ → Set E := fun ak =>
    (extChartAt 𝓘(ℝ, E) x).target ∩ c ⁻¹' ((σ ak.1).target ∩ ball x (ak.2 : ℝ))
  have hUo : ∀ ak, IsOpen (U ak) := fun ak =>
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
      ((σ ak.1).open_target.inter isOpen_ball)
  refine GC.MetricGeometry.mapCPConvergenceOn_of_isCompact_subset_sUnion (S := range U)
    (by rintro _ ⟨ak, rfl⟩; exact hUo ak) ?_ hL ?_
  · rintro _ ⟨⟨a, k⟩, rfl⟩ Q hQ hQU
    let τ : E → E := (σ a).symm ∘ c
    let V : Set E := (σ a).source ∩ σ a ⁻¹' ball x (k : ℝ)
    have hVo : IsOpen V := (σ a).toOpenPartialHomeomorph.isOpen_inter_preimage isOpen_ball
    have hcU : MapsTo c (U (a, k)) (σ a).target := fun u hu => hu.2.1
    -- the coordinate change is `C^K` on the open overlap
    have hτK : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K τ (U (a, k)) :=
      (σ a).symm.contMDiffOn.comp (((contMDiffOn_extChartAt_symm x).of_le hKle).mono
        inter_subset_left) hcU
    have hτ : ContDiffOn ℝ (K - 1 + 1 : ℕ) τ (U (a, k)) := by
      rw [hKK]
      exact contMDiffOn_iff_contDiffOn.mp hτK
    have hτUV : MapsTo τ (U (a, k)) V := by
      intro u hu
      have hcu : c u ∈ (σ a).target := hu.2.1
      refine ⟨(σ a).toPartialEquiv.map_target hcu, ?_⟩
      have hr : σ a ((σ a).symm (c u)) = c u := (σ a).toPartialEquiv.right_inv hcu
      change σ a ((σ a).symm (c u)) ∈ ball x (k : ℝ)
      rw [hr]
      exact hu.2.2
    -- the common regularity tail, from the larger compact `closedBall x k`
    have hf : ∀ᶠ i in atTop,
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (K - 1 + 1 : ℕ) ((j i : N → Y i) ∘ σ a) V := by
      filter_upwards [hexh _ (isCompact_closedBall x (k : ℝ))] with i hi
      rw [hKK]
      exact (j i).contMDiffOn.comp ((σ a).contMDiffOn.mono inter_subset_left)
        (fun v hv => hi (ball_subset_closedBall hv.2))
    have hmain := mapCPConvergenceOn_pullbackMetricCoefficients_comp g
      (fun i => (j i : N → Y i) ∘ σ a) τ (hUo (a, k)) hVo hτ hτUV hf (b a)
      ((hb a).mono inter_subset_left) (fun S hS hSV => hconv a S hS (hSV.trans inter_subset_left))
      hQ hQU
    refine hmain.congr (hUo (a, k)) hQU (fun i u hu => ?_) ?_
    · -- the maps agree on the open overlap, hence their coefficients agree there
      have hgerm : ((j i : N → Y i) ∘ c) =ᶠ[𝓝 u] (((j i : N → Y i) ∘ σ a) ∘ τ) := by
        filter_upwards [(hUo (a, k)).mem_nhds hu] with y hy
        have hr : σ a ((σ a).symm (c y)) = c y := (σ a).toPartialEquiv.right_inv hy.2.1
        change j i (c y) = j i (σ a ((σ a).symm (c y)))
        rw [hr]
      exact pullbackMetricCoefficients_eq_of_eventuallyEq (g i) hgerm
    · exact chartCoeff_eqOn_bilinearComp_fderiv hK G (σ a) (b a) (hG a) x (hUo (a, k))
        hcU (hτ.differentiableOn (by simp))
  · intro u hu
    obtain ⟨a, ha⟩ := hcover (c u)
    obtain ⟨k, hk⟩ := exists_nat_gt (dist (c u) x)
    exact ⟨U (a, k), ⟨(a, k), rfl⟩, hLt hu, ha, mem_ball.mpr hk⟩

end DifferentialGeometry.CheegerGromovCompactness
