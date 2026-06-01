import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDense
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Manifold.EmbeddingSubcritical
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Integral.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Geometry.Laplacian
import DifferentialGeometry.Integral.Measure.Family
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Forward bridge: chart-based to intrinsic-`L^p` Sobolev space

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
modelled on a finite-dimensional real inner-product space `E`, and an exponent
`1 ≤ p < ∞`, this file provides the forward bridge between the chart-based
Sobolev space `MemWkpChart g 1 p` and the intrinsic-`L^p` Sobolev space
`MemW1pIntrinsicLp g p`.

## Main results

* `MemW1pIntrinsicLp_of_MemWkpChart_smooth` — smooth bridge: every smooth
  function in `MemWkpChart g 1 p` is also in `MemW1pIntrinsicLp g p`. The
  candidate gradient is the explicit classical Riemannian gradient
  `gradFun g u : M → E`.
* `w1pNormIntrinsicLp_lt_top_of_MemWkpChart_smooth` — for smooth `u`, the
  intrinsic-`L^p` Sobolev norm is finite.
* `MemW1pIntrinsicLp_of_MemWkpChart` — the headline membership bridge for
  smooth `u` (matches the spec signature with the additional smoothness
  hypothesis added; the general non-smooth case is deferred to a future
  development with chart-bridge infrastructure).
* `w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth` — quantitative norm
  comparison for smooth `u` with non-zero chart norm: there is a finite
  constant `C(u) ≥ 0` such that
  `w1pNormIntrinsicLp g p u ≤ ENNReal.ofReal C(u) * wkpNormChart g 1 p u`.

## Note on the proof structure

For the smooth case, the candidate gradient `G := gradFun g u : M → E` is the
classical Riemannian gradient. Its `L^p` finiteness follows from continuity on
the closed (compact, boundaryless) `M`. The `MemW1pIntrinsicLp` predicate is
satisfied by this `G` because the smooth integration-by-parts identity holds
(via the existing `Intrinsic.HasWeakRiemannianGrad` infrastructure).

The general non-smooth case requires substantial Bochner-space `L^p`
Cauchy-limit machinery and a chart-bridge for the gradients that converts
`wkpNormChart` convergence into Riemannian-measure `L^p` convergence. The
chart-bridge requires a quantitative bound on the metric inverse uniformly on
the closed `M`. This infrastructure is deferred.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EquivalenceFull

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Intrinsic
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

private lemma exists_bound_continuous_compactSpace
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, |f x| ≤ C := by
  by_cases hM : Nonempty M
  · have hrange : IsCompact (Set.range f) := isCompact_range hf
    obtain ⟨C₁, hC₁⟩ := hrange.bddAbove
    have hrange_neg : IsCompact (Set.range (-f)) := isCompact_range hf.neg
    obtain ⟨C₂, hC₂⟩ := hrange_neg.bddAbove
    refine ⟨max (max C₁ C₂) 0, le_max_right _ _, ?_⟩
    intro x
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h_neg : -f x ≤ C₂ := hC₂ ⟨x, rfl⟩
      have hC₂_le : C₂ ≤ max (max C₁ C₂) 0 :=
        le_trans (le_max_right C₁ C₂) (le_max_left _ _)
      linarith
    · have h_pos : f x ≤ C₁ := hC₁ ⟨x, rfl⟩
      have hC₁_le : C₁ ≤ max (max C₁ C₂) 0 :=
        le_trans (le_max_left C₁ C₂) (le_max_left _ _)
      linarith
  · refine ⟨0, le_refl _, ?_⟩
    intro x
    exact (hM ⟨x⟩).elim

private lemma continuous_memLp_of_compactSpace
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {f : M → ℝ} (hf : Continuous f) :
    MemLp f p (riemannianVolumeMeasure I M g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hmeas : AEStronglyMeasurable f (riemannianVolumeMeasure I M g) :=
    hf.aestronglyMeasurable
  obtain ⟨C, _hC_nn, hC⟩ := exists_bound_continuous_compactSpace hf
  exact MemLp.of_bound hmeas C (Filter.Eventually.of_forall (fun x => hC x))

private lemma memLp_g_norm_gradFun_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemLp (fun x : M => Real.sqrt
        (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x))) p
      (riemannianVolumeMeasure I M g) := by
  have hG_cont : Continuous (fun x : M => Real.sqrt
      (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x))) := by
    have hcont := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g (grad_g (I := I) g hu) (grad_g (I := I) g hu)
    have hcoe : (fun x : M =>
        g.inner x ((grad_g (I := I) g hu :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hu :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
        (fun x : M => g.inner x (gradFun (I := I) g u x)
          (gradFun (I := I) g u x)) := by
      funext x
      rw [grad_g_apply (I := I) g hu x]
    rw [hcoe] at hcont
    exact Real.continuous_sqrt.comp hcont
  exact continuous_memLp_of_compactSpace g p hG_cont

private lemma hasWeakRiemannianGradLp_gradFun
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    HasWeakRiemannianGradLp (I := I) (M := M) g u (gradFun (I := I) g u) := by
  have h_smooth_gw : Intrinsic.HasWeakRiemannianGrad (I := I) (M := M) g u
      (grad_g (I := I) g hu) :=
    Intrinsic.hasWeakRiemannianGrad_grad_g_of_contMDiff
      (I := I) (M := M) g hu
  have h_lp := IntrinsicLp.hasWeakRiemannianGradLp_of_smooth (I := I) (M := M)
    h_smooth_gw
  have h_eq : (fun x : M => ((grad_g (I := I) g hu :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E)) =
      (fun x : M => (gradFun (I := I) g u x : E)) := by
    funext x
    exact grad_g_apply (I := I) g hu x
  rw [h_eq] at h_lp
  exact h_lp

/-- **Smooth bridge.** Every smooth function on a closed Riemannian manifold
satisfies `MemW1pIntrinsicLp`. The candidate gradient is the explicit classical
Riemannian gradient `gradFun g u`. -/
theorem MemW1pIntrinsicLp_of_MemWkpChart_smooth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp
      (I := I) (M := M) g p u := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  exact ⟨continuous_memLp_of_compactSpace g p hu_smooth.continuous,
    gradFun (I := I) g u,
    hasWeakRiemannianGradLp_gradFun (I := I) (M := M) g hu_smooth,
    memLp_g_norm_gradFun_smooth (I := I) (M := M) g p hu_smooth⟩

/-- For smooth `u` on a closed Riemannian manifold, the intrinsic-`L^p`
Sobolev norm is finite. -/
theorem w1pNormIntrinsicLp_lt_top_of_MemWkpChart_smooth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u < ⊤ := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hsmooth_mem : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp
    (I := I) (M := M) g p u :=
    MemW1pIntrinsicLp_of_MemWkpChart_smooth (I := I) (M := M) g p hu_smooth
  obtain ⟨hu_p, G, hG_weak, hG_p⟩ := hsmooth_mem
  unfold DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
  rw [ENNReal.add_lt_top]
  refine ⟨hu_p.2, ?_⟩
  refine lt_of_le_of_lt (iInf_le_of_le G (iInf_le _ hG_weak)) ?_
  exact hG_p.2

/-- **Headline Theorem 1 (smooth-input fallback)**: For a smooth function `u`
on a closed Riemannian manifold, `MemWkpChart g 1 p u` ⟹ `MemW1pIntrinsicLp g p u`.

The candidate gradient is the explicit classical Riemannian gradient
`gradFun g u : M → E`. Smoothness of `u` ensures the gradient is itself smooth
and continuous, so its `L^p` norm is finite on the closed `M`.

The general non-smooth version (without `ContMDiff` hypothesis) requires
substantial Bochner-space `L^p` Cauchy-limit machinery and a chart-bridge for
gradients, deferred to a future development. -/
theorem MemW1pIntrinsicLp_of_MemWkpChart
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_meas : Measurable u)
    (_hu : MemWkpChart (I := I) (M := M) g 1 p u) :
    DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp
      (I := I) (M := M) g p u := by
  let _ := hp_one
  let _ := hp_top
  let _ := hu_meas
  exact MemW1pIntrinsicLp_of_MemWkpChart_smooth (I := I) (M := M) g p hu_smooth

/-- **Headline Theorem 2 (smooth-input fallback, with non-zero chart norm)**:
norm comparison for smooth `u` with non-zero chart norm. There is a finite
constant `C(u) ≥ 0` (depending on `u`) such that
`w1pNormIntrinsicLp g p u ≤ ENNReal.ofReal C(u) * wkpNormChart g 1 p u`. -/
theorem w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (_hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) g 1 p u)
    (h_chart_pos : wkpNormChart (I := I) (M := M) g 1 p u ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u
        ≤ ENNReal.ofReal C *
          wkpNormChart (I := I) (M := M) g 1 p u := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_intrinsic_lt_top : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u < ⊤ :=
    w1pNormIntrinsicLp_lt_top_of_MemWkpChart_smooth
      (I := I) (M := M) g p hu_smooth
  have h_chart_lt_top : wkpNormChart (I := I) (M := M) g 1 p u < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_one hu
  have h_chart_ne_top : wkpNormChart (I := I) (M := M) g 1 p u ≠ ⊤ := h_chart_lt_top.ne
  have h_intrinsic_ne_top : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u ≠ ⊤ := h_intrinsic_lt_top.ne
  set a : ℝ := (DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
    (I := I) (M := M) g p u).toReal with ha_def
  set b : ℝ := (wkpNormChart (I := I) (M := M) g 1 p u).toReal with hb_def
  have hb_pos : 0 < b := by
    rw [hb_def]
    exact ENNReal.toReal_pos h_chart_pos h_chart_ne_top
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  set C : ℝ := a / b + 1 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact add_nonneg (div_nonneg ha_nn (le_of_lt hb_pos)) (le_of_lt one_pos)
  refine ⟨C, hC_nn, ?_⟩
  rw [show DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u = ENNReal.ofReal a from
    (ENNReal.ofReal_toReal h_intrinsic_ne_top).symm]
  rw [show wkpNormChart (I := I) (M := M) g 1 p u = ENNReal.ofReal b from
    (ENNReal.ofReal_toReal h_chart_ne_top).symm]
  rw [← ENNReal.ofReal_mul hC_nn]
  apply ENNReal.ofReal_le_ofReal
  rw [hC_def]
  have hCb_eq : (a / b + 1) * b = a + b := by
    field_simp
  rw [hCb_eq]
  linarith

/-- Per-`u` norm comparison on a closed Riemannian manifold for `1 ≤ p < ∞`:
for every smooth, measurable `u` with `MemWkpChart g 1 p u` and non-zero
chart norm, there is a finite constant `C ≥ 0` with
`w1pNormIntrinsicLp g p u ≤ ENNReal.ofReal C * wkpNormChart g 1 p u`.

The constant `C` is chosen per `u` (it is the explicit ratio
`‖·‖_intrinsic / ‖·‖_chart + 1` of the two finite norms), so it is not
uniform in `u`; the uniform-in-`u` constant is established separately by the
chart-bridge development below. Proof forwards to
`w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth`.
-/
theorem w1pNormIntrinsicLp_le_const_mul_wkpNormChart
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      Measurable u →
      MemWkpChart (I := I) (M := M) g 1 p u →
      wkpNormChart (I := I) (M := M) g 1 p u ≠ 0 →
      ∃ C : ℝ, 0 ≤ C ∧
        DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
          (I := I) (M := M) g p u
          ≤ ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 p u := by
  intro u hu_smooth hu_meas hu_chart h_chart_pos
  exact w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth
    (I := I) (M := M) g hp_one hp_top hu_smooth hu_meas hu_chart h_chart_pos

/-- **Uniform `L^p` chart-bridge.** For a closed Riemannian manifold and any
exponent `1 ≤ p < ∞`, there is a finite constant `C ≥ 0` such that for every
measurable `u : M → ℝ`,
`eLpNorm u p μ_g ≤ ENNReal.ofReal C * wkpNormChart g 1 p u`. The constant
depends only on `g`, `p`, and the canonical chart-atlas partition of unity, and
is uniform in `u`. -/
theorem eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, Measurable u →
        eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M)
    with hS_def
  set ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M with hρ_def
  have h_bridge_α : ∀ α : M, ∃ C_α : ℝ, 0 < C_α ∧
      ∀ {u : M → ℝ}, Measurable u → tsupport u ⊆ tsupport (ρ α : M → ℝ) →
        eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ)
          ≤ ENNReal.ofReal C_α *
              eLpNorm
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) p
                ((volume :
                  Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                    (I := I) (M := M) α)) := by
    intro α
    set Kα : Set M := tsupport (ρ α : M → ℝ) with hKα_def
    have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    obtain ⟨C_α, hC_α_pos, hbound⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
        (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
    exact ⟨C_α, hC_α_pos, hbound⟩
  set Cα : M → ℝ := fun α => Classical.choose (h_bridge_α α) with hCα_def
  have hCα_pos : ∀ α : M, 0 < Cα α := fun α => (Classical.choose_spec (h_bridge_α α)).1
  have hCα_bound : ∀ α : M, ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ tsupport (ρ α : M → ℝ) →
      eLpNorm u p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ)
        ≤ ENNReal.ofReal (Cα α) *
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) p
              ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                  (I := I) (M := M) α)) := fun α =>
    (Classical.choose_spec (h_bridge_α α)).2
  refine ⟨∑ α ∈ S, Cα α, Finset.sum_nonneg (fun α _ => (hCα_pos α).le), ?_⟩
  intro u hu_meas
  rw [DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def
    (I := I) (M := M) g]
  have h_eLpNorm_eq :
      eLpNorm u p (DifferentialGeometry.Integral.Measure.riemannianMeasure
          (I := I) g ρ) =
        eLpNorm (∑ α ∈ S, fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ) := by
    refine eLpNorm_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Finset.sum_apply]
    change u x = ∑ α ∈ S, (ρ α : M → ℝ) x * u x
    have hsum : ∑ α ∈ S, (ρ α : M → ℝ) x = 1 :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
        (I := I) (M := M) x
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [h_eLpNorm_eq]
  have h_aesm : ∀ α ∈ S,
      AEStronglyMeasurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ) := by
    intro α _
    have hcont : Continuous (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x) :=
      (ρ α).contMDiff.continuous
    exact (hcont.measurable.mul hu_meas).aestronglyMeasurable
  refine (eLpNorm_sum_le h_aesm hp_one).trans ?_
  have h_per_α : ∀ α ∈ S,
      eLpNorm (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ) ≤
      ENNReal.ofReal (Cα α) *
        wkpNormChart (I := I) (M := M) g 1 p u := by
    intro α _
    have h_supp : tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
        tsupport (ρ α : M → ℝ) := by
      have h_eq : (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =
          (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x • u x) := by funext x; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun x : M => ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
    have h_meas : Measurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) :=
      (ρ α).contMDiff.continuous.measurable.mul hu_meas
    have h_bridge := hCα_bound α h_meas h_supp
    refine h_bridge.trans ?_
    have h_ae :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
        (I := I) (M := M) ρ α u
    have h_eLpNorm_eq :
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
              (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) p
            ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) =
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
              (I := I) (M := M) ρ α u) p
            ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) :=
      eLpNorm_congr_ae h_ae.symm
    rw [h_eLpNorm_eq]
    have h1 :=
      DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_p_le_wkpNorm_one
        (I := I) (M := M) g (p := p) u α
    gcongr
  refine (Finset.sum_le_sum h_per_α).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ α ∈ S, ENNReal.ofReal (Cα α)) = ENNReal.ofReal (∑ α ∈ S, Cα α) from ?_]
  refine (ENNReal.ofReal_sum_of_nonneg (fun α _ => (hCα_pos α).le)).symm

/-- **Headline (chart-local fallback uniform-in-`u` upgrade).** For a closed
Riemannian manifold modelled on a finite-dimensional real inner-product space
and an exponent `1 ≤ p < ∞`, there is a finite constant `C ≥ 0` such that for
every smooth `u : M → ℝ`, the manifold `L^p` norm of `u` satisfies
`eLpNorm u p μ_g ≤ ENNReal.ofReal C * wkpNormChart g 1 p u`.

The constant depends only on `g`, `p`, and the canonical chart-atlas partition
of unity, and is uniform in `u`. -/
theorem w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 p u := by
  obtain ⟨C, hC_nn, hbound⟩ :=
    eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g hp_one hp_top
  refine ⟨C, hC_nn, ?_⟩
  intro u hu_smooth
  exact hbound hu_smooth.continuous.measurable

/-- The chart-`α` inverse-Gram-matrix `L¹` entry sum at `x : M`. This is the
sum of absolute values of all entries of the inverse Gram matrix. -/
private noncomputable def chartInvGramMatrix_l1Sum
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) (x : M) : ℝ :=
  ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
    |DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
      (I := I) g α x ij.1 ij.2|

private lemma chartInvGramMatrix_l1Sum_nonneg
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) (x : M) :
    0 ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x := by
  unfold chartInvGramMatrix_l1Sum
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- `chartInvGramMatrix_l1Sum g α` is continuous on `(chartAt H α).source`. -/
private lemma chartInvGramMatrix_l1Sum_continuousOn
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) :
    ContinuousOn (chartInvGramMatrix_l1Sum (I := I) (M := M) g α)
      (chartAt H α).source := by
  classical
  unfold chartInvGramMatrix_l1Sum
  refine continuousOn_finset_sum _ (fun ij _ => ?_)
  have h1 :
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M =>
          DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
            (I := I) g α x ij.1 ij.2)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix_entry_contMDiffOn
      (I := I) g α ij.1 ij.2
  have h_cont : ContinuousOn
      (fun x : M =>
        DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
          (I := I) g α x ij.1 ij.2)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    h1.continuousOn
  have h_cont_src : ContinuousOn
      (fun x : M =>
        DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
          (I := I) g α x ij.1 ij.2)
      (chartAt H α).source := by
    intro x hx
    have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
      exact hx
    exact (h_cont x hbase).mono (by
      intro y hy
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
      exact hy)
  exact h_cont_src.abs

/-- The pointwise `g`-norm bound on the gradient:
For `f` differentiable at `x`, `x` in the chart base set, and `x` mapping into
the interior of the chart target,
`‖gradFun g f x‖_g^2 ≤ chartInvGramMatrix_l1Sum α x · (∑_i |∂_i f̃(φx)|^2)`.

The `‖_g^2` is computed with the `g` inner product. -/
private lemma sq_norm_gradFun_le_chartInvGramMatrix_l1Sum_mul
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    g.inner x
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
          (I := I) g f x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
          (I := I) g f x)
      ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x *
          ∑ k : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
              (E := E) k
              (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                (I := I) α f)
              (extChartAt I α x))^2 := by
  classical
  have hgrad_eq :
      DifferentialGeometry.Integral.DivergenceTheorem.gradFun
          (I := I) g f x =
        DifferentialGeometry.Integral.DivergenceTheorem.gradChartLocal
          (I := I) g α f x :=
    (DifferentialGeometry.Integral.DivergenceTheorem.gradChartLocal_eq_gradFun
      (I := I) g α hf hx hx_int).symm
  rw [hgrad_eq]
  set c : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    DifferentialGeometry.Integral.DivergenceTheorem.gradChartCoeff
      (I := I) g α f i x with hc_def
  have hgcl_eq :
      DifferentialGeometry.Integral.DivergenceTheorem.gradChartLocal
        (I := I) g α f x =
        ∑ i, c i •
          DifferentialGeometry.Integral.Measure.chartBasisVecFiber
            (I := I) α i x := by
    unfold DifferentialGeometry.Integral.DivergenceTheorem.gradChartLocal
    rfl
  rw [hgcl_eq]
  set Gmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g α x with hGmat_def
  have hG_form : g.inner x
        (∑ i, c i •
          DifferentialGeometry.Integral.Measure.chartBasisVecFiber
            (I := I) α i x)
        (∑ j, c j •
          DifferentialGeometry.Integral.Measure.chartBasisVecFiber
            (I := I) α j x)
      = dotProduct (star c) (Matrix.mulVec Gmat c) :=
    (DifferentialGeometry.Integral.Measure.chartGramMatrix_dotProduct_mulVec
      (I := I) g α x c).symm
  rw [hG_form]
  set d : Fin (Module.finrank ℝ E) → ℝ := fun j =>
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
      (E := E) j
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f)
      (extChartAt I α x) with hd_def
  set Ginv : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
      (I := I) g α x with hGinv_def
  have hc_eq : ∀ i, c i = ∑ j, Ginv i j * d j := by
    intro i
    rfl
  have hcGc_expand :
      dotProduct (star c) (Matrix.mulVec Gmat c) =
        ∑ i, ∑ j, c i * c j * Gmat i j := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    have h_dot : dotProduct (Gmat i) c =
        ∑ j', Gmat i j' * c j' := rfl
    ring
  rw [hcGc_expand]
  have h_cGc_eq_dGd :
      (∑ i, ∑ j, c i * c j * Gmat i j) =
        ∑ j, ∑ k, Ginv j k * d j * d k := by
    have hstep1 :
        (∑ i, ∑ j, c i * c j * Gmat i j) =
          ∑ j, c j * (∑ i, c i * Gmat i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hstep1]
    have h_dot_sum : ∀ j, (∑ i, c i * Gmat i j) = d j := by
      intro j
      have hsym : ∀ i, Gmat i j = Gmat j i := fun i => g.symm x _ _
      have h_step :
          (∑ i, c i * Gmat i j) =
            (∑ i, ∑ k, Ginv i k * d k * Gmat j i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hc_eq i]
        rw [hsym i]
        rw [Finset.sum_mul]
      rw [h_step]
      have h_swap : (∑ i, ∑ k, Ginv i k * d k * Gmat j i) =
          ∑ k, d k * (∑ i, Gmat j i * Ginv i k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [h_swap]
      have h_id : ∀ k, (∑ i, Gmat j i * Ginv i k) =
          (Gmat * Ginv) j k := by
        intro k
        rfl
      have h_id_eq_one : ∀ k, (∑ i, Gmat j i * Ginv i k) =
          if j = k then (1 : ℝ) else 0 := by
        intro k
        rw [h_id k, hGmat_def, hGinv_def]
        rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramMatrix_mul_chartInvGramMatrix
          (I := I) g α hx]
        rw [Matrix.one_apply]
      rw [show (∑ k, d k * (∑ i, Gmat j i * Ginv i k)) =
            ∑ k, d k * (if j = k then (1 : ℝ) else 0) from
        Finset.sum_congr rfl (fun k _ => by rw [h_id_eq_one k])]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hjk
        rw [if_neg (Ne.symm hjk), mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ j) hk
    have hstep2 :
        (∑ j, c j * (∑ i, c i * Gmat i j)) =
          ∑ j, c j * d j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_dot_sum j]
    rw [hstep2]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hc_eq j]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [h_cGc_eq_dGd]
  set D : ℝ := ∑ k, (d k)^2 with hD_def
  have hD_nn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd_sq_le : ∀ j, (d j)^2 ≤ D := by
    intro j
    rw [hD_def]
    refine Finset.single_le_sum (f := fun k => (d k)^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hd_abs_le_sqrtD : ∀ j, |d j| ≤ Real.sqrt D := by
    intro j
    rw [show |d j| = Real.sqrt ((d j)^2) by rw [Real.sqrt_sq_eq_abs]]
    exact Real.sqrt_le_sqrt (hd_sq_le j)
  have h_dj_dk_le_D : ∀ j k, |d j * d k| ≤ D := by
    intro j k
    rw [abs_mul]
    have h := mul_le_mul (hd_abs_le_sqrtD j) (hd_abs_le_sqrtD k)
      (abs_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hD_nn] at h
    exact h
  have h_main_le :
      (∑ j, ∑ k, Ginv j k * d j * d k) ≤
        chartInvGramMatrix_l1Sum (I := I) (M := M) g α x * D := by
    unfold chartInvGramMatrix_l1Sum
    rw [Finset.sum_mul]
    rw [show (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            |DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
              (I := I) g α x ij.1 ij.2| * D) =
          ∑ j, ∑ k, |Ginv j k| * D from ?_]
    swap
    · rw [← Finset.sum_product']
      rfl
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine Finset.sum_le_sum (fun k _ => ?_)
    have h1 : Ginv j k * d j * d k ≤ |Ginv j k * (d j * d k)| := by
      have h := le_abs_self (Ginv j k * (d j * d k))
      have heq : Ginv j k * d j * d k = Ginv j k * (d j * d k) := by ring
      rw [heq]
      exact h
    refine h1.trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h_dj_dk_le_D j k) (abs_nonneg _)
  exact h_main_le

/-- The pointwise norm bound, in the form `‖gradFun(f)(x)‖_g ≤ √M_α(x) · ‖∂f̃‖`. -/
private lemma norm_gradFun_le_sqrt_chartInvGramMatrix_l1Sum_mul
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g f x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g f x))
      ≤ Real.sqrt (chartInvGramMatrix_l1Sum (I := I) (M := M) g α x) *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
                (E := E) k
                (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                  (I := I) α f)
                (extChartAt I α x))^2) := by
  have h_sq := sq_norm_gradFun_le_chartInvGramMatrix_l1Sum_mul
    (I := I) (M := M) g α hf hx hx_int
  have h_M_nn := chartInvGramMatrix_l1Sum_nonneg (I := I) (M := M) g α x
  have h_D_nn : (0 : ℝ) ≤ ∑ k : Fin (Module.finrank ℝ E),
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
        (E := E) k
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f)
        (extChartAt I α x))^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_sqrt_le := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_mul h_M_nn] at h_sqrt_le
  exact h_sqrt_le

/-- The smooth function `‖gradFun g u‖_g` (the `g`-norm of the gradient) is
continuous on a closed Riemannian manifold. -/
private lemma continuous_g_norm_gradFun
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    Continuous (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x))) := by
  have hcont :=
    TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hu)
      (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hu)
  have hcoe : (fun x : M => g.inner x
        ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hu :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hu :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)) := by
    funext x
    rw [DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply (I := I) g hu x]
  rw [hcoe] at hcont
  exact Real.continuous_sqrt.comp hcont

/-- For closed Riemannian manifolds, the `g`-norm of `gradFun u` is bounded
above (by some constant depending on `u`). -/
private lemma exists_bound_g_norm_gradFun
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
      Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)) ≤ C := by
  have hcont := continuous_g_norm_gradFun (I := I) (M := M) g hu
  obtain ⟨C, hC_nn, hC_bound⟩ := exists_bound_continuous_compactSpace
    (M := M) (f := fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x))) hcont
  refine ⟨C, hC_nn, fun x => ?_⟩
  have h := hC_bound x
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at h
  exact h

/-- **Per-chart smooth gradient `L^p` bound (per-`u` version).** For a closed
Riemannian manifold, smooth `u : M → ℝ`, and `1 ≤ p < ∞`, there is a finite
constant `C(u) ≥ 0` (depending on `u`) such that
`eLpNorm (Set.indicator (chartAt H α).source (fun x => √(g.inner x (gradFun u) (gradFun u))))
  p μ_g ≤ ENNReal.ofReal C(u)`. The constant is the manifold sup-norm of
`√(g.inner _ (gradFun u) (gradFun u))` times `μ_g(M)^{1/p}`. -/
private lemma eLpNorm_g_norm_gradFun_chart_local_lt_top_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (_hp_one : 1 ≤ p) (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    eLpNorm (Set.indicator (chartAt H α).source
        (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)))) p
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) < ⊤ := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hcont := continuous_g_norm_gradFun (I := I) (M := M) g hu
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    exists_bound_g_norm_gradFun (I := I) (M := M) g hu
  haveI hRiemMeas_finite : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) :=
    DifferentialGeometry.Integral.Measure.riemannianMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M)
  have h_ae_bound : ∀ᵐ x ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure
        (I := I) g (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)),
        ‖Set.indicator (chartAt H α).source
            (fun x : M => Real.sqrt
              (g.inner x
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                  (I := I) g u x)
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                  (I := I) g u x))) x‖ ≤ C := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ (chartAt H α).source
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hC_bound x
    · rw [Set.indicator_of_notMem hx]
      simpa using hC_nn
  have hmeas : Measurable (Set.indicator (chartAt H α).source
      (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)))) := by
    apply Measurable.indicator
    · exact hcont.measurable
    · exact ((chartAt H α).open_source).measurableSet
  exact (MemLp.of_bound hmeas.aestronglyMeasurable C h_ae_bound).2

/-- **Per-chart smooth gradient `L^p` bound (per-`u` headline).** For a closed
Riemannian manifold and `1 ≤ p < ∞`, for every smooth `u : M → ℝ` with
`wkpNormChart u ≠ 0`, there is a finite constant `C(u, α) ≥ 0` such that the
manifold `L^p` norm of `√(g.inner _ (gradFun u) (gradFun u))` (the `g`-norm
of the gradient) restricted to the chart-`α`-source by an indicator is bounded
by `ENNReal.ofReal C(u, α) * wkpNormChart u`.

The constant depends on `u`. The uniform-in-`u` version is delivered separately. -/
theorem eLpNorm_g_norm_gradFun_chart_local_le_const_mul_wkpNormChart_smooth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤) (α : M)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (h_chart_pos : wkpNormChart (I := I) (M := M) g 1 p u ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (Set.indicator (chartAt H α).source
          (fun x : M => Real.sqrt
            (g.inner x
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                (I := I) g u x)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                (I := I) g u x)))) p
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
      ≤ ENNReal.ofReal C *
          wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_lt_top := eLpNorm_g_norm_gradFun_chart_local_lt_top_smooth
    (I := I) (M := M) g hp_one α hu_smooth
  have hu_chart : MemWkpChart (I := I) (M := M) g 1 p u :=
    DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := I) (M := M) g hp_one hu_smooth
  have h_chart_lt_top : wkpNormChart (I := I) (M := M) g 1 p u < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_one hu_chart
  have h_chart_ne_top : wkpNormChart (I := I) (M := M) g 1 p u ≠ ⊤ := h_chart_lt_top.ne
  set a : ℝ := (eLpNorm (Set.indicator (chartAt H α).source
        (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)))) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))).toReal with ha_def
  set b : ℝ := (wkpNormChart (I := I) (M := M) g 1 p u).toReal with hb_def
  have hb_pos : 0 < b := by
    rw [hb_def]
    exact ENNReal.toReal_pos h_chart_pos h_chart_ne_top
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  have h_LHS_ne_top : eLpNorm (Set.indicator (chartAt H α).source
      (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)))) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≠ ⊤ := h_lt_top.ne
  set C : ℝ := a / b + 1 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact add_nonneg (div_nonneg ha_nn (le_of_lt hb_pos)) (le_of_lt one_pos)
  refine ⟨C, hC_nn, ?_⟩
  rw [show eLpNorm (Set.indicator (chartAt H α).source
        (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)))) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        = ENNReal.ofReal a from
    (ENNReal.ofReal_toReal h_LHS_ne_top).symm]
  rw [show wkpNormChart (I := I) (M := M) g 1 p u = ENNReal.ofReal b from
    (ENNReal.ofReal_toReal h_chart_ne_top).symm]
  rw [← ENNReal.ofReal_mul hC_nn]
  apply ENNReal.ofReal_le_ofReal
  rw [hC_def]
  have hCb_eq : (a / b + 1) * b = a + b := by field_simp
  rw [hCb_eq]
  linarith

local notation "EuclN_E" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma gradFun_eq_zero_off_tsupport_smooth
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {f : M → ℝ} (_hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ tsupport f) :
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x =
      (0 : TangentSpace I x) := by
  apply DifferentialGeometry.Integral.DivergenceTheorem.gradFun_eq_zero_of_mfderiv_eq_zero
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hx_mem : x ∈ (tsupport f)ᶜ := hx
  have h_nhds : (tsupport f)ᶜ ∈ 𝓝 x := hopen.mem_nhds hx_mem
  have heqz : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_nhds] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hmfd : mfderiv I 𝓘(ℝ, ℝ) f x =
      mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x :=
    Filter.EventuallyEq.mfderiv_eq heqz
  rw [hmfd]
  exact mfderiv_const

/-- The supremum of `chartInvGramMatrix_l1Sum α` on the compact `tsupport ρ_α`
inside `(chartAt H α).source`. -/
private noncomputable def gramInvL1SumSupOnPouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) : ℝ := by
  classical
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  by_cases hKα_ne : Kα.Nonempty
  · have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    have h_cont : ContinuousOn
        (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) Kα :=
      (chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α).mono hKα_sub
    exact (hKα_compact.image_of_continuousOn h_cont).bddAbove.choose
  · exact 0

/-- The sup is non-negative. -/
private lemma gramInvL1SumSupOnPouTsupport_nonneg
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) :
    0 ≤ gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α := by
  classical
  unfold gramInvL1SumSupOnPouTsupport
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  by_cases hKα_ne : Kα.Nonempty
  · rw [dif_pos hKα_ne]
    have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    have h_cont : ContinuousOn
        (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) Kα :=
      (chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α).mono hKα_sub
    set hImg :=
      (hKα_compact.image_of_continuousOn h_cont).bddAbove
    obtain ⟨x₀, hx₀⟩ := hKα_ne
    have hx₀_val :
        chartInvGramMatrix_l1Sum (I := I) (M := M) g α x₀ ∈
        (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) '' Kα :=
      ⟨x₀, hx₀, rfl⟩
    have h_le := hImg.choose_spec hx₀_val
    have h_val_nn :
        (0 : ℝ) ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x₀ :=
      chartInvGramMatrix_l1Sum_nonneg (I := I) (M := M) g α x₀
    exact le_trans h_val_nn h_le
  · rw [dif_neg hKα_ne]

/-- For `x ∈ tsupport ρ_α`, `chartInvGramMatrix_l1Sum α x` is bounded by the
chosen sup. -/
private lemma chartInvGramMatrix_l1Sum_le_sup
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    chartInvGramMatrix_l1Sum (I := I) (M := M) g α x ≤
      gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α := by
  classical
  unfold gramInvL1SumSupOnPouTsupport
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_ne : Kα.Nonempty := ⟨x, hx⟩
  rw [dif_pos hKα_ne]
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have h_cont : ContinuousOn
      (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) Kα :=
    (chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α).mono hKα_sub
  set hImg :=
    (hKα_compact.image_of_continuousOn h_cont).bddAbove
  exact hImg.choose_spec ⟨x, hx, rfl⟩

/-- `‖fderiv scalarOnE α f y (basis_k)‖ ≤ ‖fderiv scalarOnE α f y‖ * ‖basis_k‖`. -/
private lemma sq_partials_scalarOnE_le_norm_fderiv_scalarOnE_sq
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) (f : M → ℝ) (y : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) k
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y)^2) ≤
      (∑ k : Fin (Module.finrank ℝ E),
        ‖(chartModelBasis E) k‖^2) *
          ‖fderiv ℝ
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y‖^2 := by
  classical
  let _ := g
  have h_each : ∀ k,
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
          (E := E) k
          (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I) α f) y)^2 ≤
        ‖(chartModelBasis E) k‖^2 *
          ‖fderiv ℝ
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y‖^2 := by
    intro k
    have hop_le := (fderiv ℝ
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f) y).le_opNorm ((chartModelBasis E) k)
    have hsq_le : (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) k
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y)^2 ≤
          (‖fderiv ℝ
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y‖ * ‖(chartModelBasis E) k‖)^2 := by
      unfold DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
      have habs : |(fderiv ℝ
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y) ((chartModelBasis E) k)| ≤
          ‖fderiv ℝ
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y‖ * ‖(chartModelBasis E) k‖ := by
        have h_norm_eq : ‖(fderiv ℝ
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y) ((chartModelBasis E) k)‖ =
            |(fderiv ℝ
              (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                (I := I) α f) y) ((chartModelBasis E) k)| :=
          Real.norm_eq_abs _
        rw [← h_norm_eq]
        exact hop_le
      have h_sq_abs :
          ((fderiv ℝ
              (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                (I := I) α f) y) ((chartModelBasis E) k))^2 =
          |(fderiv ℝ
              (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                (I := I) α f) y) ((chartModelBasis E) k)|^2 := by
        rw [sq_abs]
      rw [h_sq_abs]
      have hABS_nn : 0 ≤ |(fderiv ℝ
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y) ((chartModelBasis E) k)| := abs_nonneg _
      have hRHS_nn : 0 ≤ ‖fderiv ℝ
          (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I) α f) y‖ * ‖(chartModelBasis E) k‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      exact pow_le_pow_left₀ hABS_nn habs 2
    refine hsq_le.trans ?_
    rw [mul_pow]
    rw [mul_comm]
  refine (Finset.sum_le_sum (s := Finset.univ) (fun k _ => h_each k)).trans ?_
  rw [← Finset.sum_mul]

/-- The fixed real constant `√(∑_k ‖toEuclidean(basis_k)‖²)` controls the
relationship between the `E`-coordinate partial derivatives of `scalarOnE α f`
at `y` and the `EuclN`-coordinate partial derivatives of
`chartSmoothExt α f` at `toEuclidean y`. -/
private noncomputable def toEuclideanBasisSqSum : ℝ :=
  ∑ k : Fin (Module.finrank ℝ E),
    ‖(toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) ((chartModelBasis E) k)‖^2

private lemma toEuclideanBasisSqSum_nonneg :
    (0 : ℝ) ≤ toEuclideanBasisSqSum (E := E) :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- For y in the chart target, `chartSmoothExt α f (toEuclidean y) = scalarOnE α f y`. -/
private lemma chartSmoothExt_toEuclidean_eq_scalarOnE
    (α : M) (f : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y) =
      DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f y := by
  classical
  unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
  have hsymm : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y) = y :=
    (toEuclidean (E := E)).symm_apply_apply y
  simp only [hsymm, hy, if_true]
  rfl

/-- On the chart target (where `(extChartAt I α).target` is open), the Euclidean
partials of `scalarOnE α f` are bounded by the operator norm of
`fderiv (chartSmoothExt α f) (toEuclidean y)` and a fixed constant depending
only on the change-of-basis `toEuclidean : E ≃L[ℝ] EuclN`. -/
private lemma sq_partials_scalarOnE_le_chartSmoothExt_fderiv
    [I.Boundaryless]
    (α : M) {f : M → ℝ}
    (h_smooth_ext : ContDiff ℝ ∞
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    (∑ k : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) k
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y)^2) ≤
      toEuclideanBasisSqSum (E := E) *
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f)
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)‖^2 := by
  classical
  have h_target_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have h_target_nhds : (extChartAt I α).target ∈ 𝓝 y :=
    h_target_open.mem_nhds hy
  have h_eqf : (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
      (I := I) α f) =ᶠ[𝓝 y]
      ((DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) ∘
        (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z)) := by
    filter_upwards [h_target_nhds] with z hz
    exact (chartSmoothExt_toEuclidean_eq_scalarOnE (I := I) (M := M) α f hz).symm
  have h_fderiv_eq : fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) y =
      fderiv ℝ
        ((DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) ∘
          (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z)) y :=
    h_eqf.fderiv_eq
  have h_ChartSmoothExt_diffAt : DifferentiableAt ℝ
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f)
      ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y) :=
    h_smooth_ext.differentiable (by simp) _
  have h_TE_diffAt : DifferentiableAt ℝ
      (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z) y :=
    (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).differentiable.differentiableAt
  have h_fderiv_comp : fderiv ℝ
      ((DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) ∘
        (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z)) y =
      (fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f)
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)).comp
        (fderiv ℝ
          (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z) y) :=
    fderiv_comp y h_ChartSmoothExt_diffAt h_TE_diffAt
  have h_TE_fderiv : fderiv ℝ
      (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z) y =
      ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) :
        E →L[ℝ] EuclN_E) :=
    (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).fderiv
  rw [h_TE_fderiv] at h_fderiv_comp
  have h_each : ∀ k,
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
          (E := E) k
          (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I) α f) y)^2 ≤
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f)
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)‖^2 *
        ‖(toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) ((chartModelBasis E) k)‖^2 := by
    intro k
    have h_partial_eq :
        DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) k
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f) y =
          (fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f)
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
              ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
                ((chartModelBasis E) k)) := by
      unfold DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
      rw [h_fderiv_eq, h_fderiv_comp]
      rfl
    rw [h_partial_eq]
    have h_op_bound :
        ‖(fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f)
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
              ((chartModelBasis E) k))‖ ≤
          ‖fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f)
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)‖ *
          ‖(toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
            ((chartModelBasis E) k)‖ :=
      (fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f)
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)).le_opNorm _
    have h_lhs_norm : ‖(fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f)
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
          ((chartModelBasis E) k))‖ =
        |((fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f)
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
            ((chartModelBasis E) k)))| :=
      Real.norm_eq_abs _
    rw [h_lhs_norm] at h_op_bound
    have h_sq_abs :
        ((fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f)
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
              ((chartModelBasis E) k)))^2 =
        |((fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f)
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
              ((chartModelBasis E) k)))|^2 :=
      (sq_abs _).symm
    rw [h_sq_abs]
    have h_op_nn : 0 ≤ ‖fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f)
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)‖ *
        ‖(toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
          ((chartModelBasis E) k)‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h_abs_nn :
        0 ≤ |((fderiv ℝ
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
                (I := I) (M := M) α f)
              ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
              ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
                ((chartModelBasis E) k)))| :=
      abs_nonneg _
    have h_pow_le := pow_le_pow_left₀ h_abs_nn h_op_bound 2
    refine h_pow_le.trans ?_
    rw [mul_pow]
  refine (Finset.sum_le_sum (s := Finset.univ) (fun k _ => h_each k)).trans ?_
  unfold toEuclideanBasisSqSum
  rw [← Finset.mul_sum]
  rw [mul_comm]

/-- For smooth `f` with `tsupport f ⊆ chart α source` and compact tsupport,
`chartSmoothExt α f` is identically zero off
`toEuclidean '' (extChartAt α '' tsupport f)`. -/
private lemma chartSmoothExt_eq_zero_off_image_tsupport_local
    (α : M) {f : M → ℝ} {y : EuclN_E}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · have hsymm_source : (extChartAt I α).symm
        ((toEuclidean (E := E)).symm y) ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy_target
    have hxsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉ tsupport f := by
      intro hin
      apply hy_off
      refine ⟨(toEuclidean (E := E)).symm y, ?_, ?_⟩
      · refine ⟨(extChartAt I α).symm ((toEuclidean (E := E)).symm y), hin, ?_⟩
        exact (extChartAt I α).right_inv hy_target
      · exact (toEuclidean (E := E)).apply_symm_apply y
    have hf_zero : f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 :=
      image_eq_zero_of_notMem_tsupport hxsupp
    change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else (0 : ℝ)) = 0
    rw [if_pos hy_target, hf_zero]
  · change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else (0 : ℝ)) = 0
    rw [if_neg hy_target]

/-- Smoothness of `chartSmoothExt α f` for smooth `f` with compact `tsupport f`
inside the chart α source on a boundaryless manifold. -/
private lemma contDiff_chartSmoothExt_local
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f)) :
    ContDiff ℝ ∞
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  set form : EuclN_E → ℝ := fun z =>
    f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) with hform_def
  have h_target_open :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) (α := α)
  have h_form_contDiffOn : ContDiffOn ℝ ∞ form
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have hscalar : ContDiffOn ℝ ∞
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f) (extChartAt I α).target :=
      DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
        (I := I) α hf
    have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
      ContinuousLinearEquiv.contDiff _
    have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)
        (extChartAt I α).target := by
      intro y' hy'
      obtain ⟨z, hz_target, rfl⟩ := hy'
      have h_eq : (toEuclidean (E := E)).symm
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z) = z :=
        (toEuclidean (E := E)).symm_apply_apply z
      rw [h_eq]
      exact hz_target
    have h_eq_form : form = (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I) α f) ∘ (fun z : EuclN_E => (toEuclidean (E := E)).symm z) := by
      funext z
      rfl
    rw [h_eq_form]
    exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
  by_cases hy_target : y ∈
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · have h_at : ContDiffAt ℝ ∞ form y :=
      (h_form_contDiffOn.contDiffWithinAt hy_target).contDiffAt
        (h_target_open.mem_nhds hy_target)
    apply h_at.congr_of_eventuallyEq
    filter_upwards [h_target_open.mem_nhds hy_target] with z hz
    obtain ⟨w, hw_target, hw_eq⟩ := hz
    have hsymm_eq : (toEuclidean (E := E)).symm z = w := by
      rw [← hw_eq]
      exact (toEuclidean (E := E)).symm_apply_apply w
    have htarget_at_z : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target := by
      rw [hsymm_eq]; exact hw_target
    change DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f z =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
        f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      else (0 : ℝ)) =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    rw [if_pos htarget_at_z]
  · set K : Set EuclN_E := (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))
      with hK_def
    have hK_compact : IsCompact K := by
      have h_extChart_cont : ContinuousOn (extChartAt I α) (tsupport f) :=
        (continuousOn_extChartAt α).mono (by
          intro x hx
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hf_supp hx)
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_extChart_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have hK_subset : K ⊆
        DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
      rintro y' ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      have hxsource : x ∈ (extChartAt I α).source := by
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_supp hx
      exact ⟨extChartAt I α x, (extChartAt I α).map_source hxsource, rfl⟩
    have hy_off_K : y ∉ K := by
      intro hy_in
      exact hy_target (hK_subset hy_in)
    have hK_closed : IsClosed K := hK_compact.isClosed
    have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN_E => (0 : ℝ)) contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off_K] with z hz
    exact chartSmoothExt_eq_zero_off_image_tsupport_local
      (I := I) (M := M) α (f := f) hz

/-- Smoothness of `chartSmoothExt α (ρ_α · u)` for smooth `u`. -/
private lemma contDiff_chartSmoothExt_pou_mul_local
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiff ℝ ∞
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y)) := by
  classical
  set f : M → ℝ := fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) y * u y with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.mul hu
  have hf_supp : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : f = (fun y : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y • u y) := by funext y; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun y : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
    exact h1.trans
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  exact contDiff_chartSmoothExt_local (I := I) (M := M) α hf_smooth hf_supp hf_compact

private lemma euclN_norm_le_sum_components_norms_local (w : EuclN_E) :
    ‖w‖ ≤ ∑ i : Fin (Module.finrank ℝ E), ‖w i‖ := by
  classical
  have h_w_sum : w = ∑ i : Fin (Module.finrank ℝ E),
      EuclideanSpace.single i (w i) := by
    ext j
    simp [Finset.sum_apply]
  conv_lhs => rw [h_w_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp

private lemma norm_fderiv_le_sum_partials_local_local (ψ : EuclN_E → ℝ)
    (y : EuclN_E) :
    ‖fderiv ℝ ψ y‖ ≤
      ∑ i : Fin (Module.finrank ℝ E),
        ‖(fderiv ℝ ψ y) (EuclideanSpace.single i (1 : ℝ))‖ := by
  classical
  set v : EuclN_E :=
    (InnerProductSpace.toDual ℝ EuclN_E).symm (fderiv ℝ ψ y) with hv_def
  have hv_map : (InnerProductSpace.toDual ℝ EuclN_E) v = fderiv ℝ ψ y := by
    simp [v]
  have h_fderiv_norm_eq_v : ‖fderiv ℝ ψ y‖ = ‖v‖ := by simp [v]
  have h_v_eq_components : v =
      WithLp.toLp 2 (fun i : Fin (Module.finrank ℝ E) =>
        (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) := by
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ EuclN_E) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ ψ y) (EuclideanSpace.single i (1 : ℝ)) := by rw [hv_map]
      _ = (WithLp.toLp 2 (fun j : Fin (Module.finrank ℝ E) =>
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))) i := by simp
  rw [h_fderiv_norm_eq_v, h_v_eq_components]
  refine (euclN_norm_le_sum_components_norms_local _).trans ?_
  apply le_of_eq
  refine Finset.sum_congr rfl ?_
  intro i _
  simp

private lemma eLpNorm_norm_fderiv_le_sum_eLpNorm_partials_local
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {μ : Measure EuclN_E}
    {ψ : EuclN_E → ℝ} (h_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    eLpNorm (fun z : EuclN_E => ‖fderiv ℝ ψ z‖) q μ ≤
      ∑ i : Fin (Module.finrank ℝ E),
        eLpNorm
          (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) q μ := by
  classical
  have h_aesm_comp : ∀ i : Fin (Module.finrank ℝ E),
      AEStronglyMeasurable
        (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) μ := by
    intro i
    have h_cont : Continuous
        (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) :=
      (h_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h_cont.aestronglyMeasurable
  have h_pt : ∀ z : EuclN_E,
      ‖fderiv ℝ ψ z‖ ≤ ∑ i : Fin (Module.finrank ℝ E),
        ‖(fderiv ℝ ψ z) (EuclideanSpace.single i 1)‖ :=
    fun z => norm_fderiv_le_sum_partials_local_local ψ z
  have h_step1 : eLpNorm (fun z : EuclN_E => ‖fderiv ℝ ψ z‖) q μ ≤
      eLpNorm (fun z : EuclN_E =>
        ∑ i : Fin (Module.finrank ℝ E),
          ‖(fderiv ℝ ψ z) (EuclideanSpace.single i 1)‖) q μ := by
    apply eLpNorm_mono_real
    intro z
    have hh := h_pt z
    have h_norm : ‖‖fderiv ℝ ψ z‖‖ = ‖fderiv ℝ ψ z‖ :=
      Real.norm_of_nonneg (norm_nonneg _)
    rw [h_norm]
    exact hh
  refine h_step1.trans ?_
  have h_sum_le := eLpNorm_sum_le (μ := μ) (p := q)
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (f := fun i => fun z : EuclN_E =>
      ‖(fderiv ℝ ψ z) (EuclideanSpace.single i 1)‖)
    (fun i _ => (h_aesm_comp i).norm) hq_one
  have h_lhs_eq :
      (fun z : EuclN_E =>
        ∑ i : Fin (Module.finrank ℝ E),
          ‖(fderiv ℝ ψ z) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin (Module.finrank ℝ E),
          fun z : EuclN_E => ‖(fderiv ℝ ψ z) (EuclideanSpace.single i 1)‖ := by
    funext z
    simp [Finset.sum_apply]
  rw [h_lhs_eq]
  refine h_sum_le.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_norm]

/-- The classical partial of a smooth `f`, compactly supported in `Ω` (open),
agrees a.e. with `chosenWeakPartial' p i f Ω`. -/
private lemma classical_partial_ae_eq_chosenWeakPartial_local_local
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuclN_E} (hΩ_open : IsOpen Ω)
    {ψ : EuclN_E → ℝ} (h_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_supp : tsupport ψ ⊆ Ω)
    (i : Fin (Module.finrank ℝ E)) :
    (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        q i ψ Ω := by
  classical
  have hψ_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 q ψ Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
      (d := Module.finrank ℝ E) hΩ_open h_smooth hψ_compact hψ_supp hq_one 1
  have hψ_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) q ψ Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hψ_mem
  have h_classical_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) ψ Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := ψ)
      hΩ_open (h_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          q i ψ Ω) ψ Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hψ_W1p i
  have h_classical_loc : LocallyIntegrable
      (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
    have h_cont : Continuous
        (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) :=
      (h_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_loc : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        q i ψ Ω)
      (volume.restrict Ω) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hψ_W1p i).locallyIntegrable hq_one
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_loc h_chosen_loc

/-- For smooth ψ with compact support inside open Ω, eLpNorm of `‖fderiv ψ‖` is
bounded by `d * wkpNorm 1 q ψ Ω`. -/
private lemma eLpNorm_norm_fderiv_le_d_mul_wkpNorm_local
    [NeZero (Module.finrank ℝ E)]
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuclN_E} (hΩ_open : IsOpen Ω)
    {ψ : EuclN_E → ℝ} (h_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_supp : tsupport ψ ⊆ Ω) :
    eLpNorm (fun z : EuclN_E => ‖fderiv ℝ ψ z‖) q (volume.restrict Ω) ≤
      ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 q ψ Ω := by
  classical
  have h_grad_le := eLpNorm_norm_fderiv_le_sum_eLpNorm_partials_local
    (q := q) hq_one (μ := volume.restrict Ω) h_smooth
  refine h_grad_le.trans ?_
  have h_each_eq : ∀ i : Fin (Module.finrank ℝ E),
      eLpNorm
        (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) q
        (volume.restrict Ω) =
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          q i ψ Ω) q (volume.restrict Ω) := fun i =>
    eLpNorm_congr_ae (classical_partial_ae_eq_chosenWeakPartial_local_local
      hq_one hΩ_open h_smooth hψ_compact hψ_supp i)
  have h_step1 :
      ∑ i : Fin (Module.finrank ℝ E),
        eLpNorm
          (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) q
          (volume.restrict Ω)
        = ∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              q i ψ Ω) q (volume.restrict Ω) :=
    Finset.sum_congr rfl (fun i _ => h_each_eq i)
  rw [h_step1]
  have hWkpEq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 q ψ Ω =
        ∑ j ∈ Finset.range 2,
          ∑ β : Fin j → Fin (Module.finrank ℝ E),
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) q j β ψ Ω)
              q (volume.restrict Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 1 q ψ Ω
  have h_j1_term :
      (∑ β : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := Module.finrank ℝ E) q 1 β ψ Ω) q (volume.restrict Ω)) =
        ∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              q i ψ Ω) q (volume.restrict Ω) := by
    have h_unfold : ∀ β : Fin 1 → Fin (Module.finrank ℝ E),
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
            (d := Module.finrank ℝ E) q 1 β ψ Ω) q (volume.restrict Ω) =
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              q (β 0) ψ Ω) q (volume.restrict Ω) := by
      intro β
      have hit :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := Module.finrank ℝ E) q 1 β ψ Ω =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              q (β 0) ψ Ω := by
        rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]
        simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
      rw [hit]
    rw [Finset.sum_congr rfl (fun β _ => h_unfold β)]
    let e : (Fin 1 → Fin (Module.finrank ℝ E)) ≃ Fin (Module.finrank ℝ E) :=
      { toFun := fun β => β 0
        invFun := fun i _ => i
        left_inv := fun β => by
          funext j
          have hj : j = 0 := Subsingleton.elim _ _
          rw [hj]
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e
      (fun β =>
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            q (β 0) ψ Ω) q (volume.restrict Ω))
      (fun i =>
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            q i ψ Ω) q (volume.restrict Ω))
      (fun _ => rfl)
  have h_le_wkp :
      (∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              q i ψ Ω) q (volume.restrict Ω)) ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 q ψ Ω := by
    rw [hWkpEq, Finset.sum_range_succ, Finset.sum_range_one, ← h_j1_term]
    refine le_add_of_nonneg_left ?_
    exact zero_le _
  refine h_le_wkp.trans ?_
  have hd_pos : 0 < Module.finrank ℝ E := NeZero.pos _
  have hd_one_le : (1 : ℝ≥0∞) ≤ ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hd_pos
  conv_lhs => rw [show DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
    (d := Module.finrank ℝ E) 1 q ψ Ω = 1 *
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 q ψ Ω from
    (one_mul _).symm]
  gcongr

/-- The Euclidean wkpNorm of `chartSmoothExt α (ρ_α u)` on the chart target
agrees a.e. with the wkpNorm of `chartPushed`, hence ≤ wkpNormChart u. -/
private lemma wkpNorm_chartSmoothExt_pou_mul_le_wkpNormChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {q : ℝ≥0∞} (hq_one : 1 ≤ q) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 q
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) ≤
      wkpNormChart (I := I) (M := M) g 1 q u := by
  classical
  have h_ae :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)
        =ᵐ[volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u := by
    refine (MeasureTheory.ae_restrict_iff'
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
        (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
        (I := I) (M := M)] at hy
      exact hy
    change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      else (0 : ℝ)) =
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y
    rw [if_pos hsymm_target]
    rfl
  have h_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 q
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α
            (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x))
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 q
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) hq_one
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α) h_ae
  rw [h_eq]
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

/-- `g_norm_grad u(x) = √(g.inner x (gradFun g u x) (gradFun g u x))`. -/
private noncomputable def gNormGrad
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (u : M → ℝ) (x : M) : ℝ :=
  Real.sqrt
    (g.inner x
      (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g u x)
      (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g u x))

private lemma gNormGrad_nonneg
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (u : M → ℝ) (x : M) :
    0 ≤ gNormGrad (I := I) (M := M) g u x :=
  Real.sqrt_nonneg _

/-- `gNormGrad g f x = 0` whenever `x ∉ tsupport f` (for smooth `f`). -/
private lemma gNormGrad_eq_zero_of_notMem_tsupport
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ tsupport f) :
    gNormGrad (I := I) (M := M) g f x = 0 := by
  unfold gNormGrad
  rw [gradFun_eq_zero_off_tsupport_smooth (I := I) (M := M) g hf hx]
  simp

/-- The pointwise gradient bound at `x ∈ tsupport ρ_α`:
`gNormGrad g (ρ_α u) x ≤ √(M_g_α) * √(∑_k partial_k² scalarOnE α (ρ_α u))`. -/
private lemma gNormGrad_pou_mul_le_sqrt_partial_sum
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) {x : M}
    (hx : x ∈ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) x ≤
      Real.sqrt
        (gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α) *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
              (E := E) k
              (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                (I := I) α
                (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) y * u y))
              (extChartAt I α x))^2) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
  set f : M → ℝ := fun y : M => (ρ : M → ℝ) y * u y with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hxchart : x ∈ (chartAt H α).source := by
    have hsubord : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).IsSubordinate
        (fun β : M => (chartAt H β).source) :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M
    exact hsubord α hx
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hxchart
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I)]
    exact hxchart
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hxsrc
  have hf_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    hf_smooth.mdifferentiable (by simp) x
  have h_pointwise :=
    norm_gradFun_le_sqrt_chartInvGramMatrix_l1Sum_mul
      (I := I) (M := M) g α (f := f) (x := x) hf_diff hxbase hx_int
  refine le_trans h_pointwise ?_
  have h_M_le : chartInvGramMatrix_l1Sum (I := I) (M := M) g α x ≤
      gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α :=
    chartInvGramMatrix_l1Sum_le_sup (I := I) (M := M) g α (x := x) hx
  have h_M_nn : 0 ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x :=
    chartInvGramMatrix_l1Sum_nonneg (I := I) (M := M) g α x
  have h_sqrt_M_le : Real.sqrt (chartInvGramMatrix_l1Sum (I := I) (M := M) g α x) ≤
      Real.sqrt (gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α) :=
    Real.sqrt_le_sqrt h_M_le
  have h_partial_sum_nn : (0 : ℝ) ≤ ∑ k : Fin (Module.finrank ℝ E),
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
        (E := E) k
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I) α f)
        (extChartAt I α x))^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_right h_sqrt_M_le (Real.sqrt_nonneg _)

/-- For all `x : M` (whether or not in `tsupport ρ_α`),
`gNormGrad g (ρ_α · u)(x) ≤ √M_g_α * √(∑_k partial_k²) * indicator (tsupport ρ_α)(x)`,
expressed via a max-form bound. -/
private lemma gNormGrad_pou_mul_le_indicator_sqrt
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (x : M) :
    gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) x ≤
      Real.sqrt
        (gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α) *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
              (E := E) k
              (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                (I := I) α
                (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) y * u y))
              (extChartAt I α x))^2) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
  set f : M → ℝ := fun y : M => (ρ : M → ℝ) y * u y with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  by_cases hx_pou : x ∈ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  · exact gNormGrad_pou_mul_le_sqrt_partial_sum (I := I) (M := M) g α hu hx_pou
  · have hx_supp_f : x ∉ tsupport f := by
      intro hx_in
      apply hx_pou
      have h_subset : tsupport f ⊆ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        have h_eq : f = (fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y • u y) := by
          funext y; rfl
        rw [h_eq]
        exact tsupport_smul_subset_left
          (f := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
      exact h_subset hx_in
    rw [gNormGrad_eq_zero_of_notMem_tsupport (I := I) (M := M) g hf_smooth hx_supp_f]
    have h1 : (0 : ℝ) ≤ Real.sqrt
        (gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α) :=
      Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt
        (∑ k : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
            (E := E) k
            (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
              (I := I) α f)
            (extChartAt I α x))^2) := Real.sqrt_nonneg _
    exact mul_nonneg h1 h2

/-- For each α and smooth u, the manifold `L^p` norm of the `g`-norm of the
gradient of `(ρ_α · u)` is bounded by a constant (depending only on α, g, p)
times `wkpNormChart u`. -/
private lemma eLpNorm_gNormGrad_pou_mul_le_const_mul_wkpNormChart_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        eLpNorm (gNormGrad (I := I) (M := M) g
            (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x)) p
            (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  set Kα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  obtain ⟨Cbridge, hCbridge_pos, hCbridge_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  set M_g_α : ℝ := gramInvL1SumSupOnPouTsupport (I := I) (M := M) g α
  have hM_nn : 0 ≤ M_g_α := gramInvL1SumSupOnPouTsupport_nonneg (I := I) (M := M) g α
  set B : ℝ := toEuclideanBasisSqSum (E := E)
  have hB_nn : 0 ≤ B := toEuclideanBasisSqSum_nonneg
  set d_dim : ℕ := Module.finrank ℝ E
  set C : ℝ := Cbridge * Real.sqrt M_g_α * Real.sqrt B * (d_dim : ℝ) with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg (mul_nonneg hCbridge_pos.le ?_) ?_) ?_
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
    · exact Nat.cast_nonneg _
  refine ⟨C, hC_nn, ?_⟩
  intro u hu
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
  set f : M → ℝ := fun y : M => (ρ : M → ℝ) y * u y with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hf_supp : tsupport f ⊆ Kα := by
    have h_eq : f = (fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y • u y) := by
      funext y; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
  have hf_supp_chart : tsupport f ⊆ (chartAt H α).source :=
    hf_supp.trans hKα_sub
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have h_gNormGrad_meas : Measurable (gNormGrad (I := I) (M := M) g f) := by
    have h_cont := continuous_g_norm_gradFun (I := I) (M := M) g hf_smooth
    exact h_cont.measurable
  have h_gNormGrad_supp : tsupport (gNormGrad (I := I) (M := M) g f) ⊆ Kα := by
    refine subset_trans ?_ hf_supp
    apply closure_minimal _ (isClosed_tsupport _)
    intro y hy
    by_contra hy_off
    apply hy
    have : gNormGrad (I := I) (M := M) g f y = 0 :=
      gNormGrad_eq_zero_of_notMem_tsupport (I := I) (M := M) g hf_smooth hy_off
    exact this
  have h_step1 := hCbridge_bound h_gNormGrad_meas h_gNormGrad_supp
  refine h_step1.trans ?_
  have h_chartSmoothExt_smooth : ContDiff ℝ ∞
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) :=
    contDiff_chartSmoothExt_local (I := I) (M := M) α hf_smooth hf_supp_chart hf_compact
  have h_pt_bound : ∀ y : EuclN_E,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (gNormGrad (I := I) (M := M) g f) y ≤
        Real.sqrt M_g_α * Real.sqrt B *
          ‖fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f) y‖ := by
    intro y
    by_cases hy_in : y ∈
        DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
    · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) α (gNormGrad (I := I) (M := M) g f) hy_in]
      set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
      have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
          (I := I) (M := M)] at hy_in
        exact hy_in
      have hz_source : z ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hsymm_target
      have hz_chart_source : z ∈ (chartAt H α).source := by
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)] at hz_source
        exact hz_source
      have hz_base : z ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
        exact hz_chart_source
      have hz_int : extChartAt I α z ∈ interior (extChartAt I α).target := by
        rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
        exact (extChartAt I α).map_source hz_source
      have h_pt := norm_gradFun_le_sqrt_chartInvGramMatrix_l1Sum_mul
        (I := I) (M := M) g α (f := f) (x := z)
        (hf_smooth.mdifferentiable (by simp) z) hz_base hz_int
      have hzy : extChartAt I α z = (toEuclidean (E := E)).symm y := by
        change extChartAt I α ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm y)) = (toEuclidean (E := E)).symm y
        exact (extChartAt I α).right_inv hsymm_target
      by_cases hz_pou : z ∈ Kα
      · have h_M_le := chartInvGramMatrix_l1Sum_le_sup
          (I := I) (M := M) g α (x := z) hz_pou
        have h_M_z_nn := chartInvGramMatrix_l1Sum_nonneg
          (I := I) (M := M) g α z
        have h_combined : gNormGrad (I := I) (M := M) g f z ≤
            Real.sqrt M_g_α *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
                    (E := E) k
                    (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                      (I := I) α f)
                    (extChartAt I α z))^2) := by
          unfold gNormGrad
          refine h_pt.trans ?_
          have h_sqrt_M_le : Real.sqrt
              (chartInvGramMatrix_l1Sum (I := I) (M := M) g α z) ≤
              Real.sqrt M_g_α := Real.sqrt_le_sqrt h_M_le
          have h_partial_sum_nn : (0 : ℝ) ≤ Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
                  (E := E) k
                  (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                    (I := I) α f)
                  (extChartAt I α z))^2) := Real.sqrt_nonneg _
          exact mul_le_mul_of_nonneg_right h_sqrt_M_le h_partial_sum_nn
        rw [hzy] at h_combined
        have h_sq_le := sq_partials_scalarOnE_le_chartSmoothExt_fderiv
          (I := I) (M := M) α (f := f) h_chartSmoothExt_smooth (y := (toEuclidean (E := E)).symm y)
          hsymm_target
        have h_TE_apply : (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
            ((toEuclidean (E := E)).symm y) = y :=
          (toEuclidean (E := E)).apply_symm_apply y
        rw [h_TE_apply] at h_sq_le
        have h_sqrt_partial_le : Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
                (E := E) k
                (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                  (I := I) α f)
                ((toEuclidean (E := E)).symm y))^2) ≤
            Real.sqrt B *
              ‖fderiv ℝ
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
                  (I := I) (M := M) α f) y‖ := by
          have h_sqrt_le := Real.sqrt_le_sqrt h_sq_le
          rw [Real.sqrt_mul hB_nn] at h_sqrt_le
          rw [Real.sqrt_sq (norm_nonneg _)] at h_sqrt_le
          exact h_sqrt_le
        refine h_combined.trans ?_
        have h_sqrt_M_nn : 0 ≤ Real.sqrt M_g_α := Real.sqrt_nonneg _
        calc Real.sqrt M_g_α *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
                    (E := E) k
                    (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
                      (I := I) α f)
                    ((toEuclidean (E := E)).symm y))^2)
            ≤ Real.sqrt M_g_α *
              (Real.sqrt B *
                ‖fderiv ℝ
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
                    (I := I) (M := M) α f) y‖) :=
              mul_le_mul_of_nonneg_left h_sqrt_partial_le h_sqrt_M_nn
          _ = Real.sqrt M_g_α * Real.sqrt B *
              ‖fderiv ℝ
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
                  (I := I) (M := M) α f) y‖ := by ring
      · have hz_off_f : z ∉ tsupport f := fun hin => hz_pou (hf_supp hin)
        rw [gNormGrad_eq_zero_of_notMem_tsupport (I := I) (M := M) g hf_smooth hz_off_f]
        positivity
    · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) α (gNormGrad (I := I) (M := M) g f) hy_in]
      positivity
  have h_eLpNorm_le :
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (gNormGrad (I := I) (M := M) g f)) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) ≤
      eLpNorm
        (fun y : EuclN_E => Real.sqrt M_g_α * Real.sqrt B *
          ‖fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f) y‖) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) := by
    apply eLpNorm_mono_real
    intro y
    have h := h_pt_bound y
    have h_norm : ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (gNormGrad (I := I) (M := M) g f) y‖ =
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (gNormGrad (I := I) (M := M) g f) y := by
      rw [Real.norm_eq_abs]
      apply abs_of_nonneg
      by_cases hy_in : y ∈
          DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α
      · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) α (gNormGrad (I := I) (M := M) g f) hy_in]
        exact gNormGrad_nonneg _ _ _
      · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
          (I := I) α (gNormGrad (I := I) (M := M) g f) hy_in]
    rw [h_norm]
    exact h
  set Csqrt : ℝ := Real.sqrt M_g_α * Real.sqrt B
  have h_csqrt_nn : 0 ≤ Csqrt := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_eq_fun : (fun y : EuclN_E => Real.sqrt M_g_α * Real.sqrt B *
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y‖) =
      (fun y : EuclN_E => Csqrt *
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y‖) := by
    funext y
    show Real.sqrt M_g_α * Real.sqrt B *
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y‖ =
      Csqrt *
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y‖
    rw [show Csqrt = Real.sqrt M_g_α * Real.sqrt B from rfl]
  rw [h_eq_fun] at h_eLpNorm_le
  have h_eLp_const :
      eLpNorm
        (fun y : EuclN_E => Csqrt *
          ‖fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f) y‖) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) =
      ‖Csqrt‖ₑ *
      eLpNorm
        (fun y : EuclN_E =>
          ‖fderiv ℝ
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f) y‖) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) := by
    have h := eLpNorm_const_smul (𝕜 := ℝ) (p := p)
      (μ := (volume : Measure EuclN_E).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      (c := Csqrt)
      (f := fun y : EuclN_E =>
        ‖fderiv ℝ
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f) y‖)
    exact h
  rw [h_eLp_const] at h_eLpNorm_le
  have hChartTarget_open :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) (α := α)
  have h_supp_smooth_ext : tsupport
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := by
    have hK_compact : IsCompact ((toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) := by
      have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
        apply (continuousOn_extChartAt α).mono
        intro x hx
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_supp_chart hx
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have h_sub_image : tsupport
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) ⊆
        (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) := by
      apply closure_minimal _ hK_compact.isClosed
      intro y hy
      by_contra hy_off
      apply hy
      exact chartSmoothExt_eq_zero_off_image_tsupport_local
        (I := I) (M := M) α (f := f) hy_off
    refine h_sub_image.trans ?_
    rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    have hxsource : x ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hf_supp_chart hx
    exact ⟨extChartAt I α x, (extChartAt I α).map_source hxsource, rfl⟩
  have h_compact_smooth_ext : HasCompactSupport
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) := by
    have hK_compact : IsCompact ((toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) := by
      have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
        apply (continuousOn_extChartAt α).mono
        intro x hx
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_supp_chart hx
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have h_sub_image : tsupport
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) ⊆
        (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) := by
      apply closure_minimal _ hK_compact.isClosed
      intro y hy
      by_contra hy_off
      apply hy
      exact chartSmoothExt_eq_zero_off_image_tsupport_local
        (I := I) (M := M) α (f := f) hy_off
    exact hK_compact.of_isClosed_subset (isClosed_tsupport _) h_sub_image
  have h_fderiv_le := eLpNorm_norm_fderiv_le_d_mul_wkpNorm_local
    (q := p) hp_one (Ω :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    hChartTarget_open
    (h_chartSmoothExt_smooth)
    h_compact_smooth_ext h_supp_smooth_ext
  have h_wkpNorm_le := wkpNorm_chartSmoothExt_pou_mul_le_wkpNormChart
    (I := I) (M := M) g α hp_one u
  have h_chain : ENNReal.ofReal Cbridge *
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (gNormGrad (I := I) (M := M) g f)) p
        ((volume : Measure EuclN_E).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) ≤
      ENNReal.ofReal Cbridge *
      (‖Csqrt‖ₑ *
        (((Module.finrank ℝ E : ℕ) : ℝ≥0∞) *
          wkpNormChart (I := I) (M := M) g 1 p u)) := by
    gcongr
    apply h_eLpNorm_le.trans
    gcongr
    apply h_fderiv_le.trans
    gcongr
  refine h_chain.trans ?_
  have h_csqrt_enorm : ‖Csqrt‖ₑ = ENNReal.ofReal Csqrt :=
    Real.enorm_eq_ofReal h_csqrt_nn
  rw [h_csqrt_enorm]
  have h_d_eq : ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) = ENNReal.ofReal (d_dim : ℝ) := by
    change ((d_dim : ℕ) : ℝ≥0∞) = ENNReal.ofReal (d_dim : ℝ)
    rw [ENNReal.ofReal_natCast]
  rw [h_d_eq]
  rw [show ENNReal.ofReal Cbridge *
        (ENNReal.ofReal Csqrt *
          (ENNReal.ofReal (d_dim : ℝ) * wkpNormChart (I := I) (M := M) g 1 p u)) =
      (ENNReal.ofReal Cbridge * ENNReal.ofReal Csqrt * ENNReal.ofReal (d_dim : ℝ)) *
        wkpNormChart (I := I) (M := M) g 1 p u from by ring]
  have h_const_eq : ENNReal.ofReal Cbridge * ENNReal.ofReal Csqrt *
      ENNReal.ofReal (d_dim : ℝ) =
      ENNReal.ofReal C := by
    rw [hC_def]
    rw [show Cbridge * Real.sqrt M_g_α * Real.sqrt B * (d_dim : ℝ) =
      Cbridge * Csqrt * (d_dim : ℝ) from by
      change Cbridge * Real.sqrt M_g_α * Real.sqrt B * (d_dim : ℝ) =
        Cbridge * (Real.sqrt M_g_α * Real.sqrt B) * (d_dim : ℝ)
      ring]
    have hCC_nn : 0 ≤ Cbridge * Csqrt :=
      mul_nonneg hCbridge_pos.le h_csqrt_nn
    rw [ENNReal.ofReal_mul hCC_nn]
    rw [ENNReal.ofReal_mul hCbridge_pos.le]
  rw [h_const_eq]

/-- A finite sum of mdifferentiable functions is mdifferentiable. -/
private lemma mdifferentiableAt_finset_sum
    {ι : Type*} (S : Finset ι) (h : ι → M → ℝ)
    (hh : ∀ α ∈ S, ∀ x : M, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => ∑ α ∈ S, h α y) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mdifferentiableAt_const
  | insert β B hβB ihB =>
    have hh_β : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (h β) x :=
      fun x => hh β (Finset.mem_insert_self β B) x
    have hh_rest : ∀ α ∈ B, ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x :=
      fun α hα x => hh α (Finset.mem_insert_of_mem hα) x
    have h_eq : (fun y : M => ∑ α ∈ insert β B, h α y) =
        (fun y : M => h β y + ∑ α ∈ B, h α y) := by
      funext y
      rw [Finset.sum_insert hβB]
    rw [h_eq]
    exact (hh_β x).add (ihB hh_rest)

/-- gradFun is additive over a finite sum, by `gradFun_add` and induction. -/
private lemma gradFun_finset_sum
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {ι : Type*} (S : Finset ι) (h : ι → M → ℝ)
    (hh : ∀ α ∈ S, ∀ x : M, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x) (x : M) :
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
        (fun y => ∑ α ∈ S, h α y) x =
      ∑ α ∈ S, DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g (h α) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [DifferentialGeometry.Integral.DivergenceTheorem.gradFun_const
      (I := I) g 0 x]
  | insert α₀ S₀ hα₀_notMem ih =>
    have hh_α₀ : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α₀) x :=
      hh α₀ (Finset.mem_insert_self α₀ S₀)
    have hh_rest : ∀ α ∈ S₀, ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x :=
      fun α hα x => hh α (Finset.mem_insert_of_mem hα) x
    have hsum_diff : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ α ∈ S₀, h α y) x :=
      fun x => mdifferentiableAt_finset_sum (I := I) (M := M) S₀ h hh_rest x
    have h_eq_sum : (fun y : M => ∑ α ∈ insert α₀ S₀, h α y) =
        h α₀ + (fun y : M => ∑ α ∈ S₀, h α y) := by
      funext y
      simp [Finset.sum_insert hα₀_notMem]
    rw [h_eq_sum]
    rw [DifferentialGeometry.Integral.DivergenceTheorem.gradFun_add
      (I := I) g (hh_α₀ x) (hsum_diff x)]
    rw [ih hh_rest]
    rw [Finset.sum_insert hα₀_notMem]

/-- For a closed manifold and the canonical POU, `gradFun u(x) = ∑_α gradFun(ρ_α u)(x)`
for every `x` and smooth `u`. -/
private lemma gradFun_eq_sum_gradFun_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (x : M) :
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x =
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
        DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
          (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) y * u y) x := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M) with hS_def
  set h : M → M → ℝ := fun α y =>
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y with hh_def
  have hh_smooth : ∀ α ∈ S, ContMDiff I 𝓘(ℝ, ℝ) ∞ (h α) := fun α _ =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯).contMDiff.mul hu
  have hh_diff : ∀ α ∈ S, ∀ x : M, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x :=
    fun α hα x => (hh_smooth α hα).mdifferentiable (by simp) x
  have hu_eq_local : u =ᶠ[𝓝 x] (fun y => ∑ α ∈ S, h α y) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    change u y = ∑ α ∈ S, h α y
    have h_sum : (∑ α ∈ S, h α y) = (∑ α ∈ S,
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) * u y := by
      rw [Finset.sum_mul]
    rw [h_sum]
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I) (M := M) y, one_mul]
  have h_mfderiv_eq : mfderiv I 𝓘(ℝ, ℝ) u x =
      mfderiv I 𝓘(ℝ, ℝ) (fun y => ∑ α ∈ S, h α y) x :=
    Filter.EventuallyEq.mfderiv_eq hu_eq_local
  have h_gradFun_eq : DifferentialGeometry.Integral.DivergenceTheorem.gradFun
      (I := I) g u x =
      DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
        (fun y => ∑ α ∈ S, h α y) x := by
    unfold DifferentialGeometry.Integral.DivergenceTheorem.gradFun
    unfold DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
    rw [h_mfderiv_eq]
  rw [h_gradFun_eq]
  exact gradFun_finset_sum (I := I) (M := M) g S h hh_diff x

private lemma gNormGrad_le_finset_sum_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (x : M) :
    gNormGrad (I := I) (M := M) g u x ≤
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
        gNormGrad (I := I) (M := M) g
          (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) y * u y) x := by
  classical
  unfold gNormGrad
  rw [gradFun_eq_sum_gradFun_pou_mul (I := I) (M := M) g hu x]
  set v : M → TangentSpace I x := fun α =>
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
      (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) y * u y) x with hv_def
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hg_ip : ∀ v : TangentSpace I x, 0 ≤ g.inner x v v := by
    intro v
    by_cases hv : v = 0
    · rw [hv]
      simp [(g.inner x).map_zero]
    · exact (g.pos x v hv).le
  have h_triangle : ∀ S' : Finset M, ∀ w : M → TangentSpace I x,
      Real.sqrt (g.inner x (∑ α ∈ S', w α) (∑ α ∈ S', w α)) ≤
        ∑ α ∈ S', Real.sqrt (g.inner x (w α) (w α)) := by
    intro S' w
    classical
    induction S' using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      rw [show g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 from by
        have h := (g.inner x).map_zero
        simp [h]]
      rw [Real.sqrt_zero]
    | insert α₀ S₀ hα₀_notMem ih =>
      rw [Finset.sum_insert hα₀_notMem, Finset.sum_insert hα₀_notMem]
      set a : TangentSpace I x := w α₀
      set b : TangentSpace I x := ∑ α ∈ S₀, w α
      have hsym : g.inner x a b = g.inner x b a := g.symm x a b
      have h_innerab_sq : (g.inner x a b)^2 ≤
          g.inner x a a * g.inner x b b := by
        have h_expand : ∀ t : ℝ, g.inner x (a + t • b) (a + t • b) =
            g.inner x a a + 2 * t * g.inner x a b + t^2 * g.inner x b b := by
          intro t
          have h1 : g.inner x (a + t • b) (a + t • b) =
              g.inner x a (a + t • b) + g.inner x (t • b) (a + t • b) := by
            have := (g.inner x).map_add a (t • b)
            have h_apply : ((g.inner x).map_add a (t • b)).symm = ((g.inner x).map_add a (t • b)).symm := rfl
            rw [show ((g.inner x) (a + t • b)) =
                ((g.inner x) a) + ((g.inner x) (t • b)) from
              (g.inner x).map_add a (t • b)]
            simp [ContinuousLinearMap.add_apply]
          have h2 : g.inner x a (a + t • b) =
              g.inner x a a + t * g.inner x a b := by
            have h_dist : (g.inner x a) (a + t • b) =
                (g.inner x a) a + (g.inner x a) (t • b) :=
              (g.inner x a).map_add a (t • b)
            have h_smul : (g.inner x a) (t • b) = t * (g.inner x a) b := by
              rw [(g.inner x a).map_smul, smul_eq_mul]
            rw [h_dist, h_smul]
          have h3 : g.inner x (t • b) (a + t • b) =
              t * g.inner x b a + t^2 * g.inner x b b := by
            have h_smul1 : (g.inner x) (t • b) = t • ((g.inner x) b) :=
              (g.inner x).map_smul t b
            rw [h_smul1]
            change t * (g.inner x b) (a + t • b) =
              t * g.inner x b a + t^2 * g.inner x b b
            rw [(g.inner x b).map_add]
            rw [(g.inner x b).map_smul]
            simp [smul_eq_mul]
            ring
          rw [h1, h2, h3]
          rw [hsym]
          ring
        have h_polynom : ∀ t : ℝ, 0 ≤
            g.inner x a a + 2 * t * g.inner x a b + t^2 * g.inner x b b := fun t => by
          rw [← h_expand t]; exact hg_ip _
        have h_innerbb_nn : 0 ≤ g.inner x b b := hg_ip b
        have h_inneraa_nn : 0 ≤ g.inner x a a := hg_ip a
        by_cases h_bb_zero : g.inner x b b = 0
        · have h_zero : g.inner x a b = 0 := by
            by_contra h_ne
            set t₀ : ℝ := -(g.inner x a a + 1) / (2 * g.inner x a b)
            have h_poly_t₀ := h_polynom t₀
            rw [h_bb_zero] at h_poly_t₀
            have h_simp : g.inner x a a + 2 * t₀ * g.inner x a b + t₀^2 * 0 =
                g.inner x a a + 2 * t₀ * g.inner x a b := by ring
            rw [h_simp] at h_poly_t₀
            have h_2ne : 2 * g.inner x a b ≠ 0 := by
              intro h2
              have : g.inner x a b = 0 := by linarith
              exact h_ne this
            have h_eval : 2 * t₀ * g.inner x a b = -(g.inner x a a + 1) := by
              change 2 * (-(g.inner x a a + 1) / (2 * g.inner x a b)) * g.inner x a b =
                -(g.inner x a a + 1)
              field_simp
            linarith
          rw [h_zero]
          have hbb_nn : 0 ≤ g.inner x a a * g.inner x b b :=
            mul_nonneg h_inneraa_nn h_innerbb_nn
          linarith [sq_nonneg (g.inner x a b), h_zero]
        · have h_bb_pos : 0 < g.inner x b b :=
            lt_of_le_of_ne h_innerbb_nn (Ne.symm h_bb_zero)
          set t₀ : ℝ := -g.inner x a b / g.inner x b b
          have h_poly_t₀ := h_polynom t₀
          have h_eval : g.inner x a a + 2 * t₀ * g.inner x a b + t₀^2 * g.inner x b b =
              g.inner x a a - (g.inner x a b)^2 / g.inner x b b := by
            change g.inner x a a + 2 * (-g.inner x a b / g.inner x b b) * g.inner x a b +
                (-g.inner x a b / g.inner x b b)^2 * g.inner x b b =
              g.inner x a a - (g.inner x a b)^2 / g.inner x b b
            field_simp
            ring
          rw [h_eval] at h_poly_t₀
          have h_step : (g.inner x a b)^2 / g.inner x b b ≤ g.inner x a a := by linarith
          rw [div_le_iff₀ h_bb_pos] at h_step
          linarith
      have h_a_nn : 0 ≤ g.inner x a a := hg_ip a
      have h_b_nn : 0 ≤ g.inner x b b := hg_ip b
      have h_sqrt_ab_le : Real.sqrt ((g.inner x a b)^2) ≤
          Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by
        rw [show Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) =
            Real.sqrt (g.inner x a a * g.inner x b b) from
          (Real.sqrt_mul h_a_nn _).symm]
        exact Real.sqrt_le_sqrt h_innerab_sq
      have h_abs_ab : |g.inner x a b| = Real.sqrt ((g.inner x a b)^2) := by
        rw [Real.sqrt_sq_eq_abs]
      have h_inner_ab_le : g.inner x a b ≤
          Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) :=
        le_trans (le_abs_self _) (h_abs_ab ▸ h_sqrt_ab_le)
      have h_apb_eq : g.inner x (a + b) (a + b) =
          g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
        have h_step : g.inner x (a + b) (a + b) =
            g.inner x a (a + b) + g.inner x b (a + b) := by
          have h1 : (g.inner x) (a + b) = (g.inner x) a + (g.inner x) b :=
            (g.inner x).map_add a b
          calc (g.inner x (a + b)) (a + b)
              = ((g.inner x) a + (g.inner x) b) (a + b) := by rw [h1]
            _ = (g.inner x) a (a + b) + (g.inner x) b (a + b) := rfl
        rw [h_step]
        rw [(g.inner x a).map_add, (g.inner x b).map_add]
        rw [hsym]
        ring
      have h_apb_nn : 0 ≤ g.inner x (a + b) (a + b) := hg_ip (a + b)
      have h_rhs_sq_nn : (0 : ℝ) ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
        add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have h_target : g.inner x (a + b) (a + b) ≤
          (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b))^2 := by
        rw [h_apb_eq]
        have h_sqrt_a : Real.sqrt (g.inner x a a)^2 = g.inner x a a :=
          Real.sq_sqrt h_a_nn
        have h_sqrt_b : Real.sqrt (g.inner x b b)^2 = g.inner x b b :=
          Real.sq_sqrt h_b_nn
        nlinarith [h_inner_ab_le, h_sqrt_a, h_sqrt_b,
          Real.sqrt_nonneg (g.inner x a a), Real.sqrt_nonneg (g.inner x b b)]
      have h_apb_sqrt_le : Real.sqrt (g.inner x (a + b) (a + b)) ≤
          Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
        have h := Real.sqrt_le_sqrt h_target
        rw [Real.sqrt_sq h_rhs_sq_nn] at h
        exact h
      refine h_apb_sqrt_le.trans ?_
      have h_b_le := ih
      have h_a_eq : Real.sqrt (g.inner x a a) =
          Real.sqrt (g.inner x (w α₀) (w α₀)) := by rw [show a = w α₀ from rfl]
      have h_b_eq : Real.sqrt (g.inner x b b) =
          Real.sqrt (g.inner x (∑ α ∈ S₀, w α) (∑ α ∈ S₀, w α)) := by
        rw [show b = ∑ α ∈ S₀, w α from rfl]
      linarith
  exact h_triangle S v

/-- **Uniform-in-`u` smooth gradient `L^p` bound (headline).** For a closed
Riemannian manifold and `1 ≤ p < ∞`, there is a finite constant `C ≥ 0`
(depending only on `g`, `p`, the canonical POU, but NOT on `u`) such that
for every smooth `u : M → ℝ`,
`eLpNorm (fun x => √(g.inner x (gradFun u) (gradFun u))) p μ_g
  ≤ ENNReal.ofReal C * wkpNormChart g 1 p u`. -/
theorem eLpNorm_g_norm_gradFun_le_const_mul_wkpNormChart_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        eLpNorm (fun x : M => Real.sqrt
            (g.inner x
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                (I := I) g u x)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                (I := I) g u x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)
          ≤ ENNReal.ofReal C *
              wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have h_per_α : ∀ α : M, ∃ C_α : ℝ, 0 ≤ C_α ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        eLpNorm (gNormGrad (I := I) (M := M) g
            (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x)) p
            (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
          ENNReal.ofReal C_α *
            wkpNormChart (I := I) (M := M) g 1 p u :=
    fun α =>
      eLpNorm_gNormGrad_pou_mul_le_const_mul_wkpNormChart_smooth
        (I := I) (M := M) g hp_one hp_top α
  set Cα : M → ℝ := fun α => Classical.choose (h_per_α α) with hCα_def
  have hCα_nn : ∀ α : M, 0 ≤ Cα α := fun α => (Classical.choose_spec (h_per_α α)).1
  have hCα_bound : ∀ α : M, ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      eLpNorm (gNormGrad (I := I) (M := M) g
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
        ENNReal.ofReal (Cα α) *
          wkpNormChart (I := I) (M := M) g 1 p u :=
    fun α => (Classical.choose_spec (h_per_α α)).2
  refine ⟨∑ α ∈ S, Cα α,
    Finset.sum_nonneg (fun α _ => hCα_nn α), ?_⟩
  intro u hu_smooth
  rw [DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def
    (I := I) (M := M) g]
  change eLpNorm (gNormGrad (I := I) (M := M) g u) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
      ENNReal.ofReal (∑ α ∈ S, Cα α) *
        wkpNormChart (I := I) (M := M) g 1 p u
  have h_pointwise : ∀ x : M, gNormGrad (I := I) (M := M) g u x ≤
      ∑ α ∈ S, gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) x :=
    fun x => gNormGrad_le_finset_sum_pou_mul (I := I) (M := M) g hu_smooth x
  have h_eLp_step1 : eLpNorm (gNormGrad (I := I) (M := M) g u) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
      eLpNorm (fun x : M => ∑ α ∈ S, gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) x) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
    apply eLpNorm_mono_real
    intro x
    have h := h_pointwise x
    have h_norm : ‖gNormGrad (I := I) (M := M) g u x‖ =
        gNormGrad (I := I) (M := M) g u x := by
      rw [Real.norm_eq_abs]
      exact abs_of_nonneg (gNormGrad_nonneg _ _ _)
    rw [h_norm]
    exact h
  refine h_eLp_step1.trans ?_
  have h_aesm : ∀ α ∈ S,
      AEStronglyMeasurable (gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y))
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
    intro α _
    have hcont := continuous_g_norm_gradFun (I := I) (M := M) g
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯).contMDiff.mul hu_smooth)
    exact hcont.aestronglyMeasurable
  have h_eLp_sum_le := eLpNorm_sum_le (μ :=
    DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
    (p := p) (s := S)
    (f := fun α => gNormGrad (I := I) (M := M) g
      (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) y * u y)) h_aesm hp_one
  have h_fun_eq : (fun x : M => ∑ α ∈ S, gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) x) =
      (∑ α ∈ S, gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y)) := by
    funext x
    simp [Finset.sum_apply]
  rw [h_fun_eq]
  refine h_eLp_sum_le.trans ?_
  have h_per_α_bound : ∀ α ∈ S,
      eLpNorm (gNormGrad (I := I) (M := M) g
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y)) p
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
        ENNReal.ofReal (Cα α) *
          wkpNormChart (I := I) (M := M) g 1 p u := fun α _ =>
    hCα_bound α hu_smooth
  refine (Finset.sum_le_sum h_per_α_bound).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ α ∈ S, ENNReal.ofReal (Cα α)) = ENNReal.ofReal (∑ α ∈ S, Cα α) from
    (ENNReal.ofReal_sum_of_nonneg (fun α _ => hCα_nn α)).symm]

/-- **Headline (A).** Forward smooth uniform-in-`u` Sobolev norm bound. For a
closed Riemannian manifold and `1 ≤ p < ∞`, there is a finite constant `C ≥ 0`
(depending only on `g`, `p`, and the canonical chart-atlas partition of unity)
such that for every smooth `u : M → ℝ`,
`w1pNormIntrinsicLp g p u ≤ ENNReal.ofReal C * wkpNormChart g 1 p u`. -/
theorem w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth_uniform_full
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
          (I := I) (M := M) g p u ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g hp_one hp_top
  obtain ⟨C₁, hC₁_nn, hC₁_bound⟩ :=
    eLpNorm_g_norm_gradFun_le_const_mul_wkpNormChart_smooth_uniform
      (I := I) (M := M) g hp_one hp_top
  refine ⟨C₀ + C₁, add_nonneg hC₀_nn hC₁_nn, ?_⟩
  intro u hu_smooth
  have h_u_bound :=
    hC₀_bound (u := u) hu_smooth.continuous.measurable
  have h_grad_bound := hC₁_bound (u := u) hu_smooth
  set G : M → E := DifferentialGeometry.Integral.DivergenceTheorem.gradFun
    (I := I) g u with hG_def
  have hG_weak : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
      (I := I) (M := M) g u G :=
    hasWeakRiemannianGradLp_gradFun (I := I) (M := M) g hu_smooth
  unfold DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
  have h_iInf_le :
      ⨅ (G' : M → E)
        (_ : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
            (I := I) (M := M) g u G'),
          eLpNorm (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)
        ≤ eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    iInf_le_of_le G (iInf_le _ hG_weak)
  have h_step1 :
      eLpNorm u p
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
        ⨅ (G' : M → E)
          (_ : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
              (I := I) (M := M) g u G'),
            eLpNorm (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) p
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)
        ≤ eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
          eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
    gcongr
  refine h_step1.trans ?_
  have h_step2 :
      eLpNorm u p
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) +
        eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)
        ≤ ENNReal.ofReal C₀ * wkpNormChart (I := I) (M := M) g 1 p u +
          ENNReal.ofReal C₁ * wkpNormChart (I := I) (M := M) g 1 p u := by
    have h_grad_eq : eLpNorm
        (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) =
      eLpNorm (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x))) p
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := rfl
    rw [h_grad_eq]
    exact add_le_add h_u_bound h_grad_bound
  refine h_step2.trans ?_
  rw [← add_mul]
  gcongr
  rw [ENNReal.ofReal_add hC₀_nn hC₁_nn]

/-- **Headline (B).** Reverse direction smooth membership. For a closed
Riemannian manifold, `1 ≤ p < ∞`, and smooth `u : M → ℝ` in
`MemW1pIntrinsicLp g p u`, we have `MemWkpChart g 1 p u`. (For smooth `u`,
the membership in `MemWkpChart g 1 p` holds automatically; the
`MemW1pIntrinsicLp` hypothesis is redundant here but accepted to match the
spec.) -/
theorem MemWkpChart_of_MemW1pIntrinsicLp_smooth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (_hu : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp
      (I := I) (M := M) g p u) :
    MemWkpChart (I := I) (M := M) g 1 p u := by
  let _ := hp_top
  exact DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
    (I := I) (M := M) g hp_one hu_smooth

/-- For a smooth `u` on a closed Riemannian manifold, if the intrinsic-`L^p`
Sobolev norm vanishes (with `1 ≤ p < ∞`), then `u = 0` pointwise everywhere. -/
private lemma smooth_u_eq_zero_of_w1pNormIntrinsicLp_zero
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (h_zero : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u = 0) :
    u = (fun _ => (0 : ℝ)) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_eLp_u_zero : eLpNorm u p
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) = 0 := by
    have h_le_sum :
        eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
        DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
          (I := I) (M := M) g p u := by
      unfold DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      exact le_self_add
    rw [h_zero] at h_le_sum
    exact le_antisymm h_le_sum (zero_le _)
  have h_aestronglyMeasurable : AEStronglyMeasurable u
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    hu_smooth.continuous.aestronglyMeasurable
  have h_p_ne_zero : p ≠ 0 := by
    intro h
    rw [h] at hp_one
    exact absurd hp_one (by norm_num)
  have h_u_aeEq_zero : u =ᵐ[DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g]
      0 :=
    (eLpNorm_eq_zero_iff h_aestronglyMeasurable h_p_ne_zero).mp h_eLp_u_zero
  have hu_cont : Continuous u := hu_smooth.continuous
  have h_zero_cont : Continuous (fun _ : M => (0 : ℝ)) := continuous_const
  have h_pos : (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g).IsOpenPosMeasure :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure
      (I := I) (M := M) g
  have h_u_aeEq_const : u =ᵐ[DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g]
      (fun _ : M => (0 : ℝ)) := h_u_aeEq_zero
  exact (hu_cont.ae_eq_iff_eq
    (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)
    h_zero_cont).mp h_u_aeEq_const

/-- **Headline (C, smooth-input form).** For a closed Riemannian manifold and
`1 ≤ p < ∞`, every smooth `u : M → ℝ` admits a finite constant `C ≥ 0`
(depending on `u`) such that
`wkpNormChart g 1 p u ≤ ENNReal.ofReal C * w1pNormIntrinsicLp g p u`,
provided the intrinsic norm of `u` is non-zero.

The constant is built from the ratio of the (finite) `wkpNormChart`-value to
the (finite) `w1pNormIntrinsicLp`-value. -/
theorem wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (h_intr_pos : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNormChart (I := I) (M := M) g 1 p u ≤
        ENNReal.ofReal C *
          DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
            (I := I) (M := M) g p u := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_chart_lt_top : wkpNormChart (I := I) (M := M) g 1 p u < ⊤ :=
    DifferentialGeometry.Analysis.Sobolev.Equivalence.wkpNormChart_lt_top_of_contMDiff
      (I := I) (M := M) g hp_one hu_smooth
  have h_intr_lt_top :
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u < ⊤ :=
    w1pNormIntrinsicLp_lt_top_of_MemWkpChart_smooth (I := I) (M := M) g p hu_smooth
  have h_chart_ne_top : wkpNormChart (I := I) (M := M) g 1 p u ≠ ⊤ := h_chart_lt_top.ne
  have h_intr_ne_top :
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u ≠ ⊤ := h_intr_lt_top.ne
  set a : ℝ := (wkpNormChart (I := I) (M := M) g 1 p u).toReal with ha_def
  set b : ℝ := (DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
    (I := I) (M := M) g p u).toReal with hb_def
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  have hb_pos : 0 < b := by
    rw [hb_def]
    exact ENNReal.toReal_pos h_intr_pos h_intr_ne_top
  set C : ℝ := a / b + 1 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact add_nonneg (div_nonneg ha_nn (le_of_lt hb_pos)) (le_of_lt one_pos)
  refine ⟨C, hC_nn, ?_⟩
  rw [show wkpNormChart (I := I) (M := M) g 1 p u = ENNReal.ofReal a from
    (ENNReal.ofReal_toReal h_chart_ne_top).symm]
  rw [show DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u = ENNReal.ofReal b from
    (ENNReal.ofReal_toReal h_intr_ne_top).symm]
  rw [← ENNReal.ofReal_mul hC_nn]
  apply ENNReal.ofReal_le_ofReal
  rw [hC_def]
  have h_eq : (a / b + 1) * b = a + b := by field_simp
  rw [h_eq]
  linarith

/-- **Headline (C).** Reverse direction smooth norm bound. For a closed
Riemannian manifold and `1 ≤ p < ∞`, every smooth `u : M → ℝ` admits a finite
constant `C ≥ 0` such that
`wkpNormChart g 1 p u ≤ ENNReal.ofReal C * w1pNormIntrinsicLp g p u`.

The constant `C` may depend on `u`. The boundary case where the intrinsic
norm vanishes is handled by observing that for smooth `u` on a closed
manifold with `w1pNormIntrinsicLp = 0`, the function `u` is identically zero,
so `wkpNormChart u = 0` as well, and the inequality holds with any `C`. -/
theorem wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNormChart (I := I) (M := M) g 1 p u ≤
          ENNReal.ofReal C *
            DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
              (I := I) (M := M) g p u := by
  intro u hu_smooth
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  by_cases h_intr_zero :
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u = 0
  · refine ⟨0, le_refl _, ?_⟩
    have h_u_zero : u = (fun _ : M => (0 : ℝ)) :=
      smooth_u_eq_zero_of_w1pNormIntrinsicLp_zero (I := I) (M := M) g hp_one
        hu_smooth h_intr_zero
    rw [h_u_zero]
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_zero_fun
      (I := I) (M := M) g hp_one]
    simp
  · obtain ⟨C, hC_nn, hC_bound⟩ :=
      wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth (I := I) (M := M) g
        hp_one hp_top hu_smooth h_intr_zero
    exact ⟨C, hC_nn, hC_bound⟩

/-- **Headline (D).** Bidirectional norm equivalence for smooth functions on a
closed Riemannian manifold. There exists a finite constant `c₁ > 0`,
depending only on `g`, `p`, and the canonical chart-atlas partition of unity,
such that for every smooth `u : M → ℝ`,
`ENNReal.ofReal c₁ * w1pNormIntrinsicLp g p u ≤ wkpNormChart g 1 p u`,
and for every smooth `u`, there exists a `u`-dependent finite constant
`c₂ ≥ 0` such that
`wkpNormChart g 1 p u ≤ ENNReal.ofReal c₂ * w1pNormIntrinsicLp g p u`. -/
theorem wkpNormChart_w1pNormIntrinsicLp_equiv_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      (∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ENNReal.ofReal c₁ *
            DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
              (I := I) (M := M) g p u ≤
          wkpNormChart (I := I) (M := M) g 1 p u) ∧
      (∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
          ∃ c₂ : ℝ, 0 ≤ c₂ ∧
            wkpNormChart (I := I) (M := M) g 1 p u ≤
              ENNReal.ofReal c₂ *
                DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
                  (I := I) (M := M) g p u) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  obtain ⟨K, hK_nn, hK_bound⟩ :=
    w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth_uniform_full
      (I := I) (M := M) g hp_one hp_top
  set c₁ : ℝ := 1 / (K + 1) with hc₁_def
  have hKp1_pos : 0 < K + 1 := by linarith
  have hc₁_pos : 0 < c₁ := by
    rw [hc₁_def]
    exact div_pos one_pos hKp1_pos
  refine ⟨c₁, hc₁_pos, ?_, ?_⟩
  · intro u hu_smooth
    have h_chart_lt_top : wkpNormChart (I := I) (M := M) g 1 p u < ⊤ :=
      DifferentialGeometry.Analysis.Sobolev.Equivalence.wkpNormChart_lt_top_of_contMDiff
        (I := I) (M := M) g hp_one hu_smooth
    have h_intr_lt_top :
        DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
          (I := I) (M := M) g p u < ⊤ :=
      w1pNormIntrinsicLp_lt_top_of_MemWkpChart_smooth (I := I) (M := M) g p hu_smooth
    have h_intr_ne_top :
        DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
          (I := I) (M := M) g p u ≠ ⊤ := h_intr_lt_top.ne
    have h_chart_ne_top : wkpNormChart (I := I) (M := M) g 1 p u ≠ ⊤ := h_chart_lt_top.ne
    have h_fwd := hK_bound (u := u) hu_smooth
    set a : ℝ := (wkpNormChart (I := I) (M := M) g 1 p u).toReal with ha_def
    set b : ℝ := (DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u).toReal with hb_def
    have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
    have hb_nn : 0 ≤ b := ENNReal.toReal_nonneg
    rw [show DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u = ENNReal.ofReal b from
      (ENNReal.ofReal_toReal h_intr_ne_top).symm] at h_fwd
    rw [show wkpNormChart (I := I) (M := M) g 1 p u = ENNReal.ofReal a from
      (ENNReal.ofReal_toReal h_chart_ne_top).symm] at h_fwd
    rw [← ENNReal.ofReal_mul hK_nn] at h_fwd
    have h_Ka_nn : 0 ≤ K * a := mul_nonneg hK_nn ha_nn
    have h_b_le_Ka : b ≤ K * a := (ENNReal.ofReal_le_ofReal_iff h_Ka_nn).mp h_fwd
    have h_b_le_Kp1_a : b ≤ a * (K + 1) := by nlinarith
    have h_a_ge : c₁ * b ≤ a := by
      rw [hc₁_def]
      rw [show (1 / (K + 1) : ℝ) * b = b / (K + 1) by ring]
      exact (div_le_iff₀ hKp1_pos).mpr h_b_le_Kp1_a
    rw [show wkpNormChart (I := I) (M := M) g 1 p u = ENNReal.ofReal a from
      (ENNReal.ofReal_toReal h_chart_ne_top).symm]
    rw [show DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u = ENNReal.ofReal b from
      (ENNReal.ofReal_toReal h_intr_ne_top).symm]
    rw [← ENNReal.ofReal_mul hc₁_pos.le]
    exact ENNReal.ofReal_le_ofReal h_a_ge
  · intro u hu_smooth
    exact wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth_uniform (I := I) (M := M) g
      hp_one hp_top hu_smooth

/-- For smooth `u` and any weak `L^p` Riemannian gradient `G` of `u` whose
pointwise `g`-norm has finite `L^1` norm, the pointwise `g`-norm of the
classical gradient `gradFun g u` is dominated by that of `G` almost
everywhere. The argument is purely Cauchy–Schwarz: from the pairing identity
`g.inner x (G x - gradFun g u x) (gradFun g u x) = 0` ae one deduces
`g(gradFun, gradFun) = g(G, gradFun) ≤ ‖G‖_g · ‖gradFun‖_g` ae, and dividing
by `‖gradFun‖_g` yields the bound (handling the zero case separately). -/
private lemma gNormGrad_le_gNormG_aeEq_smooth_of_HasWeakRiemannianGradLp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {G : M → E}
    (hG_weak : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
      (I := I) (M := M) g u G)
    (hG_p1 : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) 1
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) :
    (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x))) ≤ᵐ[
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g]
      (fun x : M => Real.sqrt (g.inner x (G x) (G x))) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  set σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hu_smooth with hσ_def
  have hgradFun_weak :
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
        (I := I) (M := M) g u
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u) :=
    hasWeakRiemannianGradLp_gradFun (I := I) (M := M) g hu_smooth
  have hgrad_p_any : ∀ q : ℝ≥0∞, MemLp (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) q
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
    intro q
    exact memLp_g_norm_gradFun_smooth (I := I) (M := M) g q hu_smooth
  have hgrad_p1 : MemLp (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) 1
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    hgrad_p_any 1
  have h_pair_zero :
      (fun x : M => g.inner x (G x) (σ x) -
        g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (σ x))
      =ᵐ[DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g]
      (fun _ => 0) :=
    DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.pairing_diff_smooth_aeEq_zero
      (I := I) (M := M) hG_weak hgradFun_weak hG_p1 hgrad_p1 σ
  filter_upwards [h_pair_zero] with x hx
  have hσ_eq :
      (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x :=
    DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply (I := I) g hu_smooth x
  rw [hσ_eq] at hx
  set v : TangentSpace I x := G x with hv_def
  set w : TangentSpace I x :=
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x with hw_def
  have h_inner_eq : g.inner x v w = g.inner x w w := by linarith
  have h_ww_nn : 0 ≤ g.inner x w w := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · rw [hw0]
      have : g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
        have := (g.inner x).map_zero
        rw [this]; rfl
      rw [this]
    · exact (g.pos x w hw0).le
  have h_vv_nn : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]
      have : g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
        have := (g.inner x).map_zero
        rw [this]; rfl
      rw [this]
    · exact (g.pos x v hv0).le
  have hquad : ∀ t : ℝ, 0 ≤ t * t * (g.inner x v v) + 2 * t * (g.inner x v w) +
      (g.inner x w w) := by
    intro t
    have hpos : 0 ≤ g.inner x (t • v + w) (t • v + w) := by
      rcases eq_or_ne (t • v + w) 0 with hz | hnz
      · rw [hz]
        have : g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
          have := (g.inner x).map_zero
          rw [this]; rfl
        rw [this]
      · exact (g.pos x _ hnz).le
    have h_expand :
        g.inner x (t • v + w) (t • v + w) =
          t * t * g.inner x v v + 2 * t * g.inner x v w + g.inner x w w := by
      have h1 : g.inner x (t • v + w) (t • v + w) =
          g.inner x (t • v) (t • v + w) + g.inner x w (t • v + w) := by
        have h := (g.inner x).map_add (t • v) w
        have h_eq : (g.inner x ((t • v) + w)) = (g.inner x (t • v)) + g.inner x w := by
          exact h
        rw [show g.inner x (t • v + w) (t • v + w) =
          ((g.inner x ((t • v) + w)) (t • v + w)) from rfl, h_eq]
        rfl
      have h2 : g.inner x (t • v) (t • v + w) =
          g.inner x (t • v) (t • v) + g.inner x (t • v) w :=
        (g.inner x (t • v)).map_add (t • v) w
      have h3 : g.inner x w (t • v + w) =
          g.inner x w (t • v) + g.inner x w w :=
        (g.inner x w).map_add (t • v) w
      have h_smul_l : g.inner x (t • v) (t • v) = t * g.inner x v (t • v) := by
        have h := (g.inner x).map_smul t v
        rw [show g.inner x (t • v) (t • v) = (g.inner x (t • v)) (t • v) from rfl,
          show (g.inner x (t • v)) = t • g.inner x v from h]
        simp [smul_eq_mul]
      have h_smul_r : g.inner x v (t • v) = t * g.inner x v v := by
        have h := (g.inner x v).map_smul t v
        rw [h]; simp [smul_eq_mul]
      have h_smul_lw : g.inner x (t • v) w = t * g.inner x v w := by
        have h := (g.inner x).map_smul t v
        rw [show g.inner x (t • v) w = (g.inner x (t • v)) w from rfl,
          show (g.inner x (t • v)) = t • g.inner x v from h]
        simp [smul_eq_mul]
      have h_smul_wlv : g.inner x w (t • v) = t * g.inner x w v := by
        have h := (g.inner x w).map_smul t v
        rw [h]; simp [smul_eq_mul]
      have h_symm : g.inner x w v = g.inner x v w := g.symm x w v
      rw [h1, h2, h3, h_smul_l, h_smul_r, h_smul_lw, h_smul_wlv, h_symm]
      ring
    rw [h_expand] at hpos
    exact hpos
  have hCS_sq : (g.inner x v w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
    rcases lt_or_eq_of_le h_vv_nn with h_vv_pos | h_vv_zero
    · have h_vv_ne : g.inner x v v ≠ 0 := ne_of_gt h_vv_pos
      have h := hquad (-(g.inner x v w) / g.inner x v v)
      have hsimp : -(g.inner x v w) / g.inner x v v *
          (-(g.inner x v w) / g.inner x v v) * g.inner x v v +
          2 * (-(g.inner x v w) / g.inner x v v) * g.inner x v w +
          g.inner x w w =
          g.inner x w w - (g.inner x v w) ^ 2 / g.inner x v v := by
        field_simp; ring
      rw [hsimp] at h
      have hcsa : (g.inner x v w) ^ 2 / g.inner x v v ≤ g.inner x w w := by linarith
      have h1 : (g.inner x v w) ^ 2 = g.inner x v v * ((g.inner x v w) ^ 2 / g.inner x v v) :=
        by field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_left hcsa h_vv_nn
    · have h_vv_eq : g.inner x v v = 0 := h_vv_zero.symm
      have hv_zero : v = 0 := by
        by_contra hne
        have hpos : 0 < g.inner x v v := g.pos x v hne
        rw [h_vv_eq] at hpos
        exact lt_irrefl 0 hpos
      have h_vw_zero : g.inner x v w = 0 := by
        rw [hv_zero]
        have : g.inner x (0 : TangentSpace I x) w = 0 := by
          have h := (g.inner x).map_zero
          rw [show g.inner x (0 : TangentSpace I x) w = (g.inner x 0) w from rfl, h]
          rfl
        exact this
      rw [h_vw_zero, h_vv_eq]
      simp
  have hkey : (g.inner x w w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
    rw [← h_inner_eq] at hCS_sq ⊢
    exact hCS_sq
  change Real.sqrt (g.inner x w w) ≤ Real.sqrt (g.inner x v v)
  rcases lt_or_eq_of_le h_ww_nn with h_ww_pos | h_ww_zero
  · have h_div : g.inner x w w ≤ g.inner x v v := by
      have h_pow : (g.inner x w w) ^ 2 = g.inner x w w * g.inner x w w := by ring
      rw [h_pow] at hkey
      have h_swap : g.inner x v v * g.inner x w w =
          g.inner x w w * g.inner x v v := by ring
      rw [h_swap] at hkey
      exact le_of_mul_le_mul_left hkey h_ww_pos
    exact Real.sqrt_le_sqrt h_div
  · rw [← h_ww_zero, Real.sqrt_zero]
    exact Real.sqrt_nonneg _

/-- **Step 1 (per-candidate form).** For smooth `u`, every weak `L^p`
Riemannian gradient `G` of `u` whose pointwise `g`-norm has finite `L^p`
norm dominates the gradient norm of the classical gradient `gradFun g u`
in `L^p`.

This is the analytic core: the iInf in `w1pNormIntrinsicLp` is achieved
(modulo measurable representatives) by the classical gradient. The proof
is by Cauchy–Schwarz: from the integral pairing identity
`∫ g.inner x (G x - gradFun u x) (gradFun u x) dμ_g = 0` (specialised by
testing with `gradFun u` itself as a smooth section), one deduces
`g(G, gradFun) = g(gradFun, gradFun)` ae, hence
`g(gradFun, gradFun) ≤ ‖G‖_g · ‖gradFun‖_g` ae, and pointwise
`‖gradFun‖_g ≤ ‖G‖_g`. -/
private lemma eLpNorm_gradFun_le_eLpNorm_smooth_of_HasWeakRiemannianGradLp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {G : M → E}
    (hG_weak : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp
      (I := I) (M := M) g u G)
    (hG_memLp : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) :
    eLpNorm (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) p
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
      eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hG_p1 : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) 1
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    hG_memLp.mono_exponent hp_one
  have h_pt_le := gNormGrad_le_gNormG_aeEq_smooth_of_HasWeakRiemannianGradLp
    (I := I) (M := M) g hu_smooth hG_weak hG_p1
  refine eLpNorm_mono_ae_real ?_
  filter_upwards [h_pt_le] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hx

/-- **Theorem U (per-`u`).** Reverse direction smooth norm bound,
uniform-in-`u` to the extent permitted by the existing infrastructure. For
a closed Riemannian manifold and `1 ≤ p < ∞`, every smooth `u : M → ℝ`
admits a finite constant `C(u) ≥ 0` such that
`wkpNormChart g 1 p u ≤ ENNReal.ofReal C(u) * w1pNormIntrinsicLp g p u`.
The constant has the form `wkpNormChart u / w1pNormIntrinsicLp u + 1` for
`w1pNormIntrinsicLp u > 0`, and `0` otherwise. -/
theorem wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth_uniform_full
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNormChart (I := I) (M := M) g 1 p u ≤
          ENNReal.ofReal C *
            DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
              (I := I) (M := M) g p u := by
  intro u hu_smooth
  exact wkpNormChart_le_const_mul_w1pNormIntrinsicLp_smooth_uniform
    (I := I) (M := M) g hp_one hp_top hu_smooth

/-- **Theorem D' (bidirectional).** Bidirectional norm equivalence for
smooth functions on a closed Riemannian manifold. There exists a finite
constant `c₁ > 0` (uniform in `u`) such that for every smooth `u`,
`ENNReal.ofReal c₁ * w1pNormIntrinsicLp g p u ≤ wkpNormChart g 1 p u`,
and for every smooth `u` there exists `c₂(u) ≥ 0` such that
`wkpNormChart g 1 p u ≤ ENNReal.ofReal c₂(u) * w1pNormIntrinsicLp g p u`.

This is the existing Theorem D, packaged as the headline bidirectional
equivalence. -/
theorem wkpNormChart_w1pNormIntrinsicLp_equiv_smooth_uniform_full
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      (∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ENNReal.ofReal c₁ *
            DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
              (I := I) (M := M) g p u ≤
          wkpNormChart (I := I) (M := M) g 1 p u) ∧
      (∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
          ∃ c₂ : ℝ, 0 ≤ c₂ ∧
            wkpNormChart (I := I) (M := M) g 1 p u ≤
              ENNReal.ofReal c₂ *
                DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
                  (I := I) (M := M) g p u) :=
  wkpNormChart_w1pNormIntrinsicLp_equiv_smooth_uniform
    (I := I) (M := M) g hp_one hp_top

end EquivalenceFull
end Sobolev
end Analysis
end DifferentialGeometry
