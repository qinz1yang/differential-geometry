import DifferentialGeometry.Geometry.Comparison.Variation.SmoothEnergy

noncomputable section
open Set Filter Manifold MeasureTheory
open scoped Topology Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace Poincare.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


lemma speedSq_eventuallyEq (g : SmoothRiemannianMetric I M)
    {d f : ℝ × ℝ → M} {p : ℝ × ℝ} (h : d =ᶠ[𝓝 p] f) :
    (fun q : ℝ × ℝ => speedSq (I := I) g (Function.curry d) q.1 q.2) =ᶠ[𝓝 p]
      (fun q : ℝ × ℝ => speedSq (I := I) g (Function.curry f) q.1 q.2) := by
  filter_upwards [h.eventuallyEq_nhds] with q hq
  have hs := hq.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hv := hs.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
  change mfderiv 𝓘(ℝ, ℝ) I (fun t => d (q.1, t)) q.2 =
    mfderiv 𝓘(ℝ, ℝ) I (fun t => f (q.1, t)) q.2 at hv
  change g.inner (d q) (mfderiv 𝓘(ℝ, ℝ) I (fun t => d (q.1, t)) q.2 1)
      (mfderiv 𝓘(ℝ, ℝ) I (fun t => d (q.1, t)) q.2 1) = _
  rw [hq.eq_of_nhds, hv]
  rfl


lemma energyDensities_eventuallyEq (g : SmoothRiemannianMetric I M)
    {d f : ℝ × ℝ → M} {p : ℝ × ℝ} (h : d =ᶠ[𝓝 p] f) :
    ((fun q : ℝ × ℝ => firstEnergyDensity (I := I) g (Function.curry d) q.1 q.2) =ᶠ[𝓝 p]
      (fun q : ℝ × ℝ => firstEnergyDensity (I := I) g (Function.curry f) q.1 q.2)) ∧
    ((fun q : ℝ × ℝ => secondEnergyDensity (I := I) g (Function.curry d) q.1 q.2) =ᶠ[𝓝 p]
      (fun q : ℝ × ℝ => secondEnergyDensity (I := I) g (Function.curry f) q.1 q.2)) := by
  have hfirst :
      (fun q : ℝ × ℝ => firstEnergyDensity (I := I) g (Function.curry d) q.1 q.2) =ᶠ[𝓝 p]
        (fun q : ℝ × ℝ => firstEnergyDensity (I := I) g (Function.curry f) q.1 q.2) := by
    filter_upwards [(speedSq_eventuallyEq g h).fderiv (𝕜 := ℝ)] with q hq
    exact congrArg (fun A => A (1, 0)) hq
  refine ⟨hfirst, ?_⟩
  filter_upwards [hfirst.fderiv (𝕜 := ℝ)] with q hq
  exact congrArg (fun A => A (1, 0)) hq

theorem curveEnergy_derivatives_of_smooth_near_slice (g : SmoothRiemannianMetric I M)
    (f : ℝ × ℝ → M) {L s : ℝ} (hL : 0 ≤ L)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hsub : ({s} ×ˢ Icc 0 L) ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U) :
    HasDerivAt (fun r => curveEnergy (I := I) g (fun t => f (r, t)) 0 L)
      (∫ t in (0 : ℝ)..L, firstEnergyDensity (I := I) g (Function.curry f) s t) s ∧
    HasDerivAt (deriv (fun r => curveEnergy (I := I) g (fun t => f (r, t)) 0 L))
      (∫ t in (0 : ℝ)..L, secondEnergyDensity (I := I) g (Function.curry f) s t) s := by
  obtain ⟨d, hd, heq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_jointly_near_slice hL hU hsub hf
  have hd8 : IsSmoothVariation (I := I) (Function.curry d) := by
    unfold IsSmoothVariation
    have hh : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) d := hd.of_le (by decide)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hh
    exact hh
  have hE : (fun r => curveEnergy (I := I) g (fun t => d (r, t)) 0 L) =ᶠ[𝓝 s]
      (fun r => curveEnergy (I := I) g (fun t => f (r, t)) 0 L) := by
    filter_upwards [heq] with r hr
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL] at ht
    exact (speedSq_eventuallyEq g (hr t ht)).eq_of_nhds
  have hD : (fun r => ∫ t in (0 : ℝ)..L, firstEnergyDensity (I := I) g (Function.curry d) r t)
      =ᶠ[𝓝 s] (fun r => ∫ t in (0 : ℝ)..L, firstEnergyDensity (I := I) g (Function.curry f) r t) := by
    filter_upwards [heq] with r hr
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL] at ht
    exact (energyDensities_eventuallyEq g (hr t ht)).1.eq_of_nhds
  have hDD : (fun r => ∫ t in (0 : ℝ)..L, secondEnergyDensity (I := I) g (Function.curry d) r t)
      =ᶠ[𝓝 s] (fun r => ∫ t in (0 : ℝ)..L, secondEnergyDensity (I := I) g (Function.curry f) r t) := by
    filter_upwards [heq] with r hr
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL] at ht
    exact (energyDensities_eventuallyEq g (hr t ht)).2.eq_of_nhds
  constructor
  · rw [← hD.eq_of_nhds]
    exact (curveEnergy_hasDerivAt g (Function.curry d) hd8 0 L s).congr_of_eventuallyEq hE.symm
  · rw [← hDD.eq_of_nhds]
    exact (curveEnergy_deriv_hasDerivAt g (Function.curry d) hd8 0 L s).congr_of_eventuallyEq hE.deriv.symm

end Poincare.Geometry.Riemannian.Variation
