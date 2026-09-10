import DifferentialGeometry.Geometry.Comparison.Variation.LocalEnergyDerivatives
import DifferentialGeometry.Geometry.Geodesic.Equation.FromIntegralCurve

noncomputable section
open Bundle Manifold Set Filter MeasureTheory
open scoped Topology Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace Poincare.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem firstVariation_curveEnergy_geodesic_of_smooth_near_slice
    (g : SmoothRiemannianMetric I M) (f : ℝ × ℝ → M) {L : ℝ} (hL : 0 < L)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hsub : ({0} ×ˢ Icc 0 L) ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U)
    (hg : IsGeodesicOn (I := I) g (fun t => f (0, t)) (Icc 0 L))
    (hunit : ∀ t ∈ Icc (0 : ℝ) L, speedSq (I := I) g (Function.curry f) 0 t = 1) :
    HasDerivAt (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L)
      (2 * (g.inner (f (0, L))
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => f (s, L)) 0 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun t => f (0, t)) L 1) -
      g.inner (f (0, 0))
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => f (s, 0)) 0 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun t => f (0, t)) 0 1))) 0 := by
  obtain ⟨d, hd, heq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_jointly_near_slice hL.le hU hsub hf
  have hjoint : ∀ t ∈ Icc (0 : ℝ) L, d =ᶠ[𝓝 (0, t)] f := heq.self_of_nhds
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      (fun u => d (0, u)) =ᶠ[𝓝 t] (fun u => f (0, u)) :=
    (hjoint t ht).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hd8 : IsSmoothVariation (I := I) (Function.curry d) := by
    unfold IsSmoothVariation
    have hh : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) d := hd.of_le (by decide)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hh
    exact hh
  have hdpath : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t => d (0, t)) :=
    hd.comp ((contDiff_const.prodMk contDiff_id).contMDiff)
  have hdunit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      speedSq (I := I) g (Function.curry d) 0 t = 1 :=
    (speedSq_eventuallyEq g (hjoint t ht)).eq_of_nhds.trans (hunit t ht)
  have hacc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      covDerivAlong (I := I) g (fun u => d (0, u))
        (fun u => mfderiv 𝓘(ℝ, ℝ) I (fun r => d (0, r)) u 1) t = 0 := by
    apply covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g _ t
      (hdpath.contMDiffAt.of_le (by decide))
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (hpath t ht).eq_of_nhds (hpath t ht) (hg t ht)
  have hpair (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      g.inner (d (0, t))
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => d (s, t)) 0 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun u => d (0, u)) t 1) =
      g.inner (f (0, t))
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => f (s, t)) 0 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun u => f (0, u)) t 1) := by
    have hv := (hpath t ht).mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
    have hparam : (fun s => d (s, t)) =ᶠ[𝓝 (0 : ℝ)] (fun s => f (s, t)) :=
      (hjoint t ht).comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
    have hw := hparam.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
    rw [(hjoint t ht).eq_of_nhds, hv, hw]
  have hE : (fun s => curveEnergy (I := I) g (fun t => d (s, t)) 0 L) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L) := by
    filter_upwards [heq] with s hs
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    exact (speedSq_eventuallyEq g (hs t ht)).eq_of_nhds
  have hfirst := firstVariation_curveEnergy_freeEndpoints_of_unitSpeed g (Function.curry d) L hd8 hL hdunit
  have hint : (∫ t in (0 : ℝ)..L, g.inner (d (0, t))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s => d (s, t)) 0 1)
      (covDerivAlong (I := I) g (fun u => d (0, u))
        (fun u => mfderiv 𝓘(ℝ, ℝ) I (fun r => d (0, r)) u 1) t)) = 0 := by
    calc
      _ = ∫ _t in (0 : ℝ)..L, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hL.le] at ht
        dsimp only
        erw [hacc t ht, ContinuousLinearMap.map_zero]
      _ = 0 := intervalIntegral.integral_zero
  apply (hfirst.congr_of_eventuallyEq hE.symm).congr_deriv
  dsimp only [Function.curry]
  erw [hint, sub_zero, hpair L ⟨hL.le, le_rfl⟩, hpair 0 ⟨le_rfl, hL.le⟩]

end Poincare.Geometry.Riemannian.Variation
