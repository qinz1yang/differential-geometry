import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HLiftAux_S86

/-!
# CH12-S86 G1: radial path lifting `hlift_S86`
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic Set Manifold
open DifferentialGeometry.CheegerGromovCompactness TopologicalSpace
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- Speed comparison of `f` on an open set where `ckErr 0 < 1/8`:
`|df v|²_{gN} ≤ 2 |v|²_h` and `|v|²_h ≤ 2 |df v|²_{gN}`. -/
theorem speed_comparison_S86 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (gN : SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N) (B : Opens H.Carrier)
    (hfB : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f B)
    (hinj : ∀ y ∈ B, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    (hck : ∀ p ∈ B, ckErr_O19 H gN 1 f 0 p < 1 / 8) :
    ∀ x ∈ B, ∀ v : TangentSpace (𝓡 3) x,
      gN.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        2 * H.metric.inner x v v ∧
      H.metric.inner x v v ≤
        2 * gN.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) := by
  intro x hx v
  have h1 := hck x hx
  rw [ckErr_one_eq_raw_O19, rawNorm_eq_metricDerivNorm_C4 gN H.metric f B hfB hinj 0 ⟨x, hx⟩]
    at h1
  have h2 := metric_equiv_two_rev_S76 _ (H.metric.restrictOpen B) ⟨x, hx⟩ (δ := 1 / 8)
    (by norm_num) h1.le v
  have h3 := metric_equiv_two_S76 _ (H.metric.restrictOpen B) ⟨x, hx⟩ (δ := 1 / 8)
    (by norm_num) h1.le v
  have e : localPullInner (I := 𝓡 3) (J := 𝓡 3) gN (fun z : B => f z) ⟨x, hx⟩ v v =
      gN.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) := by
    refine (localPullInner_apply (I := 𝓡 3) (J := 𝓡 3) gN (fun z : B => f z) ⟨x, hx⟩ v v).trans ?_
    exact congrArg₂ (fun a b => gN.inner (f x) a b) (mfderiv_comp_val_C4 f B hfB ⟨x, hx⟩ v)
      (mfderiv_comp_val_C4 f B hfB ⟨x, hx⟩ v)
  exact ⟨e.symm.le.trans h3.2, h2.2.trans (mul_le_mul_of_nonneg_left e.le (by norm_num))⟩

end GC.LongTime.Ch12
