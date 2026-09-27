import DifferentialGeometry.Geometry.Metric.DirectLimit.Defs
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.QuadraticBounds
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.SmoothSeqSystem

open Filter Set
open CheegerGromovCompactness
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {A : ℕ → Type*} [∀ j, TopologicalSpace (A j)] [∀ j, ChartedSpace H (A j)]
  [∀ j, IsManifold I ∞ (A j)] [∀ j, T2Space (A j)]
  [∀ j, Nonempty (A j)]
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)]

private theorem mfderiv_incl_surjective
    (S : SmoothSeqSystem I A) (gInf : ∀ j, SmoothRiemannianMetric I (A j))
    (hg : S.MetricCocycle gInf) (j : ℕ) (a : A j) :
    Function.Surjective (mfderiv I I (S.toSeqSystem.incl j) a) := by
  let D := mfderiv I I (S.toSeqSystem.incl j) a
  have hinj : Function.Injective D := by
    intro v w hvw
    have hzero : D (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have hinner := S.limitMetric_pullback gInf hg j a (v - w) (v - w)
    change (S.limitMetric gInf hg).inner _ (D (v - w)) (D (v - w)) = _ at hinner
    rw [hzero] at hinner
    have hvanish : (gInf j).inner a (v - w) (v - w) = 0 := by simpa using hinner.symm
    by_contra hvw'
    exact (ne_of_gt ((gInf j).pos a (v - w) (sub_ne_zero.mpr hvw'))) hvanish
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rfl : Module.finrank ℝ (TangentSpace I a) =
      Module.finrank ℝ (TangentSpace I (S.toSeqSystem.incl j a)))
    (f := D.toLinearMap)).1 hinj

theorem eventually_quadratic_bounds_of_pullback_convergence
    (S : SmoothSeqSystem I A) (gInf : ∀ j, SmoothRiemannianMetric I (A j))
    (hg : S.MetricCocycle gInf)
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (Φ : ∀ k, PartialDiffeomorph I I S.toSeqSystem.Lim (M k) ∞)
    (hsource : ∀ j, ∀ᶠ k in atTop, Set.range (S.toSeqSystem.incl j) ⊆ (Φ k).source)
    (gPull : ∀ j, ℕ → SmoothRiemannianMetric I (A j))
    (gRef : ∀ j, SmoothRiemannianMetric I (A j))
    (hconv : ∀ j, ∀ K : Set (A j), IsCompact K →
      MetricCPConvergenceOn K 0 (gPull j) (gInf j) (gRef j))
    (hinner : ∀ j, ∀ᶠ k in atTop, ∀ (a : A j) (v : TangentSpace I a),
      (gPull j k).inner a v v =
        (g k).inner ((Φ k) (S.toSeqSystem.incl j a))
          (mfderiv I I ((Φ k : S.toSeqSystem.Lim → M k) ∘ S.toSeqSystem.incl j) a v)
          (mfderiv I I ((Φ k : S.toSeqSystem.Lim → M k) ∘ S.toSeqSystem.incl j) a v))
    {K : Set S.toSeqSystem.Lim} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, K ⊆ (Φ k).source ∧ ∀ z ∈ K, ∀ v : TangentSpace I z,
      (1 - ε) * (S.limitMetric gInf hg).inner z v v ≤
        (g k).inner (Φ k z) (mfderiv I I (Φ k : S.toSeqSystem.Lim → M k) z v)
          (mfderiv I I (Φ k : S.toSeqSystem.Lim → M k) z v) ∧
      (g k).inner (Φ k z) (mfderiv I I (Φ k : S.toSeqSystem.Lim → M k) z v)
          (mfderiv I I (Φ k : S.toSeqSystem.Lim → M k) z v) ≤
        (1 + ε) * (S.limitMetric gInf hg).inner z v v := by
  obtain ⟨j, Kj, hKj, rfl⟩ := S.toSeqSystem.exists_compact_stage_representation hK
  filter_upwards [hsource j, hinner j,
    (hconv j Kj hKj).eventually_quadratic_bounds hKj hε] with k hsrc hmetric hquad
  refine ⟨(Set.image_subset_range _ _).trans hsrc, ?_⟩
  rintro z ⟨a, ha, rfl⟩ v
  obtain ⟨w, rfl⟩ := mfderiv_incl_surjective S gInf hg j a v
  rw [S.limitMetric_pullback gInf hg j a w w]
  have hΦ := (Φ k).mdifferentiableAt (by simp) (hsrc ⟨a, rfl⟩)
  have hincl := (S.contMDiff_incl j a).mdifferentiableAt (by simp)
  have hmetric' := hmetric a w
  rw [mfderiv_comp_apply a hΦ hincl] at hmetric'
  rw [← hmetric']
  exact hquad a ha w

end DifferentialGeometry.SmoothSeqSystem
