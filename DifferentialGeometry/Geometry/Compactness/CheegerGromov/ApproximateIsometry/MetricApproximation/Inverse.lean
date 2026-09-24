import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Relative
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
  [IsManifold I ∞ N] [SigmaCompactSpace N]

theorem exists_inverse_map_metric_approximation_of_pullback_bound
    (Φ : PartialDiffeomorph I I M N ∞)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (hU : (U : Set M) ⊆ Φ.source)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (G : SmoothRiemannianMetric I U)
    (hG : ∀ (z : U) (v w : TangentSpace I z),
      G.inner z v w = h.inner (Φ z)
        (mfderiv I I (Φ : M → N) (z : M) v)
        (mfderiv I I (Φ : M → N) (z : M) w))
    {u : Set U} (hu : IsOpen u)
    {p : ℕ} {δ eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1)
    (hδ : 0 ≤ δ)
    (hδdim : (Module.finrank ℝ E : ℝ) * δ ≤ 1 / 2)
    (hδbudget : metricReferenceChangeFactor (E := E) p * δ ≤ eps)
    (hclose : ∀ z ∈ u, ∀ a ≤ p,
      metricDerivNorm a G (g.restrictOpen U) (g.restrictOpen U) z ≤ δ)
    {K K' : Set N} (hK' : IsCompact K') (hKK' : K ⊆ interior K')
    (htarget : K' ⊆ Φ.target) (hcapture : K ⊆ (fun z : U => Φ z) '' u) :
    Nonempty (MapMetricApproximationOn K eps p (Φ.symm : N → M) h g) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hδ1 : δ ≤ 1 := by
    have hfour := mul_le_mul_of_nonneg_right
      (four_le_metric_reference_change_factor (E := E) p) hδ
    linarith
  have hbound : ∀ a ≤ p, ∀ z ∈ u,
      metricDerivNorm a (g.restrictOpen U) G G z ≤ eps := by
    intro a ha z hz
    exact metric_deriv_norm_reference_change_le hu (g.restrictOpen U) G
      (g.restrictOpen U) p hδ hδ1 hδdim hδbudget
      (fun y _hy q _hq => by simpa only [metricDerivNorm_self] using hδ)
      hclose z hz a ha
  let Ψ := DifferentialGeometry.PartialDiffeomorph.refl (I := I) M
  have hid : ∀ (z : U) (v w : TangentSpace I z),
      (g.restrictOpen U).inner z v w = g.inner
        ((Ψ : M → M) z)
        (mfderiv I I (Ψ : M → M) (z : M) v)
        (mfderiv I I (Ψ : M → M) (z : M) w) := by
    intro z v w
    change g.inner z v w = g.inner z (mfderiv I I id (z : M) v)
      (mfderiv I I id (z : M) w)
    rw [mfderiv_id]
    rfl
  have hsource :
      K' ⊆ (Φ.symm.trans Ψ).source := by
    intro y hy
    exact ⟨htarget hy, mem_univ _⟩
  have happrox := exists_relative_map_metric_approximation_of_pullback_bound
    Φ Ψ U hU (fun _ _ => mem_univ _)
    h g G (g.restrictOpen U) hG hid hK' hKK' hsource hcapture heps heps1 hbound
  exact happrox

theorem exists_inverse_map_metric_approximation_tolerance
    (p : ℕ) {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Φ : PartialDiffeomorph I I M N ∞)
      (U : TopologicalSpace.Opens M) [SigmaCompactSpace U],
      (U : Set M) ⊆ Φ.source →
      ∀ (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
        (G : SmoothRiemannianMetric I U),
      (∀ (z : U) (v w : TangentSpace I z),
        G.inner z v w = h.inner (Φ z)
          (mfderiv I I (Φ : M → N) (z : M) v)
          (mfderiv I I (Φ : M → N) (z : M) w)) →
      ∀ (u : Set U), IsOpen u →
      (∀ z ∈ u, ∀ a ≤ p,
        metricDerivNorm a G (g.restrictOpen U) (g.restrictOpen U) z ≤ δ) →
      ∀ K K' : Set N, IsCompact K' → K ⊆ interior K' →
        K' ⊆ Φ.target → K ⊆ (fun z : U => Φ z) '' u →
        Nonempty (MapMetricApproximationOn K eps p (Φ.symm : N → M) h g) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨δ, hδ, _hδ1, hδdim, hδbudget⟩ :=
    exists_metric_reference_change_delta (E := E) p heps
  refine ⟨δ, hδ, ?_⟩
  intro Φ U hσ hU g h G hG u hu hclose K K' hK' hKK' htarget hcapture
  exact exists_inverse_map_metric_approximation_of_pullback_bound Φ U hU g h G hG hu
    heps heps1 hδ.le hδdim hδbudget hclose hK' hKK' htarget hcapture

end DifferentialGeometry.CheegerGromovCompactness
