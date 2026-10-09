import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Comparison

set_option autoImplicit false

/-!
# CH12-S60 / G1: the abstract reference-change chain for `hcomp`

On a manifold `N` with metrics `gBase` (the reference `h`), `gHat` (the pulled-back reference
`e^*h`) and a metric `A` (the pulled-back `e^*(c f^*g')`):

if `gHat` is `C^p`-close to `gBase` (w.r.t. `gBase`) and `A` is `C^p`-close to `gHat`
(w.r.t. `gHat`, which is what the naturality of the pull-back gives from the hypothesis on `f`),
then `A` is `C^p`-close to `gBase` (w.r.t. `gBase`).  Two applications of
`metric_deriv_norm_reference_change_le`.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- `metricDerivNorm q g g R = 0`. -/
theorem metricDerivNorm_self_S60 {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [T2Space N] [IsManifold I ∞ N] (g R : SmoothRiemannianMetric I N) (q : ℕ) (x : N) :
    metricDerivNorm (I := I) q g g R x = 0 := by
  unfold metricDerivNorm metricDiffCovDerivAt
  simp [Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S]

/-- **The two-step reference change** (`δ` depends only on `p, ε` and `dim E`). -/
theorem ckComp_abstract_S60 (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
      [IsManifold I ∞ N] {u : Set N}, IsOpen u → ∀ (A gHat gBase : SmoothRiemannianMetric I N),
      (∀ x ∈ u, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := I) q gHat gBase gBase x ≤ δ) →
      (∀ x ∈ u, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := I) q A gHat gHat x ≤ δ) →
      ∀ x ∈ u, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := I) q A gBase gBase x ≤ ε := by
  obtain ⟨δ₂, hδ₂0, hδ₂1, hδ₂dim, hδ₂bud⟩ := exists_metric_reference_change_delta (E := E) p hε
  obtain ⟨δ₁, hδ₁0, hδ₁1, hδ₁dim, hδ₁bud⟩ :=
    exists_metric_reference_change_delta (E := E) p hδ₂0
  refine ⟨min δ₁ δ₂, lt_min hδ₁0 hδ₂0, ?_⟩
  intro N _ _ _ _ u hu A gHat gBase hhat hA x hx q hq
  have h1 : ∀ y ∈ u, ∀ r : ℕ, r ≤ p → metricDerivNorm (I := I) r gBase gHat gHat y ≤ δ₂ := by
    intro y hy r hr
    exact metric_deriv_norm_reference_change_le (I := I) hu gBase gHat gBase p hδ₁0.le hδ₁1.le
      hδ₁dim hδ₁bud (fun z _ s _ => by rw [metricDerivNorm_self_S60]; exact hδ₁0.le)
      (fun z hz s hs => (hhat z hz s hs).trans (min_le_left _ _)) y hy r hr
  exact metric_deriv_norm_reference_change_le (I := I) hu A gBase gHat p hδ₂0.le hδ₂1.le
    hδ₂dim hδ₂bud (fun z hz s hs => (hA z hz s hs).trans (min_le_right _ _)) h1 x hx q hq

end GC.LongTime.Ch12
