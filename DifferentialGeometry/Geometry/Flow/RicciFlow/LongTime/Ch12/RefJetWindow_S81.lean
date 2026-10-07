import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RefJetScale_S81

set_option autoImplicit false

/-!
# CH12-S81 / G2: coarse reference-connection jets of the defect on a window `[t, u] ⊆ [t, 2t]`

`refJets_window_S81`: given a Λ-equivalence `g_r ≈ r h`, the Ricci-tower Shi bound `|∇^s Ric|_{g_r} ≤ KShi r^{-1-s/2}`
(`s ≤ N`) and the order-`q` jet of `g_t` against `h` (`≤ Cinit q · t`), the defect jets
`∇_h^j (g_r + 2 r Ric g_r)` are `≤ B r` in the `h`-norm, `j ≤ N`, with `B` independent of `t, u, S`.
Route: rescale to unit scale (`qSeq_S81`), apply the all-order Hamilton tower `covOrder_tower_const` on a compact
`L ⊇ K` and `ric_bound_field_on` on `interior L`; scale back.
-/

noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [CompleteSpace E] [I.Boundaryless] [FiniteDimensional ℝ E] [T2Space M] in
theorem qSeq_equiv_S81 {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (h : SmoothRiemannianMetric I M) {t u Λ : ℝ} (ht : 0 < t) (hΛ : 1 ≤ Λ) {V : Set M}
    (hequiv : ∀ r ∈ Icc t u, ∀ x ∈ V, ∀ v : TangentSpace I x,
      Λ⁻¹ * (r * h.inner x v v) ≤ (S.base.metric r).inner x v v ∧
        (S.base.metric r).inner x v v ≤ Λ * (r * h.inner x v v))
    {τ : ℝ} (hτ1 : 1 ≤ τ) (hτ2 : τ ≤ 2) (htτ : t * τ ∈ Icc t u) :
    MetricUniformEquivalentOn (I := I) V h (qSeq_S81 S t ht 0 τ) (2 * Λ) := by
  refine ⟨by linarith, fun x hx v => ?_⟩
  have hh : 0 ≤ h.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (h.pos x v hv).le
  obtain ⟨h1, h2⟩ := hequiv (t * τ) htτ x hx v
  have hΛ0 : 0 < Λ := by linarith
  have hΛi : 0 ≤ Λ⁻¹ := inv_nonneg.2 hΛ0.le
  simp only [qSeq_S81, scaleMetric_inner]
  constructor
  · calc (2 * Λ)⁻¹ * h.inner x v v = Λ⁻¹ * (1 / 2) * h.inner x v v := by field_simp
      _ ≤ Λ⁻¹ * τ * h.inner x v v :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hΛi) hh
      _ = t⁻¹ * (Λ⁻¹ * (t * τ * h.inner x v v)) := by field_simp
      _ ≤ t⁻¹ * (S.base.metric (t * τ)).inner x v v :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ht.le)
  · calc t⁻¹ * (S.base.metric (t * τ)).inner x v v ≤ t⁻¹ * (Λ * (t * τ * h.inner x v v)) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 ht.le)
      _ = Λ * τ * h.inner x v v := by field_simp
      _ ≤ 2 * Λ * h.inner x v v :=
          mul_le_mul_of_nonneg_right (by nlinarith) hh

omit [CompleteSpace E] [I.Boundaryless] in
theorem qSeq_shi_S81 {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t u KShi : ℝ} (ht : 0 < t) (hKShi : 0 ≤ KShi) {V : Set M} (N : ℕ)
    (hShi : ∀ s ≤ N, ∀ r ∈ Icc t u, ∀ x ∈ V,
      normSq0S (S.base.metric r) x (2 + s)
        (ricCovTower (I := I) (S.base.metric r) (S.base.metric r) s x) * r ^ (2 + s) ≤ KShi ^ 2)
    {τ : ℝ} (hτ1 : 1 ≤ τ) (htτ : t * τ ∈ Icc t u) {s : ℕ} (hs : s ≤ N) {x : M} (hx : x ∈ V) :
    Real.sqrt (normSq0S (qSeq_S81 S t ht 0 τ) x (2 + s)
      (ricCovTower (I := I) (qSeq_S81 S t ht 0 τ) (qSeq_S81 S t ht 0 τ) s x)) ≤ KShi := by
  have hshi := hShi s hs (t * τ) htτ x hx
  simp only [qSeq_S81]
  rw [ricCovTower_scaleMetric_left_S81, ricCovTower_scaleMetric_right_S81, normSq0S_scale]
  rw [Real.sqrt_le_iff]
  refine ⟨hKShi, ?_⟩
  have h0 : 0 ≤ normSq0S (S.base.metric (t * τ)) x (2 + s)
      (ricCovTower (I := I) (S.base.metric (t * τ)) (S.base.metric (t * τ)) s x) :=
    normSq0S_nonneg _ _ _ _
  have hpow : (t⁻¹)⁻¹ ^ (2 + s) ≤ (t * τ) ^ (2 + s) := by
    rw [inv_inv]
    exact pow_le_pow_left₀ ht.le (by nlinarith) _
  calc (t⁻¹)⁻¹ ^ (2 + s) * normSq0S (S.base.metric (t * τ)) x (2 + s)
        (ricCovTower (I := I) (S.base.metric (t * τ)) (S.base.metric (t * τ)) s x)
      ≤ (t * τ) ^ (2 + s) * normSq0S (S.base.metric (t * τ)) x (2 + s)
        (ricCovTower (I := I) (S.base.metric (t * τ)) (S.base.metric (t * τ)) s x) :=
        mul_le_mul_of_nonneg_right hpow h0
    _ ≤ KShi ^ 2 := by rw [mul_comm]; exact hshi

end GC.LongTime.Ch12
