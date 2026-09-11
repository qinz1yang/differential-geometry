import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Real

noncomputable section

open Filter Set Topology
open scoped NNReal

namespace DifferentialGeometry.Geometry

variable {M : Type*} [MetricSpace M] [ProperSpace M]

theorem exists_isometry_mapClusterPt_of_dist_min
    (p : M) (σ : ℕ → ℝ≥0 → M) (L : ℕ → ℝ≥0)
    (hL : Tendsto L atTop atTop) (hzero : ∀ n, σ n 0 = p)
    (hdist : ∀ n s t, dist (σ n s) (σ n t) = dist (min s (L n)) (min t (L n))) :
    ∃ γ : ℝ≥0 → M, γ 0 = p ∧ Isometry γ ∧ MapClusterPt γ atTop σ := by
  have hcompact : IsCompact {γ : ℝ≥0 → M | ∀ t : ℝ≥0, γ t ∈ Metric.closedBall p (t : ℝ)} :=
    isCompact_pi_infinite fun t ↦ isCompact_closedBall p (t : ℝ)
  have hmem : ∀ᶠ n in atTop, σ n ∈ {γ : ℝ≥0 → M | ∀ t : ℝ≥0, γ t ∈ Metric.closedBall p (t : ℝ)} := by
    apply Eventually.of_forall
    intro n t
    rw [Metric.mem_closedBall, ← hzero n, hdist]
    simp only [min_eq_left (zero_le : (0 : ℝ≥0) ≤ L n), NNReal.dist_eq,
      NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast min_le_left t (L n)
  obtain ⟨γ, hγmem, hγ⟩ := hcompact.exists_mapClusterPt (Filter.le_principal_iff.mpr hmem)
  refine ⟨γ, ?_, Isometry.of_dist_eq fun s t ↦ ?_, hγ⟩
  · have hz := hγmem 0
    simpa using hz
  · have hclosed : IsClosed {f : ℝ≥0 → M | dist (f s) (f t) = dist s t} :=
      isClosed_eq ((continuous_apply s).dist (continuous_apply t)) continuous_const
    apply hclosed.mem_of_mapClusterPt hγ
    filter_upwards [hL.eventually (eventually_ge_atTop (max s t))] with n hn
    rw [hdist, min_eq_left ((le_max_left s t).trans hn),
      min_eq_left ((le_max_right s t).trans hn)]

theorem exists_isometry_ray [NoncompactSpace M] (p : M)
    (hsegment : ∀ q : M, ∃ δ : Icc (0 : ℝ≥0) (nndist p q) → M,
      Isometry δ ∧ δ ⟨0, by simp⟩ = p ∧ δ ⟨nndist p q, by simp⟩ = q) :
    ∃ γ : ℝ≥0 → M, γ 0 = p ∧ Isometry γ := by
  classical
  have hfar : ∀ n : ℕ, ∃ q : M, (n : ℝ) < dist p q := by
    intro n
    by_contra hn
    push Not at hn
    apply (isCompact_closedBall p (n : ℝ)).ne_univ
    exact Set.eq_univ_of_forall fun q ↦ by
      rw [Metric.mem_closedBall, dist_comm]
      exact hn q
  choose q hq using hfar
  choose δ hδ hδzero hδend using fun n ↦ hsegment (q n)
  let L : ℕ → ℝ≥0 := fun n ↦ nndist p (q n)
  let σ : ℕ → ℝ≥0 → M := fun n t ↦ δ n ⟨min t (L n), by simp [L]⟩
  have hL : Tendsto L atTop atTop := by
    apply NNReal.tendsto_coe_atTop.mp
    exact tendsto_atTop_mono (fun n ↦ (hq n).le) tendsto_natCast_atTop_atTop
  have hzero : ∀ n, σ n 0 = p := by
    intro n
    simpa [σ] using hδzero n
  have hdist : ∀ n s t, dist (σ n s) (σ n t) = dist (min s (L n)) (min t (L n)) := by
    intro n s t
    exact (hδ n).dist_eq _ _
  obtain ⟨γ, hγzero, hγ, _⟩ := exists_isometry_mapClusterPt_of_dist_min p σ L hL hzero hdist
  exact ⟨γ, hγzero, hγ⟩

end DifferentialGeometry.Geometry
