import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace DifferentialGeometry.Analysis.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalCone (C : Set E) (p : E) : Set E :=
  {ν | p ∈ C ∧ ∀ q ∈ C, inner ℝ ν (q - p) ≤ 0}

theorem mem_normalCone {C : Set E} {p ν : E} :
    ν ∈ normalCone C p ↔ p ∈ C ∧ ∀ q ∈ C, inner ℝ ν (q - p) ≤ 0 := Iff.rfl

@[simp] theorem zero_mem_normalCone {C : Set E} {p : E} :
    (0 : E) ∈ normalCone C p ↔ p ∈ C := by
  simp [normalCone]

theorem smul_mem_normalCone {C : Set E} {p ν : E} {a : ℝ}
    (ha : 0 ≤ a) (hν : ν ∈ normalCone C p) : a • ν ∈ normalCone C p := by
  refine ⟨hν.1, fun q hq => ?_⟩
  rw [real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos ha (hν.2 q hq)

theorem add_mem_normalCone {C : Set E} {p ν μ : E}
    (hν : ν ∈ normalCone C p) (hμ : μ ∈ normalCone C p) :
    ν + μ ∈ normalCone C p := by
  refine ⟨hν.1, fun q hq => ?_⟩
  rw [inner_add_left]
  exact add_nonpos (hν.2 q hq) (hμ.2 q hq)

theorem convex_normalCone (C : Set E) (p : E) : Convex ℝ (normalCone C p) := by
  intro ν hν μ hμ a b ha hb _
  exact add_mem_normalCone (smul_mem_normalCone ha hν) (smul_mem_normalCone hb hμ)

theorem isClosed_normalCone (C : Set E) (p : E) : IsClosed (normalCone C p) := by
  by_cases hp : p ∈ C
  · simp only [normalCone, hp, true_and]
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun q => isClosed_iInter fun _ =>
      isClosed_le (continuous_id.inner continuous_const) continuous_const
  · simp [normalCone, hp]

theorem sub_mem_normalCone_iff {C : Set E} (hC : Convex ℝ C) {z p : E} (hp : p ∈ C) :
    z - p ∈ normalCone C p ↔ ‖z - p‖ = Metric.infDist z C := by
  simp only [mem_normalCone, hp, true_and]
  rw [Metric.infDist_eq_iInf]
  simpa only [dist_eq_norm] using (norm_eq_iInf_iff_real_inner_le_zero hC hp).symm

theorem eq_of_sub_mem_normalCone {C : Set E} {z p q : E}
    (hp : z - p ∈ normalCone C p) (hq : z - q ∈ normalCone C q) : p = q := by
  have h1 := hp.2 q hq.1
  have h2 := hq.2 p hp.1
  have hsum : inner ℝ (p - q) (p - q) =
      inner ℝ (z - p) (q - p) + inner ℝ (z - q) (p - q) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hzero : inner ℝ (p - q) (p - q) = 0 :=
    le_antisymm (by rw [hsum]; exact add_nonpos h1 h2) (real_inner_self_nonneg)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

theorem existsUnique_norm_sub_eq_infDist {C : Set E}
    (hne : C.Nonempty) (hcomplete : IsComplete C) (hconvex : Convex ℝ C) (z : E) :
    ∃! p, p ∈ C ∧ ‖z - p‖ = Metric.infDist z C := by
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex z
  have hpmin : ‖z - p‖ = Metric.infDist z C := by
    rw [Metric.infDist_eq_iInf]
    simpa only [dist_eq_norm] using hmin
  refine ⟨p, ⟨hp, hpmin⟩, fun q hq => ?_⟩
  exact eq_of_sub_mem_normalCone ((sub_mem_normalCone_iff hconvex hq.1).mpr hq.2)
    ((sub_mem_normalCone_iff hconvex hp).mpr hpmin)

theorem inner_sub_le_infDist_of_mem_normalCone {C : Set E} {p ν : E}
    (hν : ν ∈ normalCone C p) (hνnorm : ‖ν‖ ≤ 1) (y : E) :
    inner ℝ ν (y - p) ≤ Metric.infDist y C := by
  apply (Metric.le_infDist ⟨p, hν.1⟩).mpr
  intro q hq
  have hnormal := hν.2 q hq
  have hinner := real_inner_le_norm ν (y - q)
  have hnorm := mul_le_of_le_one_left (norm_nonneg (y - q)) hνnorm
  rw [dist_eq_norm]
  rw [inner_sub_right] at hnormal hinner ⊢
  linarith

theorem exists_unit_mem_normalCone_of_notMem {C : Set E}
    (hne : C.Nonempty) (hcomplete : IsComplete C) (hconvex : Convex ℝ C)
    {z : E} (hz : z ∉ C) :
    ∃ p ∈ C, ‖z - p‖ = Metric.infDist z C ∧
      ‖‖z - p‖⁻¹ • (z - p)‖ = 1 ∧ ‖z - p‖⁻¹ • (z - p) ∈ normalCone C p ∧
      ∀ y : E, inner ℝ (‖z - p‖⁻¹ • (z - p)) (y - p) ≤ Metric.infDist y C := by
  obtain ⟨p, ⟨hp, hmin⟩, _⟩ := existsUnique_norm_sub_eq_infDist hne hcomplete hconvex z
  have hne : z - p ≠ 0 := fun h => hz (sub_eq_zero.mp h ▸ hp)
  have hnorm : ‖‖z - p‖⁻¹ • (z - p)‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
  have hnormal : ‖z - p‖⁻¹ • (z - p) ∈ normalCone C p :=
    smul_mem_normalCone (inv_nonneg.mpr (norm_nonneg _))
      ((sub_mem_normalCone_iff hconvex hp).mpr hmin)
  exact ⟨p, hp, hmin, hnorm, hnormal,
    inner_sub_le_infDist_of_mem_normalCone hnormal hnorm.le⟩

end DifferentialGeometry.Analysis.Convex
