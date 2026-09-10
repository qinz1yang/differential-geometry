import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

open Set

namespace DifferentialGeometry.Geometry

variable {M : Type*} [PseudoMetricSpace M]

theorem isometry_Icc_of_lipschitzOnWith_of_dist_eq
    {γ : ℝ → M} {a b : ℝ} (hγ : LipschitzOnWith 1 γ (Icc a b))
    (hend : dist (γ a) (γ b) = b - a) :
    Isometry (fun t : Icc a b ↦ γ t) := by
  apply Isometry.of_dist_eq
  intro s t
  suffices h : ∀ s t : Icc a b, (s : ℝ) ≤ t → dist (γ s) (γ t) = (t : ℝ) - s by
    rcases le_total (s : ℝ) t with hst | hts
    · simpa [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)] using h s t hst
    · rw [dist_comm, h t s hts]
      simp [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
  intro s t hst
  have hab : a ≤ b := s.2.1.trans s.2.2
  have hstUpper := hγ.dist_le_mul (s : ℝ) s.2 t t.2
  have haUpper := hγ.dist_le_mul a ⟨le_rfl, hab⟩ (s : ℝ) s.2
  have hbUpper := hγ.dist_le_mul (t : ℝ) t.2 b ⟨hab, le_rfl⟩
  simp only [NNReal.coe_one, one_mul, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hst), abs_of_nonpos (sub_nonpos.mpr s.2.1),
    abs_of_nonpos (sub_nonpos.mpr t.2.2)] at hstUpper haUpper hbUpper
  have htri := dist_triangle4 (γ a) (γ s) (γ t) (γ b)
  rw [hend] at htri
  linarith

end DifferentialGeometry.Geometry
