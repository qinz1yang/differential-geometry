import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem MemWkp.mul_contDiffOn
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hΩ_compact : IsCompact (closure Ω)) (hΩU : closure Ω ⊆ U)
    {a f : E → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a U)
    (hf : MemWkp k p f Ω) : MemWkp k p (fun x => a x * f x) Ω := by
  obtain ⟨χ, hχ_smooth, hχ_compact, hχ_one, hχ_support, _⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hΩ_compact hU hΩU
  let b : E → ℝ := fun x => χ x * a x
  have hb_smooth : ContDiff ℝ (⊤ : ℕ∞) b := by
    simpa only [b, smul_eq_mul] using
      DifferentialGeometry.Analysis.contDiff_cutoff_smul hU hχ_smooth hχ_support ha
  have hb_compact : HasCompactSupport b := by
    change HasCompactSupport (fun x => χ x • a x)
    exact hχ_compact.smul_right
  obtain ⟨C, _, hC⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport hb_smooth hb_compact k
  have hbf : MemWkp k p (fun x => b x * f x) Ω :=
    MemWkp.smul_smooth_bounded k hp hΩ hb_smooth
      (fun j hj x _ => hC x j hj) hf
  have heq : (fun x => b x * f x) =ᵐ[volume.restrict Ω] (fun x => a x * f x) := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    have hχx : χ x = 1 := hχ_one.self_of_nhdsSet (subset_closure hx)
    simp only [b, hχx, one_mul]
  exact (MemWkp_congr_ae hp hΩ heq).mp hbf

end DifferentialGeometry.Analysis.Sobolev.Euclidean
