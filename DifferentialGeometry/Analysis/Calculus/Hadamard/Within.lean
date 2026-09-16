import DifferentialGeometry.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Convex.Segment

section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem hadamard_factorization_of_contDiffOn {f : ℝ → F} {a x : ℝ}
    (hf : ContDiffOn ℝ 1 f (uIcc a x)) :
    f x - f a = (x - a) • hadamardFactor f a x := by
  rw [← intervalIntegral.integral_deriv_of_contDiffOn_uIcc hf]
  symm
  simpa only [hadamardFactor, mul_comm (x - a), zero_mul, one_mul, add_zero,
    add_sub_cancel] using
    intervalIntegral.smul_integral_comp_add_mul (deriv f) (x - a) a
      (a := (0 : ℝ)) (b := 1)

end DifferentialGeometry.Analysis.Calculus


end

section

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def hadamardFactorWithin (f : ℝ → F) (U : Set ℝ) (a x : ℝ) : F :=
  ∫ t in (0 : ℝ)..1, derivWithin f U (a + t * (x - a))

theorem hadamardFactorWithin_eq_hadamardFactor
    {f g : ℝ → F} {U W : Set ℝ} (hU : UniqueDiffOn ℝ U) (hW : IsOpen W)
    (heq : EqOn f g (W ∩ U)) (hg : DifferentiableOn ℝ g W)
    {a x : ℝ} (hseg : uIcc a x ⊆ W ∩ U) :
    hadamardFactorWithin f U a x = hadamardFactor g a x := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  have hr : a + t * (x - a) ∈ uIcc a x := by
    simpa only [segment_eq_uIcc, AffineMap.lineMap_apply_ring', add_comm] using
      (lineMap_mem_segment (𝕜 := ℝ) a x ht')
  have hpoint := hseg hr
  have hnear : f =ᶠ[𝓝[U] (a + t * (x - a))] g := by
    filter_upwards [nhdsWithin_le_nhds (hW.mem_nhds hpoint.1),
      self_mem_nhdsWithin] with y hyW hyU
    exact heq ⟨hyW, hyU⟩
  dsimp only
  rw [hnear.derivWithin_eq_of_mem hpoint.2]
  exact ((hg _ hpoint.1).differentiableAt (hW.mem_nhds hpoint.1)).derivWithin
    (hU _ hpoint.2)

theorem hadamardFactorWithin_Ici_zero_eq {f : ℝ → F} {x : ℝ} (hx : 0 < x) :
    hadamardFactorWithin f (Ici 0) 0 x = hadamardFactor f 0 x := by
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall fun t ht => by
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
    simp only [sub_zero, zero_add]
    exact derivWithin_of_mem_nhds (Ici_mem_nhds (mul_pos ht'.1 hx))

theorem hadamardFactorWithin_self [CompleteSpace F] (f : ℝ → F) (U : Set ℝ) (a : ℝ) :
    hadamardFactorWithin f U a a = derivWithin f U a := by
  simp [hadamardFactorWithin]

end DifferentialGeometry.Analysis.Calculus

end

end
