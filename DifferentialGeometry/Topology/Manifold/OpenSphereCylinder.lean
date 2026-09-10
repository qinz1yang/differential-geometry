import DifferentialGeometry.Topology.Manifold.SphereDirection
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Set Metric Manifold Module
open scoped ContDiff

namespace Poincare.Topology.Manifold

def puncturedSpace (E : Type*) [NormedAddCommGroup E] : TopologicalSpace.Opens E :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

def sphereProdRealDiffeomorphPunctured
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    Diffeomorph ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, E)
      (sphere (0 : E) 1 × ℝ) (puncturedSpace E) ∞ := by
  let f : sphere (0 : E) 1 × ℝ → puncturedSpace E := fun q ↦
    ⟨Real.exp q.2 • (q.1 : E), smul_ne_zero (Real.exp_ne_zero _) (ne_zero_of_mem_unit_sphere q.1)⟩
  let g : puncturedSpace E → sphere (0 : E) 1 × ℝ := fun x ↦
    (sphereDirection v x, Real.log ‖(x : E)‖)
  have hf : ContMDiff ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff (puncturedSpace E) f).mp
    exact (Real.contDiff_exp.contMDiff.comp contMDiff_snd).smul
      (contMDiff_coe_sphere.comp contMDiff_fst)
  have hg : ContMDiff 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ)) ∞ g := by
    have hd : ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞ (fun x : puncturedSpace E ↦ sphereDirection v x) :=
      contMDiffOn_univ.mp ((contMDiffOn_sphereDirection v).comp contMDiff_subtype_val.contMDiffOn
        (fun x _ ↦ x.property))
    have hl : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun x : puncturedSpace E ↦ Real.log ‖(x : E)‖) := by
      intro x
      exact ((Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr x.property)).comp (x : E)
        (contDiffAt_norm ℝ x.property)).contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt
    exact hd.prodMk hl
  refine { toEquiv := { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
           contMDiff_toFun := hf, contMDiff_invFun := hg }
  · intro q
    apply Prod.ext
    · exact sphereDirection_pos_smul v q.1 (Real.exp_pos _)
    · change Real.log ‖Real.exp q.2 • (q.1 : E)‖ = q.2
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_eq_of_mem_sphere,
        mul_one, Real.log_exp]
  · intro x
    apply Subtype.ext
    change Real.exp (Real.log ‖(x : E)‖) • (sphereDirection v (x : E) : E) = x
    rw [Real.exp_log (norm_pos_iff.mpr x.property)]
    exact norm_smul_sphereDirection v x.property

end Poincare.Topology.Manifold
