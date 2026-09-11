import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Comp









noncomputable section

open Set Function
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {K E F : Type*} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem continuous_deriv_family_comp {f : K × ℝ → E} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hf : ∀ k, Differentiable ℝ (fun t => f (k, t))) (hc : Continuous f)
    (hd : Continuous (fun p : K × ℝ => deriv (fun t => f (p.1, t)) p.2))
    (hmap : ∀ p, f p ∈ U) :
    Continuous (fun p : K × ℝ => deriv (fun t => g (f (p.1, t))) p.2) := by
  have heq (p : K × ℝ) : deriv (fun t => g (f (p.1, t))) p.2 =
      fderiv ℝ g (f p) (deriv (fun t => f (p.1, t)) p.2) := by
    exact (((hg _ (hmap p)).contDiffAt (hU.mem_nhds (hmap p))).differentiableAt
      one_ne_zero |>.hasFDerivAt.comp_hasDerivAt p.2 (hf p.1 p.2).hasDerivAt).deriv
  simp_rw [heq]
  exact ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).comp_continuous hc hmap).clm_apply hd



theorem continuous_iteratedDeriv_family_comp {f : K × ℝ → E} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hf : ∀ k, ContDiff ℝ ∞ (fun t => f (k, t)))
    (hjet : ∀ n, Continuous (fun p : K × ℝ => iteratedDeriv n (fun t => f (p.1, t)) p.2))
    (hmap : ∀ p, f p ∈ U) (n : ℕ) :
    Continuous (fun p : K × ℝ => iteratedDeriv n (fun t => g (f (p.1, t))) p.2) := by
  have hc : Continuous f := by simpa only [iteratedDeriv_zero] using hjet 0
  have heq (p : K × ℝ) :
      iteratedDeriv n (fun t => g (f (p.1, t))) p.2 =
        ∑ c : OrderedFinpartition n,
          iteratedFDerivWithin ℝ c.length g U (f p)
            (fun j => iteratedDeriv (c.partSize j) (fun t => f (p.1, t)) p.2) := by
    simpa only [iteratedDerivWithin_univ, Function.comp_def, Prod.mk.eta] using
      iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition (hg _ (hmap p))
        (hf p.1).contDiffAt.contDiffWithinAt hU.uniqueDiffOn uniqueDiffOn_univ
        (mem_univ p.2) (fun t _ => hmap (p.1, t)) (show (n : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  simp_rw [heq]
  apply continuous_finsetSum
  intro c _
  exact continuous_eval.comp
    (((hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hU.uniqueDiffOn).comp_continuous
      hc hmap).prodMk (continuous_pi (fun j => hjet (c.partSize j))))

end DifferentialGeometry.Analysis
