import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families
import DifferentialGeometry.Topology.Manifold.AddCircle
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {P E F H M : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem eventually_uniform_loop_family_lift_derivatives
    (e : M → F) (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {f : P → ℝ × AddCircle (1 : ℝ) → M} {U : Set P} {J : Set ℝ}
    (hU : IsOpen U) (hJ : UniqueDiffOn ℝ J) (hcompact : IsCompact J)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ).prod 𝓘(ℝ))) I ∞
      (Function.uncurry f) (U ×ˢ J ×ˢ univ))
    {a : P} (ha : a ∈ U) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 a, ∀ m : ℕ, m ≤ n → ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => e (f p (r.2, (r.1 : AddCircle (1 : ℝ))))) (univ ×ˢ J) q -
        iteratedFDerivWithin ℝ m
          (fun r : ℝ × ℝ => e (f a (r.2, (r.1 : AddCircle (1 : ℝ))))) (univ ×ˢ J) q‖ < ε := by
  let L : P × (ℝ × ℝ) → P × (ℝ × AddCircle (1 : ℝ)) :=
    fun q => (q.1, q.2.2, (q.2.1 : AddCircle (1 : ℝ)))
  have hP : ContMDiff 𝓘(ℝ, P × (ℝ × ℝ)) 𝓘(ℝ, P) ∞
      (fun q : P × (ℝ × ℝ) => q.1) := contDiff_fst.contMDiff
  have ht : ContMDiff 𝓘(ℝ, P × (ℝ × ℝ)) 𝓘(ℝ) ∞
      (fun q : P × (ℝ × ℝ) => q.2.2) :=
    (contDiff_snd.comp contDiff_snd).contMDiff
  have hx : ContMDiff 𝓘(ℝ, P × (ℝ × ℝ)) 𝓘(ℝ) ∞
      (fun q : P × (ℝ × ℝ) => q.2.1) :=
    (contDiff_fst.comp contDiff_snd).contMDiff
  have hcircle : ContMDiff 𝓘(ℝ, P × (ℝ × ℝ)) 𝓘(ℝ) ∞
      (fun q : P × (ℝ × ℝ) => (q.2.1 : AddCircle (1 : ℝ))) :=
    AddCircle.contMDiff_coe.comp hx
  have hL : ContMDiff 𝓘(ℝ, P × (ℝ × ℝ))
      (𝓘(ℝ, P).prod (𝓘(ℝ).prod 𝓘(ℝ))) ∞ L :=
    hP.prodMk (ht.prodMk hcircle)
  have hcomp : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) I ∞
      (fun q : P × (ℝ × ℝ) => f q.1 (q.2.2, (q.2.1 : AddCircle (1 : ℝ))))
      (U ×ˢ univ ×ˢ J) := by
    exact hf.comp hL.contMDiffOn (fun q hq => ⟨hq.1, hq.2.2, mem_univ _⟩)
  have hecomp : ContDiffOn ℝ ∞
      (fun q : P × (ℝ × ℝ) => e (f q.1 (q.2.2, (q.2.1 : AddCircle (1 : ℝ)))))
      (U ×ˢ univ ×ˢ J) :=
    contMDiffOn_iff_contDiffOn.mp (he.comp_contMDiffOn hcomp)
  exact DifferentialGeometry.Analysis.eventually_uniform_iteratedFDerivWithin_prod_slice
    hU (uniqueDiffOn_univ.prod hJ) hecomp ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod hcompact)
      (prod_mono (subset_univ _) subset_rfl) ha n hε

end DifferentialGeometry.Topology

end
