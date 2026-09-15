import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Field.Periodic
import Mathlib.Topology.Order.Compact

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Function.Periodic.deriv {f : ℝ → E} {c : ℝ} (hf : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  rw [← deriv_comp_add_const]
  exact congrArg (fun g : ℝ → E => _root_.deriv g x) (funext hf)

namespace DifferentialGeometry.Analysis.Parabolic

theorem isCompact_image_firstJet_of_periodic
    {u : ℝ → ℝ → E} {s v : ℝ}
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 1 ×ˢ Icc s v))
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (Icc 0 1 ×ˢ Icc s v)) :
    IsCompact ((fun p : ℝ × ℝ => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)) ''
      (univ ×ˢ Icc s v)) := by
  let Φ : ℝ × ℝ → ℝ × E × E :=
    fun p => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)
  have hΦ : ContinuousOn Φ (Icc 0 1 ×ˢ Icc s v) :=
    continuousOn_snd.prodMk (hu.prodMk hDu)
  have heq : Φ '' (univ ×ˢ Icc s v) = Φ '' (Icc 0 1 ×ˢ Icc s v) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, t⟩, hxt, rfl⟩
      have hp : Function.Periodic (fun y => Φ (y, t)) 1 := by
        intro y
        dsimp only [Φ]
        rw [hper, (show Function.Periodic (fun z => u z t) 1 from fun z => hper z t).deriv y]
      obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ (by norm_num : (0 : ℝ) < 1) x
      exact ⟨(y, t), ⟨⟨hy.1, hy.2.le⟩, hxt.2⟩, hxy.symm⟩
    · exact image_mono (prod_mono (subset_univ _) Subset.rfl)
  change IsCompact (Φ '' (univ ×ˢ Icc s v))
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn hΦ

end DifferentialGeometry.Analysis.Parabolic
