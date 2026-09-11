import DifferentialGeometry.Analysis.Calculus.Inverse.ParameterizedInverse

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

theorem exists_contDiffOn_inverse_of_bijective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {h : E × ℝ → ℝ} {V : Set E} (hV : IsOpen V)
    (hh : ContDiffOn ℝ ∞ h (V ×ˢ univ))
    (hbij : ∀ p ∈ V, Function.Bijective (fun x ↦ h (p, x)))
    (hvertical : ∀ p ∈ V, ∀ x, fderiv ℝ h (p, x) (0, 1) ≠ 0) :
    ∃ R : E × ℝ → ℝ, ContDiffOn ℝ ∞ R (V ×ˢ univ) ∧
      (∀ p ∈ V, ∀ x, R (p, h (p, x)) = x) ∧
      ∀ p ∈ V, ∀ y, h (p, R (p, y)) = y := by
  let R : E × ℝ → ℝ := fun q ↦ Function.invFun (fun x ↦ h (q.1, x)) q.2
  have hleft (p : E) (hp : p ∈ V) (x : ℝ) : R (p, h (p, x)) = x :=
    Function.leftInverse_invFun (hbij p hp).1 x
  have hright (p : E) (hp : p ∈ V) (y : ℝ) : h (p, R (p, y)) = y :=
    Function.rightInverse_invFun (hbij p hp).2 y
  refine ⟨R, ?_, hleft, hright⟩
  intro q hq
  obtain ⟨e, hp, _, _, heinv, he, hparam⟩ := exists_localInverse_preserving_parameter
    hh (hV.prod isOpen_univ) (show (q.1, R q) ∈ V ×ˢ univ from ⟨hq.1, mem_univ _⟩)
    (hvertical q.1 hq.1 (R q))
  have heq : e (q.1, R q) = q := by rw [he, hright q.1 hq.1]
  have ht : q ∈ e.target := heq ▸ e.map_source hp
  have hagree : R =ᶠ[𝓝[V ×ˢ univ] q] fun z ↦ (e.symm z).2 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds ht), self_mem_nhdsWithin]
      with z hz hzV
    apply (hbij z.1 hzV.1).1
    change h (z.1, R (z.1, z.2)) = h (z.1, (e.symm z).2)
    rw [hright z.1 hzV.1]
    have hpz := hparam z hz
    have hz' : (z.1, (e.symm z).2) = e.symm z := Prod.ext hpz.1.symm rfl
    exact (congrArg h hz').trans hpz.2 |>.symm
  have hat : R q = (e.symm q).2 := hagree.eq_of_nhdsWithin hq
  exact ((heinv.contDiffAt (e.open_target.mem_nhds ht)).snd).contDiffWithinAt.congr_of_eventuallyEq
    hagree hat

end DifferentialGeometry.Analysis
