import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

theorem exists_contDiffOn_implicit_graph_of_deriv_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ∞ω} (hn : n ≠ 0) {U : Set E} (hU : IsOpen U)
    {F : E × ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : ContDiffOn ℝ n F (U ×ˢ Ioo a b))
    (hc : ∀ x ∈ U, ContinuousOn (fun t => F (x, t)) (Icc a b))
    (hderiv : ∀ x ∈ U, ∀ t ∈ Ioo a b, deriv (fun s => F (x, s)) t < 0)
    (ha : ∀ x ∈ U, 0 < F (x, a)) (hb : ∀ x ∈ U, F (x, b) < 0) :
    ∃ g : E → ℝ, ContDiffOn ℝ n g U ∧
      (∀ x ∈ U, g x ∈ Ioo a b ∧ F (x, g x) = 0) ∧
      ∀ x ∈ U, ∀ t ∈ Icc a b,
        (F (x, t) = 0 ↔ t = g x) ∧
        (0 ≤ F (x, t) ↔ t ≤ g x) ∧ (0 < F (x, t) ↔ t < g x) := by
  classical
  have hanti (x : E) (hx : x ∈ U) : StrictAntiOn (fun t => F (x, t)) (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hc x hx)
    simpa only [interior_Icc] using hderiv x hx
  have hroot (x : E) (hx : x ∈ U) : ∃ t ∈ Ioo a b, F (x, t) = 0 := by
    obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc' hab.le (hc x hx) ⟨(hb x hx).le, (ha x hx).le⟩
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, hFt⟩
    · intro hh
      rw [← hh] at hFt
      exact (ha x hx).ne' hFt
    · intro hh
      rw [hh] at hFt
      exact (hb x hx).ne hFt
  let g : E → ℝ := fun x => if hx : x ∈ U then Classical.choose (hroot x hx) else 0
  have hspec (x : E) (hx : x ∈ U) : g x ∈ Ioo a b ∧ F (x, g x) = 0 := by
    dsimp only [g]
    rw [dif_pos hx]
    exact Classical.choose_spec (hroot x hx)
  have huniq (x : E) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Icc a b) :
      F (x, t) = 0 ↔ t = g x := by
    constructor
    · intro hh
      exact (hanti x hx).injOn ht (Ioo_subset_Icc_self (hspec x hx).1)
        (hh.trans (hspec x hx).2.symm)
    · rintro rfl
      exact (hspec x hx).2
  refine ⟨g, ?_, hspec, ?_⟩
  · intro x hx
    have hFx : ContDiffAt ℝ n F (x, g x) :=
      hF.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hx, (hspec x hx).1⟩)
    have hdf : HasFDerivAt (fun t => F (x, t))
        ((fderiv ℝ F (x, g x)).comp (ContinuousLinearMap.inr ℝ E ℝ)) (g x) := by
      exact (hFx.differentiableAt hn).hasFDerivAt.comp (g x)
        ((hasFDerivAt_const x (g x)).prodMk (hasFDerivAt_id (g x)))
    have hne : ((fderiv ℝ F (x, g x)).comp (ContinuousLinearMap.inr ℝ E ℝ)) 1 ≠ 0 := by
      rw [← hdf.hasDerivAt.deriv]
      exact (hderiv x hx (g x) (hspec x hx).1).ne
    have hinv : ((fderiv ℝ F (x, g x)).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible :=
      ⟨_, (hdf.hasDerivAt.hasFDerivAt_equiv hne).unique hdf⟩
    let ψ := hFx.implicitFunction hn hinv
    have hψ : ContDiffAt ℝ n ψ x := hFx.contDiffAt_implicitFunction hn hinv
    have hψx : ψ x = g x := hFx.implicitFunction_apply_self hn hinv
    have hψmem : ∀ᶠ y in 𝓝 x, ψ y ∈ Ioo a b := by
      apply hψ.continuousAt (isOpen_Ioo.mem_nhds _)
      rw [hψx]
      exact (hspec x hx).1
    have heq : g =ᶠ[𝓝 x] ψ := by
      filter_upwards [hU.mem_nhds hx, hψmem, hFx.eventually_apply_implicitFunction hn hinv]
        with y hy hyt heq
      apply ((huniq y hy (ψ y) (Ioo_subset_Icc_self hyt)).mp _).symm
      exact heq.trans (hspec x hx).2
    exact (hψ.congr_of_eventuallyEq heq).contDiffWithinAt
  · intro x hx t ht
    have hg : g x ∈ Icc a b := Ioo_subset_Icc_self (hspec x hx).1
    refine ⟨huniq x hx t ht, ?_, ?_⟩
    · rw [← (hspec x hx).2]
      exact (hanti x hx).le_iff_ge hg ht
    · rw [← (hspec x hx).2]
      exact (hanti x hx).lt_iff_gt hg ht

end DifferentialGeometry.Analysis
