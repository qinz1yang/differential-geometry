/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainOpenCellCylinder
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E R X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace R] [TopologicalSpace X] [T2Space X]

theorem nonempty_homeomorph_of_cylinder_ends
    {U : Set X} {P : X} (c : (R × ℝ) ≃ₜ U)
    (a : Metric.sphere (0 : E) 1 ≃ₜ R) (hP : P ∉ U)
    (hlower : ∀ V : Set X, IsOpen V → P ∈ V →
      ∃ b : ℝ, ∀ z : R × ℝ, z.2 ≤ b → (c z : X) ∈ V)
    (hupper : ∀ b : ℝ,
      P ∉ closure ((fun z => (c z : X)) '' (univ ×ˢ Ici b))) :
    Nonempty (E ≃ₜ ↥(U ∪ {P})) := by
  classical
  let r : ({0}ᶜ : Set E) ≃ₜ (R × ℝ) :=
    (homeomorphUnitSphereProd E).trans (a.prodCongr Real.expOrderIso.toHomeomorph.symm)
  have hr (x : ({0}ᶜ : Set E)) : (r x).2 = Real.log ‖(x : E)‖ := by
    change Real.expOrderIso.symm ((homeomorphUnitSphereProd E x).2) = _
    rw [Real.log_of_pos (norm_pos_iff.mpr x.property)]
    congr 1
    apply Subtype.ext
    exact homeomorphUnitSphereProd_apply_snd_coe E x
  let F : E → X := fun x => if hx : x = 0 then P else c (r ⟨x, hx⟩)
  have hF₀ : F 0 = P := dite_eq_left rfl
  have hF (x : ({0}ᶜ : Set E)) : F x = c (r x) := by
    exact dite_eq_right (show (x : E) ≠ 0 from x.property)
  have hFU (x : E) : F x ∈ U ∪ {P} := by
    by_cases hx : x = 0
    · subst x
      exact Or.inr hF₀
    · apply Or.inl
      rw [hF ⟨x, hx⟩]
      exact (c (r ⟨x, hx⟩)).property
  let f : E → ↥(U ∪ {P}) := fun x => ⟨F x, hFU x⟩
  let j : U → ↥(U ∪ {P}) := Set.inclusion subset_union_left
  have hf (x : ({0}ᶜ : Set E)) : f x = j (c (r x)) := Subtype.ext (hF x)
  have hfinj : Function.Injective f := by
    intro x y hxy
    have heq : F x = F y := congrArg Subtype.val hxy
    by_cases hx : x = 0
    · subst x
      by_contra hy
      have hy' : y ≠ 0 := Ne.symm hy
      have hyU : F y ∈ U := by
        rw [hF ⟨y, hy'⟩]
        exact (c (r ⟨y, hy'⟩)).property
      exact hP ((heq.symm.trans hF₀) ▸ hyU)
    · by_cases hy : y = 0
      · subst y
        have hxU : F x ∈ U := by
          rw [hF ⟨x, hx⟩]
          exact (c (r ⟨x, hx⟩)).property
        exact False.elim (hP ((heq.trans hF₀) ▸ hxU))
      · have hc : c (r ⟨x, hx⟩) = c (r ⟨y, hy⟩) := by
          apply Subtype.ext
          exact (hF ⟨x, hx⟩).symm.trans (heq.trans (hF ⟨y, hy⟩))
        exact congrArg Subtype.val (r.injective (c.injective hc))
  have hfsurj : Function.Surjective f := by
    intro y
    rcases y.property with hy | hy
    · refine ⟨(r.symm (c.symm ⟨y, hy⟩) : E), ?_⟩
      rw [hf, r.apply_symm_apply, c.apply_symm_apply]
    · refine ⟨0, Subtype.ext ?_⟩
      exact hF₀.trans (mem_singleton_iff.mp hy).symm
  let e : E ≃ ↥(U ∪ {P}) := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst x
      rw [continuousAt_def, hF₀]
      intro V hV
      obtain ⟨V', hV'V, hV'open, hPV'⟩ := mem_nhds_iff.mp hV
      obtain ⟨b, hb⟩ := hlower V' hV'open hPV'
      apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) (Real.exp_pos b))
      intro y hy
      by_cases hy₀ : y = 0
      · subst y
        exact hV'V (hF₀ ▸ hPV')
      · apply hV'V
        rw [hF ⟨y, hy₀⟩]
        apply hb
        rw [hr, Real.log_le_iff_le_exp (norm_pos_iff.mpr hy₀)]
        exact (by simpa only [Metric.mem_ball, dist_zero_right] using hy :
          ‖y‖ < Real.exp b).le
    · have hc : Continuous (F ∘ (Subtype.val : ({0}ᶜ : Set E) → E)) := by
        have heq : F ∘ (Subtype.val : ({0}ᶜ : Set E) → E) =
            fun z => (c (r z) : X) := funext hF
        rw [heq]
        exact continuous_subtype_val.comp (c.continuous.comp r.continuous)
      exact isOpen_compl_singleton.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
        (hc.continuousAt (x := ⟨x, hx⟩))
  have hecont : Continuous e := hFcont.subtype_mk _
  have hjopen : IsOpenEmbedding j := by
    refine ⟨IsEmbedding.inclusion subset_union_left, ?_⟩
    have hrange : range j = (Subtype.val : ↥(U ∪ {P}) → X) ⁻¹' {P}ᶜ := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩ hy
        exact hP (mem_singleton_iff.mp hy ▸ z.property)
      · intro hy
        have hyU : (y : X) ∈ U := y.property.resolve_right hy
        exact ⟨⟨y, hyU⟩, rfl⟩
    rw [hrange]
    exact isOpen_compl_singleton.preimage continuous_subtype_val
  have hinv (y : U) : e.symm (j y) = (r.symm (c.symm y) : E) := by
    apply e.symm_apply_eq.mpr
    symm
    change f _ = j y
    rw [hf, r.apply_symm_apply, c.apply_symm_apply]
  have hinv₀ : e.symm (f 0) = 0 := e.symm_apply_apply 0
  have hinvcont : Continuous e.symm := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : (y : X) = P
    · have hy₀ : y = f 0 := Subtype.ext (hy.trans hF₀.symm)
      subst y
      rw [ContinuousAt, hinv₀, Metric.tendsto_nhds]
      intro ε hε
      let V : Set X := (closure ((fun z => (c z : X)) '' (univ ×ˢ Ici (Real.log ε))))ᶜ
      have hV : V ∈ 𝓝 P := isOpen_compl_iff.mpr isClosed_closure |>.mem_nhds
        (hupper (Real.log ε))
      have hpre : (Subtype.val : ↥(U ∪ {P}) → X) ⁻¹' V ∈ 𝓝 (f 0) := by
        apply continuous_subtype_val.continuousAt
        simpa only [f, Subtype.coe_mk, hF₀] using hV
      filter_upwards [hpre] with y hyV
      rw [dist_zero_right]
      by_contra hn
      have hxnorm : ε ≤ ‖e.symm y‖ := not_lt.mp hn
      have hx : e.symm y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hε.trans_le hxnorm))
      have hheight : Real.log ε ≤ (r ⟨e.symm y, hx⟩).2 := by
        rw [hr, Real.log_le_log_iff hε (norm_pos_iff.mpr hx)]
        exact hxnorm
      apply hyV
      apply subset_closure
      refine ⟨r ⟨e.symm y, hx⟩, ⟨mem_univ _, hheight⟩, ?_⟩
      have h := congrArg Subtype.val (e.apply_symm_apply y)
      exact (hF ⟨e.symm y, hx⟩).symm.trans h
    · have hyU : (y : X) ∈ U := y.property.resolve_right hy
      have hc : Continuous (e.symm ∘ j) := by
        have heq : e.symm ∘ j = fun z => (r.symm (c.symm z) : E) := funext hinv
        rw [heq]
        exact continuous_subtype_val.comp (r.symm.continuous.comp c.symm.continuous)
      exact hjopen.continuousAt_iff.mp (hc.continuousAt (x := ⟨y, hyU⟩))
  exact ⟨⟨e, hecont, hinvcont⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
