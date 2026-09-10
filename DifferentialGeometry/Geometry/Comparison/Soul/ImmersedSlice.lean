import DifferentialGeometry.Geometry.Comparison.Soul.EmbeddedSlice
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import Mathlib.Analysis.Normed.Module.Complemented

set_option autoImplicit false
noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_slice_image [CompleteSpace E] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {f : F → E} {U : Set F} {a : F}
    (hU : IsOpen U) (ha : a ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hinj : Function.Injective (fderiv ℝ f a)) :
    ∃ V : Set F, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ InjOn f V ∧
      IsEmbeddedSlice 𝓘(ℝ, E) (Module.finrank ℝ F) (f '' V) := by
  let D := fderiv ℝ f a
  let R : Submodule ℝ E := D.range
  obtain ⟨Q, hRQ⟩ := R.exists_isCompl
  let eD : F ≃L[ℝ] R := D.equivRange hinj R.closed_of_finiteDimensional
  let e : (F × Q) ≃L[ℝ] E :=
    (eD.prodCongr (ContinuousLinearEquiv.refl ℝ Q)).trans
      (R.prodEquivOfIsTopCompl Q (Submodule.IsCompl.isTopCompl_of_isClosed hRQ
        R.closed_of_finiteDimensional Q.closed_of_finiteDimensional))
  have he (z : F × Q) : e z = D z.1 + (z.2 : E) := by
    simp only [e, eD, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsTopCompl, Submodule.coe_prodEquivOfIsCompl']
    rfl
  let j : F →L[ℝ] E := e.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ F Q)
  have hj (x : F) : j x = D x := by
    change e (x, 0) = D x
    simpa only [Submodule.coe_zero, add_zero] using he (x, 0)
  have hej (x : F) : e.symm (j x) = (x, 0) := e.symm_apply_apply (x, 0)
  let aug : F × Q → E := fun z => f z.1 + (z.2 : E)
  have hfa : DifferentiableAt ℝ f a := (hf.contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)
  have hdaug : HasFDerivAt aug e.toContinuousLinearMap (a, 0) := by
    have hleft := hfa.hasFDerivAt.comp (a, (0 : Q)) (ContinuousLinearMap.fst ℝ F Q).hasFDerivAt
    have hright := (Q.subtypeL.comp (ContinuousLinearMap.snd ℝ F Q)).hasFDerivAt (x := (a, 0))
    convert! hleft.add hright using 1
  let H : E → E := fun y => aug (e.symm y)
  let W : Set E := e.symm ⁻¹' (U ×ˢ (univ : Set Q))
  have hW : IsOpen W := (hU.prod isOpen_univ).preimage e.symm.continuous
  have haW : j a ∈ W := by change e.symm (j a) ∈ U ×ˢ univ; rw [hej]; exact ⟨ha, mem_univ _⟩
  have haug : ContDiffOn ℝ ∞ aug (U ×ˢ (univ : Set Q)) :=
    (hf.comp contDiffOn_fst fun _ hz => hz.1).add
      (Q.subtypeL.contDiff.comp contDiff_snd).contDiffOn
  have hH : ContDiffOn ℝ ∞ H W :=
    haug.comp e.symm.contDiff.contDiffOn (fun _ hy => hy)
  have hdH : HasFDerivAt H (ContinuousLinearMap.id ℝ E) (j a) := by
    have hdaug' : HasFDerivAt aug e.toContinuousLinearMap (e.symm (j a)) := by rwa [hej]
    convert! hdaug'.comp (j a) e.symm.hasFDerivAt using 1
    ext y
    exact (e.apply_symm_apply y).symm
  have hop : IsOpen {L : E →L[ℝ] E | L.IsInvertible} := by
    convert! ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := E) (F := E) using 1
  have hId : (fderiv ℝ H (j a)).IsInvertible := by
    rw [hdH.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  have hInv := ((hH.contDiffAt (hW.mem_nhds haW)).continuousAt_fderiv (by simp)).preimage_mem_nhds
    (hop.mem_nhds hId)
  obtain ⟨W', hW'sub, hW'open, haW'⟩ := mem_nhds_iff.1 (inter_mem (hW.mem_nhds haW) hInv)
  have hinv : ∀ y ∈ W',
      (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) y H)
        (extChartAt 𝓘(ℝ, E) y y)).IsInvertible := by
    intro y hy
    have hyInv : (fderiv ℝ H y).IsInvertible := (hW'sub hy).2
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, Function.id_comp, Function.comp_id, id_eq] using hyInv
  obtain ⟨c, hac, hcW', hHc⟩ := Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
    (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, E)) hW'open haW'
      (hH.mono (hW'sub.trans inter_subset_left)).contMDiffOn hinv
  let V : Set F := j ⁻¹' c.source
  have hVU : V ⊆ U := by
    intro x hx
    have hh : e.symm (j x) ∈ U ×ˢ (univ : Set Q) := (hW'sub (hcW' hx)).1
    rw [hej] at hh
    exact hh.1
  have hcj (x : F) (hx : x ∈ V) : c (j x) = f x := by
    rw [← hHc hx]
    change aug (e.symm (j x)) = f x
    rw [hej]
    exact add_zero _
  have hfinj : InjOn f V := by
    intro x hx y hy hxy
    apply hinj
    rw [← hj x, ← hj y]
    apply c.toPartialEquiv.injOn hx hy
    rw [hcj x hx, hcj y hy, hxy]
  have himage : c.toPartialEquiv.IsImage (R : Set E) (f '' V) := by
    intro y hy
    constructor
    · rintro ⟨x, hx, hxy⟩
      have heq : y = j x := c.toPartialEquiv.injOn hy hx (by rw [hcj x hx, hxy])
      rw [heq, hj]
      exact D.mem_range_self x
    · rintro ⟨x, hx⟩
      have hjx : j x = y := (hj x).trans hx
      have hxV : x ∈ V := by change j x ∈ c.source; rwa [hjx]
      exact ⟨x, hxV, by rw [← hcj x hxV, hjx]⟩
  refine ⟨V, c.open_source.preimage j.continuous, hac, hVU, hfinj, ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨c.symm, R.toAffineSubspace, inferInstance, ?_, ?_, himage.symm⟩
  · rw [← hcj z hz]
    exact c.toPartialEquiv.map_source hz
  · rw [Submodule.toAffineSubspace_direction]
    exact eD.finrank_eq.symm

end DifferentialGeometry.Geometry
