import DifferentialGeometry.Topology.Ehresmann.ArcEndDescentEFE
import DifferentialGeometry.Topology.Ehresmann.SurfaceIntervalProductEFE

/-!
# The defining function over either end of ONE base arc, descended to the base (S-BD2d2, `_OBDd`)

Lane O-BD1 (by S-BD2d2), group G10e, `SlimCutPieces74`. The kernel
`exists_end_defining_function_descent_EFE` (lane S-EDP-FDC3) treats the end `γ 0` of a base arc;
this is the same statement for an arbitrary end `t₀ ∈ {0, 1}` of the arc `γ`, for the side set
`T = γ [0, 1]` itself (so no isolation hypothesis and no excluded closed set are needed): an open
`U ⊇ f⁻¹{γ t₀}` in the total space, a regular function `h = a ∘ f` (`a` smooth on the whole base
space), `{h = 0} ∩ U = f⁻¹{γ t₀}` and `U ∩ f⁻¹(γ [0, 1]) = {h ≤ 0} ∩ U`.

* `exists_arc_end_tube_endpoint_OBDd`: the statement above, the reversed arc handling `t₀ = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Ehresmann

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- **The tube over either end of a base arc, with the defining function a smooth function of the
base point.** -/
theorem exists_arc_end_tube_endpoint_OBDd
    (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs) (γ : SmoothEmbeddedBaseArc_EFE Bs)
    {t₀ : ℝ} (ht : t₀ = 0 ∨ t₀ = 1) :
    ∃ (U : Set M) (h : M → ℝ) (a : H → ℝ), IsOpen U ∧ P.toFun ⁻¹' {γ.toFun t₀} ⊆ U ∧
      U ⊆ P.toFun ⁻¹' Bs ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U ∧
      (∀ x ∈ U, Surjective (mfderiv I 𝓘(ℝ, ℝ) h x)) ∧
      {x | x ∈ U ∧ h x = 0} = P.toFun ⁻¹' {γ.toFun t₀} ∧
      U ∩ P.toFun ⁻¹' (γ.toFun '' Icc 0 1) = {x | x ∈ U ∧ h x ≤ 0} ∧
      ContDiff ℝ ∞ a ∧ ∀ x, h x = a (P.toFun x) := by
  have hTB : γ.toFun '' Icc 0 1 ⊆ Bs := fun z ⟨t, hmem, hz⟩ => hz ▸ γ.mapsTo hmem
  rcases ht with rfl | rfl
  · obtain ⟨U, h, a, hUo, hfU, hUB, -, hh, hsurj, hlev, hside, ha, hha⟩ :=
      exists_end_defining_function_descent_EFE P γ.smooth.continuousOn γ.injOn
        (T := γ.toFun '' Icc 0 1) subset_rfl hTB ⟨univ, isOpen_univ, trivial, fun _ h => h.1⟩
        (E' := ∅) isClosed_empty (notMem_empty _)
    exact ⟨U, h, a, hUo, hfU, hUB, hh, hsurj, hlev, hside, ha, hha⟩
  · have hrev : (fun s : ℝ => γ.toFun (1 - s)) '' Icc 0 1 = γ.toFun '' Icc 0 1 := by
      ext z
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
      · rintro ⟨t, hmem, rfl⟩
        exact ⟨1 - t, ⟨by linarith [hmem.2], by linarith [hmem.1]⟩, by simp⟩
    have hcont : ContinuousOn (fun s : ℝ => γ.toFun (1 - s)) (Icc 0 1) :=
      γ.smooth.continuousOn.comp (by fun_prop) (fun s hs =>
        ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    have hinj : InjOn (fun s : ℝ => γ.toFun (1 - s)) (Icc 0 1) := by
      intro s hs t ht hst
      have := γ.injOn ⟨by linarith [hs.2], by linarith [hs.1]⟩
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ hst
      linarith
    obtain ⟨U, h, a, hUo, hfU, hUB, -, hh, hsurj, hlev, hside, ha, hha⟩ :=
      exists_end_defining_function_descent_EFE P hcont hinj (T := γ.toFun '' Icc 0 1)
        (by rw [hrev]) hTB ⟨univ, isOpen_univ, trivial, fun _ h => hrev ▸ h.1⟩
        (E' := ∅) isClosed_empty (notMem_empty _)
    refine ⟨U, h, a, hUo, ?_, hUB, hh, hsurj, ?_, hside, ha, hha⟩
    · simpa using hfU
    · simpa using hlev

end DifferentialGeometry.Topology.Ehresmann
