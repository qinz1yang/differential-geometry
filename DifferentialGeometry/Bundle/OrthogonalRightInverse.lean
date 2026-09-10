import DifferentialGeometry.Bundle.RightInverse

noncomputable section
open scoped ContDiff Manifold Topology

namespace Poincare.Geometry.VectorBundle

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem finrank_dual (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
  Subspace.dual_finrank_eq.symm.trans LinearMap.toContinuousLinearMap.finrank_eq

private theorem invertible_of_injective {A : E →L[ℝ] F}
    (hinj : Function.Injective A) (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    A.IsInvertible := by
  refine ⟨(A.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv, ?_⟩
  ext v
  rfl

private theorem metric_invertible (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G v v) : G.IsInvertible := by
  apply invertible_of_injective _ (finrank_dual E)
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change G v = 0 at hv
  by_contra hne
  have h := hpos v hne
  rw [hv, zero_apply] at h
  exact lt_irrefl _ h

private def transpose (A : E →L[ℝ] F) : (F →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ E F ℝ).flip A

private theorem normal_operator_invertible (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G v v)
    (A : E →L[ℝ] F) (hsurj : Function.Surjective A) :
    (A.comp (G.inverse.comp (transpose A))).IsInvertible := by
  have hG := metric_invertible G hpos
  apply invertible_of_injective _ (finrank_dual F).symm
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro ξ hξ
  let v := G.inverse ((transpose A) ξ)
  have hAv : A v = 0 := hξ
  have hGv : G v = ξ.comp A := hG.self_apply_inverse ((transpose A) ξ)
  have hv : v = 0 := by
    by_contra hne
    have h := hpos v hne
    rw [hGv, ContinuousLinearMap.comp_apply, hAv, map_zero] at h
    exact lt_irrefl _ h
  ext w
  obtain ⟨u, rfl⟩ := hsurj w
  have h := congrArg (fun L : E →L[ℝ] ℝ ↦ L u) hGv
  simpa only [hv, map_zero, zero_apply, ContinuousLinearMap.comp_apply] using h.symm

theorem eq_of_apply_eq_of_orthogonal_ker
    {V W : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    (G : V →L[ℝ] V →L[ℝ] ℝ)
    (hpos : ∀ v : V, v ≠ 0 → 0 < G v v) (A : V →L[ℝ] W)
    {v w : V} (hvw : A v = A w)
    (hv : ∀ u, A u = 0 → G v u = 0)
    (hw : ∀ u, A u = 0 → G w u = 0) : v = w := by
  by_contra hne
  have hker : A (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have h := hpos (v - w) (sub_ne_zero.mpr hne)
  rw [show G (v - w) = G v - G w from G.map_sub v w, sub_apply,
    hv _ hker, hw _ hker, sub_self] at h
  exact lt_irrefl _ h

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

theorem exists_contMDiffOn_rightInverse_orthogonal_ker
    {G : M → E →L[ℝ] E →L[ℝ] ℝ} {A : M → E →L[ℝ] F}
    {U : Set M} {x₀ : M}
    (hG : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n G U)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < G x v v)
    (hA : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] F) n A U)
    (hU : U ∈ 𝓝 x₀) (hsurj : Function.Surjective (A x₀)) :
    ∃ V ∈ 𝓝 x₀, V ⊆ U ∧ ∃ R : M → F →L[ℝ] E,
      ContMDiffOn I 𝓘(ℝ, F →L[ℝ] E) n R V ∧
      (∀ x ∈ V, Function.RightInverse (R x) (A x)) ∧
      ∀ x ∈ V, ∀ w v, A x v = 0 → G x (R x w) v = 0 := by
  have hGi : ∀ x ∈ U, (G x).IsInvertible := fun x hx ↦ metric_invertible _ (hpos x hx)
  have hGs : ContMDiffOn I 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E) n
      (fun x ↦ (G x).inverse) U := by
    intro x hx
    exact (hGi x hx).contDiffAt_map_inverse.comp_contMDiffWithinAt (hG x hx)
  let D : M → (F →L[ℝ] ℝ) →L[ℝ] E := fun x ↦ (G x).inverse.comp (transpose (A x))
  have hD : ContMDiffOn I 𝓘(ℝ, (F →L[ℝ] ℝ) →L[ℝ] E) n D U := by
    apply hGs.clm_comp
    apply contMDiffOn_clm_apply_iff.mpr
    intro ξ
    exact contMDiffOn_const.clm_comp hA
  let C : M → (F →L[ℝ] ℝ) →L[ℝ] F := fun x ↦ (A x).comp (D x)
  have hC : ContMDiffOn I 𝓘(ℝ, (F →L[ℝ] ℝ) →L[ℝ] F) n C U := hA.clm_comp hD
  have hC₀ : (C x₀).IsInvertible := normal_operator_invertible _
    (hpos x₀ (mem_of_mem_nhds hU)) _ hsurj
  have hnear : {x | (C x).IsInvertible} ∈ 𝓝 x₀ :=
    (hC.continuousOn.continuousAt hU).preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds hC₀)
  refine ⟨U ∩ {x | (C x).IsInvertible}, Filter.inter_mem hU hnear,
    Set.inter_subset_left, (fun x ↦ (D x).comp (C x).inverse), ?_, ?_, ?_⟩
  · intro x hx
    exact ((hD x hx.1).mono Set.inter_subset_left).clm_comp
      (hx.2.contDiffAt_map_inverse.comp_contMDiffWithinAt
        ((hC x hx.1).mono Set.inter_subset_left))
  · intro x hx w
    exact hx.2.self_apply_inverse w
  · intro x hx w v hv
    have h := congrArg (fun L : E →L[ℝ] ℝ ↦ L v)
      ((hGi x hx.1).self_apply_inverse (transpose (A x) ((C x).inverse w)))
    simpa only [D, transpose, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, hv, map_zero] using h

end Poincare.Geometry.VectorBundle
