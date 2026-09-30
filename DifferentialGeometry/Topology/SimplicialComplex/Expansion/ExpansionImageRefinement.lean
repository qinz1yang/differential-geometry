import DifferentialGeometry.Topology.SimplicialComplex.Expansion.ExpansionTransport
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.InverseSubdivision
import DifferentialGeometry.Topology.SimplicialComplex.Stellar.StellarCommonRefinement

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

variable {E F : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem exists_image_refinement_preserving_expansions
    (K : SimplicialComplex ℝ E) (Q : SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (hQ : Q.faces.Finite)
    (e : K.space ≃ₜ Q.space) (hparents : hasAffineInverseFaceParents K Q e)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ f : E → F, ∃ J : SimplicialComplex ℝ F,
      (∀ x : K.space, f x.val = (e x).val) ∧
      J.faces.Finite ∧ J.space = Q.space ∧ simplicialRefines J Q ∧
      (∀ s ∈ J.faces, s.card ≤ d + 1) ∧
      ∀ A C, C ⊆ K.space → FiniteSimplexExpansionIn K A C →
        FiniteSimplexExpansionIn J (f '' A) (f '' C) := by
  classical
  obtain ⟨r, R₀, hR₀, hR₀space, hR₀ref, hr, hra, hri, hR₀faces, hcorr⟩ :=
    exists_inverse_geometric_subdivision K Q Q e hparents hQ
      (fun s hs => ⟨s, hs, subset_rfl⟩) rfl
  let P := injectiveImageComplex Q r hra hri
  have hPR : P = R₀ := by
    apply SimplicialComplex.ext
    exact hR₀faces.symm
  have hPs : P.space = K.space := hPR ▸ hR₀space
  have hP : P.faces.Finite := hPR ▸ hR₀
  let f : E → F := fun x => if hx : x ∈ K.space then (e ⟨x, hx⟩).val else 0
  have hf (x : K.space) : f x.val = (e x).val := dite_eq_left x.property
  have hfr : ∀ y ∈ Q.space, f (r y) = y := by
    intro y hy
    rw [hr ⟨y, hy⟩, hf (e.symm ⟨y, hy⟩), e.apply_symm_apply]
  have hfaP : ∀ s ∈ P.faces, ∃ A : E →ᵃ[ℝ] F,
      EqOn f A (convexHull ℝ (s : Set E)) :=
    inverse_affine_on_injectiveImageComplex Q r hra hri f hfr
  have hfi : InjOn f K.space := by
    intro x hx y hy he
    rw [hf ⟨x, hx⟩, hf ⟨y, hy⟩] at he
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  obtain ⟨R, hR, hRs, hRK, hRP, hRd, hexp⟩ :=
    exists_common_refinement_preserving_expansions K P hK hP hPs.symm.subset hd
  have hfa : ∀ s ∈ R.faces, ∃ A : E →ᵃ[ℝ] F,
      EqOn f A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hRP s hs
    obtain ⟨A, hA⟩ := hfaP t ht
    exact ⟨A, hA.mono hst⟩
  have hfiR : InjOn f R.space := hfi.mono hRs.subset
  let J := injectiveImageComplex R f hfa hfiR
  have hJspace : J.space = Q.space := by
    rw [injectiveImageComplex_space, hRs]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hf ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro y hy
      refine ⟨(e.symm ⟨y, hy⟩).val, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [hf (e.symm ⟨y, hy⟩), e.apply_symm_apply]
  have hJref : simplicialRefines J Q := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨t, ⟨u, hu, rfl⟩, hst⟩ := hRP s hs
    obtain ⟨A, hA⟩ := hfa s hs
    obtain ⟨B, hB⟩ := hra u hu
    refine ⟨u, hu, ?_⟩
    rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap f A hA]
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hst hx
    rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap r B hB] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    rw [hfr y (Q.convexHull_subset_space hu hy)]
    exact hy
  refine ⟨f, J, hf, injectiveImageComplex_finite_faces R hR f hfa hfiR,
    hJspace, hJref, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact Finset.card_image_le.trans (hRd s hs)
  · intro A C hC he
    exact (hexp A C he).image (hC.trans hRs.symm.subset) f hfiR hfa
      (fun s hs => ⟨s, hs, rfl⟩)

end

end DifferentialGeometry.Topology.Engulfing
