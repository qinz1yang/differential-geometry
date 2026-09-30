import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementSupport
import Mathlib.Topology.Homeomorph.Lemmas

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

variable {E F : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def hasAffineInverseFaceParents (K : SimplicialComplex ℝ E) (Q : SimplicialComplex ℝ F)
    (e : K.space ≃ₜ Q.space) : Prop :=
  ∀ s ∈ Q.faces, ∃ t ∈ K.faces, ∃ A : F →ᵃ[ℝ] E,
    ∀ x : Q.space, x.val ∈ convexHull ℝ (s : Set F) →
      (e.symm x).val = A x.val ∧ A x.val ∈ convexHull ℝ (t : Set E)

omit [DecidableEq F] in
theorem exists_inverse_geometric_subdivision
    (K : SimplicialComplex ℝ E) (Q P : SimplicialComplex ℝ F)
    (e : K.space ≃ₜ Q.space) (hparents : hasAffineInverseFaceParents K Q e)
    (hP : P.faces.Finite) (href : simplicialRefines P Q) (hspace : P.space = Q.space) :
    ∃ r : F → E, ∃ R : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.space = K.space ∧ simplicialRefines R K ∧
      (∀ y : Q.space, r y.val = (e.symm y).val) ∧
      (∀ s ∈ P.faces, ∃ A : F →ᵃ[ℝ] E, EqOn r A (convexHull ℝ (s : Set F))) ∧
      InjOn r P.space ∧
      R.faces = {s | ∃ t ∈ P.faces, t.image r = s} ∧
      ∀ s ∈ P.faces, ∀ x : K.space,
        x.val ∈ convexHull ℝ (s.image r : Set E) ↔
          (e x).val ∈ convexHull ℝ (s : Set F) := by
  classical
  let r : F → E := fun y => if hy : y ∈ Q.space then (e.symm ⟨y, hy⟩).val else 0
  have hr (y : Q.space) : r y.val = (e.symm y).val := dite_eq_left y.property
  have hriQ : InjOn r Q.space := by
    intro x hx y hy hxy
    have h : e.symm ⟨x, hx⟩ = e.symm ⟨y, hy⟩ :=
      Subtype.ext ((hr ⟨x, hx⟩).symm.trans (hxy.trans (hr ⟨y, hy⟩)))
    exact congrArg Subtype.val (e.symm.injective h)
  have hri : InjOn r P.space := hriQ.mono hspace.subset
  have haff : ∀ s ∈ P.faces, ∃ A : F →ᵃ[ℝ] E, EqOn r A (convexHull ℝ (s : Set F)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := href s hs
    obtain ⟨u, hu, A, hA⟩ := hparents t ht
    refine ⟨A, fun y hy => ?_⟩
    have hyQ := Q.convexHull_subset_space ht (hst hy)
    exact (hr ⟨y, hyQ⟩).trans (hA ⟨y, hyQ⟩ (hst hy)).1
  let R := injectiveImageComplex P r haff hri
  have hRspace : R.space = K.space := by
    rw [injectiveImageComplex_space, hspace]
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      rw [hr ⟨y, hy⟩]
      exact (e.symm ⟨y, hy⟩).property
    · intro x hx
      refine ⟨(e ⟨x, hx⟩).val, (e ⟨x, hx⟩).property, ?_⟩
      rw [hr (e ⟨x, hx⟩), e.symm_apply_apply]
  have hRref : simplicialRefines R K := by
    rintro s ⟨t, ht, rfl⟩
    obtain ⟨u, hu, htu⟩ := href t ht
    obtain ⟨v, hv, A, hA⟩ := hparents u hu
    obtain ⟨B, hB⟩ := haff t ht
    refine ⟨v, hv, ?_⟩
    rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap r B hB]
    rintro _ ⟨y, hy, rfl⟩
    have hyQ := Q.convexHull_subset_space hu (htu hy)
    rw [hr ⟨y, hyQ⟩, (hA ⟨y, hyQ⟩ (htu hy)).1]
    exact (hA ⟨y, hyQ⟩ (htu hy)).2
  refine ⟨r, R, injectiveImageComplex_finite_faces P hP r haff hri,
    hRspace, hRref, hr, haff, hri, rfl, ?_⟩
  intro s hs x
  obtain ⟨A, hA⟩ := haff s hs
  rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap r A hA]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyQ := hspace.subset (P.convexHull_subset_space hs hy)
    have heq : e.symm ⟨y, hyQ⟩ = x := Subtype.ext ((hr ⟨y, hyQ⟩).symm.trans hyx)
    have heq' : (e x).val = y := by rw [← heq, e.apply_symm_apply]
    rwa [heq']
  · intro hx
    refine ⟨(e x).val, hx, ?_⟩
    rw [hr (e x), e.symm_apply_apply]

end

end DifferentialGeometry.Topology.Engulfing
