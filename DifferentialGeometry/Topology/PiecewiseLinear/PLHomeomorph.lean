import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem isPiecewiseAffineOn_of_forall_isHPolytope {ι : Type*} [Finite ι] (C : ι → Set E)
    (hC : ∀ i, IsHPolytope (C i)) {f : E → F}
    (hf : ∀ i, ∃ A : E →ᵃ[ℝ] F, EqOn f A (C i)) : IsPiecewiseAffineOn f (⋃ i, C i) := by
  intro x _
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  choose A hA using hf
  refine ⟨Fin n, inferInstance, fun j => C (e.symm j), fun j => A (e.symm j),
    fun j => ⟨hC _, subset_iUnion C _, hA _⟩, ?_⟩
  rw [e.symm.surjective.iUnion_comp C]
  exact self_mem_nhdsWithin

theorem IsPiecewiseAffineWithinAt.mono_of_isPolyhedron {f : E → F} {u v : Set E} {x : E}
    (hf : IsPiecewiseAffineWithinAt f u x) (hv : IsPolyhedron v) (hvu : v ⊆ u) :
    IsPiecewiseAffineWithinAt f v x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  obtain ⟨κ, hκ, D, hD, rfl⟩ := hv
  have := hι
  have := hκ
  refine ⟨ι × κ, inferInstance, fun q => C q.1 ∩ D q.2, fun q => A q.1,
    fun q => ⟨(hC q.1).1.inter (hD q.2), inter_subset_right.trans (subset_iUnion D q.2),
      (hC q.1).2.2.mono inter_subset_left⟩, ?_⟩
  have hU : (⋃ q : ι × κ, C q.1 ∩ D q.2) = (⋃ i, C i) ∩ ⋃ j, D j := by
    ext y
    simp only [mem_iUnion, mem_inter_iff, Prod.exists]
    exact ⟨fun ⟨i, j, hi, hj⟩ => ⟨⟨i, hi⟩, ⟨j, hj⟩⟩, fun ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ => ⟨i, j, hi, hj⟩⟩
  rw [hU]
  exact Filter.inter_mem (nhdsWithin_mono x hvu hCx) self_mem_nhdsWithin

theorem IsPiecewiseAffineOn.mono_of_isPolyhedron {f : E → F} {u v : Set E}
    (hf : IsPiecewiseAffineOn f u) (hv : IsPolyhedron v) (hvu : v ⊆ u) :
    IsPiecewiseAffineOn f v := fun x hx => (hf x (hvu hx)).mono_of_isPolyhedron hv hvu

namespace IsPLHomeomorphOn

variable {f : E → F} {g : F → G} {P : Set E} {Q : Set F} {R : Set G}

theorem bijOn (h : IsPLHomeomorphOn f P Q) : BijOn f P Q := h.1

theorem isPiecewiseAffineOn (h : IsPLHomeomorphOn f P Q) : IsPiecewiseAffineOn f P := h.2.1

theorem isPiecewiseAffineOn_invFunOn (h : IsPLHomeomorphOn f P Q) :
    IsPiecewiseAffineOn (Function.invFunOn f P) Q := h.2.2

theorem image_eq (h : IsPLHomeomorphOn f P Q) : f '' P = Q := h.1.image_eq

theorem symm (h : IsPLHomeomorphOn f P Q) : IsPLHomeomorphOn (Function.invFunOn f P) Q P := by
  have hinv : InvOn (Function.invFunOn f P) f P Q := h.1.invOn_invFunOn
  have hbij : BijOn (Function.invFunOn f P) Q P :=
    hinv.symm.bijOn h.1.surjOn.mapsTo_invFunOn h.1.mapsTo
  refine ⟨hbij, h.2.2, h.2.1.congr fun x hx => ?_⟩
  have hy : Function.invFunOn (Function.invFunOn f P) Q x ∈ Q := hbij.surjOn.mapsTo_invFunOn hx
  have hxy : Function.invFunOn f P (Function.invFunOn (Function.invFunOn f P) Q x) = x :=
    hbij.invOn_invFunOn.2 hx
  calc Function.invFunOn (Function.invFunOn f P) Q x
      = f (Function.invFunOn f P (Function.invFunOn (Function.invFunOn f P) Q x)) :=
        (hinv.2 hy).symm
    _ = f x := by rw [hxy]

theorem trans [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    (hf : IsPLHomeomorphOn f P Q) (hg : IsPLHomeomorphOn g Q R) :
    IsPLHomeomorphOn (g ∘ f) P R := by
  have hgf : BijOn (g ∘ f) P R := hg.1.comp hf.1
  refine ⟨hgf, ?_, ?_⟩
  · have h := hg.2.1.comp hf.2.1
    have hsub : P ⊆ f ⁻¹' Q := fun x hx => hf.1.mapsTo hx
    rwa [inter_eq_left.mpr hsub] at h
  · have h := hf.2.2.comp hg.2.2
    have hsub : R ⊆ Function.invFunOn g Q ⁻¹' Q := fun y hy => hg.1.surjOn.mapsTo_invFunOn hy
    rw [inter_eq_left.mpr hsub] at h
    refine h.congr fun z hz => ?_
    have h1 : Function.invFunOn (g ∘ f) P z ∈ P := hgf.surjOn.mapsTo_invFunOn hz
    have h2 : (g ∘ f) (Function.invFunOn (g ∘ f) P z) = z := hgf.invOn_invFunOn.2 hz
    have h3 : Function.invFunOn g Q z ∈ Q := hg.1.surjOn.mapsTo_invFunOn hz
    have h4 : g (Function.invFunOn g Q z) = z := hg.1.invOn_invFunOn.2 hz
    have h5 : Function.invFunOn f P (Function.invFunOn g Q z) ∈ P :=
      hf.1.surjOn.mapsTo_invFunOn h3
    have h6 : f (Function.invFunOn f P (Function.invFunOn g Q z)) = Function.invFunOn g Q z :=
      hf.1.invOn_invFunOn.2 h3
    refine hgf.injOn h1 h5 ?_
    simp only [Function.comp_apply] at h2 ⊢
    rw [h2, h6, h4]

end IsPLHomeomorphOn

theorem IsPLBall.of_isPLHomeomorphOn [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ}
    {P : Set E} (hP : IsPLBall n P) {f : E → F} {Q : Set F} (hf : IsPLHomeomorphOn f P Q) :
    IsPLBall n Q := by
  obtain ⟨g, hg⟩ := hP
  exact ⟨f ∘ g, hg.trans hf⟩

theorem IsPLSphere.of_isPLHomeomorphOn [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ}
    {P : Set E} (hP : IsPLSphere n P) {f : E → F} {Q : Set F} (hf : IsPLHomeomorphOn f P Q) :
    IsPLSphere n Q := by
  obtain ⟨g, hg⟩ := hP
  exact ⟨f ∘ g, hg.trans hf⟩

end DifferentialGeometry.Topology.PiecewiseLinear
