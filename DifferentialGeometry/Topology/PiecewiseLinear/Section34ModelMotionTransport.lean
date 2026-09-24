import DifferentialGeometry.Topology.Homeomorph.Conjugate
import DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PLCompactModelEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]

theorem IsPLOn.isPLHomeomorphInto_of_isPLCellOn {d : ℕ} {S B : Set M} {f : M → N}
    (hf : IsPLOn 3 3 f S) (hS : IsPLCellOn d S B) (hinj : InjOn f S) :
    IsPLHomeomorphInto 3 f S := by
  obtain ⟨P, r, u, hr, hu, hS, -⟩ := hS
  have hmap : MapsTo u P S := fun x hx => hS.symm ▸ ⟨x, hx, rfl⟩
  have hfu : IsPLHomeomorphInto 3 (f ∘ u) P :=
    (hf.comp_of_mapsTo hu.isPLOn hmap).isPLHomeomorphInto_model
      (IsPLBall.isPolyhedron ⟨r, hr⟩).isCompact
      (fun x hx y hy hxy => hu.injOn hx hy (hinj (hmap hx) (hmap hy) hxy))
  have himage : f '' S = (f ∘ u) '' P := by rw [hS, image_comp]
  have hleft := hfu.injOn.leftInvOn_invFunOn
  have hmaps := hfu.injOn.bijOn_image.surjOn.mapsTo_invFunOn
  have hpl := hu.isPLOn.comp_of_mapsTo (hfu.isPLOn_inverse hleft) hmaps
  refine ⟨hf, hinj, ?_⟩
  intro y hy
  refine ⟨u ∘ Function.invFunOn (f ∘ u) P, ?_, ?_⟩
  · rw [himage] at hy ⊢
    exact hpl y hy
  · intro x hx
    rw [hS] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    change u (Function.invFunOn (f ∘ u) P ((f ∘ u) z)) = u z
    rw [hleft hz]

theorem IsPLHomeomorphInto.postcomp_of_supported_isPLOn {d : ℕ} {D Bd : Set M}
    {f : M → N} (hf : IsPLHomeomorphInto 3 f D) (hD : IsPLCellOn d D Bd)
    (φ : N ≃ₜ N) {O K : Set N} (hφ : IsPLOn 3 3 φ O) (hO : IsOpen O)
    (hK : IsClosed K) (hKO : K ⊆ O) (hfix : EqOn φ id Kᶜ) :
    IsPLHomeomorphInto 3 (φ ∘ f) D := by
  have hpl : IsPLOn 3 3 (φ ∘ f) D := by
    intro x hx
    by_cases hxO : f x ∈ O
    · exact (hφ.isPLAt_of_isOpen hO hxO).comp_isPLWithinAt (hf.isPLOn x hx)
    · have hxK : f x ∉ K := fun hmem => hxO (hKO hmem)
      apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
        (hf.isPLOn x hx) _ hx
      filter_upwards [(hf.continuousOn x hx).preimage_mem_nhdsWithin
        (hK.isOpen_compl.mem_nhds hxK)] with y hy
      exact hfix hy
  exact hpl.isPLHomeomorphInto_of_isPLCellOn hD
    (fun x hx y hy hxy => hf.injOn hx hy (φ.injective hxy))


theorem IsPLHomeomorphInto.exists_supported_model_motion
    {P C : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → N}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPolyhedron P)
    (hC : IsCompact C) (hCP : C ⊆ interior P)
    (φ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
    (hφ : IsPLHomeomorphOn φ univ univ) (hfix : EqOn φ id Cᶜ) :
    ∃ ψ : N ≃ₜ N, EqOn ψ id (u '' C)ᶜ ∧
      (∀ x ∈ P, ψ (u x) = u (φ x)) ∧ IsPLOn 3 3 ψ (interior (u '' P)) := by
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτ : MapsTo τ (u '' P) P := hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn
  have hτpl : IsPLOn 3 3 τ (u '' P) := hu.isPLOn_inverse hleft
  have hτint : MapsTo τ (interior (u '' P)) (interior P) := by
    intro y hy
    rw [← hu.image_interior] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hleft (interior_subset hx)]
    exact hx
  have hτcont : ContinuousOn τ (u '' P) := fun y hy => (hτpl y hy).continuousWithinAt
  let e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) N :=
    { toFun := u
      invFun := τ
      source := interior P
      target := interior (u '' P)
      map_source' := fun x hx => hu.image_interior ▸ ⟨x, hx, rfl⟩
      map_target' := hτint
      left_inv' := fun x hx => hleft (interior_subset hx)
      right_inv' := fun y hy => hright (interior_subset hy)
      open_source := isOpen_interior
      open_target := isOpen_interior
      continuousOn_toFun := hu.continuousOn.mono interior_subset
      continuousOn_invFun := hτcont.mono interior_subset }
  let ψ := e.symm.conjugateHomeomorph φ hC hCP hfix
  have hoff : EqOn ψ id (u '' C)ᶜ := e.symm.conjugateMap_eqOn_compl hfix
  have hconj : ∀ x ∈ P, ψ (u x) = u (φ x) := by
    intro x hx
    by_cases hxi : x ∈ interior P
    · have hux : u x ∈ e.symm.source := by
        change u x ∈ interior (u '' P)
        exact hu.image_interior ▸ ⟨x, hxi, rfl⟩
      change e.symm.conjugateMap φ (u x) = u (φ x)
      rw [e.symm.conjugateMap_of_mem φ hux]
      change u (φ (τ (u x))) = u (φ x)
      rw [hleft hx]
    · have hxC : x ∉ C := fun hmem => hxi (hCP hmem)
      have huxC : u x ∉ u '' C := by
        rintro ⟨y, hy, heq⟩
        exact hxC ((hu.injOn (interior_subset (hCP hy)) hx heq) ▸ hy)
      rw [hoff huxC, hfix hxC]
      rfl
  have hφP : MapsTo φ P P := by
    intro x hx
    by_contra hnot
    have hnotC : φ x ∉ C := fun hmem => hnot (interior_subset (hCP hmem))
    have heq : φ x = x := φ.injective (hfix hnotC)
    exact hnot (heq.symm ▸ hx)
  have hφpl : IsPLOn 3 3 φ P := isPLOn_iff_isPiecewiseAffineOn.mpr
    (hφ.isPiecewiseAffineOn.mono_of_isPolyhedron hP (subset_univ P))
  have hcomp := hu.isPLOn.comp_of_mapsTo (hφpl.comp_of_mapsTo hτpl hτ)
    (hφP.comp hτ)
  have hψ : IsPLOn 3 3 ψ (u '' P) := hcomp.congr fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    change ψ (u x) = u (φ (τ (u x)))
    rw [hleft hx, hconj x hx]
  exact ⟨ψ, hoff, hconj, hψ.mono_of_isOpen isOpen_interior interior_subset⟩

end DifferentialGeometry.Topology.PiecewiseLinear
