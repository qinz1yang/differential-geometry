/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HoledDiskBoundaryExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLHomeomorphOn.exists_holed_surface_extension_of_planar_charts
    {ι : Type*} [Finite ι] {C C' : Set E3} {D D' : Set Plane}
    {A B : ι → Set Plane} {χ χ' : E3 → Plane}
    {f : Plane → Plane} {ψ : ι → Plane → Plane}
    (hχ : IsPLHomeomorphOn χ C D) (hχ' : IsPLHomeomorphOn χ' C' D')
    (hf : IsPLHomeomorphOn f D D')
    (hD : IsPLBall 2 D) (hD' : IsPLBall 2 D')
    (hA : ∀ i, IsPLBall 2 (A i)) (hB : ∀ i, IsPLBall 2 (B i))
    (hAD : ∀ i, A i ⊆ D) (hBD : ∀ i, B i ⊆ interior D')
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hmatch : ∀ i, f '' A i = B i)
    (hψ : ∀ i, IsPLHomeomorphOn (ψ i) (frontier (A i)) (frontier (B i)))
    (hpos : ∀ i, IsPLCirclePositive (frontier (B i))
      (ψ i ∘ Function.invFunOn f D)) :
    ∃ G : E3 → E3,
      IsPLHomeomorphOn G
        (Function.invFunOn χ C '' (D \ ⋃ i, interior (A i)))
        (Function.invFunOn χ' C' '' (D' \ ⋃ i, interior (B i))) ∧
      EqOn G (Function.invFunOn χ' C' ∘ f ∘ χ)
        (Function.invFunOn χ C '' frontier D) ∧
      ∀ i, EqOn G (Function.invFunOn χ' C' ∘ ψ i ∘ χ)
        (Function.invFunOn χ C '' frontier (A i)) := by
  let R := D \ ⋃ i, interior (A i)
  let R' := D' \ ⋃ i, interior (B i)
  obtain ⟨g, hg, hgf, hgψ⟩ :=
    hf.exists_holed_disk_extension_of_positive_boundary_corrections
      hD hD' hA hB hAD hBD hBdis hmatch hψ hpos
  have hR : IsPolyhedron R := hD.isPolyhedron.sdiff_iUnion_interior_of_isPLBall hA
  have hR' : IsPolyhedron R' := hD'.isPolyhedron.sdiff_iUnion_interior_of_isPLBall hB
  have hRD : R ⊆ D := sdiff_subset
  have hR'D' : R' ⊆ D' := sdiff_subset
  have hsource : IsPolyhedron (Function.invFunOn χ C '' R) :=
    hR.image_of_isPiecewiseAffineOn
      (hχ.symm.isPiecewiseAffineOn.mono_of_isPolyhedron hR hRD)
      (hχ.symm.bijOn.injOn.mono hRD)
  have hsourceC : Function.invFunOn χ C '' R ⊆ C := by
    rintro x ⟨y, hy, rfl⟩
    exact hχ.symm.bijOn.mapsTo (hRD hy)
  have hχRimage : χ '' (Function.invFunOn χ C '' R) = R := by
    apply Subset.antisymm
    · rintro z ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [hχ.bijOn.invOn_invFunOn.2 (hRD hy)] using hy
    · intro y hy
      exact ⟨Function.invFunOn χ C y, ⟨y, hy, rfl⟩,
        hχ.bijOn.invOn_invFunOn.2 (hRD hy)⟩
  have hχR : IsPLHomeomorphOn χ (Function.invFunOn χ C '' R) R := by
    have hr := hχ.restrict hsource hsourceC
    rwa [hχRimage] at hr
  have hχ'R' : IsPLHomeomorphOn (Function.invFunOn χ' C') R'
      (Function.invFunOn χ' C' '' R') := hχ'.symm.restrict hR' hR'D'
  refine ⟨Function.invFunOn χ' C' ∘ g ∘ χ, (hχR.trans hg).trans hχ'R', ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    have hyD : y ∈ D := hD.isPolyhedron.isClosed.frontier_subset hy
    have hleft := hχ.bijOn.invOn_invFunOn.2 hyD
    change Function.invFunOn χ' C' (g (χ (Function.invFunOn χ C y))) =
      Function.invFunOn χ' C' (f (χ (Function.invFunOn χ C y)))
    rw [hleft, hgf hy]
  · intro i
    rintro x ⟨y, hy, rfl⟩
    have hyD : y ∈ D :=
      hAD i ((hA i).isPolyhedron.isClosed.frontier_subset hy)
    have hleft := hχ.bijOn.invOn_invFunOn.2 hyD
    change Function.invFunOn χ' C' (g (χ (Function.invFunOn χ C y))) =
      Function.invFunOn χ' C' (ψ i (χ (Function.invFunOn χ C y)))
    rw [hleft, hgψ i hy]

theorem IsPLHomeomorphOn.exists_holed_surface_extension_of_prescribed_boundary_maps
    {ι : Type*} [Finite ι] {C C' : Set E3} {D D' : Set Plane}
    {A B : ι → Set Plane} {χ χ' : E3 → Plane}
    {f : Plane → Plane} {φ : E3 → E3} {ψ : ι → E3 → E3}
    (hχ : IsPLHomeomorphOn χ C D) (hχ' : IsPLHomeomorphOn χ' C' D')
    (hf : IsPLHomeomorphOn f D D')
    (hD : IsPLBall 2 D) (hD' : IsPLBall 2 D')
    (hA : ∀ i, IsPLBall 2 (A i)) (hB : ∀ i, IsPLBall 2 (B i))
    (hAD : ∀ i, A i ⊆ D) (hBD : ∀ i, B i ⊆ interior D')
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hmatch : ∀ i, f '' A i = B i)
    (hφC : MapsTo φ (Function.invFunOn χ C '' frontier D) C')
    (hfφ : EqOn f (χ' ∘ φ ∘ Function.invFunOn χ C) (frontier D))
    (hψC : ∀ i, MapsTo (ψ i) (Function.invFunOn χ C '' frontier (A i)) C')
    (hψ : ∀ i, IsPLHomeomorphOn
      (χ' ∘ ψ i ∘ Function.invFunOn χ C) (frontier (A i)) (frontier (B i)))
    (hpos : ∀ i, IsPLCirclePositive (frontier (B i))
      ((χ' ∘ ψ i ∘ Function.invFunOn χ C) ∘ Function.invFunOn f D)) :
    ∃ G : E3 → E3,
      IsPLHomeomorphOn G
        (Function.invFunOn χ C '' (D \ ⋃ i, interior (A i)))
        (Function.invFunOn χ' C' '' (D' \ ⋃ i, interior (B i))) ∧
      EqOn G φ (Function.invFunOn χ C '' frontier D) ∧
      ∀ i, EqOn G (ψ i) (Function.invFunOn χ C '' frontier (A i)) := by
  obtain ⟨G, hG, hGouter, hGinner⟩ :=
    IsPLHomeomorphOn.exists_holed_surface_extension_of_planar_charts hχ hχ' hf hD hD' hA hB hAD hBD
      hBdis hmatch hψ hpos
  refine ⟨G, hG, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyD : y ∈ D := hD.isPolyhedron.isClosed.frontier_subset hy
    have hxy := hχ.bijOn.invOn_invFunOn.2 hyD
    have hφy : φ (Function.invFunOn χ C y) ∈ C' :=
      hφC ⟨y, hy, rfl⟩
    have hback := hχ'.bijOn.invOn_invFunOn.1 hφy
    calc
      G (Function.invFunOn χ C y) =
          Function.invFunOn χ' C' (f (χ (Function.invFunOn χ C y))) :=
        hGouter ⟨y, hy, rfl⟩
      _ = φ (Function.invFunOn χ C y) := by
        rw [hxy, hfφ hy]
        exact hback
  · intro i x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyD : y ∈ D :=
      hAD i ((hA i).isPolyhedron.isClosed.frontier_subset hy)
    have hxy := hχ.bijOn.invOn_invFunOn.2 hyD
    have hψy : ψ i (Function.invFunOn χ C y) ∈ C' :=
      hψC i ⟨y, hy, rfl⟩
    have hback := hχ'.bijOn.invOn_invFunOn.1 hψy
    calc
      G (Function.invFunOn χ C y) =
          Function.invFunOn χ' C'
            ((χ' ∘ ψ i ∘ Function.invFunOn χ C) (χ (Function.invFunOn χ C y))) :=
        hGinner i ⟨y, hy, rfl⟩
      _ = ψ i (Function.invFunOn χ C y) := by
        rw [hxy]
        exact hback

end DifferentialGeometry.Topology.PiecewiseLinear
