import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap
import DifferentialGeometry.Topology.PiecewiseLinear.DiskPseudoIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem exists_prism_extension_of_periodic_lateral_map
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {u : E → E} {φ : E × ℝ → E × ℝ}
    (hu : IsPLHomeomorphOn u (boundaryComplex 2 D).space (boundaryComplex 2 D).space)
    (hφ : IsPLHomeomorphOn φ ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)
      ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))
    (hφ0 : ∀ x ∈ (boundaryComplex 2 D).space, φ (x, 0) = (u x, 0))
    (hφ1 : ∀ x ∈ (boundaryComplex 2 D).space, φ (x, 1) = (u x, 1)) :
    ∃ (a : E → E) (Φ : E × ℝ → E × ℝ), IsPLHomeomorphOn a D.space D.space ∧
      IsPLHomeomorphOn Φ (D.space ×ˢ Icc (0 : ℝ) 1) (D.space ×ˢ Icc (0 : ℝ) 1) ∧
      EqOn Φ φ ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ D.space, Φ (x, 0) = (a x, 0)) ∧
      ∀ x ∈ D.space, Φ (x, 1) = (a x, 1) := by
  classical
  let _ : Finite (boundaryComplex 2 D).faces := (boundaryComplex_faces_finite 2 D).to_subtype
  have hB := isPolyhedron_space (boundaryComplex 2 D)
  have hBD := boundaryComplex_space_subset 2 D
  obtain ⟨a, ha, hau⟩ := exists_isPLHomeomorphOn_of_boundaryComplex D D hD hD hu
  have hends : IsPolyhedron ({0, 1} : Set ℝ) := by
    rw [← singleton_union]
    exact (isHPolytope_singleton (0 : ℝ)).isPolyhedron.union
      (isHPolytope_singleton (1 : ℝ)).isPolyhedron
  have hcaps := hD.isPolyhedron.prod hends
  have hside : IsPolyhedron ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1) :=
    hB.prod isHPolytope_Icc.isPolyhedron
  have hacaps := ha.prodMap hends.isPLHomeomorphOn_id
  have heq : EqOn (Prod.map a (id : ℝ → ℝ)) φ
      ((D.space ×ˢ {0, 1}) ∩ ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)) := by
    intro z hz
    rcases hz.1.2 with h0 | h1
    · have hz0 : z.2 = 0 := h0
      rw [show z = (z.1, 0) from Prod.ext rfl hz0, hφ0 z.1 hz.2.1]
      exact Prod.ext (hau hz.2.1) rfl
    · have hz1 : z.2 = 1 := h1
      rw [show z = (z.1, 1) from Prod.ext rfl hz1, hφ1 z.1 hz.2.1]
      exact Prod.ext (hau hz.2.1) rfl
  have hsurj : SurjOn (Prod.map a (id : ℝ → ℝ))
      ((D.space ×ˢ {0, 1}) ∩ ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))
      ((D.space ×ˢ {0, 1}) ∩ ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)) := by
    intro z hz
    obtain ⟨x, hx, hux⟩ := hu.bijOn.surjOn hz.2.1
    exact ⟨(x, z.2), ⟨⟨hBD hx, hz.1.2⟩, hx, hz.2.2⟩,
      Prod.ext ((hau hx).trans hux) rfl⟩
  obtain ⟨b, hb, hbcap, hbside⟩ :=
    exists_isPLHomeomorphOn_union hcaps hside hacaps hφ heq hsurj
  have hprism := isPLBall_three_prod hD (isPLBall_Icc (zero_lt_one' ℝ))
  obtain ⟨K, hKfin, hKspace⟩ := hprism.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 3 K.space := hKspace.symm ▸ hprism
  have hbd := boundaryComplex_space_prism D hD (zero_lt_one' ℝ) K hKspace
  have hbb : IsPLHomeomorphOn b (boundaryComplex 3 K).space
      (boundaryComplex 3 K).space := by rw [hbd]; exact hb
  obtain ⟨Φ, hΦ, hΦb⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K K hK hK hbb
  rw [hKspace] at hΦ
  rw [hbd] at hΦb
  refine ⟨a, Φ, ha, hΦ, fun z hz => (hΦb (Or.inr hz)).trans (hbside hz), ?_, ?_⟩
  · intro x hx
    have hxcap : (x, (0 : ℝ)) ∈ D.space ×ˢ {0, 1} := ⟨hx, by simp⟩
    exact (hΦb (Or.inl hxcap)).trans (hbcap hxcap)
  · intro x hx
    have hxcap : (x, (1 : ℝ)) ∈ D.space ×ˢ {0, 1} := ⟨hx, by simp⟩
    exact (hΦb (Or.inl hxcap)).trans (hbcap hxcap)

open Classical in
theorem IsCylindricalDiagram.exists_lateral_extension_of_periodic_lift
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {f : E × ℝ → F} {S : Set F} (hf : IsCylindricalDiagram f D.space S)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    {u : E → E} {φ : E × ℝ → E × ℝ}
    (hu : IsPLHomeomorphOn u (boundaryComplex 2 D).space (boundaryComplex 2 D).space)
    (hφ : IsPLHomeomorphOn φ ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)
      ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))
    (hφ0 : ∀ x ∈ (boundaryComplex 2 D).space, φ (x, 0) = (u x, 0))
    (hφ1 : ∀ x ∈ (boundaryComplex 2 D).space, φ (x, 1) = (u x, 1)) :
    ∃ H : F → F, IsPLHomeomorphOn H S S ∧
      ∀ z ∈ (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1, H (f z) = f (φ z) := by
  obtain ⟨a, Φ, ha, hΦ, hside, hΦ0, hΦ1⟩ :=
    exists_prism_extension_of_periodic_lateral_map D hD hu hφ hφ0 hφ1
  have hg := hf.comp_of_ends ha ha hΦ hΦ0 hΦ1
  have hgends : ∀ x ∈ D.space, (f ∘ Φ) (x, 0) = (f ∘ Φ) (x, 1) := by
    intro x hx
    simp only [Function.comp_apply, hΦ0 x hx, hΦ1 x hx]
    exact hends (a x) (ha.bijOn.mapsTo hx)
  obtain ⟨H, hH, hHf⟩ := exists_isPLHomeomorphOn_of_eq_endMap hD.isPolyhedron hf hg
    hD.isPolyhedron.isPLHomeomorphOn_id hends hgends
  refine ⟨H, hH, fun z hz => ?_⟩
  rw [hHf z ⟨boundaryComplex_space_subset 2 D hz.1, hz.2⟩]
  exact congrArg f (hside hz)

end DifferentialGeometry.Topology.PiecewiseLinear
