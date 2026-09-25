import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalCappingBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapCoreCapping
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoreCylinderAbsorption
import DifferentialGeometry.Topology.Manifold.CylinderCollar.SlabGluing

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance cellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance cellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem capCore_cap_and_frontier (b : T.Boundary) :
    Nonempty (CapCore (range (C.cap b))) ∧
      frontier (range (C.cap b)) = range (C.coreInclusion.comp (T.coreBoundarySphere b)) := by
  obtain ⟨B, hB, hBf⟩ := Manifold.exists_partialDiffeomorph_extension_closedCell
    (C.cap b) (C.cap_embedding b)
  have hball : B '' Metric.closedBall (0 : ThreeSpace) 1 = range (C.cap b) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, mem_closedBall_zero_iff.mp hz⟩, (hBf _).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, mem_closedBall_zero_iff.mpr z.property, hBf z⟩
  refine ⟨⟨CapCore.ball B hB hball⟩, ?_⟩
  rw [← hball, ← B.image_frontier_of_isCompact (isCompact_closedBall _ _) hB,
    frontier_closedBall _ one_ne_zero]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    let q : Sphere 2 := ⟨z, hz⟩
    refine ⟨C.attaching b q, ?_⟩
    exact (C.boundary_eq b q).symm.trans (hBf (sphereToClosedCell q)).symm
  · rintro ⟨q, rfl⟩
    refine ⟨((C.attaching b).symm q).val, ((C.attaching b).symm q).property, ?_⟩
    exact (hBf (sphereToClosedCell ((C.attaching b).symm q))).trans
      ((C.boundary_eq b _).trans (by simp))

theorem isPoincareStandard_component_of_cylindrical_core_boundary_ranges
    (x : T.core) (U : PartialDiffeomorph IC (𝓡 3) Cylinder M.Carrier ∞)
    (hU : univ ×ˢ Icc (0 : ℝ) 1 ⊆ U.source)
    (hcore : U '' (univ ×ˢ Icc (0 : ℝ) 1) = Subtype.val '' connectedComponent x)
    (b₀ b₁ : T.Boundary)
    (hzero : range (fun z : Sphere 2 => U (z, 0)) = range (T.boundarySphere b₀))
    (hone : range (fun z : Sphere 2 => U (z, 1)) = range (T.boundarySphere b₁))
    (hboundary : ∀ b : T.Boundary,
      (∃ z : Sphere 2, T.coreBoundarySphere b z ∈ connectedComponent x) →
        b = b₀ ∨ b = b₁) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  have hUcore {z : Cylinder} (hz : z ∈ univ ×ˢ Icc (0 : ℝ) 1) : U z ∈ T.core := by
    obtain ⟨w, _, hw⟩ := hcore ▸ mem_image_of_mem U hz
    exact hw ▸ w.property
  have hend (b : T.Boundary) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (he : range (fun z : Sphere 2 => U (z, t)) = range (T.boundarySphere b))
      (z : Sphere 2) :
      T.coreBoundarySphere b z ∈ connectedComponent x := by
    have hz : T.boundarySphere b z ∈ Subtype.val '' connectedComponent x := by
      rw [← hcore]
      obtain ⟨w, hw⟩ := he.symm ▸ mem_range_self z
      exact ⟨(w, t), ⟨mem_univ _, ht⟩, hw⟩
    obtain ⟨w, hw, hwz⟩ := hz
    exact (Subtype.ext hwz : w = T.coreBoundarySphere b z) ▸ hw
  have hb₀ := hend b₀ 0 (by norm_num) hzero
  have hb₁ := hend b₁ 1 (by norm_num) hone
  have hcover : (C.coreInclusion '' connectedComponent x ∪ range (C.cap b₀)) ∪
      range (C.cap b₁) = connectedComponent (C.coreInclusion x) := by
    have hh := C.image_coreComponent_union_caps_eq_connectedComponent x {b₀, b₁}
      (by
        intro b hb
        rcases hb with rfl | hb
        · exact hb₀
        · exact mem_singleton_iff.mp hb ▸ hb₁)
      (by intro b hb; simpa only [mem_insert_iff, mem_singleton_iff] using hboundary b hb)
    simpa only [biUnion_insert, biUnion_singleton, union_assoc] using hh
  obtain ⟨F, hFs, _, hF, _⟩ := C.exists_core_neighborhood_partialDiffeomorph x
  let V := U.trans F
  have hV : univ ×ˢ Icc (0 : ℝ) 1 ⊆ V.source := by
    intro z hz
    exact ⟨hU hz, hFs (hUcore hz)⟩
  have hVe (z : Cylinder) (hz : z ∈ univ ×ˢ Icc (0 : ℝ) 1) :
      V z = C.coreInclusion ⟨U z, hUcore hz⟩ := hF ⟨U z, hUcore hz⟩
  have himage : V '' (univ ×ˢ Icc (0 : ℝ) 1) = C.coreInclusion '' connectedComponent x := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hwz⟩ := hcore ▸ mem_image_of_mem U hz
      exact ⟨w, hw, (congrArg C.coreInclusion (Subtype.ext hwz)).trans (hVe z hz).symm⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨z, hz, hzw⟩ := hcore.symm ▸ mem_image_of_mem Subtype.val hw
      exact ⟨z, hz, (hVe z hz).trans (congrArg C.coreInclusion (Subtype.ext hzw))⟩
  obtain ⟨⟨cap₀⟩, hfront₀⟩ := C.capCore_cap_and_frontier b₀
  have hfront : frontier (range (C.cap b₀)) = range (fun z : Sphere 2 => V (z, 0)) := by
    rw [hfront₀]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := hzero.symm ▸ mem_range_self z
      exact ⟨w, (hVe (w, 0) ⟨mem_univ _, by norm_num⟩).trans
        (congrArg C.coreInclusion (Subtype.ext hw))⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := hzero ▸ mem_range_self z
      exact ⟨w, (congrArg C.coreInclusion (Subtype.ext hw)).trans
        (hVe (z, 0) ⟨mem_univ _, by norm_num⟩).symm⟩
  have hside (z : Sphere 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (hcap : V (z, t) ∈ range (C.cap b₀)) : t = 0 := by
    have hzt : (z, t) ∈ univ ×ˢ Icc (0 : ℝ) 1 := ⟨mem_univ _, ht⟩
    have hmem : C.coreInclusion ⟨U (z, t), hUcore hzt⟩ ∈
        range C.coreInclusion ∩ range (C.cap b₀) :=
      ⟨mem_range_self _, (hVe (z, t) hzt) ▸ hcap⟩
    rw [C.core_cap_intersection b₀] at hmem
    obtain ⟨w, hw⟩ := hmem
    have heq : T.boundarySphere b₀ w = U (z, t) :=
      congrArg Subtype.val (C.core_embedding.isEmbedding.injective hw)
    obtain ⟨w', hw'⟩ := hzero.symm ▸ mem_range_self w
    have hcoords : (w', (0 : ℝ)) = (z, t) :=
      U.injOn (hU ⟨mem_univ _, by norm_num⟩) (hU hzt) (hw'.trans heq)
    exact (congrArg Prod.snd hcoords).symm
  obtain ⟨capK⟩ := cap₀.nonempty_union_cylinder V hV hfront hside
  apply C.isPoincareStandard_component_of_capCore_union_cap capK b₁
    (ConnectedComponents.mk (C.coreInclusion x))
  rw [himage, union_comm (range (C.cap b₀)), hcover, ClosedOrientedManifold.componentSet_mk]

theorem isPoincareStandard_component_of_cylindrical_core
    (x : T.core) (U : PartialDiffeomorph IC (𝓡 3) Cylinder M.Carrier ∞)
    (hU : univ ×ˢ Icc (0 : ℝ) 1 ⊆ U.source)
    (hcore : U '' (univ ×ˢ Icc (0 : ℝ) 1) = Subtype.val '' connectedComponent x)
    (b₀ b₁ : T.Boundary)
    (hzero : ∀ z : Sphere 2, U (z, 0) = T.boundarySphere b₀ z)
    (hone : ∀ z : Sphere 2, U (z, 1) = T.boundarySphere b₁ z)
    (hboundary : ∀ b : T.Boundary,
      (∃ z : Sphere 2, T.coreBoundarySphere b z ∈ connectedComponent x) →
        b = b₀ ∨ b = b₁) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  apply C.isPoincareStandard_component_of_cylindrical_core_boundary_ranges x U hU hcore b₀ b₁
    (by simp only [hzero]) (by simp only [hone]) hboundary

theorem isPoincareStandard_component_of_finite_cylindrical_core
    (x : T.core) (P : ℕ → PartialDiffeomorph IC (𝓡 3) Cylinder M.Carrier ∞)
    (η : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (n : ℕ)
    (hsource : ∀ k ≤ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P k).source)
    (hseam : ∀ k < n, ∀ z : Sphere 2, P (k + 1) (z, 0) = P k (η k z, 1))
    (hmeet : ∀ k < n,
      (⋃ j ≤ k, P j '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
          P (k + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) =
        P k '' (univ ×ˢ ({1} : Set ℝ)))
    (hcore : (⋃ k ≤ n, P k '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      Subtype.val '' connectedComponent x)
    (b₀ b₁ : T.Boundary)
    (hzero : ∀ z : Sphere 2, P 0 (z, 0) = T.boundarySphere b₀ z)
    (hone : ∀ z : Sphere 2, P n (z, 1) = T.boundarySphere b₁ z)
    (hboundary : ∀ b : T.Boundary,
      (∃ z : Sphere 2, T.coreBoundarySphere b z ∈ connectedComponent x) →
        b = b₀ ∨ b = b₁) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  obtain ⟨R, hR, hRi, hR0, hR1⟩ :=
    Manifold.exists_finite_unit_slab_concatenation P η n hsource hseam hmeet
  apply C.isPoincareStandard_component_of_cylindrical_core_boundary_ranges x R hR
    (hRi.trans hcore) b₀ b₁
  · simp only [hR0, hzero]
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      change R (z, 1) ∈ range (T.boundarySphere b₁)
      rw [hR1, hone]
      exact mem_range_self _
    · rintro ⟨z, rfl⟩
      refine ⟨(Manifold.cylinderSeamTransport η n).symm z, ?_⟩
      change R ((Manifold.cylinderSeamTransport η n).symm z, 1) = _
      rw [hR1, Diffeomorph.apply_symm_apply, hone]
  · exact hboundary

theorem isPoincareStandard_component_of_returned_cylinder
    (R : PartialDiffeomorph IC I3 Cylinder M.Carrier ∞)
    (hR : univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source)
    (b₀ b₁ : T.Boundary)
    (hzero : range (fun z : Sphere 2 => R (z, 0)) = range (T.boundarySphere b₀))
    (hone : range (fun z : Sphere 2 => R (z, 1)) = range (T.boundarySphere b₁))
    (hinter : R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
        (⋃ a, T.tube a '' {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1}) =
      range (T.boundarySphere b₀) ∪ range (T.boundarySphere b₁))
    (hfront : frontier ((⋃ a, T.tube a ''
        {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1}) ∪
        R '' (univ ×ˢ Icc (0 : ℝ) 1)) ⊆
      ⋃ b : {b : T.Boundary // b ≠ b₀ ∧ b ≠ b₁}, range (T.boundarySphere b.val))
    (x : T.core) (hx : x.val ∈ R '' (univ ×ˢ Icc (0 : ℝ) 1)) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  obtain ⟨_, hcomponent⟩ := T.toTopological.cylinder_eq_image_coreComponent_of_return
    R hR b₀ b₁ hinter hfront
  obtain ⟨hcore, hboundary⟩ := hcomponent x hx
  exact C.isPoincareStandard_component_of_cylindrical_core_boundary_ranges
    x R hR hcore b₀ b₁ hzero hone hboundary

end DifferentialGeometry.Topology.SphericalCapping
