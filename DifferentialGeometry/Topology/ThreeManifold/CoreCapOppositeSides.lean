import DifferentialGeometry.Topology.ThreeManifold.CutCap

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

local instance coreCapOppositeSidesCharted : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance coreCapOppositeSidesIsManifold : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

private theorem sphereToClosedCell_norm
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ‖(sphereToClosedCell z).1‖ = 1 := by
  have h : dist z.1 (0 : EuclideanSpace ℝ (Fin 3)) = 1 := z.2
  rw [dist_eq_norm, sub_zero] at h
  exact h

theorem image_inter_disjoint_of_core_cap_intersection
    {N A Z S : Type*} (coreInclusion : A → N) (cap : Z → N) (center : S → A)
    (boundary : S → Z) (cellInterior : Set Z)
    (hinter : Set.range coreInclusion ∩ Set.range cap = Set.range (coreInclusion ∘ center))
    (hcap : Function.Injective cap)
    (hboundary : ∀ s, cap (boundary s) = coreInclusion (center s))
    (hsphere : ∀ s, boundary s ∉ cellInterior) :
    cap '' cellInterior ∩ Set.range coreInclusion = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨⟨z, hz, rfl⟩, x, hx⟩
  have hmem : cap z ∈ Set.range coreInclusion ∩ Set.range cap :=
    ⟨⟨x, hx⟩, ⟨z, rfl⟩⟩
  rw [hinter] at hmem
  obtain ⟨s, hs⟩ := hmem
  have h1 : cap (boundary s) = cap z := by rw [hboundary s]; exact hs
  exact hsphere s (hcap h1 ▸ hz)

theorem SphericalCapping.cap_interiorImage_disjoint_coreImage
    {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
    (K : SphericalCapping M N T) (b : T.Boundary) :
    (K.cap b) '' {z : ClosedCell 3 | ‖z.1‖ < 1} ∩ Set.range K.coreInclusion = ∅ :=
  image_inter_disjoint_of_core_cap_intersection
    (fun x => K.coreInclusion x) (fun z => K.cap b z)
    (fun y => T.coreBoundarySphere b y)
    (fun z => sphereToClosedCell ((K.attaching b).symm z))
    {z : ClosedCell 3 | ‖z.1‖ < 1}
    (K.core_cap_intersection b) (K.cap_embedding b).isEmbedding.injective
    (fun z => by rw [K.boundary_eq b ((K.attaching b).symm z), Diffeomorph.apply_symm_apply])
    (fun z => by
      simp only [Set.mem_ofPred_eq]
      rw [sphereToClosedCell_norm]
      norm_num)

theorem SphericalCapping.eq_sphereToClosedCell_of_cap_mem_coreImage
    {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
    (K : SphericalCapping M N T) (b : T.Boundary) {z : ClosedCell 3}
    (hz : K.cap b z ∈ Set.range K.coreInclusion) :
    ∃ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, sphereToClosedCell w = z := by
  obtain ⟨x, hx⟩ := hz
  have hmem : K.cap b z ∈ Set.range K.coreInclusion ∩ Set.range (K.cap b) :=
    ⟨⟨x, hx⟩, ⟨z, rfl⟩⟩
  rw [K.core_cap_intersection b] at hmem
  obtain ⟨y, hy⟩ := hmem
  refine ⟨(K.attaching b).symm y, ?_⟩
  have hb := K.boundary_eq b ((K.attaching b).symm y)
  rw [Diffeomorph.apply_symm_apply] at hb
  exact (K.cap_embedding b).isEmbedding.injective (hb.trans hy)

theorem SphericalCapping.cap_sphereImage_eq_coreBoundarySphere
    {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
    (K : SphericalCapping M N T) (b : T.Boundary) :
    (K.cap b) '' Set.range sphereToClosedCell =
      Set.range (K.coreInclusion.comp (T.coreBoundarySphere b)) := by
  ext y
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    exact ⟨K.attaching b w, (K.boundary_eq b w).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨sphereToClosedCell ((K.attaching b).symm y), ⟨_, rfl⟩, ?_⟩
    rw [K.boundary_eq b ((K.attaching b).symm y), Diffeomorph.apply_symm_apply]
    rfl

theorem SphericalCapping.compl_coreImage_subset_iUnion_capInteriorImage
    {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
    (K : SphericalCapping M N T) :
    (Set.range K.coreInclusion)ᶜ ⊆
      ⋃ b, (K.cap b) '' {z : ClosedCell 3 | ‖z.1‖ < 1} := by
  intro y hy
  have hmem : y ∈ Set.range K.coreInclusion ∪ ⋃ b, Set.range (K.cap b) := by
    rw [K.exhaustive]
    trivial
  rcases hmem with h | h
  · exact absurd h hy
  · obtain ⟨b, z, rfl⟩ := Set.mem_iUnion.mp h
    refine Set.mem_iUnion.mpr ⟨b, ⟨z, ?_, rfl⟩⟩
    by_contra hz
    refine hy ?_
    have hw : sphereToClosedCell
        (⟨z.1, Metric.mem_sphere.mpr
          (by rw [dist_eq_norm, sub_zero]; exact le_antisymm z.2 (not_lt.mp hz))⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) = z := Subtype.ext rfl
    have hsphere : K.cap b z ∈ Set.range (K.coreInclusion.comp (T.coreBoundarySphere b)) := by
      rw [← K.cap_sphereImage_eq_coreBoundarySphere b]
      exact ⟨z, ⟨_, hw⟩, rfl⟩
    obtain ⟨x, hx⟩ := hsphere
    exact ⟨(T.coreBoundarySphere b) x, hx⟩

def SphericalCapping.corePositiveAtBoundary {M N : ClosedOrientedManifold.{u} 3}
    {T : SphericalTubeSystem M} (K : SphericalCapping M N T) : Prop :=
  letI := K.coreCharts
  letI := K.coreSmooth
  ∀ x : T.core, (𝓡∂ 3).IsBoundaryPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : T.core → M.Carrier) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) K.coreInclusion x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : T.core → M.Carrier) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) K.coreInclusion x).toLinearMap hj))
        (M.orientation.orientation x.1) = N.orientation.orientation (K.coreInclusion x)

def SphericalTubeSystem.outwardNormalFirstIsStandardSphereOrientation
    {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M) : Prop :=
  ∀ (b : T.Boundary) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (v w : TangentSpace (𝓡 2) z),
    let _ : FiniteDimensional ℝ (TangentSpace (𝓡 3) (T.boundarySphere b z)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
    let d := mfderiv (𝓡 2) (𝓡 3) (⇑(T.boundarySphere b)) z
    let e := mfderiv (𝓡 2) (𝓡 3)
      (Subtype.val : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
        EuclideanSpace ℝ (Fin 3)) z
    (0 < ((M.orientation.orientation (T.boundarySphere b z)).someBasis (by
      change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
      simp)).det
      (Fin.cons (T.outwardVector b z) (Fin.cons (d v) (Fin.cons (d w) ![])))) ↔
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
        (Fin.cons z.1 (Fin.cons (e v) (Fin.cons (e w) ![]))) < 0

theorem image_inter_disjoint_of_core_cap_intersection_witness :
    (id : ℝ → ℝ) '' {z : ℝ | z ≠ 0} ∩ Set.range (fun _ : ℝ => (0 : ℝ)) = ∅ :=
  image_inter_disjoint_of_core_cap_intersection
    (fun _ : ℝ => (0 : ℝ)) id id (fun _ : ℝ => (0 : ℝ))
    {z : ℝ | z ≠ 0}
    (by rw [Set.range_id, Set.inter_univ, Function.comp_id])
    Function.injective_id (fun _ => rfl) (fun _ hs => hs rfl)

theorem exists_core_cap_intersection_not_disjoint :
    ∃ (coreInclusion cap center boundary : ℝ → ℝ) (cellInterior : Set ℝ),
      Set.range coreInclusion ∩ Set.range cap = Set.range (coreInclusion ∘ center) ∧
        Function.Injective cap ∧
        (∀ s, cap (boundary s) = coreInclusion (center s)) ∧
        cap '' cellInterior ∩ Set.range coreInclusion ≠ ∅ :=
  ⟨fun _ : ℝ => (0 : ℝ), id, id, fun _ : ℝ => (0 : ℝ), Set.univ,
    by rw [Set.range_id, Set.inter_univ, Function.comp_id],
    Function.injective_id, (fun _ => rfl), by
      intro h
      have h0 : (0 : ℝ) ∈ id '' Set.univ ∩ Set.range (fun _ : ℝ => (0 : ℝ)) :=
        ⟨⟨0, trivial, rfl⟩, ⟨0, rfl⟩⟩
      rw [h] at h0
      exact h0⟩

end DifferentialGeometry.Topology
