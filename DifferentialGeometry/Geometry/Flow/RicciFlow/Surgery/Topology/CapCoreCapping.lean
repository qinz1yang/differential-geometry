import DifferentialGeometry.Topology.ThreeManifold.SmoothUncapping
import DifferentialGeometry.Topology.Manifold.ClosedBall.Extension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoverClassification
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization
import DifferentialGeometry.Topology.ThreeManifold.CapCoreBallReplacement

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

open Set Metric

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
private local instance cellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance cellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem nonempty_capCore_image_coreInclusion
    {K : Set M.Carrier} (cap : CapCore K) (hK : K ⊆ T.core) :
    Nonempty (CapCore (C.coreInclusion '' (Subtype.val ⁻¹' K : Set T.core))) := by
  obtain ⟨x,hx⟩ := cap.nonempty_carrier
  obtain ⟨F,hFs,_,hF,_⟩ := C.exists_core_neighborhood_partialDiffeomorph ⟨x,hK hx⟩
  have heq : F '' K = C.coreInclusion '' (Subtype.val ⁻¹' K : Set T.core) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hK hz⟩,hz,(hF ⟨z,hK hz⟩).symm⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,hz,hF z⟩
  rw [← heq]
  exact cap.image_of_partialDiffeomorph F (hK.trans hFs)


theorem isPoincareStandard_component_of_capCore_union_cap
    {K : Set N.Carrier} (cap : CapCore K) (b : T.Boundary)
    (c : ConnectedComponents N.Carrier)
    (hcover : K ∪ range (C.cap b) = N.componentSet c) :
    isPoincareStandard (N.component c).Carrier := by
  let U := N.componentOpen c
  have hKU : K ⊆ U := by
    intro x hx
    change x ∈ N.componentSet c
    rw [← hcover]
    exact Or.inl hx
  have hfU (x : ClosedCell 3) : C.cap b x ∈ U := by
    change C.cap b x ∈ N.componentSet c
    rw [← hcover]
    exact Or.inr (mem_range_self x)
  obtain ⟨capU⟩ := cap.nonempty_preimage_open U hKU
  let f : ClosedCell 3 → U := fun x => ⟨C.cap b x, hfU x⟩
  have hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f := by
    apply DifferentialGeometry.Topology.isSmoothEmbedding_of_lift_through_localDiffeomorph
      (I := 𝓡∂ 3) (J := 𝓡 3) (N := U) (g := f)
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val U) (C.cap_embedding b)
      ((C.cap b).continuous.subtype_mk hfU)
    intro x
    rfl
  obtain ⟨B, hB, hBf⟩ := Manifold.exists_partialDiffeomorph_extension_closedCell f hf
  have hBimage : B '' Metric.closedBall (0 : ThreeSpace) 1 = range f := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, mem_closedBall_zero_iff.mp hx⟩, (hBf _).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, mem_closedBall_zero_iff.mpr x.property, hBf x⟩
  have hcov : B '' Metric.closedBall (0 : ThreeSpace) 1 ∪
      (Subtype.val ⁻¹' K : Set U) = univ := by
    rw [hBimage]
    apply eq_univ_of_forall
    intro y
    have hy : y.val ∈ K ∪ range (C.cap b) := by
      rw [hcover]
      exact y.property
    rcases hy with hy | ⟨x, hx⟩
    · exact Or.inr hy
    · exact Or.inl ⟨x, Subtype.ext hx⟩
  obtain ⟨W⟩ := nonempty_positiveComponent_of_ball_cap_cover B hB capU hcov
  exact isPoincareStandard_of_positiveComponent W


theorem isPoincareStandard_component_of_capCore_and_cap_cover
    {K : Set M.Carrier} (cap : CapCore K) (hK : K ⊆ T.core)
    (b : T.Boundary) (c : ConnectedComponents N.Carrier)
    (hcover : (C.coreInclusion '' (Subtype.val ⁻¹' K : Set T.core)) ∪
      range (C.cap b) = N.componentSet c) :
    isPoincareStandard (N.component c).Carrier := by
  obtain ⟨capA⟩ := C.nonempty_capCore_image_coreInclusion cap hK
  exact C.isPoincareStandard_component_of_capCore_union_cap capA b c hcover


theorem exists_cap_partialDiffeomorph (b : T.Boundary) :
    ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace N.Carrier ∞,
      closedBall (0 : ThreeSpace) 1 ⊆ G.source ∧
      (∀ z : ClosedCell 3, G z.val = C.cap b z) ∧
      G '' closedBall (0 : ThreeSpace) 1 = range (C.cap b) ∧
      G '' sphere (0 : ThreeSpace) 1 = range (C.coreInclusion.comp (T.coreBoundarySphere b)) := by
  obtain ⟨G, hG, hGeq⟩ := Manifold.exists_partialDiffeomorph_extension_closedCell
    (C.cap b) (C.cap_embedding b)
  refine ⟨G, hG, hGeq, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, mem_closedBall_zero_iff.mp hz⟩, (hGeq _).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, mem_closedBall_zero_iff.mpr z.property, hGeq z⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      let q : Sphere 2 := ⟨z, hz⟩
      exact ⟨C.attaching b q, (C.boundary_eq b q).symm.trans (hGeq (sphereToClosedCell q)).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨((C.attaching b).symm q).val, ((C.attaching b).symm q).property,
        (hGeq (sphereToClosedCell ((C.attaching b).symm q))).trans
          ((C.boundary_eq b _).trans (by simp))⟩

theorem nonempty_capCore_union_caps_of_finite_ball_complement
    {Ω : Set M.Carrier} (cap : CapCore Ω) (s : Finset T.Boundary)
    (B : T.Boundary → PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M.Carrier ∞)
    (hB : ∀ b ∈ s, closedBall (0 : ThreeSpace) 1 ⊆ (B b).source)
    (hinside : ∀ b ∈ s, B b '' closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
    (hdis : (s : Set T.Boundary).Pairwise (fun b c =>
      Disjoint (B b '' closedBall (0 : ThreeSpace) 1) (B c '' closedBall (0 : ThreeSpace) 1)))
    (hsphere : ∀ b ∈ s, B b '' sphere (0 : ThreeSpace) 1 = range (T.boundarySphere b))
    (x : T.core)
    (hcomponent : Ω \ ⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1 =
      (Subtype.val : T.core → M.Carrier) '' connectedComponent x) :
    Nonempty (CapCore (C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, range (C.cap b))) ∧
      ∃ J : PartialDiffeomorph (𝓡 3) (𝓡 3) M.Carrier N.Carrier ∞,
        Ω ⊆ J.source ∧
        J '' Ω = C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, range (C.cap b) ∧
        (∀ z ∈ connectedComponent x, J z.val = C.coreInclusion z) ∧
        (∀ b ∈ s, ∃ (D : ThreeSpace ≃ₘ[ℝ] ThreeSpace)
          (hD : D '' closedBall (0 : ThreeSpace) 1 = closedBall (0 : ThreeSpace) 1),
          ∀ z : ClosedCell 3,
            J (B b z.val) = C.cap b ⟨D z.val, mem_closedBall_zero_iff.mp
              (hD ▸ mem_image_of_mem D (mem_closedBall_zero_iff.mpr z.property))⟩) ∧
        ∃ O : Set M.Carrier, IsOpen O ∧
          (Subtype.val : T.core → M.Carrier) '' connectedComponent x ⊆ O ∧
          ∀ (z : T.core), z.val ∈ O → J z.val = C.coreInclusion z := by
  classical
  choose G hG hGeq hGclosed hGsphere using C.exists_cap_partialDiffeomorph
  let K := Ω \ ⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1
  have hcomp : K = (Subtype.val : T.core → M.Carrier) '' connectedComponent x := hcomponent
  have hKcore : K ⊆ T.core := by
    intro y hy
    obtain ⟨z, _, hz⟩ := hcomp ▸ hy
    exact hz ▸ z.property
  obtain ⟨P, hPsource, _, hPeq, _⟩ := C.exists_core_neighborhood_partialDiffeomorph x
  have hP : K ⊆ P.source := hKcore.trans hPsource
  have hPK : P '' K = C.coreInclusion '' connectedComponent x := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hwz⟩ := hcomp ▸ hz
      exact ⟨w, hw, (hPeq w).symm.trans (congrArg P hwz)⟩
    · rintro ⟨z, hz, rfl⟩
      have hzK : z.val ∈ K := hcomp.symm ▸ mem_image_of_mem Subtype.val hz
      exact ⟨z.val, hzK, hPeq z⟩
  have hboundary : ∀ b ∈ s, P '' (B b '' sphere (0 : ThreeSpace) 1) =
      G b '' sphere (0 : ThreeSpace) 1 := by
    intro b hb
    rw [hsphere b hb, hGsphere b]
    ext y
    constructor
    · rintro ⟨z, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, (hPeq (T.coreBoundarySphere b q)).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨T.boundarySphere b q, mem_range_self q, hPeq (T.coreBoundarySphere b q)⟩
  have hinter : ∀ b ∈ s, P '' K ∩ G b '' closedBall (0 : ThreeSpace) 1 ⊆
      G b '' sphere (0 : ThreeSpace) 1 := by
    intro b _
    rw [hPK, hGclosed b, hGsphere b]
    exact (inter_subset_inter_left _ (image_subset_range _ _)).trans (C.core_cap_intersection b).subset
  have hdisG : (s : Set T.Boundary).Pairwise (fun b c =>
      Disjoint (G b '' closedBall (0 : ThreeSpace) 1) (G c '' closedBall (0 : ThreeSpace) 1)) := by
    intro b _ c _ hbc
    rw [hGclosed b, hGclosed c]
    exact C.cap_disjoint hbc
  obtain ⟨hcap, J, hJ, hJimage, hballs, O, hO, hKO, _, hJP⟩ :=
    cap.nonempty_finite_ball_replacement s B G hB (fun b _ => hG b)
      hinside hdis hdisG P hP hboundary hinter
  have htarget : P '' K ∪ ⋃ b ∈ s, G b '' closedBall (0 : ThreeSpace) 1 =
      C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, range (C.cap b) := by
    simp only [hPK, hGclosed]
  refine ⟨htarget ▸ hcap, J, hJ, hJimage.trans htarget, ?_, ?_, O, hO, ?_, ?_⟩
  · intro z hz
    have hzK : z.val ∈ K := hcomp.symm ▸ mem_image_of_mem Subtype.val hz
    exact (hJP (hKO hzK)).trans (hPeq z)
  · intro b hb
    obtain ⟨D, hD, hDb⟩ := hballs b hb
    refine ⟨D, hD, ?_⟩
    intro z
    let z' : ClosedCell 3 := ⟨D z.val, mem_closedBall_zero_iff.mp (hD ▸ mem_image_of_mem D (mem_closedBall_zero_iff.mpr z.property))⟩
    exact (hDb z.val (mem_closedBall_zero_iff.mpr z.property)).trans (hGeq b z')
  · rwa [← hcomp]
  · intro z hz
    exact (hJP hz).trans (hPeq z)

end DifferentialGeometry.Topology.SphericalCapping
