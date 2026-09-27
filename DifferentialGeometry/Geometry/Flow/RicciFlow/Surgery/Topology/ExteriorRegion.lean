import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalRegion
import DifferentialGeometry.Topology.Connected.CoverBySides
import DifferentialGeometry.Topology.SphereSeparation.NormalChartHalves
import DifferentialGeometry.Topology.Manifold.InteriorImage
import DifferentialGeometry.Topology.VanKampen.SmoothSphereSeparation
import DifferentialGeometry.Topology.SphereSeparation.HalfSpaceClosure

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

noncomputable def SmoothSphericalRegion.interiorImage (P : OrientedThreeStage.{u})
    (C : SmoothSphericalRegion P) : Set P.Carrier :=
  letI := C.charts
  letI := C.smooth
  (Subtype.val : C.region → P.Carrier) '' (𝓡∂ 3).interior C.region

theorem SmoothSphericalRegion.region_eq_interiorImage_union_spheres {P : OrientedThreeStage.{u}}
    (C : SmoothSphericalRegion P) :
    C.region = C.interiorImage ∪ (⋃ b, Set.range (fun y : Sphere 2 => (C.sphere b y).1)) :=
  letI := C.charts
  letI := C.smooth
  let h := ModelWithCorners.interior_union_boundary_eq_univ (I := (𝓡∂ 3)) (M := C.region)
  let himg : (Subtype.val : C.region → P.Carrier) '' (𝓡∂ 3).interior C.region ∪
      (⋃ b, (Subtype.val : C.region → P.Carrier) '' Set.range (C.sphere b)) = C.region := by
    simpa only [Set.image_univ, Subtype.range_coe, Set.image_union, C.boundary_eq,
      Set.image_iUnion] using
      congrArg (fun s : Set C.region => (Subtype.val : C.region → P.Carrier) '' s) h
  have hgoal : (Subtype.val : C.region → P.Carrier) '' (𝓡∂ 3).interior C.region ∪
      (⋃ b, (Subtype.val : C.region → P.Carrier) '' Set.range (C.sphere b)) =
      C.interiorImage ∪ (⋃ b, Set.range (fun y : Sphere 2 => (C.sphere b y).1)) := by
    rw [SmoothSphericalRegion.interiorImage]
    congr 1
    exact Set.iUnion_congr fun b =>
      (Set.range_comp (Subtype.val : C.region → P.Carrier) (⇑(C.sphere b))).symm
  himg.symm.trans hgoal

theorem SmoothSphericalRegion.interiorImage_subset_region {P : OrientedThreeStage.{u}}
    (C : SmoothSphericalRegion P) : C.interiorImage ⊆ C.region :=
  letI := C.charts
  letI := C.smooth
  fun x hx => by
    obtain ⟨p, -, rfl⟩ := hx
    exact p.2

theorem SmoothSphericalRegion.isOpen_interiorImage {P : OrientedThreeStage.{u}}
    (C : SmoothSphericalRegion P) : IsOpen C.interiorImage :=
  letI := C.charts
  letI := C.smooth
  by
    have h := DifferentialGeometry.Topology.Manifold.isOpen_image_interior_of_isImmersion
      (I := (𝓡∂ 3)) (J := ThreeModel) C.induced.isImmersion (by rfl)
    simpa only [SmoothSphericalRegion.interiorImage] using h

theorem SmoothSphericalRegion.interiorImage_subset_interior {P : OrientedThreeStage.{u}}
    (C : SmoothSphericalRegion P) : C.interiorImage ⊆ interior C.region :=
  interior_maximal C.interiorImage_subset_region C.isOpen_interiorImage

theorem SmoothSphericalRegion.closure_interiorImage_eq_region {P : OrientedThreeStage.{u}}
    (C : SmoothSphericalRegion P) : closure C.interiorImage = C.region :=
  letI := C.charts
  letI := C.smooth
  by
    have h := DifferentialGeometry.Topology.Manifold.closure_image_interior_eq_closure_range
      (I := (𝓡∂ 3)) (M := C.region)
    rw [SmoothSphericalRegion.interiorImage]
    exact h.trans C.compact.isClosed.closure_eq

theorem SmoothSphericalRegion.frontier_subset_spheres {P : OrientedThreeStage.{u}}
    (C : SmoothSphericalRegion P) :
    frontier C.region ⊆ ⋃ b, Set.range (fun y : Sphere 2 => (C.sphere b y).1) :=
  letI := C.charts
  letI := C.smooth
  fun x hx => by
    have hxR : x ∈ C.region := by
      have h1 : x ∈ closure C.region := hx.1
      rwa [C.compact.isClosed.closure_eq] at h1
    have h2 : x ∈ C.interiorImage ∪
        ⋃ b, Set.range (fun y : Sphere 2 => (C.sphere b y).1) := by
      rw [← C.region_eq_interiorImage_union_spheres]
      exact hxR
    rcases h2 with h | h
    · exact absurd (C.interiorImage_subset_interior h) hx.2
    · exact h

structure SphericalSide {P : OrientedThreeStage.{u}} (C : SmoothSphericalRegion P)
    (b : C.Boundary) where
  outer : Set P.Carrier
  inner : Set P.Carrier
  isOpen_outer : IsOpen outer
  isOpen_inner : IsOpen inner
  isConnected_outer : IsConnected outer
  isConnected_inner : IsConnected inner
  disjoint_outer_inner : Disjoint outer inner
  disjoint_outer_region : Disjoint outer C.region
  union_eq_compl : outer ∪ inner = (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ
  closure_outer : closure outer = outer ∪ Set.range (fun y : Sphere 2 => (C.sphere b y).1)
  closure_inner : closure inner = inner ∪ Set.range (fun y : Sphere 2 => (C.sphere b y).1)
  interiorImage_subset_inner : C.interiorImage ⊆ inner

namespace SphericalSide

variable {P : OrientedThreeStage.{u}} {C : SmoothSphericalRegion P} {b : C.Boundary}

theorem outer_subset_compl (d : SphericalSide C b) :
    d.outer ⊆ (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ :=
  fun _ hx => d.union_eq_compl ▸ Set.mem_union_left _ hx

theorem inner_subset_compl (d : SphericalSide C b) :
    d.inner ⊆ (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ :=
  fun _ hx => d.union_eq_compl ▸ Set.mem_union_right _ hx

theorem disjoint_outer_range (d : SphericalSide C b) :
    Disjoint d.outer (Set.range (fun y : Sphere 2 => (C.sphere b y).1)) :=
  Set.disjoint_left.mpr fun _ hx hy => d.outer_subset_compl hx hy

theorem disjoint_inner_range (d : SphericalSide C b) :
    Disjoint d.inner (Set.range (fun y : Sphere 2 => (C.sphere b y).1)) :=
  Set.disjoint_left.mpr fun _ hx hy => d.inner_subset_compl hx hy

theorem exists_nhds_inter_compl_region_subset (d : SphericalSide C b) (y : Sphere 2) :
    ∃ U ∈ 𝓝 (C.sphere b y).1, U ∩ C.regionᶜ ⊆ d.outer := by
  classical
  let finBdry : Fintype C.Boundary := C.finiteBoundary
  let e : Sphere 2 → P.Carrier := fun y => (C.sphere b y).1
  let other : Set P.Carrier := ⋃ d' : {d' : C.Boundary // d' ≠ b},
    Set.range (fun y : Sphere 2 => (C.sphere d'.1 y).1)
  have hclosed : IsClosed other := by
    refine isClosed_iUnion_of_finite fun d' : {d' : C.Boundary // d' ≠ b} => ?_
    exact DifferentialGeometry.Topology.SphereSeparation.isClosed_range_sphereTwo_of_isSmoothEmbedding
      (C.sphere_smooth d'.1)
  have hyO : e y ∈ otherᶜ := by
    intro hmem
    obtain ⟨d', hd'⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨y', hy'⟩ := hd'
    exact Set.disjoint_left.mp (C.sphere_disjoint d'.2) ⟨y', rfl⟩
      ⟨y, Subtype.ext hy'.symm⟩
  obtain ⟨c, hcpos, hcneg, hcO⟩ :=
    DifferentialGeometry.Topology.SphereSeparation.exists_normalChart_connectedHalves_subset
      (C.sphere_smooth b) y hclosed.isOpen_compl hyO
  have hVfront : c.neighborhood ∩ frontier C.region ⊆
      Set.range (fun y : Sphere 2 => (C.sphere b y).1) := by
    rintro z ⟨hzV, hzfront⟩
    obtain ⟨d', hd'⟩ := Set.mem_iUnion.mp (C.frontier_subset_spheres hzfront)
    by_cases hdb : d' = b
    · subst hdb
      exact hd'
    · exact absurd (Set.mem_iUnion.mpr ⟨⟨d', hdb⟩, hd'⟩) (hcO hzV)
  have hpos : c.positiveHalf ⊆ d.outer ∨ c.positiveHalf ⊆ d.inner :=
    hcpos.isPreconnected.subset_or_subset d.isOpen_outer d.isOpen_inner d.disjoint_outer_inner
      fun z hz => d.union_eq_compl.symm ▸ c.positiveHalf_subset_compl_range hz
  have hneg : c.negativeHalf ⊆ d.outer ∨ c.negativeHalf ⊆ d.inner :=
    hcneg.isPreconnected.subset_or_subset d.isOpen_outer d.isOpen_inner d.disjoint_outer_inner
      fun z hz => d.union_eq_compl.symm ▸ c.negativeHalf_subset_compl_range hz
  have hnotbothOuter : ¬ (c.positiveHalf ⊆ d.outer ∧ c.negativeHalf ⊆ d.outer) :=
    (DifferentialGeometry.Topology.SphereSeparation.not_both_normalHalves_subset_of_twoSidedCover
      d.disjoint_outer_inner d.union_eq_compl d.closure_outer d.closure_inner c).1
  have hnotbothInner : ¬ (c.positiveHalf ⊆ d.inner ∧ c.negativeHalf ⊆ d.inner) :=
    (DifferentialGeometry.Topology.SphereSeparation.not_both_normalHalves_subset_of_twoSidedCover
      d.disjoint_outer_inner d.union_eq_compl d.closure_outer d.closure_inner c).2
  have hycl : e y ∈ closure C.interiorImage := by
    rw [C.closure_interiorImage_eq_region]
    exact (C.sphere b y).2
  obtain ⟨q, hqV, hqW⟩ :=
    mem_closure_iff.mp hycl c.neighborhood c.isOpen_neighborhood c.image_mem_neighborhood
  have hqinner : q ∈ d.inner := d.interiorImage_subset_inner hqW
  have hqnotrange : q ∉ Set.range (fun y : Sphere 2 => (C.sphere b y).1) :=
    d.inner_subset_compl hqinner
  have hqhalves : q ∈ c.positiveHalf ∪ c.negativeHalf := by
    rw [← c.neighborhood_diff_range_eq_halves]
    exact ⟨hqV, hqnotrange⟩
  have contains : ∀ {H : Set P.Carrier}, IsPreconnected H → H ⊆ c.neighborhood →
      H ⊆ (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ →
      (H ∩ C.interiorImage).Nonempty → H ⊆ C.region := by
    intro H hHpre hHV hHrange hneW
    have hdisj : Disjoint H (frontier C.region) :=
      Set.disjoint_left.mpr fun z hzH hzfront =>
        hHrange hzH (hVfront ⟨hHV hzH, hzfront⟩)
    have hne : (H ∩ C.region).Nonempty :=
      hneW.imp fun z hz => ⟨hz.1, C.interiorImage_subset_region hz.2⟩
    exact (DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
      hHpre hne hdisj).trans interior_subset
  rcases hqhalves with hqpos | hqneg
  · have hposInner : c.positiveHalf ⊆ d.inner := by
      rcases hpos with h | h
      · exact absurd ⟨h hqpos, hqinner⟩ fun hbad => d.disjoint_outer_inner.le_bot hbad
      · exact h
    have hnegOuter : c.negativeHalf ⊆ d.outer := by
      rcases hneg with h | h
      · exact h
      · exact absurd ⟨hposInner, h⟩ hnotbothInner
    have hposregion : c.positiveHalf ⊆ C.region :=
      contains hcpos.isPreconnected (fun z hz => hz.1)
        c.positiveHalf_subset_compl_range ⟨q, hqpos, hqW⟩
    refine ⟨c.neighborhood, c.isOpen_neighborhood.mem_nhds c.image_mem_neighborhood, ?_⟩
    rintro z ⟨hzV, hzRc⟩
    have hznotrange : z ∉ Set.range (fun y : Sphere 2 => (C.sphere b y).1) := by
      rintro ⟨y', hy'⟩
      exact hzRc (hy' ▸ (C.sphere b y').2)
    have hzhalves : z ∈ c.positiveHalf ∪ c.negativeHalf := by
      rw [← c.neighborhood_diff_range_eq_halves]
      exact ⟨hzV, hznotrange⟩
    rcases hzhalves with hz | hz
    · exact absurd (hposregion hz) hzRc
    · exact hnegOuter hz
  · have hnegInner : c.negativeHalf ⊆ d.inner := by
      rcases hneg with h | h
      · exact absurd ⟨h hqneg, hqinner⟩ fun hbad => d.disjoint_outer_inner.le_bot hbad
      · exact h
    have hposOuter : c.positiveHalf ⊆ d.outer := by
      rcases hpos with h | h
      · exact h
      · exact absurd ⟨h, hnegInner⟩ hnotbothInner
    have hnegregion : c.negativeHalf ⊆ C.region :=
      contains hcneg.isPreconnected (fun z hz => hz.1)
        c.negativeHalf_subset_compl_range ⟨q, hqneg, hqW⟩
    refine ⟨c.neighborhood, c.isOpen_neighborhood.mem_nhds c.image_mem_neighborhood, ?_⟩
    rintro z ⟨hzV, hzRc⟩
    have hznotrange : z ∉ Set.range (fun y : Sphere 2 => (C.sphere b y).1) := by
      rintro ⟨y', hy'⟩
      exact hzRc (hy' ▸ (C.sphere b y').2)
    have hzhalves : z ∈ c.positiveHalf ∪ c.negativeHalf := by
      rw [← c.neighborhood_diff_range_eq_halves]
      exact ⟨hzV, hznotrange⟩
    rcases hzhalves with hz | hz
    · exact hposOuter hz
    · exact absurd (hnegregion hz) hzRc

end SphericalSide

theorem exists_sphericalSide (P : OrientedThreeStage.{u}) [ConnectedSpace P.Carrier]
    [SimplyConnectedSpace P.Carrier] (C : SmoothSphericalRegion P) (b : C.Boundary) :
    Nonempty (SphericalSide C b) := by
  classical
  let : LocallyPathConnectedSpace P.Carrier :=
    ChartedSpace.locallyPathConnectedSpace ThreeSpace P.Carrier
  let : LocallyConnectedSpace P.Carrier :=
    ChartedSpace.locallyConnectedSpace ThreeSpace P.Carrier
  obtain ⟨h⟩ := DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_smoothSphereEmbedding
    (fun y : Sphere 2 => (C.sphere b y).1) (C.sphere_smooth b)
  let n := h.toTwoSidedCollar
  have hBopen : IsOpen n.negativeSide := n.isOpen_negativeSide
  have hDopen : IsOpen n.positiveSide := n.isOpen_positiveSide
  have hBconn : IsConnected n.negativeSide :=
    isConnected_connectedComponent.image (Subtype.val : n.complement → P.Carrier)
      continuous_subtype_val.continuousOn
  have hDconn : IsConnected n.positiveSide :=
    isConnected_connectedComponent.image (Subtype.val : n.complement → P.Carrier)
      continuous_subtype_val.continuousOn
  have hBsub : n.negativeSide ⊆
      (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ := n.negativeSide_subset_complement
  have hDsub : n.positiveSide ⊆
      (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ := n.positiveSide_subset_complement
  have hBdisj : Disjoint n.negativeSide n.positiveSide := n.disjoint_negativeSide_positiveSide
  have hunionSplit : n.complement = n.negativeSide ∪ n.positiveSide :=
    n.complement_eq_negativeSide_union_positiveSide
  have hunion : n.negativeSide ∪ n.positiveSide =
      (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ := hunionSplit.symm
  have hunionComm : n.positiveSide ∪ n.negativeSide =
      (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ := by
    rw [Set.union_comm]; exact hunion
  have hBcl : closure n.negativeSide =
      n.negativeSide ∪ Set.range (fun y : Sphere 2 => (C.sphere b y).1) :=
    n.closure_negativeSide
  have hDcl : closure n.positiveSide =
      n.positiveSide ∪ Set.range (fun y : Sphere 2 => (C.sphere b y).1) :=
    n.closure_positiveSide
  have hsplit : C.interiorImage ⊆ n.negativeSide ∨ C.interiorImage ⊆ n.positiveSide :=
    interiorImage_subset_side_of_union P C b hBopen hDopen hBdisj hunionSplit
  have hregion : ∀ S T : Set P.Carrier, Disjoint S T →
      closure T = T ∪ Set.range (fun y : Sphere 2 => (C.sphere b y).1) →
      S ⊆ (Set.range (fun y : Sphere 2 => (C.sphere b y).1))ᶜ →
      C.interiorImage ⊆ T → Disjoint S C.region := by
    intro S T hST hTcl hSsub hW
    refine Set.disjoint_left.mpr fun z hzS hzR => ?_
    have hcl : C.region ⊆ closure T := by
      rw [← C.closure_interiorImage_eq_region]
      exact closure_mono hW
    rw [hTcl] at hcl
    rcases hcl hzR with hzT | hzrange
    · exact hST.le_bot ⟨hzS, hzT⟩
    · exact hSsub hzS hzrange
  rcases hsplit with hW | hW
  · refine ⟨SphericalSide.mk n.positiveSide n.negativeSide hDopen hBopen hDconn hBconn
      hBdisj.symm (hregion n.positiveSide n.negativeSide hBdisj.symm hBcl hDsub hW) hunionComm
      hDcl hBcl hW⟩
  · refine ⟨SphericalSide.mk n.negativeSide n.positiveSide hBopen hDopen hBconn hDconn
      hBdisj (hregion n.negativeSide n.positiveSide hBdisj hDcl hBsub hW) hunion
      hBcl hDcl hW⟩

noncomputable def sphericalSide (P : OrientedThreeStage.{u}) [ConnectedSpace P.Carrier]
    [SimplyConnectedSpace P.Carrier] (C : SmoothSphericalRegion P) (b : C.Boundary) :
    SphericalSide C b :=
  Classical.choice (exists_sphericalSide P C b)

theorem exists_exteriorRegions (P : OrientedThreeStage.{u}) [ConnectedSpace P.Carrier]
    [SimplyConnectedSpace P.Carrier] (C : SmoothSphericalRegion P) :
    Nonempty (ExteriorRegions C) := by
  classical
  let : LocallyConnectedSpace P.Carrier :=
    ChartedSpace.locallyConnectedSpace ThreeSpace P.Carrier
  refine rfs_exterior_branches_of_boundary_sides P C
    (fun b => (sphericalSide P C b).outer)
    (fun b => (sphericalSide P C b).isOpen_outer)
    (fun b => (sphericalSide P C b).isConnected_outer)
    (fun b => Set.disjoint_iff_inter_eq_empty.mp (sphericalSide P C b).disjoint_outer_region)
    (fun b => (sphericalSide P C b).closure_outer) ?_ ?_
  · intro b x
    exact DifferentialGeometry.Topology.SphereSeparation.exists_embeddedSphereSideNormalChart_of_isOpen_side
      (C.sphere_smooth b) (sphericalSide P C b).isOpen_outer
      (sphericalSide P C b).isOpen_inner (sphericalSide P C b).outer_subset_compl
      (sphericalSide P C b).disjoint_outer_inner (sphericalSide P C b).union_eq_compl
      (sphericalSide P C b).closure_outer (sphericalSide P C b).closure_inner x
  · refine DifferentialGeometry.Topology.union_iUnion_closure_eq_univ_of_local_side
      (fun b => Set.range (fun y : Sphere 2 => (C.sphere b y).1))
      (fun b => (sphericalSide P C b).outer) C.region C.compact.isClosed C.connected.nonempty
      C.frontier_subset_spheres (fun b => (sphericalSide P C b).isOpen_outer) ?_ ?_
    · intro b z hz
      rw [(sphericalSide P C b).closure_outer] at hz
      rcases hz.1 with h | h
      · exact h
      · obtain ⟨y, hy⟩ := h
        exact absurd (hy ▸ (C.sphere b y).2) hz.2
    · intro b p hp
      obtain ⟨y, rfl⟩ := hp
      exact (sphericalSide P C b).exists_nhds_inter_compl_region_subset y

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
