import DifferentialGeometry.Geometry.Neck.CompactComplementaryComponents
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSmoothSphericalRegion
import DifferentialGeometry.Geometry.Neck.SpatialLevelEmbedding
import DifferentialGeometry.Topology.Manifold.SignedGraphCollar
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollarAmbient
import DifferentialGeometry.Topology.Connected.ComponentFilling
import DifferentialGeometry.Topology.Manifold.FiniteCollarBoundaryAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.Manifold.ConnectedInterior
import DifferentialGeometry.Topology.Embedding.Frontier

open private exists_ambient_spherical_region from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSmoothSphericalRegion

noncomputable section

open Set Manifold
open DifferentialGeometry.Topology
  (exists_smoothBoundaryAtlas_union_connectedComponentIn_closed_exterior)
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {P : OrientedThreeStage.{u}}

private theorem exists_smoothSphericalRegion_of_filled_neck_frontier
    (U : TopologicalSpace.Opens P.Carrier) (g : SmoothRiemannianMetric ThreeModel U)
    {ι : Type u} [Finite ι] {eps : ℝ}
    (point : ι → U)
    (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i, |level i| < eps⁻¹)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun q : Sphere 2 => (neck i).map (q, level i)))
      (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    {W C : Set U} (hCclosed : IsClosed C)
    (hVcompact : IsCompact (W ∪ C)) (hVconn : IsConnected (W ∪ C))
    (hregular : closure (interior (W ∪ C)) = W ∪ C)
    (hfront : frontier (W ∪ C) =
      ⋃ i ∈ {i | Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i))) C},
        range (fun q : Sphere 2 => (neck i).map (q, level i))) :
    let J := {i : ι // Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i))) C}
    ∃ (S : SmoothSphericalRegion P) (label : J ≃ S.Boundary),
      S.region = Subtype.val '' (W ∪ C) ∧
      Subtype.val '' interior W ⊆ interior S.region ∧
      (∀ i q, (S.sphere (label i) q).val = ((neck i.val).map (q, level i.val)).val) ∧
      frontier (W ∪ C) =
        ⋃ i : J, range (fun q : Sphere 2 => (neck i.val).map (q, level i.val)) ∧
      ∀ (i : J) (r σ : ℝ), 0 < r → (σ = 1 ∨ σ = -1) →
        (∀ q t, t ∈ Ioo (-r) r → (q, level i.val + σ * t) ∈ (neck i.val).map.source) →
        (∀ q t, t ∈ Ioo (-r) r →
          ((neck i.val).map (q, level i.val + σ * t) ∈ W ↔ t ≤ 0)) →
        ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 ThreeModel
            (fun q : Sphere 2 => (S.sphere (label i) q).val),
          c.radius < r ∧ ∀ p,
            c.toFun p = ((neck i.val).map (p.1, level i.val + σ * (p.2 : ℝ))).val ∧
            (c.toFun p ∈ S.region ↔ (p.2 : ℝ) ≤ 0) ∧
            (c.toFun p ∈ interior S.region ↔ (p.2 : ℝ) < 0) := by
  have hsmooth (i : ι) : IsSmoothEmbedding I2 I3 ∞
      (fun q : Sphere 2 => (neck i).map (q, level i)) :=
    (neck i).isSmoothEmbedding_level (hlevel i)
  let V := W ∪ C
  let J := {i : ι // Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i))) C}
  have hfrontV : frontier V = ⋃ i : J,
      range (fun q : Sphere 2 => (neck i.val).map (q, level i.val)) := by
    simpa only [iUnion_subtype, V, J, mem_ofPred_eq] using hfront
  obtain ⟨atlas, hatlas⟩ := exists_smoothBoundaryAtlas_of_finite_spatial_neck_levels
    g point neck level hlevel (fun _ => Diffeomorph.refl I2 (Sphere 2) ∞)
    (by simpa only [Diffeomorph.coe_refl, id_eq] using hdisjoint) hregular (by
      intro y hy
      obtain ⟨i, hiy⟩ := mem_iUnion.mp (hfrontV ▸ hy)
      exact mem_iUnion.mpr ⟨i.val, hiy⟩)
  let _ := atlas.toChartedSpace
  let _ := atlas.isManifold
  have hbound := atlas.image_boundary_subtype_val hVcompact.isClosed hatlas
  have hint := atlas.image_interior_subtype_val hatlas
  let _ : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  have hVint : IsConnected (interior V) := by
    refine ⟨?_, ?_⟩
    · by_contra hempty
      have heq : interior V = ∅ := not_nonempty_iff_eq_empty.mp hempty
      have hVempty : V = ∅ := by
        change closure (interior V) = V at hregular
        simpa only [heq, closure_empty] using hregular.symm
      exact hVconn.nonempty.ne_empty hVempty
    · rw [← hint]
      exact (DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior
        (I := 𝓡∂ 3) (M := V)).image Subtype.val continuous_subtype_val.continuousOn
  have hmem (i : J) (q : Sphere 2) : (neck i.val).map (q, level i.val) ∈ V :=
    hVcompact.isClosed.frontier_subset (hfrontV.symm ▸ mem_iUnion.mpr ⟨i, q, rfl⟩)
  let sphere : J → C(Sphere 2, V) := fun i =>
    ⟨fun q => ⟨(neck i.val).map (q, level i.val), hmem i q⟩,
      (hsmooth i.val).contMDiff.continuous.subtype_mk _⟩
  have hdisj : Pairwise (fun i j => Disjoint (range (sphere i)) (range (sphere j))) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro y ⟨p, hp⟩ ⟨q, hq⟩
    exact disjoint_left.mp (hdisjoint (fun he => hij (Subtype.ext he)))
      ⟨p, congrArg Subtype.val hp⟩ ⟨q, congrArg Subtype.val hq⟩
  have hboundary : (𝓡∂ 3).boundary V = ⋃ i, range (sphere i) := by
    ext y
    constructor
    · intro hy
      have hyf : y.val ∈ frontier V := hbound ▸ mem_image_of_mem Subtype.val hy
      obtain ⟨i, q, hq⟩ := mem_iUnion.mp (hfrontV ▸ hyf)
      exact mem_iUnion.mpr ⟨i, q, Subtype.ext hq⟩
    · intro hy
      obtain ⟨i, q, hq⟩ := mem_iUnion.mp hy
      have hyf : y.val ∈ frontier V :=
        hfrontV.symm ▸ mem_iUnion.mpr ⟨i, q, congrArg Subtype.val hq⟩
      rw [← hbound] at hyf
      obtain ⟨z, hz, hzy⟩ := hyf
      exact Subtype.ext hzy ▸ hz
  obtain ⟨S, label, hS, hlabels⟩ := exists_ambient_spherical_region
    U V hVcompact hVconn atlas.isSmoothEmbedding_subtype_val
    (by rw [hint]; exact hVint) sphere (fun i => hsmooth i.val) hdisj hboundary
  refine ⟨S, label, hS, ?_, hlabels, hfrontV, ?_⟩
  · rw [hS, DifferentialGeometry.Topology.Embedding.interior_image_of_isOpenEmbedding
      U.isOpenEmbedding']
    exact image_mono (interior_mono subset_union_left)
  · intro i r σ hr hσ hsource hside
    obtain ⟨r', hr', hr'r, hsource', hside', hinside'⟩ :=
      DifferentialGeometry.Topology.exists_signed_collar_union_of_isClosed
        (neck i.val).map.toOpenPartialHomeomorph hr hσ hsource hside hCclosed i.property
    have hslice (q : Sphere 2) : (q, level i.val) ∈ (neck i.val).map.source := by
      simpa only [mul_zero, add_zero] using hsource q 0 ⟨neg_lt_zero.mpr hr, hr⟩
    obtain ⟨c₀, hcr, _, hcoord⟩ :=
      DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_signed_partialDiffeomorph_graph
        (neck i.val).map (fun _ => level i.val) contMDiff_const hslice σ hσ hr'
    let c₁ := c₀.mapAmbient (Subtype.val : U → P.Carrier)
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val U)
      Subtype.val_injective
    let c : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 ThreeModel
        (fun q : Sphere 2 => (S.sphere (label i) q).val) :=
      { c₁ with zero_eq := fun q => (c₁.zero_eq q).trans (hlabels i q).symm }
    refine ⟨c, hcr.trans_le hr'r, ?_⟩
    intro p
    have ht : (p.2 : ℝ) ∈ Ioo (-r') r' := by
      have hp : -c₀.radius < (p.2 : ℝ) ∧ (p.2 : ℝ) < c₀.radius := p.2.property
      constructor <;> linarith [hp.1, hp.2]
    have hmap : c.toFun p =
        ((neck i.val).map (p.1, level i.val + σ * (p.2 : ℝ))).val :=
      congrArg Subtype.val (hcoord p)
    refine ⟨hmap, ?_, ?_⟩
    · have hmem (y : U) : y.val ∈ S.region ↔ y ∈ V := by
        rw [hS, Subtype.val_injective.mem_set_image]
      rw [hmap, hmem]
      exact hside' p.1 p.2 ht
    · have hmem (y : U) : y.val ∈ interior S.region ↔
          y ∈ interior V := by
        rw [hS, DifferentialGeometry.Topology.Embedding.interior_image_of_isOpenEmbedding
          U.isOpenEmbedding', Subtype.val_injective.mem_set_image]
      rw [hmap, hmem]
      exact hinside' p.1 p.2 ht


theorem exists_smoothSphericalRegion_union_compact_exterior_component
    (U : TopologicalSpace.Opens P.Carrier) (g : SmoothRiemannianMetric ThreeModel U)
    {ι : Type u} [Finite ι] {eps : ℝ}
    (point : ι → U)
    (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i, |level i| < eps⁻¹)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun q : Sphere 2 => (neck i).map (q, level i)))
      (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    {W : Set U} (hWcompact : IsCompact W)
    (hWregular : closure (interior W) = W)
    (hfrontier : frontier W = ⋃ i, range (fun q : Sphere 2 => (neck i).map (q, level i)))
    (x : U)
    (hcompact : IsCompact (connectedComponentIn (interior W)ᶜ x))
    (hx : x ∈ (interior W)ᶜ)
    (hmeet : ∀ y ∈ W,
      (connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W y).Nonempty) :
    let C := connectedComponentIn (interior W)ᶜ x
    let J := {i : ι // Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i))) C}
    ∃ (S : SmoothSphericalRegion P) (label : J ≃ S.Boundary),
      S.region = Subtype.val '' (W ∪ C) ∧
      Subtype.val '' interior W ⊆ interior S.region ∧
      (∀ i q, (S.sphere (label i) q).val = ((neck i.val).map (q, level i.val)).val) ∧
      frontier (W ∪ C) =
        ⋃ i : J, range (fun q : Sphere 2 => (neck i.val).map (q, level i.val)) ∧
      ∀ (i : J) (r σ : ℝ), 0 < r → (σ = 1 ∨ σ = -1) →
        (∀ q t, t ∈ Ioo (-r) r → (q, level i.val + σ * t) ∈ (neck i.val).map.source) →
        (∀ q t, t ∈ Ioo (-r) r →
          ((neck i.val).map (q, level i.val + σ * t) ∈ W ↔ t ≤ 0)) →
        ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 ThreeModel
            (fun q : Sphere 2 => (S.sphere (label i) q).val),
          c.radius < r ∧ ∀ p,
            c.toFun p = ((neck i.val).map (p.1, level i.val + σ * (p.2 : ℝ))).val ∧
            (c.toFun p ∈ S.region ↔ (p.2 : ℝ) ≤ 0) ∧
            (c.toFun p ∈ interior S.region ↔ (p.2 : ℝ) < 0) := by
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  let e : ι → PartialDiffeomorph IC I3 Cylinder U ∞ := fun i =>
    (((Diffeomorph.refl I2 (Sphere 2) ∞).prodCongr
      (DifferentialGeometry.Topology.translateDiffeomorph (level i))).toPartialDiffeomorph).trans
      (neck i).map
  have heq (i : ι) (q : Sphere 2) (t : ℝ) :
      e i (q, t) = (neck i).map (q, t + level i) := rfl
  have hzero (i : ι) (q : Sphere 2) : (q, (0 : ℝ)) ∈ (e i).source := by
    refine ⟨mem_univ _, ?_⟩
    change (q, 0 + level i) ∈ (neck i).map.source
    rw [zero_add]
    exact (neck i).domain ⟨mem_univ _, (abs_lt.mp (hlevel i)).1, (abs_lt.mp (hlevel i)).2⟩
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 1))) U :=
    inferInstanceAs (ChartedSpace ThreeSpace U)
  let _ : IsManifold (𝓡 (2 + 1)) ∞ U :=
    inferInstanceAs (IsManifold I3 ∞ U)
  obtain ⟨_, hregular, hfront, _⟩ :=
    exists_smoothBoundaryAtlas_union_connectedComponentIn_closed_exterior
      (n := 2)
      e hzero (by simpa only [heq, zero_add] using hdisjoint) hWregular
      (by simpa only [heq, zero_add] using hfrontier) x
  let C := connectedComponentIn (interior W)ᶜ x
  let V := W ∪ C
  have hVcompact : IsCompact V := hWcompact.union hcompact
  have hCclosed : IsClosed C := isOpen_interior.isClosed_compl.connectedComponentIn x
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hx
  have hVconn : IsConnected V :=
    DifferentialGeometry.Topology.isConnected_union_of_inter_connectedComponentIn hCconn hmeet
  exact exists_smoothSphericalRegion_of_filled_neck_frontier U g point neck level hlevel
    hdisjoint hCclosed hVcompact hVconn hregular (by
      simpa only [heq, zero_add, C, mem_ofPred_eq] using hfront)


theorem exists_smoothSphericalRegion_of_compact_bridging_exterior_components
    (U : TopologicalSpace.Opens P.Carrier) (g : SmoothRiemannianMetric ThreeModel U)
    [PreconnectedSpace U] {ι : Type u} [Finite ι] {eps : ℝ}
    (point : ι → U)
    (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i, |level i| < eps⁻¹)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun q : Sphere 2 => (neck i).map (q, level i)))
      (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    {W : Set U} (hWcompact : IsCompact W)
    (hWregular : closure (interior W) = W)
    (hfrontier : frontier W = ⋃ i, range (fun q : Sphere 2 => (neck i).map (q, level i)))
    {A B : ℝ}
    (hscalar : ∀ i q, A < metricScalarAt g ((neck i).map (q, level i)) ∧
      metricScalarAt g ((neck i).map (q, level i)) ≤ B)
    (hne : W.Nonempty)
    (hcompact : ∀ x : U, x ∈ (interior W)ᶜ → ∀ p q : U,
      (connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W p).Nonempty →
      (connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W q).Nonempty →
      connectedComponentIn W p ≠ connectedComponentIn W q →
        IsCompact (connectedComponentIn (interior W)ᶜ x)) :
    ∃ (rep : ConnectedComponents ↥((interior W)ᶜ) → ↥((interior W)ᶜ))
      (chosen : Finset (ConnectedComponents ↥((interior W)ᶜ))),
      (∀ i, ConnectedComponents.mk (rep i) = i) ∧
      (∀ i, i ∈ chosen ↔ IsCompact (connectedComponentIn (interior W)ᶜ (rep i))) ∧
    let C := ⋃ i ∈ chosen, connectedComponentIn (interior W)ᶜ (rep i)
    let J := {i : ι // Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i))) C}
    ∃ (S : SmoothSphericalRegion P) (label : J ≃ S.Boundary) (hSU : S.region ⊆ U),
      S.region = Subtype.val '' (W ∪ C) ∧
      Subtype.val '' interior W ⊆ interior S.region ∧
      (∀ i q, (S.sphere (label i) q).val = ((neck i.val).map (q, level i.val)).val) ∧
      frontier (W ∪ C) =
        ⋃ i : J, range (fun q : Sphere 2 => (neck i.val).map (q, level i.val)) ∧
      (∀ b q, A < metricScalarAt g (Set.inclusion hSU (S.sphere b q)) ∧
        metricScalarAt g (Set.inclusion hSU (S.sphere b q)) ≤ B) ∧
      ∀ (i : J) (r σ : ℝ), 0 < r → (σ = 1 ∨ σ = -1) →
        (∀ q t, t ∈ Ioo (-r) r → (q, level i.val + σ * t) ∈ (neck i.val).map.source) →
        (∀ q t, t ∈ Ioo (-r) r →
          ((neck i.val).map (q, level i.val + σ * t) ∈ W ↔ t ≤ 0)) →
        ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 ThreeModel
            (fun q : Sphere 2 => (S.sphere (label i) q).val),
          c.radius < r ∧ ∀ p,
            c.toFun p = ((neck i.val).map (p.1, level i.val + σ * (p.2 : ℝ))).val ∧
            (c.toFun p ∈ S.region ↔ (p.2 : ℝ) ≤ 0) ∧
            (c.toFun p ∈ interior S.region ↔ (p.2 : ℝ) < 0) := by
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have hWclosed : IsClosed W := hWcompact.isClosed
  have hEregular : closure (interior ((interior W)ᶜ)) = (interior W)ᶜ := by
    rw [interior_compl, hWregular, closure_compl]
  have hEfrontier : frontier ((interior W)ᶜ) = frontier W := by
    rw [frontier_compl]
    simp only [frontier, interior_interior, hWregular, hWclosed.closure_eq]
  obtain ⟨atlasE, _⟩ := exists_smoothBoundaryAtlas_of_finite_spatial_neck_levels
    g point neck level hlevel (fun _ => Diffeomorph.refl I2 (Sphere 2) ∞)
    (by simpa only [Diffeomorph.coe_refl, id_eq] using hdisjoint) hEregular (by
      simpa only [Diffeomorph.coe_refl, id_eq, hEfrontier] using hfrontier.subset)
  let _ := atlasE.toChartedSpace
  let _ := atlasE.isManifold
  let _ : LocallyConnectedSpace ↥((interior W)ᶜ) :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 3) ↥((interior W)ᶜ)
  obtain ⟨rep, chosen, hrep, hchosen, hKcompact, hKconn, hKregular, _⟩ :=
    DifferentialGeometry.Topology.exists_compact_connected_union_closed_exterior_components
      hWcompact hne hWregular hcompact
  let C := ⋃ i ∈ chosen, connectedComponentIn (interior W)ᶜ (rep i)
  have hCclosed : IsClosed C := chosen.finite_toSet.isClosed_biUnion
    (fun i _ => isOpen_interior.isClosed_compl.connectedComponentIn (rep i).val)
  have hfaces (i : ι) : IsPreconnected (range (fun q : Sphere 2 => (neck i).map (q, level i))) :=
    isPreconnected_range ((neck i).isSmoothEmbedding_level (hlevel i)).contMDiff.continuous
  have hfront : frontier (W ∪ C) =
      ⋃ i ∈ {i | Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i))) C},
        range (fun q : Sphere 2 => (neck i).map (q, level i)) := by
    simpa only [iUnion_subtype, C] using
      DifferentialGeometry.Topology.frontier_union_iUnion_closed_exterior_components_eq_iUnion
        (fun i => range (fun q : Sphere 2 => (neck i).map (q, level i))) hfaces hfrontier
        (fun i : {i // i ∈ chosen} => (rep i.val).val)
  obtain ⟨S, label, hS, hlow, hlabels, hfrontV, hcollar⟩ :=
    exists_smoothSphericalRegion_of_filled_neck_frontier U g point neck level hlevel
      hdisjoint hCclosed hKcompact hKconn hKregular hfront
  have hSU : S.region ⊆ U := by
    intro y hy
    rw [hS] at hy
    obtain ⟨z, _, rfl⟩ := hy
    exact z.property
  refine ⟨rep, chosen, hrep, hchosen, S, label, hSU, hS, hlow, hlabels, hfrontV, ?_, hcollar⟩
  intro b q
  obtain ⟨i, rfl⟩ := label.surjective b
  have heq : Set.inclusion hSU (S.sphere (label i) q) =
      (neck i.val).map (q, level i.val) := Subtype.ext (hlabels i q)
  rw [heq]
  exact hscalar i.val q


theorem exists_smoothSphericalRegion_of_spatial_neck_exterior_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (P : OrientedThreeStage.{u}) (U : TopologicalSpace.Opens P.Carrier)
        [PreconnectedSpace U] (g : SmoothRiemannianMetric ThreeModel U)
        (ι : Type u) [Finite ι] (point : ι → U)
        (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ),
        (∀ i, |level i| ≤ 4) →
        Pairwise (fun i j => Disjoint
          (range (fun q : Sphere 2 => (neck i).map (q, level i)))
          (range (fun q : Sphere 2 => (neck j).map (q, level j)))) →
        ∀ W : Set U, IsCompact W → closure (interior W) = W →
        frontier W = ⋃ i, range (fun q : Sphere 2 => (neck i).map (q, level i)) →
        ∀ A B : ℝ,
        (∀ i q, A < metricScalarAt g ((neck i).map (q, level i)) ∧
          metricScalarAt g ((neck i).map (q, level i)) ≤ B) →
        W.Nonempty →
        (∀ x : U, x ∉ interior W → Nonempty (SpatialNeck g eps x)) →
        (∀ R : ℝ, IsCompact {x : U | metricScalarAt g x ≤ R}) →
    ∃ (rep : ConnectedComponents ↥((interior W)ᶜ) → ↥((interior W)ᶜ))
      (chosen : Finset (ConnectedComponents ↥((interior W)ᶜ))),
      (∀ i, ConnectedComponents.mk (rep i) = i) ∧
      (∀ i, i ∈ chosen ↔ IsCompact (connectedComponentIn (interior W)ᶜ (rep i))) ∧
    let C := ⋃ i ∈ chosen, connectedComponentIn (interior W)ᶜ (rep i)
    let J := {i : ι // Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i))) C}
    ∃ (S : SmoothSphericalRegion P) (label : J ≃ S.Boundary) (hSU : S.region ⊆ U),
      S.region = Subtype.val '' (W ∪ C) ∧
      Subtype.val '' interior W ⊆ interior S.region ∧
      (∀ i q, (S.sphere (label i) q).val = ((neck i.val).map (q, level i.val)).val) ∧
      frontier (W ∪ C) =
        ⋃ i : J, range (fun q : Sphere 2 => (neck i.val).map (q, level i.val)) ∧
      (∀ b q, A < metricScalarAt g (Set.inclusion hSU (S.sphere b q)) ∧
        metricScalarAt g (Set.inclusion hSU (S.sphere b q)) ≤ B) ∧
      ∀ (i : J) (r σ : ℝ), 0 < r → (σ = 1 ∨ σ = -1) →
        (∀ q t, t ∈ Ioo (-r) r → (q, level i.val + σ * t) ∈ (neck i.val).map.source) →
        (∀ q t, t ∈ Ioo (-r) r →
          ((neck i.val).map (q, level i.val + σ * t) ∈ W ↔ t ≤ 0)) →
        ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 ThreeModel
            (fun q : Sphere 2 => (S.sphere (label i) q).val),
          c.radius < r ∧ ∀ p,
            c.toFun p = ((neck i.val).map (p.1, level i.val + σ * (p.2 : ℝ))).val ∧
            (c.toFun p ∈ S.region ↔ (p.2 : ℝ) ≤ 0) ∧
            (c.toFun p ∈ interior S.region ↔ (p.2 : ℝ) < 0) := by
  obtain ⟨eta, heta, hbridge⟩ := exists_spatial_neck_compact_bridging_component_tolerance.{u, u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps P U _ g ι _ point neck level hlevel hdisjoint W hW hregular hfront
    A B hscalar hne hneck hsublevel
  have hlevel' (i : ι) : |level i| < eps⁻¹ := by
    have hfour : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck i).eps_pos).mpr (by linarith [(neck i).eps_small])
    exact (hlevel i).trans_lt hfour
  apply exists_smoothSphericalRegion_of_compact_bridging_exterior_components U g point neck level
    hlevel' hdisjoint hW hregular hfront hscalar hne
  intro x _ p q hp hq hpq
  exact hbridge eps heps U g W hW hregular ι point neck level hlevel hdisjoint hfront
    hneck hsublevel x p q hp hq hpq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
