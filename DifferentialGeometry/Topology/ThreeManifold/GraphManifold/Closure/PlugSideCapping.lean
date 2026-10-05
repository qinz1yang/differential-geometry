import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugComponentCapCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCappingCore
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingRestriction
import DifferentialGeometry.Topology.Covering.ImmersionLift

/-!
One-sphere side capping on the same actual bounded plug cut and capped components.
The full collars and all core, cap, retaining and attachment maps are their original restrictions.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.GraphManifold.MixedBoundaryCertificate
open scoped Manifold ContDiff Topology

universe u
namespace GC.Seifert.ElementaryPresentation
variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))
  (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)

local notation "B₀" => E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
local notation "D₀" => E.fibrePlugCutComponents h hlin hc hn d hs heq
local notation "D₁" => E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ
local notation "port" => E.fibrePlugCutPortEquiv h hc hn
abbrev plugComponentCutCarrier (i : Fin 2) : CompactCarrier.{u} :=
  GC.Topology.componentCarrier (boundedPlugCutCarrier d hs)
    (E.fibrePlugCutComponents h hlin hc hn d hs heq) i

local notation "Cᵢ" i => E.plugComponentCutCarrier h hlin d hs heq hc hn i
local notation "Sᵢ" i => E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i

private theorem plugSide_sphere_owned (i : Fin 2) :
    ((B₀).sphere i).target ⊆ (D₀).piece i :=
  E.fibrePlugCutComponents_fullSphere_owned h hlin hc hn d hs heq i

private def plugSideTori (i : Fin 2) : BoundaryTori (Cᵢ i) 1 where
  collar r := codRestrictOpens ((B₀).tori.collar (port i)) ((D₀).piece i)
    ((D₀).connected i).toNonempty
  source_eq r := (codRestrictOpens_source _ _ _
    (E.fibrePlugCutComponents_fullTorus_owned h hlin hc hn d hs heq hρ hρ1 hI havρ i)).trans
      ((B₀).tori.source_eq (port i))
  boundary_zero r t := by
    apply (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val
      (I := (boundedPlugCutCarrier d hs).model) (u := (D₀).piece i)).mpr
    rw [codRestrictOpens_apply]
    · exact (B₀).tori.boundary_zero (port i) t
    · exact E.fibrePlugCutComponents_torus_owned h hlin hc hn d hs heq hρ hρ1 hI havρ i t
  disjoint r s hrs := (hrs (Subsingleton.elim r s)).elim

private theorem plugSideTori_apply (i : Fin 2) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) : (E.plugSideTori h hlin d hs hI heq hc hn hρ hρ1 havρ i
      |>.collar 0 p).val = (B₀).tori.collar (port i) p :=
  codRestrictOpens_apply (I := halfCollarModel) (J := (boundedPlugCutCarrier d hs).model) _ _ _
    (E.fibrePlugCutComponents_fullTorus_owned h hlin hc hn d hs heq hρ hρ1 hI havρ i
      (((B₀).tori.collar (port i)).map_source (((B₀).tori.source_eq (port i)).symm.subset hp)))

private def plugSideSphere (i : Fin 2) :
    PartialDiffeomorph sphereHalfCollarModel (Cᵢ i).model
      (ClosureSphere.{u} × EuclideanHalfSpace 1) (Cᵢ i).Carrier ∞ :=
  codRestrictOpens ((B₀).sphere i) ((D₀).piece i) ((D₀).connected i).toNonempty

private theorem plugSideSphere_source (i : Fin 2) :
    (E.plugSideSphere h hlin d hs hI heq hc hn hρ hρ1 havρ i).source =
      sphereHalfCollarSource :=
  (codRestrictOpens_source _ _ _
    (E.plugSide_sphere_owned h hlin d hs hI heq hc hn hρ hρ1 havρ i)).trans
      ((B₀).sphere_source i)

private theorem plugSideSphere_apply (i : Fin 2)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    (E.plugSideSphere h hlin d hs hI heq hc hn hρ hρ1 havρ i p).val = (B₀).sphere i p :=
  codRestrictOpens_apply (I := sphereHalfCollarModel)
    (J := (boundedPlugCutCarrier d hs).model) _ _ _
    (E.plugSide_sphere_owned h hlin d hs hI heq hc hn hρ hρ1 havρ i
      (((B₀).sphere i).map_source (((B₀).sphere_source i).symm.subset hp)))

private theorem plugSide_zero_source (z : ClosureSphere.{u}) :
    (z, halfZero) ∈ sphereHalfCollarSource := by
  change (0 : ℝ) < 1
  norm_num

abbrev plugSideBoundary (i : Fin 2) : MixedBoundaryCertificate (Cᵢ i) where
  torusCount := 1
  tori := E.plugSideTori h hlin d hs hI heq hc hn hρ hρ1 havρ i
  sphereCount := 1
  sphere r := E.plugSideSphere h hlin d hs hI heq hc hn hρ hρ1 havρ i
  sphere_source r := E.plugSideSphere_source h hlin d hs hI heq hc hn hρ hρ1 havρ i
  sphere_disjoint r s hrs := (hrs (Subsingleton.elim r s)).elim
  sphere_zero_boundary r z := by
    apply (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val
      (I := (boundedPlugCutCarrier d hs).model) (u := (D₀).piece i)).mpr
    rw [E.plugSideSphere_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
      (plugSide_zero_source z)]
    exact (B₀).sphere_zero_boundary i z
  cross_disjoint r s := by
    change Disjoint (codRestrictOpens ((B₀).tori.collar (port i)) ((D₀).piece i) _).target
      (codRestrictOpens ((B₀).sphere i) ((D₀).piece i) _).target
    rw [codRestrictOpens_target, codRestrictOpens_target]
    exact ((B₀).cross_disjoint (port i) i).preimage Subtype.val
  exhausted := by
    ext x
    constructor
    · intro hx
      have hb := (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val
        (I := (boundedPlugCutCarrier d hs).model) (u := (D₀).piece i)).mp hx
      change x.val ∈ (boundedPlugCutCarrier d hs).model.boundary
        (boundedPlugCutCarrier d hs).Carrier at hb
      rw [(B₀).exhausted] at hb
      rcases hb with ht | hsp
      · obtain ⟨r, t, he⟩ := mem_iUnion.mp ht
        have hr := (E.fibrePlugCutComponents_torus_mem_iff h hlin hc hn d hs heq
          hρ hρ1 hI havρ r i t).mp (he ▸ x.property)
        subst r
        exact Or.inl (mem_iUnion.mpr ⟨0, t, Subtype.ext
          ((E.plugSideTori_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
            (zero_mem_halfCollarSource t)).trans he)⟩)
      · obtain ⟨k, z, he⟩ := mem_iUnion.mp hsp
        have hk : k = i := by
          by_contra hne
          exact disjoint_left.mp ((D₀).disjoint hne)
            (E.plugSide_sphere_owned h hlin d hs hI heq hc hn hρ hρ1 havρ k
              (((B₀).sphere k).map_source (((B₀).sphere_source k).symm.subset
                (plugSide_zero_source z)))) (by
                exact (congrArg (fun y => y ∈ (D₀).piece i) he).mpr x.property)
        subst k
        exact Or.inr (mem_iUnion.mpr ⟨0, z, Subtype.ext
          ((E.plugSideSphere_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
            (plugSide_zero_source z)).trans he)⟩)
    · rintro (ht | hsp)
      · obtain ⟨r, t, rfl⟩ := mem_iUnion.mp ht
        exact (E.plugSideTori h hlin d hs hI heq hc hn hρ hρ1 havρ i).boundary_zero r t
      · obtain ⟨r, z, rfl⟩ := mem_iUnion.mp hsp
        apply (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val
          (I := (boundedPlugCutCarrier d hs).model) (u := (D₀).piece i)).mpr
        rw [E.plugSideSphere_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
          (plugSide_zero_source z)]
        exact (B₀).sphere_zero_boundary i z

local instance plugSideQuotientCharts :
    ChartedSpace (EuclideanHalfSpace 3) (B₀).SphereCapQuotient :=
  (B₀).sphereCapQuotientChartedSpace

local instance plugSideQuotientSmooth : IsManifold (𝓡∂ 3) ∞ (B₀).SphereCapQuotient :=
  (B₀).sphereCapQuotientIsManifold

local instance plugSideCapCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance plugSideCapSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

private def plugSideCore (i : Fin 2) : C((Cᵢ i).Carrier, (Sᵢ i).Carrier) :=
  ⟨fun x => ⟨(B₀).sphereCapCore x.val,
    (E.fibrePlugCapComponents_core_mem h hlin hc hn d hs heq hρ hρ1 hI havρ i x.val).mpr
      x.property⟩,
    ((B₀).sphereCapCore.continuous.comp continuous_subtype_val).subtype_mk
      (fun x => (E.fibrePlugCapComponents_core_mem h hlin hc hn d hs heq
        hρ hρ1 hI havρ i x.val).mpr x.property)⟩

private def plugSideCap (i : Fin 2) : C(ClosedCell 3, (Sᵢ i).Carrier) :=
  ⟨fun x => ⟨(B₀).sphereCapReparameterizedCap i x,
    E.fibrePlugCapComponents_cap_owned h hlin hc hn d hs heq hρ hρ1 hI havρ i x⟩,
    ((B₀).sphereCapReparameterizedCap i).continuous.subtype_mk
      (fun x => E.fibrePlugCapComponents_cap_owned h hlin hc hn d hs heq
        hρ hρ1 hI havρ i x)⟩

private theorem plugSideCore_embedding (i : Fin 2) :
    IsSmoothEmbedding (Cᵢ i).model (Sᵢ i).model ∞
      (E.plugSideCore h hlin d hs hI heq hc hn hρ hρ1 havρ i) := by
  apply DifferentialGeometry.Topology.isSmoothEmbedding_of_lift_through_localDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val
      (I := (B₀).sphereCapCarrier.model) ((D₁).piece i))
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen
      (boundedPlugCutCarrier d hs).model (B₀).sphereCapCarrier.model
      (B₀).sphereCapRelativeCapping.core (B₀).sphereCapRelativeCapping.core_embedding
      ((D₀).piece i))
    (E.plugSideCore h hlin d hs hI heq hc hn hρ hρ1 havρ i).continuous
  intro x
  rfl

private theorem plugSideCap_embedding (i : Fin 2) :
    IsSmoothEmbedding (𝓡∂ 3) (Sᵢ i).model ∞
      (E.plugSideCap h hlin d hs hI heq hc hn hρ hρ1 havρ i) := by
  apply DifferentialGeometry.Topology.isSmoothEmbedding_of_lift_through_localDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val
      (I := (B₀).sphereCapCarrier.model) ((D₁).piece i))
    ((B₀).sphereCapRelativeCapping.cap_embedding i)
    (E.plugSideCap h hlin d hs hI heq hc hn hρ hρ1 havρ i).continuous
  intro x
  rfl

private theorem plugSideCap_mem_iff {i k : Fin 2} (x : ClosedCell 3) :
    (B₀).sphereCapReparameterizedCap k x ∈ (D₁).piece i ↔ k = i := by
  change (B₀).sphereCapBall k ((B₀).sphereCapOrientationData.reparameterization k x) ∈
    (B₀).sphereCapComponentSet D₀ i ↔ k = i
  have hi := (B₀).sphereCapComponentSet_ball_mem D₀ i k
    ((B₀).sphereCapOrientationData.reparameterization k x)
  have ho := E.fibrePlugCutBoundary_sphere_owner h hlin hc hn d hs heq hρ hρ1 hI havρ k
  constructor
  · intro hm
    exact ho.symm.trans (hi.mp hm)
  · intro hk
    exact hi.mpr (ho.trans hk)

private def plugSideRetained (i : Fin 2) : BoundaryTori (Sᵢ i) 1 where
  collar r := codRestrictOpens ((B₀).sphereCapRetained.collar (port i)) ((D₁).piece i)
    ((D₁).connected i).toNonempty
  source_eq r := (codRestrictOpens_source _ _ _
    (E.fibrePlugCapComponents_fullTorus_owned h hlin hc hn d hs heq hρ hρ1 hI havρ i)).trans
      ((B₀).sphereCapRetained.source_eq (port i))
  boundary_zero r t := by
    apply (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val
      (I := (B₀).sphereCapCarrier.model) (u := (D₁).piece i)).mpr
    rw [codRestrictOpens_apply]
    · exact (B₀).sphereCapRetained.boundary_zero (port i) t
    · exact (E.fibrePlugCapComponents_torus_mem_iff h hlin hc hn d hs heq
        hρ hρ1 hI havρ (port i) i t).mpr rfl
  disjoint r s hrs := (hrs (Subsingleton.elim r s)).elim

private theorem plugSideRetained_apply (i : Fin 2) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    ((E.plugSideRetained h hlin d hs hI heq hc hn hρ hρ1 havρ i).collar 0 p).val =
      (B₀).sphereCapRetained.collar (port i) p :=
  codRestrictOpens_apply (I := halfCollarModel) (J := (B₀).sphereCapCarrier.model) _ _ _
    (E.fibrePlugCapComponents_fullTorus_owned h hlin hc hn d hs heq hρ hρ1 hI havρ i
      (((B₀).sphereCapRetained.collar (port i)).map_source
        (((B₀).sphereCapRetained.source_eq (port i)).symm.subset hp)))

private theorem plugSideCore_mfderiv (i : Fin 2) (x : (Cᵢ i).Carrier) :
    mfderiv (Cᵢ i).model (Sᵢ i).model
      (E.plugSideCore h hlin d hs hI heq hc hn hρ hρ1 havρ i) x =
    mfderiv (boundedPlugCutCarrier d hs).model (𝓡∂ 3)
      (B₀).sphereCapCore x.val := by
  exact (DifferentialGeometry.mfderiv_subtypeVal_comp
    (I := (Cᵢ i).model) (J := (B₀).sphereCapCarrier.model)
    (E.plugSideCore h hlin d hs hI heq hc hn hρ hρ1 havρ i) x).symm.trans
      (DifferentialGeometry.mfderiv_restrict_open
        (I := (boundedPlugCutCarrier d hs).model) (J := 𝓡∂ 3)
        (B₀).sphereCapCore ((D₀).piece i) x)

private theorem plugSideCap_mfderiv (i : Fin 2) (x : ClosedCell 3) :
    mfderiv (𝓡∂ 3) (Sᵢ i).model
      (E.plugSideCap h hlin d hs hI heq hc hn hρ hρ1 havρ i) x =
    mfderiv (𝓡∂ 3) (𝓡∂ 3)
      ((B₀).sphereCapReparameterizedCap i) x := by
  exact (DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓡∂ 3) (J := (B₀).sphereCapCarrier.model)
    (E.plugSideCap h hlin d hs hI heq hc hn hρ hρ1 havρ i) x).symm

def plugSideCapping (i : Fin 2) : RelativeSphereCapping (Cᵢ i) (Sᵢ i)
    (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i) := by
  let : NeZero (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).torusCount := by
    change NeZero 1
    infer_instance
  let : NeZero (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).sphereCount := by
    change NeZero 1
    infer_instance
  let : Subsingleton
      (Fin (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).sphereCount) := by
    change Subsingleton (Fin 1)
    infer_instance
  refine {
    core := E.plugSideCore h hlin d hs hI heq hc hn hρ hρ1 havρ i
    core_embedding := E.plugSideCore_embedding h hlin d hs hI heq hc hn hρ hρ1 havρ i
    cap r := E.plugSideCap h hlin d hs hI heq hc hn hρ hρ1 havρ i
    cap_embedding r := E.plugSideCap_embedding h hlin d hs hI heq hc hn hρ hρ1 havρ i
    attaching r := (B₀).sphereCapOrientationData.attaching i
    boundary_eq r z := by
      apply Subtype.ext
      change (B₀).sphereCapReparameterizedCap i (closureSphereToBall z) =
        (B₀).sphereCapCore
          (E.plugSideSphere h hlin d hs hI heq hc hn hρ hρ1 havρ i
            ((B₀).sphereCapOrientationData.attaching i z, halfZero)).val
      rw [E.plugSideSphere_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
        (plugSide_zero_source _)]
      exact (B₀).sphereCapRelativeCapping.boundary_eq i z
    covers := by
      apply eq_univ_of_forall
      intro x
      rcases (B₀).sphereCapRelativeCapping.every_point x.val with ⟨y, hy⟩ | ⟨k, y, hy⟩
      · have hm : y ∈ (D₀).piece i :=
          (E.fibrePlugCapComponents_core_mem h hlin hc hn d hs heq hρ hρ1 hI havρ i y).mp
            (hy ▸ x.property)
        exact Or.inl ⟨⟨y, hm⟩, Subtype.ext hy⟩
      · have hk : k = i := (E.plugSideCap_mem_iff h hlin d hs hI heq hc hn hρ hρ1 havρ
          (i := i) (k := k) y).mp
          (hy ▸ x.property)
        subst k
        exact Or.inr (mem_iUnion.mpr ⟨0, y, Subtype.ext hy⟩)
    core_cap_intersection r := by
      ext x
      constructor
      · rintro ⟨⟨y, hy⟩, z, hz⟩
        have hm : x.val ∈ range (B₀).sphereCapRelativeCapping.core ∩
            range ((B₀).sphereCapRelativeCapping.cap i) :=
          ⟨⟨y.val, congrArg Subtype.val hy⟩, ⟨z, congrArg Subtype.val hz⟩⟩
        rw [(B₀).sphereCapRelativeCapping.core_cap_intersection i] at hm
        obtain ⟨w, hw⟩ := hm
        refine ⟨w, Subtype.ext ?_⟩
        change (B₀).sphereCapCore
          (E.plugSideSphere h hlin d hs hI heq hc hn hρ hρ1 havρ i (w, halfZero)).val = x.val
        rw [E.plugSideSphere_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
          (plugSide_zero_source w)]
        exact hw
      · rintro ⟨z, rfl⟩
        refine ⟨mem_range_self _, ?_⟩
        refine ⟨closureSphereToBall (((B₀).sphereCapOrientationData.attaching i).symm z),
          Subtype.ext ?_⟩
        change (B₀).sphereCapReparameterizedCap i
          (closureSphereToBall (((B₀).sphereCapOrientationData.attaching i).symm z)) = _
        have hbound := (B₀).sphereCapReparameterizedCap_boundary i
          (((B₀).sphereCapOrientationData.attaching i).symm z)
        have hsphere := E.plugSideSphere_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
          (plugSide_zero_source z)
        exact hbound.trans
          ((congrArg (fun w => (B₀).sphereCapCore ((B₀).sphere i (w, halfZero)))
            (((B₀).sphereCapOrientationData.attaching i).apply_symm_apply z)).trans
            (congrArg (B₀).sphereCapCore hsphere.symm))
    cap_disjoint r s hrs := (hrs (Subsingleton.elim r s)).elim
    retained := E.plugSideRetained h hlin d hs hI heq hc hn hρ hρ1 havρ i
    retained_collar r p hp := by
      apply Subtype.ext
      have hr : r = (0 : Fin 1) := Subsingleton.elim r 0
      subst r
      rw [E.plugSideRetained_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i hp]
      change (B₀).sphereCapRetained.collar (port i) p =
        (B₀).sphereCapCore
          ((E.plugSideTori h hlin d hs hI heq hc hn hρ hρ1 havρ i).collar 0 p).val
      rw [E.plugSideTori_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i hp]
      exact (B₀).sphereCapRetained_collar (port i) hp
    boundary_exhausted := by
      ext x
      constructor
      · intro hx
        have hb := (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val
          (I := (B₀).sphereCapCarrier.model) (u := (D₁).piece i)).mp hx
        change x.val ∈ (B₀).sphereCapCarrier.model.boundary (B₀).sphereCapCarrier.Carrier at hb
        rw [(B₀).sphereCapRetained_exhausted] at hb
        obtain ⟨r, t, he⟩ := mem_iUnion.mp hb
        have hr := (E.fibrePlugCapComponents_torus_mem_iff h hlin hc hn d hs heq
          hρ hρ1 hI havρ r i t).mp (he ▸ x.property)
        subst r
        exact mem_iUnion.mpr ⟨0, t, Subtype.ext
          ((E.plugSideRetained_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
            (zero_mem_halfCollarSource t)).trans he)⟩
      · intro hx
        obtain ⟨r, t, rfl⟩ := mem_iUnion.mp hx
        exact (E.plugSideRetained h hlin d hs hI heq hc hn hρ hρ1 havρ i).boundary_zero r t
    core_positive x hx := by
      have hx' := (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val
        (I := (boundedPlugCutCarrier d hs).model) (u := (D₀).piece i)).mp hx
      obtain ⟨hb, ho⟩ := (B₀).sphereCapRelativeCapping.core_positive x.val hx'
      have he := E.plugSideCore_mfderiv h hlin d hs hI heq hc hn hρ hρ1 havρ i x
      change Bijective (mfderiv (boundedPlugCutCarrier d hs).model (𝓡∂ 3)
        (B₀).sphereCapCore x.val) at hb
      have hb' := (congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) =>
        Bijective L) he).mpr hb
      refine ⟨hb', ?_⟩
      have hL : LinearEquiv.ofBijective
          (mfderiv (Cᵢ i).model (Sᵢ i).model
            (E.plugSideCore h hlin d hs hI heq hc hn hρ hρ1 havρ i) x).toLinearMap hb' =
          LinearEquiv.ofBijective
            (mfderiv (boundedPlugCutCarrier d hs).model (𝓡∂ 3)
              (B₀).sphereCapCore x.val).toLinearMap hb := by
        apply LinearEquiv.ext
        intro v
        exact congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L v) he
      exact (congrArg (fun L => Orientation.map (Fin 3) L
        ((boundedPlugCutCarrier d hs).orientation.orientation x.val)) hL).trans ho
    cap_positive r x hx := by
      obtain ⟨hi, hj, ho⟩ := (B₀).sphereCapRelativeCapping.cap_positive i x hx
      have he := E.plugSideCap_mfderiv h hlin d hs hI heq hc hn hρ hρ1 havρ i x
      change Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3)
        ((B₀).sphereCapReparameterizedCap i) x) at hj
      have hj' := (congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) =>
        Bijective L) he).mpr hj
      refine ⟨hi, hj', ?_⟩
      have hL : LinearEquiv.ofBijective
          (mfderiv (𝓡∂ 3) (Sᵢ i).model
            (E.plugSideCap h hlin d hs hI heq hc hn hρ hρ1 havρ i) x).toLinearMap hj' =
          LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) (𝓡∂ 3) ((B₀).sphereCapReparameterizedCap i) x).toLinearMap hj := by
        apply LinearEquiv.ext
        intro v
        exact congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L v) he
      exact (congrArg (fun L => Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x).toLinearMap hi).symm.trans L)
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation)) hL).trans ho
  }

theorem plugSideBoundary_torusCount (i : Fin 2) :
    (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).torusCount = 1 := rfl

theorem plugSideBoundary_sphereCount (i : Fin 2) :
    (E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).sphereCount = 1 := rfl

theorem plugSideBoundary_torus_source (i : Fin 2) :
    ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).tori.collar 0).source =
      halfCollarSource :=
  (E.plugSideTori h hlin d hs hI heq hc hn hρ hρ1 havρ i).source_eq 0

theorem plugSideBoundary_sphere_source (i : Fin 2) :
    ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).sphere 0).source =
      sphereHalfCollarSource :=
  E.plugSideSphere_source h hlin d hs hI heq hc hn hρ hρ1 havρ i

theorem plugSideBoundary_torus_apply (i : Fin 2) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).tori.collar 0 p).val =
      (B₀).tori.collar (port i) p :=
  E.plugSideTori_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i hp

theorem plugSideBoundary_sphere_apply (i : Fin 2)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereHalfCollarSource) :
    ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).sphere 0 p).val =
      (B₀).sphere i p :=
  E.plugSideSphere_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i hp

theorem plugSideBoundary_torus_zero (i : Fin 2) (t : Torus) :
    ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).tori.torusMap 0 t).val =
      (B₀).tori.torusMap (port i) t :=
  E.plugSideBoundary_torus_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
    (t, halfZero) (zero_mem_halfCollarSource t)

theorem plugSideBoundary_sphere_zero (i : Fin 2) (z : ClosureSphere.{u}) :
    ((E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i).sphereMap 0 z).val =
      (B₀).sphereMap i z :=
  E.plugSideBoundary_sphere_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
    (z, halfZero) (plugSide_zero_source z)

theorem plugSideCapping_core (i : Fin 2) (x : (Cᵢ i).Carrier) :
    ((E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).core x).val =
      (B₀).sphereCapCore x.val := rfl

theorem plugSideCapping_cap (i : Fin 2) (x : ClosedCell 3) :
    ((E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).cap 0 x).val =
      (B₀).sphereCapReparameterizedCap i x := rfl

theorem plugSideCapping_attaching (i : Fin 2) :
    (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).attaching 0 =
      (B₀).sphereCapOrientationData.attaching i := rfl

theorem plugSideCapping_retained_apply (i : Fin 2) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    ((E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).retained.collar 0 p).val =
      (B₀).sphereCapRetained.collar (port i) p :=
  E.plugSideRetained_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i hp

theorem plugSideCapping_retained_zero (i : Fin 2) (t : Torus) :
    ((E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).retained.torusMap 0 t).val =
      (B₀).sphereCapRetained.torusMap (port i) t :=
  E.plugSideCapping_retained_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i
    (t, halfZero) (zero_mem_halfCollarSource t)

def plugSidePunctureHomeomorph (i : Fin 2) :
    (Cᵢ i).Carrier ≃ₜ
      ↥(E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).capInteriorImageᶜ :=
  (E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i).corePunctureHomeomorph

theorem plugSidePunctureHomeomorph_apply (i : Fin 2) (x : (Cᵢ i).Carrier) :
    (E.plugSidePunctureHomeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ i x).val.val =
      (B₀).sphereCapCore x.val := rfl

end GC.Seifert.ElementaryPresentation
