import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Section
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.GraphCylinder
import DifferentialGeometry.Topology.Ends.CylindricalExtension
import Mathlib.Topology.MetricSpace.Isometry
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.ThinRegionCover
import Mathlib.SetTheory.Cardinal.Finite
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.GraphRegion
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.AxialGraphChart
import DifferentialGeometry.Topology.Connected.GraphExterior
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

noncomputable section

open Set

private theorem exists_graph_band_subset_source
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    (A : OpenPartialHomeomorph (X × ℝ) Y) (f : C(X, ℝ))
    (hsource : ∀ x, (x, f x) ∈ A.source) :
    ∃ a : ℝ, 0 < a ∧ ∀ p : X × ℝ, |p.2 - f p.1| < a → p ∈ A.source := by
  let F : X × ℝ → X × ℝ := fun z => (z.1, f z.1 + z.2)
  have hopen : IsOpen (F ⁻¹' A.source) :=
    A.open_source.preimage (continuous_fst.prodMk ((f.continuous.comp continuous_fst).add continuous_snd))
  have hzero : (univ : Set X) ×ˢ ({0} : Set ℝ) ⊆ F ⁻¹' A.source := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    simpa only [F, mem_preimage, ht0, add_zero] using hsource x
  obtain ⟨U, V, _, hV, hU, h0, hUV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hopen hzero
  obtain ⟨a, ha, hVa⟩ := Metric.isOpen_iff.mp hV 0 (h0 (mem_singleton 0))
  refine ⟨a, ha, fun p hp => ?_⟩
  have ht : p.2 - f p.1 ∈ V := hVa (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hp)
  have hm := hUV (a := (p.1, p.2 - f p.1)) ⟨hU (mem_univ p.1), ht⟩
  change (p.1, f p.1 + (p.2 - f p.1)) ∈ A.source at hm
  simpa only [add_sub_cancel] using hm

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (by decide) Δ

private theorem pair_stabilizer_preserves (Λ : Subgroup (PO 3 1))
    (a b : BoundaryH 3) (γ : CuspCrossSections.endStabilizer (by decide) Λ {a, b}) :
    (poBoundaryMulAction (by decide)).smul (γ : PO 3 1) a ∈ ({a, b} : Set (BoundaryH 3)) ∧
    (poBoundaryMulAction (by decide)).smul (γ : PO 3 1) b ∈ ({a, b} : Set (BoundaryH 3)) := by
  have he := (ElementaryEnds.mem_setStabilizer (by decide) {a, b} γ).mp γ.property.2
  exact ⟨he.subset (mem_image_of_mem _ (by simp)),
    he.subset (mem_image_of_mem _ (by simp))⟩

variable {Γ Λ : Subgroup (PO 3 1)} [DiscreteTopology Γ] [DiscreteTopology Λ]
  {r s : ℝ} (D : FiniteCuspTruncation (by decide) Γ r)
  (E : FiniteCuspTruncation (by decide) Λ s)

local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "hΛ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Λ))
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper 3)
local notation "QΛ" => MulAction.orbitRel.Quotient Λ (HUpper 3)
local notation "πΛ" => Quotient.mk (MulAction.orbitRel Λ (HUpper 3))
local notation "CΓ" => fun ξ : D.centers =>
  (Quotient.mk (MulAction.orbitRel (CuspCrossSections.endStabilizer (by decide) Γ (Set.singleton (Subtype.val ξ))) (HUpper 3))) ''
    Busemann.horosphere (Subtype.val ξ) (D.level ξ)
local notation "CΛ" => fun η : E.centers =>
  (Quotient.mk (MulAction.orbitRel (CuspCrossSections.endStabilizer (by decide) Λ (Set.singleton (Subtype.val η))) (HUpper 3))) ''
    Busemann.horosphere (Subtype.val η) (E.level η)
local notation "Pairs" => {p : BoundaryH 3 × BoundaryH 3 // Prod.fst p ≠ Prod.snd p}
local notation "AP" => fun p : Pairs => CuspCrossSections.endStabilizer (by decide) Λ (Set.insert (Prod.fst (Subtype.val p)) (Set.singleton (Prod.snd (Subtype.val p))))
local notation "AS" => fun p : Pairs =>
  {z : MulAction.orbitRel.Quotient (AP p) (HUpper 3) //
    AxisGeometry.quotientAxisDistance 2 (AP p) (Prod.fst (Subtype.val p)) (Prod.snd (Subtype.val p)) (Subtype.property p)
      (pair_stabilizer_preserves Λ (Prod.fst (Subtype.val p)) (Prod.snd (Subtype.val p))) z = Real.arsinh 1}

variable [IsCancelSMul Λ (HUpper 3)]

private local instance (S : Set (BoundaryH 3)) :
    IsCancelSMul (CuspCrossSections.endStabilizer (Nat.succ_le_succ (Nat.zero_le 2)) Λ S) (HUpper 3) :=
  EquivariantMap.isCancelSMul_subAction (Nat.succ_le_succ (Nat.zero_le 2)) (show CuspCrossSections.endStabilizer (by decide) Λ S ≤ Λ from inf_le_left)

private abbrev TargetSection (c : E.centers ⊕ Pairs) : Type :=
  Sum.elim (fun η => (CΛ η : Type)) (fun p => AS p) c

local notation "T" => TargetSection E

private local instance (c : E.centers ⊕ Pairs) : TopologicalSpace (T c) := by
  cases c with
  | inl η => exact inferInstanceAs (TopologicalSpace (CΛ η))
  | inr p => exact inferInstanceAs (TopologicalSpace (AS p))

private def targetChart (c : E.centers ⊕ Pairs) : OpenPartialHomeomorph ((T c) × ℝ) QΛ := by
  cases c with
  | inl η => exact E.horosphereGraphChart hΛ η
  | inr p => exact OrbifoldThinRegions.axialGraphChart 2 Λ p.val.1 p.val.2 p.property (by decide) s

local notation "A" => targetChart E

private def targetInward (c : E.centers ⊕ Pairs) : ((T c) → ℝ) → Set QΛ := by
  cases c with
  | inl η => exact E.openGraphRegion hΛ η
  | inr p =>
    let _ : IsCancelSMul (AP p) (HUpper 3) :=
      EquivariantMap.isCancelSMul_subAction (Nat.succ_le_succ (Nat.zero_le 2)) inf_le_left
    exact OrbifoldThinRegions.axialGraphAmbientInward 2 Λ p.val.1 p.val.2 p.property

local notation "U" => targetInward E

local notation "L" => fun c : E.centers ⊕ Pairs =>
  Sum.rec (fun η => Set.singleton (Subtype.val η))
    (fun p => Set.insert (Prod.fst (Subtype.val p)) (Set.singleton (Prod.snd (Subtype.val p)))) c

include E in
private theorem graph_region_properties
    (hs : 0 < s)
    (hgeom : ∀ p : HUpper 3, BoundaryStabilizer.ElementaryGeometry (by decide)
      (OrbifoldStrata.closedSmallSubgroup (by decide) Λ s p))
    (c : E.centers ⊕ Pairs) [CompactSpace (T c)]
    (f : C(T c, ℝ)) (hgraph : ∀ q, (q, f q) ∈ (A c).source) :
    IsOpen (U c f) ∧ frontier (U c f) = range (fun q => A c (q, f q)) ∧
      (∀ p ∈ (A c).source, A c p ∈ U c f ↔ p.2 < f p.1) ∧
      closure (U c f) ⊆ πΛ '' OrbifoldThinRegions.thinRegion (by decide) Λ s (L c) := by
  cases c with
  | inl η =>
    change IsOpen (E.openGraphRegion hΛ η f) ∧ _
    refine ⟨E.isOpen_openGraphRegion hΛ η f f.continuous,
      E.frontier_openGraphRegion hΛ η hs hgeom f f.continuous hgraph,
      fun p hp => E.mem_openGraphRegion_iff hΛ η hs hgeom f hgraph p hp, ?_⟩
    change closure (E.openGraphRegion hΛ η f) ⊆ _
    rw [E.closure_openGraphRegion hΛ η hs hgeom f f.continuous hgraph,
      E.closedGraphRegion_eq_image hΛ η f]
    rintro y ⟨p, hp, rfl⟩
    have hin := E.graph_sublevel_subset_interior_thinRegion hΛ η hs hgeom f hgraph
      (a := Quotient.mk (MulAction.orbitRel (CuspCrossSections.endStabilizer (by decide) Λ {η.val}) (HUpper 3)) p) hp
    obtain ⟨z, hz, hzp⟩ := hin
    refine ⟨z, interior_subset hz, ?_⟩
    exact congrArg (EquivariantMap.quotientInclusion (by decide)
      (show CuspCrossSections.endStabilizer (by decide) Λ {η.val} ≤ Λ from inf_le_left)) hzp
  | inr p =>
    let _ : IsCancelSMul (AP p) (HUpper 3) :=
      EquivariantMap.isCancelSMul_subAction (Nat.succ_le_succ (Nat.zero_le 2)) inf_le_left
    let _ : CompactSpace (AS p) := inferInstanceAs (CompactSpace (T (Sum.inr p)))
    have hpre := OrbifoldThinRegions.graph_preimage_subset_thinRegion_of_mem_quotient_interior
      2 Λ p.val.1 p.val.2 p.property s f hgraph
    refine ⟨OrbifoldThinRegions.isOpen_axialGraphAmbientInward 2 Λ p.val.1 p.val.2 p.property
        f f.continuous, ?_, ?_, ?_⟩
    · change frontier (OrbifoldThinRegions.axialGraphAmbientInward 2 Λ p.val.1 p.val.2 p.property f) = _
      rw [OrbifoldThinRegions.frontier_axialGraphAmbientInward 2 Λ p.val.1 p.val.2 p.property
        (by decide) s hgeom f f.continuous hpre,
        OrbifoldThinRegions.axialGraphAmbient_eq_range 2 Λ p.val.1 p.val.2 p.property f]
      rfl
    · intro z hz
      exact OrbifoldThinRegions.axialGraphAmbientPoint_mem_inward_iff
        2 Λ p.val.1 p.val.2 p.property (by decide) s hgeom f f.continuous hpre
        z.1 z.2 (Set.image_mono interior_subset hz)
    · change closure (OrbifoldThinRegions.axialGraphAmbientInward 2 Λ p.val.1 p.val.2 p.property f) ⊆ _
      rw [OrbifoldThinRegions.closure_axialGraphAmbientInward 2 Λ p.val.1 p.val.2 p.property
        (by decide) s hgeom f f.continuous hpre]
      exact OrbifoldThinRegions.axialGraphAmbientClosed_subset_quotient_thinRegion
        2 Λ p.val.1 p.val.2 p.property (by decide) s hgeom f f.continuous hpre

theorem image_cylindricalCore_eq_compl_iUnion_of_boundary_graphs
    (hs : 0 < s)
    (hgeom : ∀ p : HUpper 3, BoundaryStabilizer.ElementaryGeometry (by decide)
      (OrbifoldStrata.closedSmallSubgroup (by decide) Λ s p))
    (χ : OpenPartialHomeomorph QΓ QΛ) (d : D.centers → ℝ) (hd : ∀ ξ, 0 < d ξ)
    (hsource : Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d ⊆ χ.source)
    (x₀ : QΓ) (hx₀ : x₀ ∈ interior (Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d))
    (hthick : ∀ S : Set (BoundaryH 3),
      χ x₀ ∉ πΛ '' OrbifoldThinRegions.thinRegion (by decide) Λ s S)
    (choice : D.centers → E.centers ⊕ Pairs)
    (f : ∀ ξ, C(T (choice ξ), ℝ)) (θ : ∀ ξ, (CΓ ξ) ≃ₜ T (choice ξ))
    (hgraph : ∀ ξ q, (q, f ξ q) ∈ (A (choice ξ)).source)
    (hmatch : ∀ ξ c,
      χ (D.horoballCylinderMap hΓ ξ (c, ⟨d ξ, (hd ξ).le⟩)) =
        A (choice ξ) (θ ξ c, f ξ (θ ξ c))) :
    χ '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d =
      (⋃ ξ, U (choice ξ) (f ξ))ᶜ := by
  let _ : Finite D.centers := D.finite_centers
  let _ : ContinuousConstSMul Λ (HUpper 3) :=
    ⟨fun γ => (HyperbolicAction.contMDiff_po_smul 2 ⊤ (γ : PO 3 1)).continuous⟩
  let _ : ProperlyDiscontinuousSMul Λ (HUpper 3) :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (by decide) Λ hΛ
  let _ : PathConnectedSpace (HUpper 3) := HyperbolicGeodesic.pathConnectedSpace (by decide)
  let _ : ∀ ξ : D.centers, CompactSpace (CΓ ξ) := fun ξ =>
    isCompact_iff_compactSpace.mp (D.isCompact_quotient_horosphere_of_compact_core hΓ ξ)
  let _ : ∀ ξ : D.centers, ConnectedSpace (CΓ ξ) := fun ξ =>
    isConnected_iff_connectedSpace.mp (D.isConnected_quotient_horosphere ξ)
  let _ : ∀ ξ : D.centers, CompactSpace (T (choice ξ)) := fun ξ => (θ ξ).compactSpace
  let _ : ∀ ξ : D.centers, ConnectedSpace (T (choice ξ)) := fun ξ =>
    (θ ξ).surjective.connectedSpace (θ ξ).continuous
  let K := Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d
  let W := χ '' K
  have hKclosed : IsClosed K := Topology.isClosed_cylindricalCore
    (fun ξ => D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
    (D.isOpen_image_horoballCylinderMap_pos hΓ) d (fun ξ => (hd ξ).le)
  have hKcompact : IsCompact K := by
    apply Topology.isCompact_cylindricalCore
      (fun ξ => D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
      (D.isOpen_image_horoballCylinderMap_pos hΓ) _ d (fun ξ => (hd ξ).le)
    rw [D.cylindricalCore_zero hΓ]
    exact D.isCompact_quotient
  have hWcompact : IsCompact W := hKcompact.image_of_continuousOn (χ.continuousOn.mono hsource)
  have hWregular : closure (interior W) = W :=
    χ.closure_interior_image_of_subset_source hsource
      (D.closure_interior_cylindricalCore hΓ d hd) hWcompact.isClosed
  have hWinterior : IsConnected (interior W) := by
    rw [show interior W = χ '' interior K from (χ.image_interior_of_subset_source hsource).symm]
    exact (D.isConnected_interior_cylindricalCore hΓ d hd).image χ
      (χ.continuousOn.mono (interior_subset.trans hsource))
  let G (ξ : D.centers) : Set QΛ := range (fun q => A (choice ξ) (q, f ξ q))
  have hslice (ξ : D.centers) :
      χ '' (D.horoballCylinderMap hΓ ξ '' {p | p.2.val = d ξ}) = G ξ := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨c, t⟩, ht, rfl⟩, rfl⟩
      have ht' : t = ⟨d ξ, (hd ξ).le⟩ := Subtype.ext ht
      rw [ht', hmatch]
      exact mem_range_self (θ ξ c)
    · rintro ⟨q, rfl⟩
      refine ⟨D.horoballCylinderMap hΓ ξ ((θ ξ).symm q, ⟨d ξ, (hd ξ).le⟩),
        ⟨((θ ξ).symm q, ⟨d ξ, (hd ξ).le⟩), rfl, rfl⟩, ?_⟩
      rw [hmatch, (θ ξ).apply_symm_apply]
  have hfrontW : frontier W = ⋃ ξ, G ξ := by
    rw [show frontier W = χ '' frontier K from
      (χ.image_frontier_of_subset_source hsource hKclosed hWcompact.isClosed).symm,
      D.frontier_cylindricalCore hΓ d (fun ξ => (hd ξ).le), image_iUnion]
    exact iUnion_congr hslice
  have hgraphs_disjoint : Pairwise fun ξ η => Disjoint (G ξ) (G η) := by
    intro ξ η hξη
    rw [← hslice ξ, ← hslice η]
    apply disjoint_left.mpr
    rintro y ⟨x, ⟨p, hp, hpx⟩, hxy⟩ ⟨z, ⟨q, hq, hqz⟩, hzy⟩
    have hpK : D.horoballCylinderMap hΓ ξ p ∈ K :=
      (Topology.mem_cylindricalCore_image_iff (fun ξ => D.horoballCylinderMap hΓ ξ)
        (fun ξ => (D.horoballCylinderMap_isClosedEmbedding hΓ ξ).injective)
        (D.pairwise_disjoint_range_horoballCylinderMap hΓ) d ξ p).mpr hp.le
    have hqK : D.horoballCylinderMap hΓ η q ∈ K :=
      (Topology.mem_cylindricalCore_image_iff (fun ξ => D.horoballCylinderMap hΓ ξ)
        (fun ξ => (D.horoballCylinderMap_isClosedEmbedding hΓ ξ).injective)
        (D.pairwise_disjoint_range_horoballCylinderMap hΓ) d η q).mpr hq.le
    have hxK : x ∈ K := hpx ▸ hpK
    have hzK : z ∈ K := hqz ▸ hqK
    have hxz : x = z := χ.injOn (hsource hxK) (hsource hzK) (hxy.trans hzy.symm)
    exact disjoint_left.mp (D.pairwise_disjoint_range_horoballCylinderMap hΓ hξη)
      ⟨p, hpx⟩ ⟨q, hqz.trans hxz.symm⟩
  have hprops (ξ : D.centers) := graph_region_properties E hs hgeom (choice ξ) (f ξ) (hgraph ξ)
  choose a ha hband using fun ξ => exists_graph_band_subset_source (A (choice ξ)) (f ξ) (hgraph ξ)
  have hχx : χ x₀ ∈ interior W := by
    rw [show interior W = χ '' interior K from (χ.image_interior_of_subset_source hsource).symm]
    exact mem_image_of_mem χ hx₀
  exact Topology.eq_compl_iUnion_of_frontier_graphs
    (fun ξ => A (choice ξ)) (fun ξ => (f ξ : T (choice ξ) → ℝ)) (fun ξ => (f ξ).continuous)
    (fun ξ => U (choice ξ) (f ξ)) (fun ξ => (hprops ξ).1) a ha hband
    (fun ξ p hp => (hprops ξ).2.2.1 p (hband ξ p hp))
    (fun ξ => (hprops ξ).2.1) hgraphs_disjoint hWregular hWinterior.isPreconnected hfrontW
    (χ x₀) hχx (fun ξ hx => hthick (L (choice ξ)) ((hprops ξ).2.2.2 hx))

theorem exists_equiv_centers_of_boundary_graphs_of_card_le
    (hs : 0 < s)
    (hgeom : ∀ p : HUpper 3, BoundaryStabilizer.ElementaryGeometry (by decide)
      (OrbifoldStrata.closedSmallSubgroup (by decide) Λ s p))
    (χ : OpenPartialHomeomorph QΓ QΛ) (d : D.centers → ℝ) (hd : ∀ ξ, 0 < d ξ)
    (hsource : Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d ⊆ χ.source)
    (x₀ : QΓ) (hx₀ : x₀ ∈ interior (Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d))
    (hthick : ∀ S : Set (BoundaryH 3),
      χ x₀ ∉ πΛ '' OrbifoldThinRegions.thinRegion (by decide) Λ s S)
    (choice : D.centers → E.centers ⊕ Pairs)
    (f : ∀ ξ, C(T (choice ξ), ℝ)) (θ : ∀ ξ, (CΓ ξ) ≃ₜ T (choice ξ))
    (hgraph : ∀ ξ q, (q, f ξ q) ∈ (A (choice ξ)).source)
    (hmatch : ∀ ξ c,
      χ (D.horoballCylinderMap hΓ ξ (c, ⟨d ξ, (hd ξ).le⟩)) =
        A (choice ξ) (θ ξ c, f ξ (θ ξ c)))
    (hcount : Nat.card D.centers ≤ Nat.card E.centers) :
    ∃ σ : D.centers ≃ E.centers, ∀ ξ, choice ξ = Sum.inl (σ ξ) := by
  classical
  let _ : Finite D.centers := D.finite_centers
  let _ : Finite E.centers := E.finite_centers
  let _ : ∀ ξ : D.centers, CompactSpace (CΓ ξ) := fun ξ =>
    isCompact_iff_compactSpace.mp (D.isCompact_quotient_horosphere_of_compact_core hΓ ξ)
  let _ : ∀ ξ : D.centers, CompactSpace (T (choice ξ)) := fun ξ => (θ ξ).compactSpace
  have hKcompact : IsCompact (Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d) := by
    apply Topology.isCompact_cylindricalCore
      (fun ξ => D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
      (D.isOpen_image_horoballCylinderMap_pos hΓ) _ d (fun ξ => (hd ξ).le)
    rw [D.cylindricalCore_zero hΓ]
    exact D.isCompact_quotient
  have heq := D.image_cylindricalCore_eq_compl_iUnion_of_boundary_graphs E hs hgeom χ d hd
    hsource x₀ hx₀ hthick choice f θ hgraph hmatch
  have hcompact : IsCompact (⋃ ξ, U (choice ξ) (f ξ))ᶜ :=
    heq ▸ hKcompact.image_of_continuousOn (χ.continuousOn.mono hsource)
  have hU (ξ : D.centers) : U (choice ξ) (f ξ) ⊆
      πΛ '' OrbifoldThinRegions.thinRegion (by decide) Λ s (L (choice ξ)) :=
    subset_closure.trans (graph_region_properties E hs hgeom (choice ξ) (f ξ) (hgraph ξ)).2.2.2
  have hcover (η : E.centers) : ∃ ξ : D.centers, choice ξ = Sum.inl η := by
    obtain ⟨ξ, γ, hγ⟩ := E.exists_label_of_isCompact_compl_iUnion_thin_regions hΛ
      (fun ξ => L (choice ξ)) (fun ξ => U (choice ξ) (f ξ)) hU hcompact η
    cases hchoice : choice ξ with
    | inl ζ =>
      have horbit : (poBoundaryMulAction (by decide)).smul (γ : PO 3 1) η.val = ζ.val := by
        rw [hchoice] at hγ
        exact hγ.subset (mem_image_of_mem _ (mem_singleton η.val))
      have hηζ : η = ζ := E.distinct_orbits η ζ γ horbit
      exact ⟨ξ, hchoice.trans (congrArg Sum.inl hηζ.symm)⟩
    | inr p =>
      rw [hchoice] at hγ
      simp only [image_singleton] at hγ
      have ha : p.val.1 = (poBoundaryMulAction (by decide)).smul (γ : PO 3 1) η.val :=
        hγ.symm.subset (Or.inl rfl)
      have hb : p.val.2 = (poBoundaryMulAction (by decide)).smul (γ : PO 3 1) η.val :=
        hγ.symm.subset (Or.inr rfl)
      exact False.elim (p.property (ha.trans hb.symm))
  choose select hselect using hcover
  have hinj : Function.Injective select := by
    intro η ζ hηζ
    apply Sum.inl_injective
    exact (hselect η).symm.trans ((congrArg choice hηζ).trans (hselect ζ))
  let e : E.centers ≃ D.centers := Equiv.ofBijective select (hinj.bijective_of_nat_card_le hcount)
  refine ⟨e.symm, fun ξ => ?_⟩
  have h := hselect (e.symm ξ)
  change choice (e (e.symm ξ)) = Sum.inl (e.symm ξ) at h
  simpa only [e.apply_symm_apply] using h

theorem exists_homeomorph_of_boundary_graphs_of_card_le
    (hs : 0 < s)
    (hgeom : ∀ p : HUpper 3, BoundaryStabilizer.ElementaryGeometry (by decide)
      (OrbifoldStrata.closedSmallSubgroup (by decide) Λ s p))
    (χ : OpenPartialHomeomorph QΓ QΛ) (d : D.centers → ℝ) (hd : ∀ ξ, 0 < d ξ)
    (hsource : Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d ⊆ χ.source)
    (x₀ : QΓ) (hx₀ : x₀ ∈ interior (Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d))
    (hthick : ∀ S : Set (BoundaryH 3),
      χ x₀ ∉ πΛ '' OrbifoldThinRegions.thinRegion (by decide) Λ s S)
    (choice : D.centers → E.centers ⊕ Pairs)
    (f : ∀ ξ, C(T (choice ξ), ℝ)) (θ : ∀ ξ, (CΓ ξ) ≃ₜ T (choice ξ))
    (hgraph : ∀ ξ q, (q, f ξ q) ∈ (A (choice ξ)).source)
    (hmatch : ∀ ξ c,
      χ (D.horoballCylinderMap hΓ ξ (c, ⟨d ξ, (hd ξ).le⟩)) =
        A (choice ξ) (θ ξ c, f ξ (θ ξ c)))
    (hcount : Nat.card D.centers ≤ Nat.card E.centers) :
    ∃ F : QΓ ≃ₜ QΛ,
      (∀ x ∈ Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d, F x = χ x) ∧
      (∀ (ξ : D.centers) (c : CΓ ξ) (t : Set.Ici (0 : ℝ)),
        F (D.horoballCylinderMap hΓ ξ (c, ⟨d ξ + t.val, add_nonneg (hd ξ).le t.property⟩)) =
          A (choice ξ) (θ ξ c, f ξ (θ ξ c) - t.val)) ∧
      (∀ y ∈ χ '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d,
        F.symm y = χ.symm y) ∧
      ∀ (ξ : D.centers) (q : T (choice ξ)) (t : Set.Ici (0 : ℝ)),
        F.symm (A (choice ξ) (q, f ξ q - t.val)) =
          D.horoballCylinderMap hΓ ξ ((θ ξ).symm q,
            ⟨d ξ + t.val, add_nonneg (hd ξ).le t.property⟩) := by
  classical
  obtain ⟨σ, hσ⟩ := D.exists_equiv_centers_of_boundary_graphs_of_card_le E hs hgeom χ d hd
    hsource x₀ hx₀ hthick choice f θ hgraph hmatch hcount
  have hchoice : choice = fun ξ => Sum.inl (σ ξ) := funext hσ
  subst choice
  let _ : Finite D.centers := D.finite_centers
  let _ : ∀ ξ : D.centers, CompactSpace (CΓ ξ) := fun ξ =>
    isCompact_iff_compactSpace.mp (D.isCompact_quotient_horosphere_of_compact_core hΓ ξ)
  let _ : ContinuousConstSMul Λ (HUpper 3) :=
    ⟨fun γ => (HyperbolicAction.contMDiff_po_smul 2 ⊤ (γ : PO 3 1)).continuous⟩
  let _ : ProperlyDiscontinuousSMul Λ (HUpper 3) :=
    OrbifoldCompactness.properlyDiscontinuous_subAction (by decide) Λ hΛ
  let K := Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) d
  let W := χ '' K
  let e (ξ : D.centers) (p : (CΓ ξ) × Ici (0 : ℝ)) : QΓ :=
    D.horoballCylinderMap hΓ ξ (p.1, ⟨d ξ + p.2.val, add_nonneg (hd ξ).le p.2.property⟩)
  let g (ξ : D.centers) := E.horosphereGraphCylinderMap hΛ (σ ξ) (f ξ) (f ξ).continuous
  have he (ξ : D.centers) : _root_.Topology.IsClosedEmbedding (e ξ) := by
    let _ : CompleteSpace (Ici (0 : ℝ)) := isClosed_Ici.isComplete.completeSpace_coe
    let shift (t : Ici (0 : ℝ)) : Ici (0 : ℝ) :=
      ⟨d ξ + t.val, add_nonneg (hd ξ).le t.property⟩
    have hshift : Isometry shift := Isometry.of_dist_eq fun t u => by
      change dist (d ξ + t.val) (d ξ + u.val) = dist t.val u.val
      exact dist_add_left _ _ _
    exact (D.horoballCylinderMap_isClosedEmbedding hΓ ξ).comp
      (_root_.Topology.IsClosedEmbedding.id.prodMap hshift.isClosedEmbedding)
  have hg (ξ : D.centers) : _root_.Topology.IsClosedEmbedding (g ξ) :=
    E.horosphereGraphCylinderMap_isClosedEmbedding hΛ (σ ξ) hs hgeom
      (f ξ) (f ξ).continuous (hgraph ξ)
  have hzeroX (ξ : D.centers) (p : (CΓ ξ) × Ici (0 : ℝ)) : e ξ p ∈ K ↔ p.2.val = 0 := by
    change D.horoballCylinderMap hΓ ξ (_, _) ∈ K ↔ _
    rw [Topology.mem_cylindricalCore_image_iff (fun ξ => D.horoballCylinderMap hΓ ξ)
      (fun ξ => (D.horoballCylinderMap_isClosedEmbedding hΓ ξ).injective)
      (D.pairwise_disjoint_range_horoballCylinderMap hΓ)]
    change d ξ + p.2.val ≤ d ξ ↔ p.2.val = 0
    have hp0 : 0 ≤ p.2.val := p.2.property
    constructor <;> intro h <;> linarith [hp0]
  have hedis : Pairwise fun ξ η => Disjoint (range (e ξ)) (range (e η)) := by
    intro ξ η hne
    exact (D.pairwise_disjoint_range_horoballCylinderMap hΓ hne).mono
      (by rintro y ⟨p, rfl⟩; exact ⟨_, rfl⟩)
      (by rintro y ⟨p, rfl⟩; exact ⟨_, rfl⟩)
  let _ : ∀ ξ : D.centers, CompactSpace (T (Sum.inl (σ ξ))) := fun ξ => (θ ξ).compactSpace
  have hprops (ξ : D.centers) := graph_region_properties E hs hgeom (Sum.inl (σ ξ)) (f ξ) (hgraph ξ)
  have hW : W = (⋃ ξ, E.openGraphRegion hΛ (σ ξ) (f ξ))ᶜ :=
    D.image_cylindricalCore_eq_compl_iUnion_of_boundary_graphs E hs hgeom χ d hd hsource
      x₀ hx₀ hthick (fun ξ => Sum.inl (σ ξ)) f θ hgraph hmatch
  have hgthin (ξ : D.centers) : range (g ξ) ⊆
      πΛ '' OrbifoldThinRegions.thinRegion (by decide) Λ s {((σ ξ).val)} := by
    rw [show range (g ξ) = closure (E.openGraphRegion hΛ (σ ξ) (f ξ)) from
      E.range_horosphereGraphCylinderMap_eq_closure hΛ (σ ξ) hs hgeom (f ξ) (f ξ).continuous (hgraph ξ)]
    exact (hprops ξ).2.2.2
  have hgdis : Pairwise fun ξ η => Disjoint (range (g ξ)) (range (g η)) := by
    intro ξ η hne
    apply disjoint_left.mpr
    intro y hyξ hyη
    obtain ⟨γ, hγ⟩ := OrbifoldThinRegions.label_orbit_of_mem_quotient_thinRegion
      (by decide) Λ hΛ s (hgthin ξ hyξ) (hgthin η hyη)
    have horbit : (poBoundaryMulAction (by decide)).smul (γ : PO 3 1) (σ ξ).val = (σ η).val :=
      hγ.subset (mem_image_of_mem _ (mem_singleton (σ ξ).val))
    exact hne (σ.injective (E.distinct_orbits (σ ξ) (σ η) γ horbit))
  have hKclosed : IsClosed K := Topology.isClosed_cylindricalCore
    (fun ξ => D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
    (D.isOpen_image_horoballCylinderMap_pos hΓ) d (fun ξ => (hd ξ).le)
  have hKcompact : IsCompact K := by
    apply Topology.isCompact_cylindricalCore
      (fun ξ => D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
      (D.isOpen_image_horoballCylinderMap_pos hΓ) _ d (fun ξ => (hd ξ).le)
    rw [D.cylindricalCore_zero hΓ]
    exact D.isCompact_quotient
  have hWclosed : IsClosed W := (hKcompact.image_of_continuousOn (χ.continuousOn.mono hsource)).isClosed
  have hcoverX : K ∪ ⋃ ξ, range (e ξ) = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · exact Or.inl hx
    · obtain ⟨ξ, p, hp, rfl⟩ := mem_iUnion.mp (not_not.mp hx)
      refine Or.inr (mem_iUnion.mpr ⟨ξ, (p.1, ⟨p.2.val - d ξ, (show 0 ≤ p.2.val - d ξ from (sub_pos.mpr hp).le)⟩), ?_⟩)
      change D.horoballCylinderMap hΓ ξ (_, _) = D.horoballCylinderMap hΓ ξ p
      congr 1
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change d ξ + (p.2.val - d ξ) = p.2.val
        ring
  have hcoverY : W ∪ ⋃ ξ, range (g ξ) = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ W
    · exact Or.inl hy
    · rw [hW] at hy
      obtain ⟨ξ, hξ⟩ := mem_iUnion.mp (not_not.mp hy)
      refine Or.inr (mem_iUnion.mpr ⟨ξ, ?_⟩)
      rw [show range (g ξ) = closure (E.openGraphRegion hΛ (σ ξ) (f ξ)) from
        E.range_horosphereGraphCylinderMap_eq_closure hΛ (σ ξ) hs hgeom (f ξ) (f ξ).continuous (hgraph ξ)]
      exact subset_closure hξ
  have hzeroY (ξ : D.centers) (p : (CΛ (σ ξ)) × Ici (0 : ℝ)) : g ξ p ∈ W ↔ p.2.val = 0 := by
    constructor
    · intro hp
      apply (E.horosphereGraphCylinderMap_notMem_openGraphRegion_iff hΛ (σ ξ) hs hgeom
        (f ξ) (f ξ).continuous (hgraph ξ) p).mp
      intro hin
      exact (hW ▸ hp) (mem_iUnion.mpr ⟨ξ, hin⟩)
    · intro ht
      have ht' : p.2 = ⟨0, by simp⟩ := Subtype.ext ht
      rw [show p = (p.1, ⟨0, by simp⟩) from Prod.ext rfl ht']
      change E.horosphereGraphCylinderMap hΛ (σ ξ) (f ξ) (f ξ).continuous (p.1, ⟨0, by simp⟩) ∈ W
      rw [E.horosphereGraphCylinderMap_zero hΛ (σ ξ) (f ξ) (f ξ).continuous p.1]
      have hk : e ξ ((θ ξ).symm p.1, ⟨0, by simp⟩) ∈ K := (hzeroX ξ _).mpr rfl
      refine ⟨_, hk, ?_⟩
      change χ (D.horoballCylinderMap hΓ ξ ((θ ξ).symm p.1, _)) = _
      have h := hmatch ξ ((θ ξ).symm p.1)
      have hpoint : θ ξ ((θ ξ).symm p.1) = p.1 := (θ ξ).apply_symm_apply p.1
      rw [hpoint] at h
      convert h using 1 <;> first | rfl | simp only [add_zero]
  let κ : K ≃ₜ W := χ.homeomorphOfImageSubsetSource hsource rfl
  have hκ (x : K) : (κ x : QΛ) = χ x := rfl
  have hκsymm (y : W) : (κ.symm y : QΓ) = χ.symm y := rfl
  have hboundary (ξ : D.centers) (c : CΓ ξ) :
      (κ ⟨e ξ (c, ⟨0, by simp⟩), (hzeroX ξ _).mpr rfl⟩ : QΛ) =
        g ξ (θ ξ c, ⟨0, by simp⟩) := by
    have hszero : e ξ (c, ⟨0, by simp⟩) =
        D.horoballCylinderMap hΓ ξ (c, ⟨d ξ, (hd ξ).le⟩) := by
      simp only [e, add_zero]
    calc
      (κ ⟨e ξ (c, ⟨0, by simp⟩), (hzeroX ξ _).mpr rfl⟩ : QΛ) = χ (e ξ (c, ⟨0, by simp⟩)) := hκ _
      _ = χ (D.horoballCylinderMap hΓ ξ (c, ⟨d ξ, (hd ξ).le⟩)) := congrArg χ hszero
      _ = E.horosphereGraphChart hΛ (σ ξ) (θ ξ c, f ξ (θ ξ c)) := hmatch ξ c
      _ = g ξ (θ ξ c, ⟨0, by simp⟩) :=
        (E.horosphereGraphCylinderMap_zero hΛ (σ ξ) (f ξ) (f ξ).continuous (θ ξ c)).symm
  obtain ⟨F, hFK, hFe, hFW, hFg⟩ := Topology.exists_homeomorph_of_cylindrical_cover
    (C := fun ξ => CΓ ξ) (D := fun ξ => CΛ (σ ξ)) e (fun ξ => (g ξ : _ → QΛ)) he hg
    hedis hgdis hKclosed hWclosed hcoverX hcoverY hzeroX hzeroY κ θ hboundary
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hFK ⟨x, hx⟩).trans (hκ ⟨x, hx⟩)
  · intro ξ c t
    exact hFe ξ c t
  · intro y hy
    exact (hFW ⟨y, hy⟩).trans (hκsymm ⟨y, hy⟩)
  · intro ξ q t
    exact hFg ξ q t

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
