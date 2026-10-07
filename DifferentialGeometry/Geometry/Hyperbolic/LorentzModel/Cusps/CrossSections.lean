/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.HorosphericalGroups
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Projection
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegions

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.CuspCrossSections

open Hyperbolic HyperbolicAction HyperbolicBoundary HyperbolicFaithful
open AsymptoticRays Busemann BusemannCocycle BoundaryStabilizer
open OrbifoldStrata ElementaryEnds OrbifoldThinRegions HorosphereProjection

variable {n : ℕ}

def endStabilizer (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (S : Set (BoundaryH n)) :
    Subgroup (PO n 1) := Γ ⊓ setStabilizer hn S

theorem mem_endStabilizer_singleton (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ξ : BoundaryH n) (g : PO n 1) :
    g ∈ endStabilizer hn Γ {ξ} ↔ g ∈ Γ ∧ (poBoundaryMulAction hn).smul g ξ = ξ := by
  change g ∈ Γ ∧ g ∈ setStabilizer hn {ξ} ↔ _
  rw [mem_setStabilizer, image_singleton]
  exact and_congr_right (fun _ => singleton_injective.eq_iff)

theorem hasEnds_endStabilizer (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {r : ℝ} {S : Set (BoundaryH n)}
    (hS : (thinRegion hn Γ r S).Nonempty) :
    HasEnds hn (endStabilizer hn Γ S) S := by
  obtain ⟨x, hx⟩ := hS
  let := hx.1
  exact hx.2.of_le (hΓ.mono inf_le_left)
    (le_inf (closedSmallSubgroup_le hn Γ r x) hx.2.le_setStabilizer)
      (geometry_setStabilizer hn Γ hΓ hx.2)

theorem horospherical_endStabilizer (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {r : ℝ} {ξ : BoundaryH n}
    (hξ : (thinRegion hn Γ r {ξ}).Nonempty) :
    ∀ g : endStabilizer hn Γ {ξ},
      (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ ∧ poConfFactor hn (g : PO n 1) ξ = 1 :=
  (hasEnds_endStabilizer hn Γ hΓ hξ).horospherical

theorem thinRegion_eq_stabilizer_infiniteLocus (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    {S : Set (BoundaryH n)} (hS : (thinRegion hn Γ r S).Nonempty) :
    thinRegion hn Γ r S = (finiteLocus hn (endStabilizer hn Γ S) r)ᶜ := by
  let P := endStabilizer hn Γ S
  have hP : HasEnds hn P S := hasEnds_endStabilizer hn Γ hΓ hS
  ext x
  constructor
  · intro hx hf
    let := hx.1
    have he := closedSmallSubgroup_eq_of_le hn (show P ≤ Γ from inf_le_left) r x
      (le_inf (closedSmallSubgroup_le hn Γ r x) hx.2.le_setStabilizer)
    have hfin : Finite (closedSmallSubgroup hn Γ r x) := he ▸ hf
    exact hfin.false
  · intro hx
    let : Infinite (closedSmallSubgroup hn P r x) := not_finite_iff_infinite.mp hx
    have hle := closedSmallSubgroup_mono_group hn (show P ≤ Γ from inf_le_left) r x
    refine ⟨Infinite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _), ?_⟩
    exact (hP.mono (closedSmallSubgroup_le hn P r x)).of_le
      (hΓ.mono (closedSmallSubgroup_le hn Γ r x)) hle (hgeom x)

theorem eventually_rayTo_mem_thinRegion (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 < r)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) (p : HUpper n) :
    ∀ᶠ t : ℝ in atTop, rayTo p ξ t ∈ thinRegion hn Γ r {ξ} := by
  obtain ⟨x, hx⟩ := hξ
  let := hx.1
  have hfix := hx.2.horospherical
  have hshort : ∀ᶠ t : ℝ in atTop, ∀ g ∈ closedSmallElements hn Γ r x,
      dist ((poMulAction hn).smul g (rayTo p ξ t)) (rayTo p ξ t) < r := by
    apply (finite_closedSmallElements hn Γ hΓ r x).eventually_all.mpr
    intro g hg
    have h := hfix ⟨g, Subgroup.subset_closure hg⟩
    exact (ParabolicRegions.tendsto_displacement_rayTo hn g ξ h.1 h.2 p).eventually
      (Iio_mem_nhds hr)
  filter_upwards [hshort] with t ht
  have hle : closedSmallSubgroup hn Γ r x ≤ closedSmallSubgroup hn Γ r (rayTo p ξ t) := by
    apply Subgroup.closure_mono
    intro g hg
    exact ⟨hg.1, (ht g hg).le⟩
  exact ⟨Infinite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _),
    hx.2.of_le (hΓ.mono (closedSmallSubgroup_le hn Γ r _)) hle (hgeom _)⟩

theorem eventually_rayTo_neg_notMem_thinRegion (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 ≤ r)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) (p : HUpper n) :
    ∀ᶠ t : ℝ in atTop, rayTo p ξ (-t) ∉ thinRegion hn Γ r {ξ} := by
  have he := thinRegion_eq_stabilizer_infiniteLocus hn Γ hΓ r hgeom hξ
  have hfinite := ElementaryThickPoint.eventually_finite_horospherical hn
    (endStabilizer hn Γ {ξ}) (hΓ.mono inf_le_left) hr ξ
      (horospherical_endStabilizer hn Γ hΓ hξ) p
  filter_upwards [hfinite] with t ht
  rw [he]
  exact fun h => h ht

theorem exists_frontier_on_ray (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 < r)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (closedSmallSubgroup hn Γ r x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) (p : HUpper n) :
    ∃ t : ℝ, rayTo p ξ t ∈ frontier (thinRegion hn Γ r {ξ}) := by
  let A := (rayTo p ξ) ⁻¹' thinRegion hn Γ r {ξ}
  obtain ⟨t, ht⟩ := (eventually_rayTo_mem_thinRegion hn Γ hΓ hr hgeom hξ p).exists
  obtain ⟨s, hs⟩ := (eventually_rayTo_neg_notMem_thinRegion hn Γ hΓ hr.le hgeom hξ p).exists
  have hA : A.Nonempty := ⟨t, ht⟩
  have hproper : A ≠ univ := by
    intro he
    have hsA : -s ∈ A := he.symm ▸ mem_univ (-s)
    exact hs hsA
  obtain ⟨u, hu⟩ := nonempty_frontier_iff.mpr ⟨hA, hproper⟩
  have hc : Continuous (rayTo p ξ) :=
    (continuous_rayTo ξ).comp (continuous_const.prodMk continuous_id)
  exact ⟨u, hc.frontier_preimage_subset _ hu⟩

def interiorHomeomorph (hn : 1 ≤ n) (g : PO n 1) : HUpper n ≃ₜ HUpper n := by
  letI := poMulAction hn
  exact
    { toFun := fun x => g • x
      invFun := fun x => g⁻¹ • x
      left_inv := inv_smul_smul g
      right_inv := smul_inv_smul g
      continuous_toFun := (Isometry.of_dist_eq (po_dist_smul hn g)).continuous
      continuous_invFun := (Isometry.of_dist_eq (po_dist_smul hn g⁻¹)).continuous }

theorem smul_mem_frontier (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (r : ℝ)
    {S : Set (BoundaryH n)} {x : HUpper n}
    (hx : x ∈ frontier (thinRegion hn Γ r S)) (γ : Γ) :
    (poMulAction hn).smul (γ : PO n 1) x ∈ frontier (thinRegion hn Γ r
      ((fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S)) := by
  have he := (interiorHomeomorph hn γ).image_frontier (thinRegion hn Γ r S)
  change (fun x => (poMulAction hn).smul (γ : PO n 1) x) '' frontier (thinRegion hn Γ r S) =
    frontier ((fun x => (poMulAction hn).smul (γ : PO n 1) x) '' thinRegion hn Γ r S) at he
  rw [image_thinRegion] at he
  exact he ▸ mem_image_of_mem _ hx

theorem exists_compact_frontier_core (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (S : Set (BoundaryH n)) :
    ∃ C : Set (HUpper n), IsCompact C ∧ C ⊆ frontier (thinRegion hn Γ r S) ∧
      ∀ x ∈ frontier (thinRegion hn Γ r S), ∃ γ : Γ,
        (fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S = S ∧
        (poMulAction hn).smul (γ : PO n 1) x ∈ C := by
  classical
  let := poMulAction hn
  let := poBoundaryMulAction hn
  have hcgeom (x : HUpper n) := closedSmallSubgroup_geometry hn Γ hre x (hgeom x)
  have hc (T : Set (BoundaryH n)) := isClosed_thinRegion hn Γ hΓ r hcgeom T
  obtain ⟨K, hK, _, hcover⟩ := FiniteLocusCompactness.exists_compact_finiteLocus_core
    hn hdim Γ hΓ hcov hr hcgeom
  let A : Set (Set (BoundaryH n)) := {T | (thinRegion hn Γ r T ∩ K).Nonempty ∧
    ∃ δ : Γ, (fun ξ : BoundaryH n => (δ : PO n 1) • ξ) '' S = T}
  have hA : A.Finite := (finite_labels_meeting_compact hn Γ hΓ r hK).subset (fun _ h => h.1)
  let : Finite A := hA
  choose δ hδ using fun T : A => T.property.2
  let C : Set (HUpper n) :=
    (⋃ T : A, (fun p : HUpper n => ((δ T : Γ) : PO n 1)⁻¹ • p) '' K) ∩
      frontier (thinRegion hn Γ r S)
  have hC : IsCompact C := by
    apply IsCompact.inter_right _ isClosed_frontier
    apply isCompact_iUnion
    intro T
    exact hK.image (interiorHomeomorph hn ((δ T : Γ) : PO n 1)⁻¹).continuous
  refine ⟨C, hC, inter_subset_right, ?_⟩
  intro x hx
  obtain ⟨d, hd⟩ := hcover x (frontier_subset_closure_finiteLocus hn Γ hΓ hre hgeom S hx)
  have hxR : x ∈ thinRegion hn Γ r S := (hc S).closure_eq ▸ hx.1
  let T : A := ⟨(fun ξ : BoundaryH n => (d : PO n 1) • ξ) '' S,
    ⟨⟨(d : PO n 1) • x, smul_mem_thinRegion hn Γ r hxR d, hd⟩, d, rfl⟩⟩
  let γ : Γ := (δ T)⁻¹ * d
  have hlabel : (fun ξ : BoundaryH n => (γ : PO n 1) • ξ) '' S = S := by
    change (fun ξ : BoundaryH n => (((δ T : Γ) : PO n 1)⁻¹ * (d : PO n 1)) • ξ) '' S = S
    simp only [mul_smul, ← image_image]
    change (fun ξ : BoundaryH n => ((δ T : Γ) : PO n 1)⁻¹ • ξ) '' T.val = S
    rw [← hδ T, image_image]
    simp only [inv_smul_smul, image_id']
  refine ⟨γ, hlabel, mem_iUnion.mpr ⟨T, (d : PO n 1) • x, hd, ?_⟩, ?_⟩
  · change _ = (((δ T : Γ) : PO n 1)⁻¹ * (d : PO n 1)) • x
    rw [mul_smul]
  · have h := smul_mem_frontier hn Γ r hx γ
    change (γ : PO n 1) • x ∈ frontier (thinRegion hn Γ r
      ((fun ξ : BoundaryH n => (γ : PO n 1) • ξ) '' S)) at h
    rwa [hlabel] at h

theorem exists_compact_horosphere_core (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) (c : ℝ) :
    ∃ C : Set (HUpper n), IsCompact C ∧ C ⊆ horosphere ξ c ∧
      ∀ p ∈ horosphere ξ c, ∃ γ : Γ,
        (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
        (poMulAction hn).smul (γ : PO n 1) p ∈ C := by
  obtain ⟨K, hK, _, hcover⟩ := exists_compact_frontier_core hn hdim Γ hΓ hcov hr hre hgeom {ξ}
  refine ⟨retract ξ c '' K, hK.image (continuous_retract ξ c), ?_, ?_⟩
  · rintro _ ⟨p, _, rfl⟩
    exact retract_mem_horosphere ξ c p
  · intro p hp
    obtain ⟨t, ht⟩ := exists_frontier_on_ray hn Γ hΓ hr
      (fun x => closedSmallSubgroup_geometry hn Γ hre x (hgeom x)) hξ p
    obtain ⟨γ, hlabel, hγ⟩ := hcover _ ht
    have hfix : (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ :=
      singleton_injective (by simpa only [image_singleton] using hlabel)
    have hmem : (γ : PO n 1) ∈ endStabilizer hn Γ {ξ} :=
      (mem_endStabilizer_singleton hn Γ ξ γ).mpr ⟨γ.property, hfix⟩
    have hscale := (horospherical_endStabilizer hn Γ hΓ hξ ⟨γ, hmem⟩).2
    refine ⟨γ, hfix, (poMulAction hn).smul (γ : PO n 1) (rayTo p ξ t), hγ, ?_⟩
    rw [retract_smul hn γ ξ c hfix hscale, retract_rayTo, retract_eq_self ξ c hp]

theorem isCompact_quotient_horosphere (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) (c : ℝ) :
    letI := EquivariantMap.subAction hn (endStabilizer hn Γ {ξ})
    IsCompact ((Quotient.mk (MulAction.orbitRel (endStabilizer hn Γ {ξ}) (HUpper n))) ''
      horosphere ξ c) := by
  let P := endStabilizer hn Γ {ξ}
  let := EquivariantMap.subAction hn P
  obtain ⟨K, hK, hKsub, hcover⟩ := exists_compact_horosphere_core hn hdim Γ hΓ hcov hr hre hgeom hξ c
  let q := Quotient.mk (MulAction.orbitRel P (HUpper n))
  have he : q '' K = q '' horosphere ξ c := by
    apply Subset.antisymm (image_mono hKsub)
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨γ, hγfix, hγK⟩ := hcover p hp
    let δ : P := ⟨γ, (mem_endStabilizer_singleton hn Γ ξ γ).mpr ⟨γ.property, hγfix⟩⟩
    exact ⟨(poMulAction hn).smul (γ : PO n 1) p, hγK, Quotient.sound ⟨δ, rfl⟩⟩
  rw [← he]
  exact hK.image continuous_quotient_mk'

theorem cobounded_of_compact_horosphere_core {m : ℕ} (P : Subgroup (PO (m + 1) 1))
    (hfix : ∀ g : P,
      (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (g : PO (m + 1) 1) MobiusBoundary.ptInfty =
        MobiusBoundary.ptInfty ∧
      poConfFactor (by omega : 1 ≤ m + 1) (g : PO (m + 1) 1) MobiusBoundary.ptInfty = 1)
    (hcore : ∃ K : Set (HUpper (m + 1)), IsCompact K ∧
      ∀ p ∈ horosphere (MobiusBoundary.ptInfty : BoundaryH (m + 1)) 0, ∃ g : P,
        (poMulAction (by omega : 1 ≤ m + 1)).smul (g : PO (m + 1) 1) p ∈ K) :
    DifferentialGeometry.CrystallographicActions.CoboundedOrbit (HorosphereGroups.affineAction P hfix) := by
  let := poMulAction (by omega : 1 ≤ m + 1)
  let ρ := HorosphereGroups.affineAction P hfix
  obtain ⟨K, hK, hcover⟩ := hcore
  obtain ⟨R, hR⟩ := (hK.image continuous_horizontal).isBounded.subset_closedBall
    (0 : Horospherical.Horizontal m)
  refine ⟨max 0 R, le_max_left _ _, ?_⟩
  intro x
  have hp : Horospherical.ofCoords x 1 zero_lt_one ∈
      horosphere (MobiusBoundary.ptInfty : BoundaryH (m + 1)) 0 := by
    change busemann _ _ = 0
    rw [Horospherical.busemann_ofCoords, Real.log_one, neg_zero]
  obtain ⟨g, hg⟩ := hcover _ hp
  have hflat : Horospherical.horizontal
      ((poMulAction (by omega : 1 ≤ m + 1)).smul (g : PO (m + 1) 1)
        (Horospherical.ofCoords x 1 zero_lt_one)) = ρ g x := by
    change Horospherical.horizontal ((g : PO (m + 1) 1) •
      Horospherical.ofCoords x 1 zero_lt_one) = ρ g x
    have h := congrArg Horospherical.horizontal
      (HorosphereGroups.affineAction_spec P hfix g x 1 zero_lt_one)
    simpa only [Horospherical.horizontal_ofCoords] using h
  have hbound : dist (ρ g x) 0 ≤ R := by
    have h := hR (mem_image_of_mem Horospherical.horizontal hg)
    rwa [Metric.mem_closedBall, hflat] at h
  refine ⟨g⁻¹, ?_⟩
  have hinv : ρ g (ρ g⁻¹ 0) = 0 := by
    have h := congrArg (fun a : Horospherical.Horizontal m ≃ᵃⁱ[ℝ] Horospherical.Horizontal m => a 0)
      (map_mul ρ g g⁻¹)
    simpa only [mul_inv_cancel, map_one, AffineIsometryEquiv.coe_one, id_eq,
      AffineIsometryEquiv.coe_mul, Function.comp_apply] using h.symm
  calc
    dist x (ρ g⁻¹ 0) = dist (ρ g x) (ρ g (ρ g⁻¹ 0)) := ((ρ g).dist_map _ _).symm
    _ = dist (ρ g x) 0 := by rw [hinv]
    _ ≤ R := hbound
    _ ≤ max 0 R := le_max_right _ _

theorem exists_cobounded_endStabilizer_action {m : ℕ} (hm : 1 ≤ m)
    (Γ : Subgroup (PO (m + 1) 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [hfd : @HasFundamentalDomain Γ (PO (m + 1) 1) _
      (MulAction.compHom (PO (m + 1) 1) Γ.subtype).toSMul _ volume]
    (hcov : @covolume Γ (PO (m + 1) 1) _
      (MulAction.compHom (PO (m + 1) 1) Γ.subtype).toSMul _ volume ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper (m + 1), ElementaryGeometry (by omega)
      (Margulis.smallSubgroup (by omega) Γ ε x))
    (hξ : (thinRegion (by omega : 1 ≤ m + 1) Γ r {MobiusBoundary.ptInfty}).Nonempty) :
    let P := endStabilizer (by omega : 1 ≤ m + 1) Γ {MobiusBoundary.ptInfty}
    ∃ hfix : ∀ g : P,
      (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (g : PO (m + 1) 1) MobiusBoundary.ptInfty =
        MobiusBoundary.ptInfty ∧
      poConfFactor (by omega : 1 ≤ m + 1) (g : PO (m + 1) 1) MobiusBoundary.ptInfty = 1,
      DifferentialGeometry.CrystallographicActions.CoboundedOrbit (HorosphereGroups.affineAction P hfix) := by
  have hn : 1 ≤ m + 1 := by omega
  let P := endStabilizer hn Γ {MobiusBoundary.ptInfty}
  let hfix := horospherical_endStabilizer hn Γ hΓ hξ
  refine ⟨hfix, cobounded_of_compact_horosphere_core P hfix ?_⟩
  obtain ⟨K, hK, _, hcover⟩ := @exists_compact_horosphere_core (m + 1) hn (by omega) Γ hΓ hfd hcov r ε hr hre hgeom _ hξ 0
  refine ⟨K, hK, fun p hp => ?_⟩
  obtain ⟨γ, hγfix, hγK⟩ := hcover p hp
  exact ⟨⟨γ, (mem_endStabilizer_singleton hn Γ _ γ).mpr ⟨γ.property, hγfix⟩⟩, hγK⟩

theorem exists_full_translation_lattice {m : ℕ} (hm : 1 ≤ m)
    (Γ : Subgroup (PO (m + 1) 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [hfd : @HasFundamentalDomain Γ (PO (m + 1) 1) _
      (MulAction.compHom (PO (m + 1) 1) Γ.subtype).toSMul _ volume]
    (hcov : @covolume Γ (PO (m + 1) 1) _
      (MulAction.compHom (PO (m + 1) 1) Γ.subtype).toSMul _ volume ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper (m + 1), ElementaryGeometry (by omega)
      (Margulis.smallSubgroup (by omega) Γ ε x))
    (hξ : (thinRegion (by omega : 1 ≤ m + 1) Γ r {MobiusBoundary.ptInfty}).Nonempty) :
    let P := endStabilizer (by omega : 1 ≤ m + 1) Γ {MobiusBoundary.ptInfty}
    ∃ (D : Submodule ℤ (Horospherical.Horizontal m)) (hD : DiscreteTopology D),
      letI := hD
      IsZLattice ℝ D ∧ TranslationLattices.latticeGroup D ≤ P ∧
        ((TranslationLattices.latticeGroup D).subgroupOf P).FiniteIndex := by
  obtain ⟨hfix, hco⟩ := @exists_cobounded_endStabilizer_action m hm Γ hΓ hfd hcov r ε hr hre hgeom hξ
  exact HorosphereGroups.exists_full_translation_lattice_of_cobounded _ hfix
    (hΓ.mono inf_le_left) hco

end DifferentialGeometry.CuspCrossSections
