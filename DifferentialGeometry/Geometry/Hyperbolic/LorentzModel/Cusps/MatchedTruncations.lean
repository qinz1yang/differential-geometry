/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Maps
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Truncation

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.MatchedCusps

open Hyperbolic HyperbolicAction HyperbolicBoundary
open Busemann BusemannCocycle BoundaryStabilizer OrbifoldStrata
open OrbifoldThinRegions CuspCrossSections CuspHoroballs CuspTruncation
open CuspCorrespondence CuspMaps

variable {n : ℕ}

theorem exists_compact_retruncated_core (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (T : FiniteCuspTruncation hn Γ r) (A : Set (BoundaryH n)) (c : A → ℝ)
    (hcover : ∀ ξ : T.centers, ∃ γ : Γ,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ.val ∈ A) :
    ∃ K : Set (HUpper n), IsCompact K ∧ K ⊆ truncatedSet hn Γ A c ∧
      ∀ p ∈ truncatedSet hn Γ A c, ∃ γ : Γ,
        (poMulAction hn).smul (γ : PO n 1) p ∈ K := by
  classical
  let := poMulAction hn
  let : Finite T.centers := T.finite_centers
  choose δ hδ using hcover
  let a (ξ : T.centers) : A := ⟨(poBoundaryMulAction hn).smul (δ ξ : PO n 1) ξ.val, hδ ξ⟩
  let d (ξ : T.centers) := c (a ξ) + Real.log (poConfFactor hn (δ ξ : PO n 1) ξ.val)
  choose C hC hCsub hCcover using fun ξ : T.centers =>
    exists_compact_cuspCollar_core hn hdim Γ hΓ hcov hr hre hgeom (T.region_nonempty ξ) (d ξ)
  let K := (T.core ∪ ⋃ ξ : T.centers, C ξ) ∩ truncatedSet hn Γ A c
  refine ⟨K, (T.compact_core.union (isCompact_iUnion hC)).inter_right
    (isClosed_truncatedSet hn Γ A c), inter_subset_right, fun p hp => ?_⟩
  by_cases hold : p ∈ truncatedSet hn Γ T.centers T.level
  · obtain ⟨γ, hγ⟩ := T.covers_truncated p hold
    exact ⟨γ, Or.inl hγ, smul_mem_truncatedSet hn Γ A c hp γ⟩
  have hremoved : p ∈ openCuspSet hn Γ T.centers T.level := not_not.mp hold
  obtain ⟨ξ, hξ⟩ := mem_iUnion.mp hremoved
  obtain ⟨γ, x, hx, rfl⟩ := mem_iUnion.mp hξ
  have hxnew : x ∈ truncatedSet hn Γ A c := by
    have h := smul_mem_truncatedSet hn Γ A c hp γ⁻¹
    change (γ : PO n 1)⁻¹ • ((γ : PO n 1) • x) ∈ _ at h
    rwa [inv_smul_smul] at h
  have hlevel := level_le_of_mem_truncatedSet hn Γ A c
    (smul_mem_truncatedSet hn Γ A c hxnew (δ ξ)) (a ξ)
  have hshift := po_busemann_smul hn (δ ξ : PO n 1) ξ.val x
  have hlow : d ξ ≤ busemann ξ.val x := by
    change c (a ξ) ≤ busemann ((poBoundaryMulAction hn).smul (δ ξ : PO n 1) ξ.val)
      ((poMulAction hn).smul (δ ξ : PO n 1) x) at hlevel
    rw [hshift] at hlevel
    dsimp only [d]
    linarith
  have hxT : x ∈ thinRegion hn Γ r {ξ.val} :=
    interior_subset (T.horoball_inside ξ (show busemann ξ.val x ≤ T.level ξ from le_of_lt hx))
  obtain ⟨β, _, hβ⟩ := hCcover ξ x ⟨hxT, hlow⟩
  change (β : PO n 1) • x ∈ C ξ at hβ
  refine ⟨β * γ⁻¹, Or.inr (mem_iUnion.mpr ⟨ξ, ?_⟩),
    smul_mem_truncatedSet hn Γ A c hp (β * γ⁻¹)⟩
  change (((β : PO n 1) * (γ : PO n 1)⁻¹) • ((γ : PO n 1) • x)) ∈ C ξ
  simpa only [mul_smul, inv_smul_smul] using hβ

structure MatchedTruncation (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (f : Γ ≃* Λ) (r : ℝ) where
  source : FiniteCuspTruncation hn Γ r
  target : FiniteCuspTruncation hn Λ r
  centersEquiv : source.centers ≃ target.centers
  peripheralIso : ∀ ξ : source.centers,
    endStabilizer hn Γ {ξ.val} ≃* endStabilizer hn Λ {(centersEquiv ξ).val}
  peripheralIso_coe : ∀ (ξ : source.centers) (g : endStabilizer hn Γ {ξ.val}),
    (peripheralIso ξ g : PO n 1) = (f ⟨g, g.property.1⟩ : PO n 1)
  cuspMap : ∀ ξ : source.centers, CuspMap hn (peripheralIso ξ) ξ.val (centersEquiv ξ).val
  level_match : ∀ ξ : source.centers,
    target.level (centersEquiv ξ) = source.level ξ + (cuspMap ξ).shift

theorem MatchedTruncation.image_horoball {hn : 1 ≤ n}
    {Γ Λ : Subgroup (PO n 1)} {f : Γ ≃* Λ} {r : ℝ}
    (T : MatchedTruncation hn Γ Λ f r) (ξ : T.source.centers) :
    (T.cuspMap ξ).toEquiv '' horoball ξ.val (T.source.level ξ) =
      horoball (T.centersEquiv ξ).val (T.target.level (T.centersEquiv ξ)) := by
  rw [T.level_match]
  exact (T.cuspMap ξ).image_horoball _

theorem MatchedTruncation.compatible_on_overlap {hn : 1 ≤ n}
    {Γ Λ : Subgroup (PO n 1)} {f : Γ ≃* Λ} {r : ℝ}
    (T : MatchedTruncation hn Γ Λ f r) (hΓ : IsDiscrete (SetLike.coe Γ))
    (i j : T.source.centers) (γ δ : Γ) (x y : HUpper n)
    (hx : x ∈ horoball i.val (T.source.level i))
    (hy : y ∈ horoball j.val (T.source.level j))
    (he : (poMulAction hn).smul (γ : PO n 1) x = (poMulAction hn).smul (δ : PO n 1) y) :
    (poMulAction hn).smul (f γ : PO n 1) ((T.cuspMap i).toEquiv x) =
      (poMulAction hn).smul (f δ : PO n 1) ((T.cuspMap j).toEquiv y) := by
  let := poMulAction hn
  let := poBoundaryMulAction hn
  have hc : (γ : PO n 1) • i.val = (δ : PO n 1) • j.val := by
    by_contra h
    exact Set.disjoint_left.mp (T.source.disjoint_horoballs hΓ i j γ δ h)
      ⟨x, hx, rfl⟩ ⟨y, hy, he.symm⟩
  have hcenter : ((δ⁻¹ * γ : Γ) : PO n 1) • i.val = j.val := by
    have h := congrArg (fun ζ : BoundaryH n => (δ : PO n 1)⁻¹ • ζ) hc
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul] using h
  have hij := T.source.distinct_orbits i j (δ⁻¹ * γ) hcenter
  subst j
  let k : endStabilizer hn Γ {i.val} :=
    ⟨(δ⁻¹ * γ : Γ), (mem_endStabilizer_singleton hn Γ i.val _).mpr
      ⟨(δ⁻¹ * γ : Γ).property, hcenter⟩⟩
  have hxy : (k : PO n 1) • x = y := by
    have h := congrArg (fun p : HUpper n => (δ : PO n 1)⁻¹ • p) he
    change (δ : PO n 1)⁻¹ • ((γ : PO n 1) • x) = (δ : PO n 1)⁻¹ • ((δ : PO n 1) • y) at h
    change ((δ : PO n 1)⁻¹ * (γ : PO n 1)) • x = y
    simpa only [mul_smul, inv_smul_smul] using h
  have hm : (T.cuspMap i).toEquiv y =
      ((f δ : PO n 1)⁻¹ * (f γ : PO n 1)) • (T.cuspMap i).toEquiv x := by
    have h := (T.cuspMap i).equivariant k x
    change (T.cuspMap i).toEquiv ((k : PO n 1) • x) =
      (T.peripheralIso i k : PO n 1) • (T.cuspMap i).toEquiv x at h
    rw [hxy, T.peripheralIso_coe] at h
    change (T.cuspMap i).toEquiv y =
      (f (δ⁻¹ * γ) : PO n 1) • (T.cuspMap i).toEquiv x at h
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h
  change (f γ : PO n 1) • (T.cuspMap i).toEquiv x =
    (f δ : PO n 1) • (T.cuspMap i).toEquiv y
  rw [hm, mul_smul, smul_inv_smul]

theorem exists_matched_truncation (hn : 1 ≤ n) (hdim : 3 ≤ n)
    (Γ Λ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (hΛ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (hcovΓ : covolume Γ (PO n 1) ≠ ⊤) (hcovΛ : covolume Λ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeomΓ : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (hgeomΛ : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Λ ε x))
    (TΓ : FiniteCuspTruncation hn Γ r) (TΛ : FiniteCuspTruncation hn Λ r)
    (f : Γ ≃* Λ) : Nonempty (MatchedTruncation hn Γ Λ f r) := by
  classical
  let I := TΓ.centers
  let : Finite I := TΓ.finite_centers
  let z (i : I) : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ} :=
    ⟨i.val, isCuspCenter_of_thinRegion hn hdim Γ hΓ hcovΓ hr hre hgeomΓ (TΓ.region_nonempty i)⟩
  let φ := centerEquiv hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f
  let η (i : I) : BoundaryH n := (φ (z i)).val
  let iso (i : I) : endStabilizer hn Γ {i.val} ≃* endStabilizer hn Λ {η i} :=
    CuspCorrespondence.peripheralIso hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f (z i)
  let M (i : I) : CuspMap hn (iso i) i.val (η i) :=
    Classical.choice (exists_cuspMap_for_iso hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f (z i))
  have hηT (i : I) : (thinRegion hn Λ r {η i}).Nonempty :=
    (φ (z i)).property.thinRegion_nonempty hΛ hr
      (fun x => closedSmallSubgroup_geometry hn Λ hre x (hgeomΛ x))
  have hinj : Function.Injective η := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun v : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ} => v.val)
      (φ.injective (Subtype.ext hij))
  have horbits (i j : I) (δ : Λ)
      (hδ : (poBoundaryMulAction hn).smul (δ : PO n 1) (η i) = η j) : i = j := by
    let v : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ} :=
      ⟨(poBoundaryMulAction hn).smul (f.symm δ : PO n 1) i.val, (z i).property.smul (f.symm δ)⟩
    have hv : φ v = φ (z j) := by
      apply Subtype.ext
      have h := centerEquiv_equivariant hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f (z i) (f.symm δ)
      rw [f.apply_symm_apply] at h
      exact h.trans hδ
    exact TΓ.distinct_orbits i j (f.symm δ) (congrArg Subtype.val (φ.injective hv))
  let B : Set (BoundaryH n) := range η
  have hB : B.Finite := finite_range η
  let e : I ≃ B := Equiv.ofInjective η hinj
  have hηe (y : B) : η (e.symm y) = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hcoverB (ζ : BoundaryH n) (hζ : (thinRegion hn Λ r {ζ}).Nonempty) :
      ∃ δ : Λ, (poBoundaryMulAction hn).smul (δ : PO n 1) ζ ∈ B := by
    let w : {η : BoundaryH n // IsCuspCenter hn Λ η} :=
      ⟨ζ, isCuspCenter_of_thinRegion hn hdim Λ hΛ hcovΛ hr hre hgeomΛ hζ⟩
    let v := φ.symm w
    have hvT : (thinRegion hn Γ r {v.val}).Nonempty :=
      v.property.thinRegion_nonempty hΓ hr
        (fun x => closedSmallSubgroup_geometry hn Γ hre x (hgeomΓ x))
    obtain ⟨γ, hγ⟩ := TΓ.covers_centers v.val hvT
    let i : I := ⟨(poBoundaryMulAction hn).smul (γ : PO n 1) v.val, hγ⟩
    have himage : η i = (poBoundaryMulAction hn).smul (f γ : PO n 1) ζ := by
      have h := centerEquiv_equivariant hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f v γ
      have hv : (φ v).val = ζ := congrArg Subtype.val (φ.apply_symm_apply w)
      change η i = (poBoundaryMulAction hn).smul (f γ : PO n 1) (φ v).val at h
      exact h.trans (congrArg ((poBoundaryMulAction hn).smul (f γ : PO n 1)) hv)
    exact ⟨f γ, ⟨i, himage⟩⟩
  choose t ht using fun i : I =>
    exists_horoball_subset_interior hn (by omega) Λ hΛ hcovΛ hr hre hgeomΛ (hηT i)
  let s (i : I) : ℝ := min (TΓ.level i) (t i - (M i).shift) - 1
  let d (y : B) : ℝ := s (e.symm y) + (M (e.symm y)).shift
  have hsource (i : I) : horoball i.val (s i) ⊆ interior (thinRegion hn Γ r {i.val}) := by
    intro x hx
    apply TΓ.horoball_inside i
    have hx' : busemann i.val x ≤ s i := hx
    have hs := min_le_left (TΓ.level i) (t i - (M i).shift)
    change busemann i.val x ≤ TΓ.level i
    dsimp only [s] at hx'
    linarith
  have htarget (i : I) :
      horoball (η i) (s i + (M i).shift) ⊆ interior (thinRegion hn Λ r {η i}) := by
    intro x hx
    apply ht i
    have hx' : busemann (η i) x ≤ s i + (M i).shift := hx
    have hs := min_le_right (TΓ.level i) (t i - (M i).shift)
    change busemann (η i) x ≤ t i
    dsimp only [s] at hx'
    linarith
  obtain ⟨KΓ, hKΓ, hsubΓ, hcoverΓ⟩ :=
    exists_compact_retruncated_core hn (by omega) Γ hΓ hcovΓ hr hre hgeomΓ TΓ I s
      (fun i => ⟨1, by
        change (poBoundaryMulAction hn).smul (1 : PO n 1) i.val ∈ TΓ.centers
        have h : (poBoundaryMulAction hn).smul (1 : PO n 1) i.val = i.val :=
          (poBoundaryMulAction hn).one_smul i.val
        rw [h]
        exact i.property⟩)
  obtain ⟨KΛ, hKΛ, hsubΛ, hcoverΛ⟩ :=
    exists_compact_retruncated_core hn (by omega) Λ hΛ hcovΛ hr hre hgeomΛ TΛ B d
      (fun i => hcoverB i.val (TΛ.region_nonempty i))
  let S : FiniteCuspTruncation hn Γ r :=
    { centers := I
      finite_centers := TΓ.finite_centers
      level := s
      region_nonempty := TΓ.region_nonempty
      horoball_inside := hsource
      distinct_orbits := TΓ.distinct_orbits
      covers_centers := TΓ.covers_centers
      core := KΓ
      compact_core := hKΓ
      core_subset := hsubΓ
      covers_truncated := hcoverΓ }
  let U : FiniteCuspTruncation hn Λ r :=
    { centers := B
      finite_centers := hB
      level := d
      region_nonempty := fun y => hηe y ▸ hηT (e.symm y)
      horoball_inside := fun y => hηe y ▸ htarget (e.symm y)
      distinct_orbits := fun x y δ hδ => e.symm.injective
        (horbits (e.symm x) (e.symm y) δ (by simpa only [hηe] using hδ))
      covers_centers := hcoverB
      core := KΛ
      compact_core := hKΛ
      core_subset := hsubΛ
      covers_truncated := hcoverΛ }
  refine ⟨
    { source := S
      target := U
      centersEquiv := e
      peripheralIso := iso
      peripheralIso_coe := fun i g => CuspCorrespondence.peripheralIso_coe
        hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f (z i) g
      cuspMap := M
      level_match := ?_ }⟩
  intro i
  change s (e.symm (e i)) + (M (e.symm (e i))).shift = s i + (M i).shift
  rw [e.symm_apply_apply]

end DifferentialGeometry.MatchedCusps
