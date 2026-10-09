/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Horoballs
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.AxialThinCompactness

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology Pointwise

namespace DifferentialGeometry.CuspTruncation

open Hyperbolic HyperbolicAction HyperbolicBoundary HyperbolicFaithful
open Busemann BoundaryStabilizer OrbifoldStrata ElementaryEnds
open OrbifoldThinRegions CuspCrossSections CuspHoroballs HorosphereProjection

variable {n : ℕ}

theorem exists_finite_thin_orbit_representatives (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    ∃ A : Set (Set (BoundaryH n)), A.Finite ∧
      (∀ S ∈ A, (thinRegion hn Γ r S).Nonempty) ∧
      (∀ S ∈ A, ∀ T ∈ A, ∀ γ : Γ,
        (fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S = T → S = T) ∧
      ∀ S : Set (BoundaryH n), (thinRegion hn Γ r S).Nonempty →
        ∃ γ : Γ, (fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S ∈ A := by
  classical
  let := poBoundaryMulAction hn
  let : MulAction Γ (BoundaryH n) := MulAction.compHom _ Γ.subtype
  obtain ⟨A₀, hA₀, hcover₀⟩ := exists_finite_thin_representatives hn hdim Γ hΓ hcov hr hre hgeom
  let A₁ := A₀ ∩ {S | (thinRegion hn Γ r S).Nonempty}
  have hA₁ : A₁.Finite := hA₀.inter_of_left _
  have hcover₁ (S : Set (BoundaryH n)) (hS : (thinRegion hn Γ r S).Nonempty) :
      ∃ γ : Γ, (fun ξ : BoundaryH n => (γ : PO n 1) • ξ) '' S ∈ A₁ := by
    obtain ⟨γ, hγ⟩ := hcover₀ S hS
    obtain ⟨x, hx⟩ := hS
    exact ⟨γ, hγ, (poMulAction hn).smul (γ : PO n 1) x, smul_mem_thinRegion hn Γ r hx γ⟩
  let q := Quotient.mk (MulAction.orbitRel Γ (Set (BoundaryH n)))
  have hsurj : SurjOn q A₁ (q '' A₁) := by
    rintro _ ⟨S, hS, rfl⟩
    exact ⟨S, hS, rfl⟩
  obtain ⟨A, hsub, hinj, himage⟩ := hsurj.exists_subset_injOn_image_eq
  refine ⟨A, hA₁.subset hsub, fun S hS => (hsub hS).2, ?_, ?_⟩
  · intro S hS T hT γ hγ
    apply hinj hS hT
    exact (Quotient.sound ⟨γ, hγ⟩ : q T = q S).symm
  · intro S hS
    obtain ⟨γ, hγ⟩ := hcover₁ S hS
    have hm : q ((fun ξ : BoundaryH n => (γ : PO n 1) • ξ) '' S) ∈ q '' A := by
      rw [himage]
      exact mem_image_of_mem _ hγ
    obtain ⟨T, hT, he⟩ := hm
    obtain ⟨δ, hδ⟩ := Quotient.exact he
    change (fun ξ : BoundaryH n => (δ : PO n 1) • ξ) ''
      ((fun ξ : BoundaryH n => (γ : PO n 1) • ξ) '' S) = T at hδ
    refine ⟨δ * γ, ?_⟩
    have he' : (fun ξ : BoundaryH n => ((δ * γ : Γ) : PO n 1) • ξ) '' S = T := by
      simpa only [Subgroup.coe_mul, mul_smul, image_image] using hδ
    exact he'.symm ▸ hT

def openCuspSet (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (A : Set (BoundaryH n)) (c : A → ℝ) : Set (HUpper n) :=
  ⋃ ξ : A, ⋃ γ : Γ,
    (fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) ''
      {p | busemann ξ.val p < c ξ}

def truncatedSet (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (A : Set (BoundaryH n)) (c : A → ℝ) : Set (HUpper n) :=
  (openCuspSet hn Γ A c)ᶜ

theorem isOpen_openCuspSet (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (A : Set (BoundaryH n)) (c : A → ℝ) : IsOpen (openCuspSet hn Γ A c) :=
  isOpen_iUnion fun ξ => isOpen_iUnion fun γ =>
    (interiorHomeomorph hn γ).isOpenMap _ (isOpen_lt (continuous_busemann ξ.val) continuous_const)

theorem isClosed_truncatedSet (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (A : Set (BoundaryH n)) (c : A → ℝ) : IsClosed (truncatedSet hn Γ A c) :=
  (isOpen_openCuspSet hn Γ A c).isClosed_compl

theorem smul_mem_openCuspSet (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (A : Set (BoundaryH n)) (c : A → ℝ) {p : HUpper n}
    (hp : p ∈ openCuspSet hn Γ A c) (δ : Γ) :
    (poMulAction hn).smul (δ : PO n 1) p ∈ openCuspSet hn Γ A c := by
  obtain ⟨ξ, hξ⟩ := mem_iUnion.mp hp
  obtain ⟨γ, x, hx, rfl⟩ := mem_iUnion.mp hξ
  exact mem_iUnion.mpr ⟨ξ, mem_iUnion.mpr ⟨δ * γ, x, hx,
    (poMulAction hn).mul_smul (δ : PO n 1) (γ : PO n 1) x⟩⟩

theorem smul_mem_truncatedSet (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (A : Set (BoundaryH n)) (c : A → ℝ) {p : HUpper n}
    (hp : p ∈ truncatedSet hn Γ A c) (δ : Γ) :
    (poMulAction hn).smul (δ : PO n 1) p ∈ truncatedSet hn Γ A c := by
  let := poMulAction hn
  intro h
  have hi := smul_mem_openCuspSet hn Γ A c h δ⁻¹
  change (δ : PO n 1)⁻¹ • ((δ : PO n 1) • p) ∈ openCuspSet hn Γ A c at hi
  rw [inv_smul_smul] at hi
  exact hp hi

theorem level_le_of_mem_truncatedSet (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (A : Set (BoundaryH n)) (c : A → ℝ) {p : HUpper n}
    (hp : p ∈ truncatedSet hn Γ A c) (ξ : A) : c ξ ≤ busemann ξ.val p := by
  apply le_of_not_gt
  intro h
  apply hp
  exact mem_iUnion.mpr ⟨ξ, mem_iUnion.mpr ⟨1, p, h, (poMulAction hn).one_smul p⟩⟩

structure FiniteCuspTruncation (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (r : ℝ) where
  centers : Set (BoundaryH n)
  finite_centers : centers.Finite
  level : centers → ℝ
  region_nonempty : ∀ ξ : centers, (thinRegion hn Γ r {ξ.val}).Nonempty
  horoball_inside : ∀ ξ : centers,
    horoball ξ.val (level ξ) ⊆ interior (thinRegion hn Γ r {ξ.val})
  distinct_orbits : ∀ ξ η : centers, ∀ γ : Γ,
    (poBoundaryMulAction hn).smul (γ : PO n 1) ξ.val = η.val → ξ = η
  covers_centers : ∀ ξ : BoundaryH n, (thinRegion hn Γ r {ξ}).Nonempty →
    ∃ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ centers
  core : Set (HUpper n)
  compact_core : IsCompact core
  core_subset : core ⊆ truncatedSet hn Γ centers level
  covers_truncated : ∀ p ∈ truncatedSet hn Γ centers level, ∃ γ : Γ,
    (poMulAction hn).smul (γ : PO n 1) p ∈ core

theorem exists_finite_cusp_truncation (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    Nonempty (FiniteCuspTruncation hn Γ r) := by
  classical
  have hcgeom (x : HUpper n) := closedSmallSubgroup_geometry hn Γ hre x (hgeom x)
  obtain ⟨B, hBfinite, hBne, hBdistinct, hBcover⟩ :=
    exists_finite_thin_orbit_representatives hn hdim Γ hΓ hcov hr hre hgeom
  let A : Set (BoundaryH n) := (fun ξ : BoundaryH n => ({ξ} : Set (BoundaryH n))) ⁻¹' B
  have hA : A.Finite := hBfinite.preimage singleton_injective.injOn
  have hAne (ξ : A) : (thinRegion hn Γ r {ξ.val}).Nonempty := hBne _ ξ.property
  choose c hc using fun ξ : A =>
    exists_horoball_subset_interior hn hdim Γ hΓ hcov hr hre hgeom (hAne ξ)
  have hpiece (S : B) : ∃ K : Set (HUpper n), IsCompact K ∧
      ∀ p ∈ thinRegion hn Γ r S.val, p ∈ truncatedSet hn Γ A c →
        ∃ γ : Γ, (poMulAction hn).smul (γ : PO n 1) p ∈ K := by
    obtain ⟨x, hx⟩ := hBne S S.property
    rcases hx.2 with ⟨ξ, hS, _⟩ | ⟨ξ, η, hne, hS, _⟩
    · let a : A := ⟨ξ, show ({ξ} : Set (BoundaryH n)) ∈ B from hS ▸ S.property⟩
      obtain ⟨K, hK, _, hcover⟩ := exists_compact_cuspCollar_core hn hdim Γ hΓ hcov
        hr hre hgeom (hAne a) (c a)
      refine ⟨K, hK, fun p hp hpt => ?_⟩
      obtain ⟨γ, _, hγ⟩ := hcover p
        ⟨hS ▸ hp, level_le_of_mem_truncatedSet hn Γ A c hpt a⟩
      exact ⟨γ, hγ⟩
    · obtain ⟨K, hK, _, hcover⟩ := AxialThinCompactness.exists_compact_axial_core
        hn hdim Γ hΓ hcov hr hre hgeom ξ η hne
      refine ⟨K, hK, fun p hp _ => ?_⟩
      obtain ⟨γ, _, hγ⟩ := hcover p (hS ▸ hp)
      exact ⟨γ, hγ⟩
  let : Finite B := hBfinite
  choose C hCcompact hCcover using hpiece
  obtain ⟨Q, hQcompact, _, hQcover⟩ := FiniteLocusCompactness.exists_compact_finiteLocus_core
    hn hdim Γ hΓ hcov hr hcgeom
  let K := (Q ∪ ⋃ S : B, C S) ∩ truncatedSet hn Γ A c
  have hK : IsCompact K := (hQcompact.union (isCompact_iUnion hCcompact)).inter_right
    (isClosed_truncatedSet hn Γ A c)
  refine ⟨
    { centers := A
      finite_centers := hA
      level := c
      region_nonempty := hAne
      horoball_inside := hc
      distinct_orbits := ?_
      covers_centers := ?_
      core := K
      compact_core := hK
      core_subset := inter_subset_right
      covers_truncated := ?_ }⟩
  · intro ξ η γ hγ
    apply Subtype.ext
    apply singleton_injective
    exact hBdistinct {ξ.val} ξ.property {η.val} η.property γ
      (by simp only [image_singleton, hγ])
  · intro ξ hξ
    obtain ⟨γ, hγ⟩ := hBcover {ξ} hξ
    exact ⟨γ, by simpa only [A, mem_preimage, image_singleton] using hγ⟩
  · intro p hp
    by_cases hfinite : p ∈ finiteLocus hn Γ r
    · obtain ⟨γ, hγ⟩ := hQcover p (subset_closure hfinite)
      exact ⟨γ, Or.inl hγ, smul_mem_truncatedSet hn Γ A c hp γ⟩
    · obtain ⟨S, hpS⟩ := exists_thinRegion_of_not_finite hn Γ r p hfinite (hcgeom p)
      obtain ⟨γ, hγ⟩ := hBcover S ⟨p, hpS⟩
      let T : B := ⟨(fun ξ : BoundaryH n => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ) '' S, hγ⟩
      obtain ⟨δ, hδ⟩ := hCcover T _ (smul_mem_thinRegion hn Γ r hpS γ)
        (smul_mem_truncatedSet hn Γ A c hp γ)
      refine ⟨δ * γ, Or.inr (mem_iUnion.mpr ⟨T, ?_⟩),
        smul_mem_truncatedSet hn Γ A c hp (δ * γ)⟩
      have he : (poMulAction hn).smul ((δ * γ : Γ) : PO n 1) p =
          (poMulAction hn).smul (δ : PO n 1) ((poMulAction hn).smul (γ : PO n 1) p) :=
        (poMulAction hn).mul_smul (δ : PO n 1) (γ : PO n 1) p
      exact he.symm ▸ hδ

theorem FiniteCuspTruncation.precisely_invariant {hn : 1 ≤ n}
    {Γ : Subgroup (PO n 1)} (hΓ : IsDiscrete (SetLike.coe Γ)) {r : ℝ}
    (D : FiniteCuspTruncation hn Γ r) (ξ : D.centers) (γ : Γ) :
    ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ.val = ξ.val →
      (fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) '' horoball ξ.val (D.level ξ) =
        horoball ξ.val (D.level ξ)) ∧
    ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ.val ≠ ξ.val →
      Disjoint ((fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) ''
        horoball ξ.val (D.level ξ)) (horoball ξ.val (D.level ξ))) :=
  precisely_invariant_of_subset hn Γ hΓ (D.region_nonempty ξ) (D.level ξ)
    ((D.horoball_inside ξ).trans interior_subset) γ

theorem FiniteCuspTruncation.disjoint_horoballs {hn : 1 ≤ n}
    {Γ : Subgroup (PO n 1)} (hΓ : IsDiscrete (SetLike.coe Γ)) {r : ℝ}
    (D : FiniteCuspTruncation hn Γ r) (ξ η : D.centers) (γ δ : Γ)
    (hne : (poBoundaryMulAction hn).smul (γ : PO n 1) ξ.val ≠
      (poBoundaryMulAction hn).smul (δ : PO n 1) η.val) :
    Disjoint ((fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) ''
      horoball ξ.val (D.level ξ))
      ((fun p : HUpper n => (poMulAction hn).smul (δ : PO n 1) p) ''
        horoball η.val (D.level η)) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨x, hx, hxp⟩ ⟨y, hy, hyp⟩
  change (poMulAction hn).smul (γ : PO n 1) x = p at hxp
  change (poMulAction hn).smul (δ : PO n 1) y = p at hyp
  have hxT := smul_mem_thinRegion hn Γ r (interior_subset (D.horoball_inside ξ hx)) γ
  have hyT := smul_mem_thinRegion hn Γ r (interior_subset (D.horoball_inside η hy)) δ
  rw [hxp] at hxT
  rw [hyp] at hyT
  let := hxT.1
  have he := hxT.2.unique (hΓ.mono (closedSmallSubgroup_le hn Γ r p)) hyT.2
  exact hne (singleton_injective (by simpa only [image_singleton] using he))

theorem FiniteCuspTruncation.finiteLocus_subset {hn : 1 ≤ n}
    {Γ : Subgroup (PO n 1)} {r : ℝ} (D : FiniteCuspTruncation hn Γ r) :
    finiteLocus hn Γ r ⊆ truncatedSet hn Γ D.centers D.level := by
  intro p hp hremoved
  obtain ⟨ξ, hξ⟩ := mem_iUnion.mp hremoved
  obtain ⟨γ, y, hy, rfl⟩ := mem_iUnion.mp hξ
  have hyb : busemann ξ.val y < D.level ξ := hy
  have hyHB : y ∈ horoball ξ.val (D.level ξ) := hyb.le
  have hyT := interior_subset (D.horoball_inside ξ hyHB)
  exact mem_thinRegion_not_finite (smul_mem_thinRegion hn Γ r hyT γ) hp

theorem FiniteCuspTruncation.core_nonempty {hn : 1 ≤ n} (hdim : 2 ≤ n)
    {Γ : Subgroup (PO n 1)} (hΓ : IsDiscrete (SetLike.coe Γ)) {r ε : ℝ}
    (D : FiniteCuspTruncation hn Γ r) (hr : 0 ≤ r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    D.core.Nonempty := by
  obtain ⟨p, hp⟩ := finiteLocus_nonempty hn hdim Γ hΓ hr hre hgeom
  obtain ⟨γ, hγ⟩ := D.covers_truncated p (D.finiteLocus_subset hp)
  exact ⟨(poMulAction hn).smul (γ : PO n 1) p, hγ⟩

theorem FiniteCuspTruncation.isCompact_quotient {hn : 1 ≤ n}
    {Γ : Subgroup (PO n 1)} {r : ℝ} (D : FiniteCuspTruncation hn Γ r) :
    letI := EquivariantMap.subAction hn Γ
    IsCompact ((Quotient.mk (MulAction.orbitRel Γ (HUpper n))) ''
      truncatedSet hn Γ D.centers D.level) := by
  let := EquivariantMap.subAction hn Γ
  let q := Quotient.mk (MulAction.orbitRel Γ (HUpper n))
  have he : q '' D.core = q '' truncatedSet hn Γ D.centers D.level := by
    apply Subset.antisymm (image_mono D.core_subset)
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨γ, hγ⟩ := D.covers_truncated p hp
    exact ⟨(poMulAction hn).smul (γ : PO n 1) p, hγ, Quotient.sound ⟨γ, rfl⟩⟩
  rw [← he]
  exact D.compact_core.image continuous_quotient_mk'

end DifferentialGeometry.CuspTruncation
