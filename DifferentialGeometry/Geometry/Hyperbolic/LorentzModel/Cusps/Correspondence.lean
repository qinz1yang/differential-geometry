/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Charts
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.PeripheralGroups

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.CuspCorrespondence

open Hyperbolic HyperbolicAction HyperbolicBoundary Horospherical
open BusemannCocycle BoundaryStabilizer ParabolicRegions
open OrbifoldThinRegions CuspCrossSections PeripheralGroups

variable {n m : ℕ}

def IsCuspCenter (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ξ : BoundaryH n) : Prop :=
  ∃ g : Γ, IsParabolicAt hn (g : PO n 1) ξ

theorem IsCuspCenter.smul {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)}
    {ξ : BoundaryH n} (hξ : IsCuspCenter hn Γ ξ) (g : Γ) :
    IsCuspCenter hn Γ ((poBoundaryMulAction hn).smul (g : PO n 1) ξ) := by
  obtain ⟨a, ha⟩ := hξ
  exact ⟨g * a * g⁻¹, ha.conj g⟩

theorem IsCuspCenter.thinRegion_nonempty {hn : 1 ≤ n}
    {Γ : Subgroup (PO n 1)} (hΓ : IsDiscrete (SetLike.coe Γ))
    {r : ℝ} (hr : 0 < r)
    (hgeom : ∀ x : HUpper n,
      ElementaryGeometry hn (OrbifoldStrata.closedSmallSubgroup hn Γ r x))
    {ξ : BoundaryH n} (hξ : IsCuspCenter hn Γ ξ) :
    (thinRegion hn Γ r {ξ}).Nonempty := by
  obtain ⟨g, hg⟩ := hξ
  obtain ⟨x, a, ha, hshort⟩ := region_nonempty hn Γ hr g hg
  exact ⟨x, parabolic_closedRegion_subset hn Γ hΓ r hgeom ξ ⟨a, ha, hshort.le⟩⟩

theorem exists_infinite_order_of_translation_lattice
    (hm : 2 ≤ m) (D : Submodule ℤ (Horizontal m))
    [DiscreteTopology D] [IsZLattice ℝ D]
    (P : Subgroup (PO n 1)) (H : Subgroup P) (e : Multiplicative D ≃* H) :
    ∃ g : P, ¬IsOfFinOrder (g : PO n 1) := by
  let : IsAddTorsionFree D := .of_isTorsionFree ℤ D
  have hinf : Infinite (Multiplicative D) := not_finite_iff_infinite.mp (by
    intro hf
    let := hf
    exact not_virtualCyclic_lattice D (by simpa [Horizontal] using hm) ⟨1, inferInstance⟩)
  let := hinf
  obtain ⟨u, hu⟩ := exists_ne (1 : Multiplicative D)
  refine ⟨(e u : P), fun hfin => ?_⟩
  have hP : IsOfFinOrder (e u : P) :=
    (P.subtype_injective.isOfFinOrder_iff (f := P.subtype)).mp hfin
  have hH : IsOfFinOrder (e u) :=
    (H.subtype_injective.isOfFinOrder_iff (f := H.subtype)).mp hP
  have he : IsOfFinOrder u := by
    have h := e.symm.toMonoidHom.isOfFinOrder hH
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using h
  exact hu he.eq_one'

theorem isCuspCenter_of_thinRegion (hn : 1 ≤ n) (hdim : 3 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) :
    IsCuspCenter hn Γ ξ := by
  obtain ⟨D, hD, hfull, H, _, ⟨e⟩⟩ :=
    CuspCharts.exists_virtual_translation_lattice hn (by omega) Γ hΓ hcov hr hre hgeom hξ
  let := hD
  let := hfull
  let P := endStabilizer hn Γ {ξ}
  obtain ⟨g, hg⟩ := exists_infinite_order_of_translation_lattice (by omega) D P H e
  have hfix := horospherical_endStabilizer hn Γ hΓ hξ
  exact ⟨⟨g, g.property.1⟩, hg, (hfix g).1,
    AxialGroups.unique_boundary_fixed_of_horospherical hn P (hΓ.mono inf_le_left) ξ hfix g hg⟩

theorem IsCuspCenter.virtual_translation_lattice {hn : 1 ≤ n} (hdim : 3 ≤ n)
    {Γ : Subgroup (PO n 1)} (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ξ : BoundaryH n} (hξ : IsCuspCenter hn Γ ξ) :
    let P := endStabilizer hn Γ {ξ}
    ∃ (D : Submodule ℤ (Horizontal (n - 1))) (hD : DiscreteTopology D),
      letI := hD
      IsZLattice ℝ D ∧ ∃ H : Subgroup P, H.FiniteIndex ∧ Nonempty (Multiplicative D ≃* H) := by
  obtain ⟨ε, hε, hgeom⟩ := exists_margulis_geometry_constant hn
  have hcgeom (x : HUpper n) :=
    OrbifoldStrata.closedSmallSubgroup_geometry hn Γ (by linarith : ε / 2 < ε)
      x (hgeom Γ hΓ x)
  exact CuspCharts.exists_virtual_translation_lattice hn (by omega) Γ hΓ hcov
    (by linarith : 0 < ε / 2) (by linarith : ε / 2 < ε)
      (hgeom Γ hΓ) (hξ.thinRegion_nonempty hΓ (by linarith) hcgeom)

def restrictedHom {Γ Λ P : Subgroup (PO n 1)} (f : Γ ≃* Λ) (hP : P ≤ Γ) :
    P →* PO n 1 :=
  Λ.subtype.comp (f.toMonoidHom.comp (Subgroup.inclusion hP))

theorem restrictedHom_injective {Γ Λ P : Subgroup (PO n 1)}
    (f : Γ ≃* Λ) (hP : P ≤ Γ) : Function.Injective (restrictedHom f hP) :=
  Λ.subtype_injective.comp (f.injective.comp (Subgroup.inclusion_injective hP))

theorem restrictedHom_range_le {Γ Λ P : Subgroup (PO n 1)}
    (f : Γ ≃* Λ) (hP : P ≤ Γ) : (restrictedHom f hP).range ≤ Λ := by
  rintro _ ⟨g, rfl⟩
  exact (f (Subgroup.inclusion hP g)).property

theorem not_isOfFinOrder_image {Γ Λ : Subgroup (PO n 1)} (f : Γ ≃* Λ) (g : Γ)
    (hg : ¬IsOfFinOrder (g : PO n 1)) : ¬IsOfFinOrder (f g : PO n 1) := by
  intro h
  have hΛ : IsOfFinOrder (f g) :=
    (Λ.subtype_injective.isOfFinOrder_iff (f := Λ.subtype)).mp h
  have hΓ : IsOfFinOrder g := (f.injective.isOfFinOrder_iff (f := f.toMonoidHom)).mp hΛ
  exact hg (Γ.subtype.isOfFinOrder hΓ)

theorem exists_horospherical_image (hn : 1 ≤ n) (hdim : 3 ≤ n)
    (Γ Λ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (hΛ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) {ξ : BoundaryH n} (hξ : IsCuspCenter hn Γ ξ) :
    ∃ η : BoundaryH n, IsCuspCenter hn Λ η ∧
      (∀ g : Γ, (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ →
        (poBoundaryMulAction hn).smul (f g : PO n 1) η = η ∧
          poConfFactor hn (f g : PO n 1) η = 1) ∧
      (∀ g : Γ, (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ →
        ¬IsOfFinOrder (g : PO n 1) → IsParabolicAt hn (f g : PO n 1) η) := by
  obtain ⟨D, hD, hfull, H, hH, ⟨e⟩⟩ := hξ.virtual_translation_lattice hdim hΓ hcov
  let := hD
  let := hfull
  let := hH
  let P := endStabilizer hn Γ {ξ}
  let j := restrictedHom f (show P ≤ Γ from inf_le_left)
  let ej : P ≃* j.range := MonoidHom.ofInjective (restrictedHom_injective f inf_le_left)
  obtain ⟨η, hfix, huniq⟩ := parabolic_image_of_iso (by omega) hn D P j.range
    (hΛ.mono (restrictedHom_range_le f inf_le_left)) ej H e
  have hfix' (g : Γ) (hg : (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ) :
      (poBoundaryMulAction hn).smul (f g : PO n 1) η = η ∧
        poConfFactor hn (f g : PO n 1) η = 1 := by
    let a : P := ⟨g, (mem_endStabilizer_singleton hn Γ ξ g).mpr ⟨g.property, hg⟩⟩
    exact hfix a
  have hpara (g : Γ) (hg : (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ)
      (hinf : ¬IsOfFinOrder (g : PO n 1)) : IsParabolicAt hn (f g : PO n 1) η := by
    let a : P := ⟨g, (mem_endStabilizer_singleton hn Γ ξ g).mpr ⟨g.property, hg⟩⟩
    exact ⟨not_isOfFinOrder_image f g hinf, (hfix' g hg).1, huniq a hinf⟩
  obtain ⟨g, hg⟩ := hξ
  exact ⟨η, ⟨f g, hpara g hg.fix hg.infinite_order⟩, hfix', hpara⟩

theorem existsUnique_matching_center (hn : 1 ≤ n) (hdim : 3 ≤ n)
    (Γ Λ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (hΛ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (hcovΓ : covolume Γ (PO n 1) ≠ ⊤) (hcovΛ : covolume Λ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) {ξ : BoundaryH n} (hξ : IsCuspCenter hn Γ ξ) :
    ∃! η : BoundaryH n, IsCuspCenter hn Λ η ∧
      ∀ g : Γ, (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ ↔
        (poBoundaryMulAction hn).smul (f g : PO n 1) η = η := by
  obtain ⟨η, hη, hforward, hpara⟩ :=
    exists_horospherical_image hn hdim Γ Λ hΓ hΛ hcovΓ f hξ
  obtain ⟨ζ, _, hback, _⟩ :=
    exists_horospherical_image hn hdim Λ Γ hΛ hΓ hcovΛ f.symm hη
  obtain ⟨a, ha⟩ := hξ
  have hζ : ζ = ξ := ha.unique ζ (by
    have h := (hback (f a) (hforward a ha.fix).1).1
    simpa only [f.symm_apply_apply] using h)
  subst ζ
  refine ⟨η, ⟨hη, fun g => ⟨fun hg => (hforward g hg).1, fun hg => ?_⟩⟩, ?_⟩
  · have h := (hback (f g) hg).1
    simpa only [f.symm_apply_apply] using h
  · intro η' hη'
    exact (hpara a ha.fix ha.infinite_order).unique η' ((hη'.2 a).mp ha.fix)

section Correspondence

variable (hn : 1 ≤ n) (hdim : 3 ≤ n)
    (Γ Λ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (hΛ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (hcovΓ : covolume Γ (PO n 1) ≠ ⊤) (hcovΛ : covolume Λ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ)

def centerMap (ξ : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ}) :
    {η : BoundaryH n // IsCuspCenter hn Λ η} :=
  let h := existsUnique_matching_center hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ.property
  ⟨h.exists.choose, h.exists.choose_spec.1⟩

theorem centerMap_spec (ξ : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ}) (g : Γ) :
    (poBoundaryMulAction hn).smul (g : PO n 1) ξ.val = ξ.val ↔
      (poBoundaryMulAction hn).smul (f g : PO n 1)
          (centerMap hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ).val =
        (centerMap hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ).val :=
  (existsUnique_matching_center hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ.property).exists.choose_spec.2 g

theorem centerMap_symm (ξ : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ}) :
    centerMap hn hdim Λ Γ hΛ hΓ hcovΛ hcovΓ f.symm
      (centerMap hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ) = ξ := by
  apply Subtype.ext
  let η := centerMap hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ
  apply (existsUnique_matching_center hn hdim Λ Γ hΛ hΓ hcovΛ hcovΓ f.symm η.property).unique
  · exact ⟨(centerMap hn hdim Λ Γ hΛ hΓ hcovΛ hcovΓ f.symm η).property,
      centerMap_spec hn hdim Λ Γ hΛ hΓ hcovΛ hcovΓ f.symm η⟩
  · refine ⟨ξ.property, fun g => ?_⟩
    have h := centerMap_spec hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ (f.symm g)
    simpa only [f.apply_symm_apply] using h.symm

def centerEquiv : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ} ≃
    {η : BoundaryH n // IsCuspCenter hn Λ η} where
  toFun := centerMap hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f
  invFun := centerMap hn hdim Λ Γ hΛ hΓ hcovΛ hcovΓ f.symm
  left_inv := centerMap_symm hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f
  right_inv := centerMap_symm hn hdim Λ Γ hΛ hΓ hcovΛ hcovΓ f.symm

@[simp] theorem centerEquiv_apply (ξ : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ}) :
    centerEquiv hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ =
      centerMap hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ := rfl

theorem fixes_smul_iff (g a : PO n 1) (ξ : BoundaryH n) :
    (poBoundaryMulAction hn).smul g ((poBoundaryMulAction hn).smul a ξ) =
        (poBoundaryMulAction hn).smul a ξ ↔
      (poBoundaryMulAction hn).smul (a⁻¹ * g * a) ξ = ξ := by
  let := poBoundaryMulAction hn
  change g • (a • ξ) = a • ξ ↔ (a⁻¹ * g * a) • ξ = ξ
  constructor
  · intro h
    simpa only [mul_smul, inv_smul_smul] using congrArg (fun η => a⁻¹ • η) h
  · intro h
    simpa only [mul_smul, smul_inv_smul] using congrArg (fun η => a • η) h

theorem centerEquiv_equivariant (ξ : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ}) (a : Γ) :
    (centerEquiv hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f
      ⟨(poBoundaryMulAction hn).smul (a : PO n 1) ξ.val, ξ.property.smul a⟩).val =
        (poBoundaryMulAction hn).smul (f a : PO n 1)
          (centerEquiv hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ).val := by
  let η := centerMap hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ
  let ξ' : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ} :=
    ⟨(poBoundaryMulAction hn).smul (a : PO n 1) ξ.val, ξ.property.smul a⟩
  apply (existsUnique_matching_center hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ'.property).unique
  · exact ⟨(centerMap hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ').property,
      centerMap_spec hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ'⟩
  · refine ⟨η.property.smul (f a), fun g => ?_⟩
    change (poBoundaryMulAction hn).smul (g : PO n 1)
        ((poBoundaryMulAction hn).smul (a : PO n 1) ξ.val) = _ ↔ _
    rw [fixes_smul_iff hn, fixes_smul_iff hn]
    have h := centerMap_spec hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ (a⁻¹ * g * a)
    simpa only [centerEquiv_apply, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem map_peripheral_eq (ξ : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ}) :
    ((endStabilizer hn Γ {ξ.val}).subgroupOf Γ).map f.toMonoidHom =
      (endStabilizer hn Λ
        {(centerEquiv hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ).val}).subgroupOf Λ := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hfix := (mem_endStabilizer_singleton hn Γ ξ.val a).mp ha
    exact (mem_endStabilizer_singleton hn Λ _ (f a)).mpr
      ⟨(f a).property, (centerMap_spec hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ a).mp hfix.2⟩
  · intro hg
    have hfix := (mem_endStabilizer_singleton hn Λ _ g).mp hg
    refine ⟨f.symm g, ?_, f.apply_symm_apply g⟩
    apply (mem_endStabilizer_singleton hn Γ ξ.val (f.symm g)).mpr
    refine ⟨(f.symm g).property, ?_⟩
    apply (centerMap_spec hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ (f.symm g)).mpr
    simpa only [centerEquiv_apply, f.apply_symm_apply] using hfix.2

def peripheralIso (ξ : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ}) :
    endStabilizer hn Γ {ξ.val} ≃*
      endStabilizer hn Λ {(centerEquiv hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ).val} :=
  ((Subgroup.subgroupOfEquivOfLe (show endStabilizer hn Γ {ξ.val} ≤ Γ from inf_le_left)).symm.trans
    (f.subgroupMap ((endStabilizer hn Γ {ξ.val}).subgroupOf Γ))).trans
      ((MulEquiv.subgroupCongr (map_peripheral_eq hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ)).trans
        (Subgroup.subgroupOfEquivOfLe inf_le_left))

theorem peripheralIso_coe (ξ : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ})
    (g : endStabilizer hn Γ {ξ.val}) :
    (peripheralIso hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ g : PO n 1) =
      (f ⟨g, g.property.1⟩ : PO n 1) := rfl

end Correspondence

end DifferentialGeometry.CuspCorrespondence
