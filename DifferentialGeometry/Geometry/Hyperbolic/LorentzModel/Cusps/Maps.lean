/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Affine.Crystallographic.Rigidity
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Correspondence

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.CuspMaps

open Hyperbolic HyperbolicAction HyperbolicBoundary Horospherical MobiusBoundary
open Busemann BusemannCocycle BoundaryStabilizer PseudoIsometry
open CuspCrossSections CuspCorrespondence DifferentialGeometry.CrystallographicActions

variable {n m : ℕ}

structure CuspMap (hn : 1 ≤ n) {P Q : Subgroup (PO n 1)} (f : P ≃* Q)
    (ξ η : BoundaryH n) where
  toEquiv : HUpper n ≃ HUpper n
  error : ℝ
  inverseError : ℝ
  forward_bound : IsPseudoIsometry 1 error toEquiv
  inverse_bound : IsPseudoIsometry 1 inverseError toEquiv.symm
  uniform_toFun : UniformContinuous toEquiv
  uniform_invFun : UniformContinuous toEquiv.symm
  equivariant : IsFEquivariant f hn toEquiv
  shift : ℝ
  busemann_map : ∀ x : HUpper n, busemann η (toEquiv x) = busemann ξ x + shift

theorem CuspMap.inverse_equivariant {hn : 1 ≤ n} {P Q : Subgroup (PO n 1)}
    {f : P ≃* Q} {ξ η : BoundaryH n} (M : CuspMap hn f ξ η) :
    IsFEquivariant f.symm hn M.toEquiv.symm := by
  intro g x
  apply M.toEquiv.injective
  rw [M.toEquiv.apply_symm_apply]
  have h := M.equivariant (f.symm g) (M.toEquiv.symm x)
  rw [f.apply_symm_apply, M.toEquiv.apply_symm_apply] at h
  exact h.symm

theorem CuspMap.coarse_inverse_bounds {hn : 1 ≤ n} {P Q : Subgroup (PO n 1)}
    {f : P ≃* Q} {ξ η : BoundaryH n} (M : CuspMap hn f ξ η) :
    (∀ x, dist (M.toEquiv.symm (M.toEquiv x)) x ≤ 0) ∧
      (∀ y, dist (M.toEquiv (M.toEquiv.symm y)) y ≤ 0) := by
  constructor <;> intro x <;> simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, dist_self, le_refl]

def CuspMap.symm {hn : 1 ≤ n} {P Q : Subgroup (PO n 1)}
    {f : P ≃* Q} {ξ η : BoundaryH n} (M : CuspMap hn f ξ η) : CuspMap hn f.symm η ξ where
  toEquiv := M.toEquiv.symm
  error := M.inverseError
  inverseError := M.error
  forward_bound := M.inverse_bound
  inverse_bound := M.forward_bound
  uniform_toFun := M.uniform_invFun
  uniform_invFun := M.uniform_toFun
  equivariant := M.inverse_equivariant
  shift := -M.shift
  busemann_map x := by
    have h := M.busemann_map (M.toEquiv.symm x)
    rw [M.toEquiv.apply_symm_apply] at h
    linarith

theorem CuspMap.image_horoball {hn : 1 ≤ n} {P Q : Subgroup (PO n 1)}
    {f : P ≃* Q} {ξ η : BoundaryH n} (M : CuspMap hn f ξ η) (c : ℝ) :
    M.toEquiv '' horoball ξ c = horoball η (c + M.shift) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change busemann η (M.toEquiv x) ≤ c + M.shift
    rw [M.busemann_map]
    have hx' : busemann ξ x ≤ c := hx
    linarith
  · intro hy
    refine ⟨M.toEquiv.symm y, ?_, M.toEquiv.apply_symm_apply y⟩
    have h := M.busemann_map (M.toEquiv.symm y)
    rw [M.toEquiv.apply_symm_apply] at h
    change busemann ξ (M.toEquiv.symm y) ≤ c
    change busemann η y ≤ c + M.shift at hy
    linarith

theorem CuspMap.image_horosphere {hn : 1 ≤ n} {P Q : Subgroup (PO n 1)}
    {f : P ≃* Q} {ξ η : BoundaryH n} (M : CuspMap hn f ξ η) (c : ℝ) :
    M.toEquiv '' horosphere ξ c = horosphere η (c + M.shift) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change busemann η (M.toEquiv x) = c + M.shift
    rw [M.busemann_map, show busemann ξ x = c from hx]
  · intro hy
    refine ⟨M.toEquiv.symm y, ?_, M.toEquiv.apply_symm_apply y⟩
    have h := M.busemann_map (M.toEquiv.symm y)
    rw [M.toEquiv.apply_symm_apply] at h
    change busemann ξ (M.toEquiv.symm y) = c
    change busemann η y = c + M.shift at hy
    linarith

def CuspMap.boundaryHomeomorph {hn : 1 ≤ n} {P Q : Subgroup (PO n 1)}
    {f : P ≃* Q} {ξ η : BoundaryH n} (M : CuspMap hn f ξ η) :
    BoundaryH n ≃ₜ BoundaryH n :=
  BoundaryHomeomorph.bExtHomeomorph M.forward_bound M.inverse_bound
    M.coarse_inverse_bounds.1 M.coarse_inverse_bounds.2 hn

theorem CuspMap.boundaryHomeomorph_converges {hn : 1 ≤ n} {P Q : Subgroup (PO n 1)}
    {f : P ≃* Q} {ξ η : BoundaryH n} (M : CuspMap hn f ξ η) (ζ : BoundaryH n) :
    BoundaryTopology.ConvergesToBoundary
      (fun k : ℕ => M.toEquiv (BoundaryTopology.geodesicRay ζ (k : ℝ)))
        (M.boundaryHomeomorph ζ) := by
  unfold CuspMap.boundaryHomeomorph
  rw [BoundaryHomeomorph.bExtHomeomorph_apply]
  simpa only [MorseStability.rayTo_basepointH_eq_geodesicRay] using
    BoundaryExtension.bExt_spec
      (BoundaryHomeomorph.gromovCauchy_image_ray M.forward_bound hn) ζ

theorem CuspMap.boundaryHomeomorph_equivariant {hn : 1 ≤ n} {P Q : Subgroup (PO n 1)}
    {f : P ≃* Q} {ξ η : BoundaryH n} (M : CuspMap hn f ξ η) (g : P) (ζ : BoundaryH n) :
    M.boundaryHomeomorph ((poBoundaryMulAction hn).smul (g : PO n 1) ζ) =
      (poBoundaryMulAction hn).smul (f g : PO n 1) (M.boundaryHomeomorph ζ) := by
  unfold CuspMap.boundaryHomeomorph
  simp only [BoundaryHomeomorph.bExtHomeomorph_apply]
  exact BoundaryExtension.bExt_equivariant M.forward_bound
    (BoundaryHomeomorph.gromovCauchy_image_ray M.forward_bound hn) hn M.equivariant g ζ

theorem exists_normalized_cuspMap
    (P Q : Subgroup (PO (m + 1) 1)) (hP : IsDiscrete (SetLike.coe P))
    (hQ : IsDiscrete (SetLike.coe Q))
    (hfixP : ∀ g : P,
      (poBoundaryMulAction (by omega)).smul (g : PO (m + 1) 1) ptInfty = ptInfty ∧
        poConfFactor (by omega) (g : PO (m + 1) 1) ptInfty = 1)
    (hfixQ : ∀ g : Q,
      (poBoundaryMulAction (by omega)).smul (g : PO (m + 1) 1) ptInfty = ptInfty ∧
        poConfFactor (by omega) (g : PO (m + 1) 1) ptInfty = 1)
    (hcoP : CoboundedOrbit (HorosphereGroups.affineAction P hfixP))
    (hcoQ : CoboundedOrbit (HorosphereGroups.affineAction Q hfixQ))
    (f : P ≃* Q) : Nonempty (CuspMap (by omega) f ptInfty ptInfty) := by
  let := poMulAction (by omega : 1 ≤ m + 1)
  let ρ := HorosphereGroups.affineAction P hfixP
  let σ := (HorosphereGroups.affineAction Q hfixQ).comp f.toMonoidHom
  have hcoσ : CoboundedOrbit σ := by
    obtain ⟨R, hR, hcover⟩ := hcoQ
    refine ⟨R, hR, fun x => ?_⟩
    obtain ⟨g, hg⟩ := hcover x
    refine ⟨f.symm g, ?_⟩
    simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, f.apply_symm_apply] using hg
  have hpσ (B : ℝ) : {g : P | ‖σ g 0‖ ≤ B}.Finite :=
    (HorosphereGroups.finite_affine_displacement Q hfixQ hQ B).preimage f.injective.injOn
  obtain ⟨L, b, hL⟩ := AffineCrystallographic.exists_affine_intertwiner ρ σ
    (HorosphereGroups.affineAction_injective P hfixP)
    ((HorosphereGroups.affineAction_injective Q hfixQ).comp f.injective)
    hcoP hcoσ (HorosphereGroups.finite_affine_displacement P hfixP hP) hpσ
    (HorosphereGroups.virtuallyNilpotent_of_cobounded P hfixP hP hcoP)
  refine ⟨
    { toEquiv := HoroballMaps.affineEquiv L b
      error := Real.log (2 * HoroballMaps.distortion L)
      inverseError := Real.log (2 * HoroballMaps.distortion L.symm)
      forward_bound := HoroballMaps.affine_isPseudoIsometry L b
      inverse_bound := HoroballMaps.affine_isPseudoIsometry L.symm (-L.symm b)
      uniform_toFun := HoroballMaps.uniformContinuous_affine L b
      uniform_invFun := HoroballMaps.uniformContinuous_affineEquiv_symm L b
      equivariant := ?_
      shift := 0
      busemann_map := ?_ }⟩
  · intro g X
    obtain ⟨⟨x, h, hh⟩, rfl⟩ := coordsEquiv.symm.surjective X
    change HoroballMaps.affine L b
        ((g : PO (m + 1) 1) • ofCoords x h hh) =
      (f g : PO (m + 1) 1) • HoroballMaps.affine L b (ofCoords x h hh)
    rw [HorosphereGroups.affineAction_spec P hfixP, HoroballMaps.affine_ofCoords,
      HoroballMaps.affine_ofCoords, HorosphereGroups.affineAction_spec Q hfixQ]
    exact congrArg (fun y => ofCoords y h hh) (hL g x)
  · intro x
    exact (HoroballMaps.busemann_lift (fun x => L x + b) x).trans (add_zero _).symm

theorem pseudoIsometry_smul_comp (hn : 1 ≤ n) (a b : PO n 1)
    {K C : ℝ} {Φ : HUpper n → HUpper n} (hΦ : IsPseudoIsometry K C Φ) :
    IsPseudoIsometry K C
      (fun x => (poMulAction hn).smul b (Φ ((poMulAction hn).smul a x))) := by
  simpa only [one_mul, mul_one, mul_zero, zero_add, add_zero, Function.comp_def] using
    (isPseudoIsometry_po_smul hn b).comp (hΦ.comp (isPseudoIsometry_po_smul hn a))

def CuspMap.ofCharts (hn : 1 ≤ n) {P Q : Subgroup (PO n 1)} (f : P ≃* Q)
    (a b : PO n 1) {ξ η ζ τ : BoundaryH n}
    (ha : (poBoundaryMulAction hn).smul a ξ = ζ)
    (hb : (poBoundaryMulAction hn).smul b η = τ)
    (M : CuspMap hn
      (((MulAut.conj a).subgroupMap P).symm.trans (f.trans ((MulAut.conj b).subgroupMap Q))) ζ τ) :
    CuspMap hn f ξ η := by
  letI := poMulAction hn
  let eP := (MulAut.conj a).subgroupMap P
  let eQ := (MulAut.conj b).subgroupMap Q
  let Φ : HUpper n ≃ HUpper n :=
    (interiorHomeomorph hn a).toEquiv.trans
      (M.toEquiv.trans (interiorHomeomorph hn b).symm.toEquiv)
  have hUa (g : PO n 1) : UniformContinuous (fun x : HUpper n => g • x) :=
    (Isometry.of_dist_eq (po_dist_smul hn g)).uniformContinuous
  refine
    { toEquiv := Φ
      error := M.error
      inverseError := M.inverseError
      forward_bound := pseudoIsometry_smul_comp hn a b⁻¹ M.forward_bound
      inverse_bound := pseudoIsometry_smul_comp hn b a⁻¹ M.inverse_bound
      uniform_toFun := (hUa b⁻¹).comp (M.uniform_toFun.comp (hUa a))
      uniform_invFun := (hUa a⁻¹).comp (M.uniform_invFun.comp (hUa b))
      equivariant := ?_
      shift := M.shift - Real.log (poConfFactor hn a ξ) + Real.log (poConfFactor hn b η)
      busemann_map := ?_ }
  · intro g x
    have h := M.equivariant (eP g) (a • x)
    have he : (eP.symm.trans (f.trans eQ)) (eP g) = eQ (f g) := by
      simp only [MulEquiv.trans_apply, eP.symm_apply_apply]
    rw [he] at h
    change M.toEquiv ((a * (g : PO n 1) * a⁻¹) • (a • x)) =
      (b * (f g : PO n 1) * b⁻¹) • M.toEquiv (a • x) at h
    simp only [mul_smul, inv_smul_smul] at h
    change b⁻¹ • M.toEquiv (a • ((g : PO n 1) • x)) =
      (f g : PO n 1) • (b⁻¹ • M.toEquiv (a • x))
    rw [h, inv_smul_smul]
  · intro x
    have hsource := po_busemann_smul hn a ξ x
    have htarget := po_busemann_smul hn b η (b⁻¹ • M.toEquiv (a • x))
    have hmiddle := M.busemann_map (a • x)
    change busemann ((poBoundaryMulAction hn).smul b η)
      (b • (b⁻¹ • M.toEquiv (a • x))) =
        busemann η (b⁻¹ • M.toEquiv (a • x)) - _ at htarget
    rw [hb, smul_inv_smul] at htarget
    rw [ha] at hsource
    change busemann ζ (a • x) = busemann ξ x - Real.log (poConfFactor hn a ξ) at hsource
    change busemann η (b⁻¹ • M.toEquiv (a • x)) = _
    linarith

theorem exists_cuspMap (hn : 1 ≤ n) (hdim : 3 ≤ n)
    (Γ Λ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (hΛ : IsDiscrete (SetLike.coe Λ))
    [hfdΓ : HasFundamentalDomain Γ (PO n 1)] [hfdΛ : HasFundamentalDomain Λ (PO n 1)]
    (hcovΓ : covolume Γ (PO n 1) ≠ ⊤) (hcovΛ : covolume Λ (PO n 1) ≠ ⊤)
    {ξ η : BoundaryH n} (hξ : IsCuspCenter hn Γ ξ) (hη : IsCuspCenter hn Λ η)
    (f : endStabilizer hn Γ {ξ} ≃* endStabilizer hn Λ {η}) :
    Nonempty (CuspMap hn f ξ η) := by
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨ε, hε, hgeom⟩ := exists_margulis_geometry_constant hn
    have hr : 0 < ε / 2 := by linarith
    have hre : ε / 2 < ε := by linarith
    have hcΓ (x : HUpper (m + 1)) :=
      OrbifoldStrata.closedSmallSubgroup_geometry hn Γ hre x (hgeom Γ hΓ x)
    have hcΛ (x : HUpper (m + 1)) :=
      OrbifoldStrata.closedSmallSubgroup_geometry hn Λ hre x (hgeom Λ hΛ x)
    obtain ⟨a, ha, hfixP, hcoP⟩ := @CuspCharts.exists_cobounded_chart m (by omega)
      Γ hΓ hfdΓ hcovΓ (ε / 2) ε hr hre (hgeom Γ hΓ) ξ (hξ.thinRegion_nonempty hΓ hr hcΓ)
    obtain ⟨b, hb, hfixQ, hcoQ⟩ := @CuspCharts.exists_cobounded_chart m (by omega)
      Λ hΛ hfdΛ hcovΛ (ε / 2) ε hr hre (hgeom Λ hΛ) η (hη.thinRegion_nonempty hΛ hr hcΛ)
    let eP := (MulAut.conj a).subgroupMap (endStabilizer hn Γ {ξ})
    let eQ := (MulAut.conj b).subgroupMap (endStabilizer hn Λ {η})
    obtain ⟨M⟩ := exists_normalized_cuspMap _ _
      (DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.isDiscrete_map_conj a (hΓ.mono inf_le_left))
      (DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.isDiscrete_map_conj b (hΛ.mono inf_le_left))
      hfixP hfixQ hcoP hcoQ (eP.symm.trans (f.trans eQ))
    exact ⟨M.ofCharts hn f a b ha hb⟩

theorem exists_cuspMap_for_iso (hn : 1 ≤ n) (hdim : 3 ≤ n)
    (Γ Λ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (hΛ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (hcovΓ : covolume Γ (PO n 1) ≠ ⊤) (hcovΛ : covolume Λ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) (ξ : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ}) :
    Nonempty (CuspMap hn (peripheralIso hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ)
      ξ.val (centerEquiv hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ).val) :=
  exists_cuspMap hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ ξ.property
    (centerEquiv hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ).property
    (peripheralIso hn hdim Γ Λ hΓ hΛ hcovΓ hcovΛ f ξ)

end DifferentialGeometry.CuspMaps
