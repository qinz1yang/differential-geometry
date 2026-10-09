/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CrossSections

noncomputable section

open Set MeasureTheory Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.CuspCharts

open Hyperbolic HyperbolicAction HyperbolicBoundary MobiusBoundary Horospherical
open Busemann BusemannCocycle BoundaryStabilizer ElementaryEnds
open OrbifoldThinRegions CuspCrossSections

variable {m n : ℕ}

theorem invert_po_smul_ptInfty :
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul
      (QuotientGroup.mk' _ invertLor : PO (m + 1) 1) ptInfty =
        horo (0 : Fin m → ℝ) := by
  let := poBoundaryMulAction (by omega : 1 ≤ m + 1)
  change (QuotientGroup.mk' _ invertLor : PO (m + 1) 1) •
    (ptInfty : BoundaryH (m + 1)) = horo (0 : Fin m → ℝ)
  rw [po_boundary_smul_mk]
  apply BoundaryH.ext
  change boundaryRep (matOf invertLor *ᵥ (ptInfty : BoundaryH (m + 1)).val) =
    boundaryRep (horoVec (0 : Fin m → ℝ))
  have he : matOf invertLor *ᵥ (ptInfty : BoundaryH (m + 1)).val =
      (2 : ℝ) • horoVec (0 : Fin m → ℝ) := by
    funext i
    rw [invertLor_matOf, signMat_mulVec_apply]
    rcases i with j | j
    · by_cases hj : j = Fin.last m
      · subst j
        norm_num [ptInfty_val_last, horoVec_last, normSq]
      · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
        simp [ptInfty_val_castSucc, horoVec_castSucc]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [ptInfty_val_time, horoVec_time, normSq]
  rw [he, boundaryRep_smul _ (by norm_num : (2 : ℝ) ≠ 0)]

theorem exists_normalizing_element (ξ : BoundaryH (m + 1)) :
    ∃ a : PO (m + 1) 1,
      (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul a ξ = ptInfty := by
  let ρ := poBoundaryMulAction (by omega : 1 ≤ m + 1)
  by_cases hξ : ξ = ptInfty
  · exact ⟨1, (ρ.one_smul ξ).trans hξ⟩
  obtain ⟨x, rfl⟩ := exists_horo_eq_of_ne_ptInfty ξ hξ
  let a : PO (m + 1) 1 := QuotientGroup.mk' _ (transLor x) * QuotientGroup.mk' _ invertLor
  have ha : ρ.smul a ptInfty = horo x := by
    have hi : ρ.smul (QuotientGroup.mk' _ invertLor) ptInfty = horo (0 : Fin m → ℝ) :=
      invert_po_smul_ptInfty
    calc
      ρ.smul a ptInfty = ρ.smul (QuotientGroup.mk' _ (transLor x))
          (ρ.smul (QuotientGroup.mk' _ invertLor) ptInfty) := ρ.mul_smul _ _ _
      _ = ρ.smul (QuotientGroup.mk' _ (transLor x)) (horo 0) :=
        congrArg (ρ.smul (QuotientGroup.mk' _ (transLor x))) hi
      _ = horo x := (trans_po_smul_horo x 0).trans (by simp only [zero_add])
  refine ⟨a⁻¹, ?_⟩
  calc
    ρ.smul a⁻¹ (horo x) = ρ.smul a⁻¹ (ρ.smul a ptInfty) := congrArg (ρ.smul a⁻¹) ha.symm
    _ = ρ.smul (a⁻¹ * a) ptInfty := (ρ.mul_smul _ _ _).symm
    _ = ptInfty := by rw [inv_mul_cancel]; exact ρ.one_smul _

theorem conjugate_horospherical (P : Subgroup (PO (m + 1) 1))
    (ξ : BoundaryH (m + 1))
    (hfix : ∀ g : P,
      (poBoundaryMulAction (by omega)).smul (g : PO (m + 1) 1) ξ = ξ ∧
        poConfFactor (by omega) (g : PO (m + 1) 1) ξ = 1)
    (a : PO (m + 1) 1)
    (ha : (poBoundaryMulAction (by omega)).smul a ξ = ptInfty) :
    ∀ g : P.map (MulAut.conj a).toMonoidHom,
      (poBoundaryMulAction (by omega)).smul (g : PO (m + 1) 1) ptInfty = ptInfty ∧
        poConfFactor (by omega) (g : PO (m + 1) 1) ptInfty = 1 := by
  intro g
  obtain ⟨d, hd, he⟩ := g.property
  have h := horospherical_conj (by omega) a d ξ (hfix ⟨d, hd⟩).1 (hfix ⟨d, hd⟩).2
  change a * d * a⁻¹ = (g : PO (m + 1) 1) at he
  rwa [ha, he] at h

theorem compact_horosphere_core_conj (P : Subgroup (PO (m + 1) 1))
    (ξ : BoundaryH (m + 1)) (a : PO (m + 1) 1)
    (ha : (poBoundaryMulAction (by omega)).smul a ξ = ptInfty)
    (hcore : ∀ c : ℝ, ∃ K : Set (HUpper (m + 1)), IsCompact K ∧
      ∀ p ∈ horosphere ξ c, ∃ g : P,
        (poMulAction (by omega)).smul (g : PO (m + 1) 1) p ∈ K) :
    ∃ K : Set (HUpper (m + 1)), IsCompact K ∧
      ∀ p ∈ horosphere (ptInfty : BoundaryH (m + 1)) 0,
        ∃ g : P.map (MulAut.conj a).toMonoidHom,
          (poMulAction (by omega)).smul (g : PO (m + 1) 1) p ∈ K := by
  let := poMulAction (by omega : 1 ≤ m + 1)
  obtain ⟨K, hK, hcover⟩ := hcore (Real.log (poConfFactor (by omega) a ξ))
  refine ⟨(fun x : HUpper (m + 1) => a • x) '' K,
    hK.image (interiorHomeomorph (by omega) a).continuous, fun p hp => ?_⟩
  have hshift := po_busemann_smul (by omega) a ξ (a⁻¹ • p)
  change busemann ((poBoundaryMulAction (by omega)).smul a ξ) (a • (a⁻¹ • p)) =
    busemann ξ (a⁻¹ • p) - _ at hshift
  rw [ha, smul_inv_smul] at hshift
  have hp' : a⁻¹ • p ∈ horosphere ξ (Real.log (poConfFactor (by omega) a ξ)) := by
    change busemann ξ (a⁻¹ • p) = _
    change busemann ptInfty p = 0 at hp
    linarith
  obtain ⟨g, hg⟩ := hcover _ hp'
  refine ⟨⟨a * g * a⁻¹, ⟨g, g.property, rfl⟩⟩, (g : PO (m + 1) 1) • (a⁻¹ • p),
    hg, ?_⟩
  change a • ((g : PO (m + 1) 1) • (a⁻¹ • p)) = (a * g * a⁻¹) • p
  simp only [mul_smul]

theorem exists_cobounded_chart (hm : 1 ≤ m)
    (Γ : Subgroup (PO (m + 1) 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [hfd : @HasFundamentalDomain Γ (PO (m + 1) 1) _
      (MulAction.compHom (PO (m + 1) 1) Γ.subtype).toSMul _ volume]
    (hcov : @covolume Γ (PO (m + 1) 1) _
      (MulAction.compHom (PO (m + 1) 1) Γ.subtype).toSMul _ volume ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper (m + 1), ElementaryGeometry (by omega)
      (Margulis.smallSubgroup (by omega) Γ ε x))
    {ξ : BoundaryH (m + 1)}
    (hξ : (thinRegion (by omega : 1 ≤ m + 1) Γ r {ξ}).Nonempty) :
    let P := endStabilizer (by omega : 1 ≤ m + 1) Γ {ξ}
    ∃ a : PO (m + 1) 1,
      (poBoundaryMulAction (by omega)).smul a ξ = ptInfty ∧
      ∃ hfix : ∀ g : P.map (MulAut.conj a).toMonoidHom,
        (poBoundaryMulAction (by omega)).smul (g : PO (m + 1) 1) ptInfty = ptInfty ∧
          poConfFactor (by omega) (g : PO (m + 1) 1) ptInfty = 1,
        DifferentialGeometry.CrystallographicActions.CoboundedOrbit (HorosphereGroups.affineAction _ hfix) := by
  let P := endStabilizer (by omega : 1 ≤ m + 1) Γ {ξ}
  obtain ⟨a, ha⟩ := exists_normalizing_element ξ
  let hfix := conjugate_horospherical P ξ
    (horospherical_endStabilizer (by omega) Γ hΓ hξ) a ha
  refine ⟨a, ha, hfix, cobounded_of_compact_horosphere_core _ hfix ?_⟩
  apply compact_horosphere_core_conj P ξ a ha
  intro c
  obtain ⟨K, hK, _, hcover⟩ :=
    @exists_compact_horosphere_core (m + 1) (by omega) (by omega) Γ hΓ hfd hcov r ε hr hre hgeom ξ hξ c
  refine ⟨K, hK, fun p hp => ?_⟩
  obtain ⟨g, hgfix, hgK⟩ := hcover p hp
  exact ⟨⟨g, (mem_endStabilizer_singleton (by omega) Γ ξ g).mpr ⟨g.property, hgfix⟩⟩, hgK⟩

theorem exists_full_translation_chart (hm : 1 ≤ m)
    (Γ : Subgroup (PO (m + 1) 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [hfd : @HasFundamentalDomain Γ (PO (m + 1) 1) _
      (MulAction.compHom (PO (m + 1) 1) Γ.subtype).toSMul _ volume]
    (hcov : @covolume Γ (PO (m + 1) 1) _
      (MulAction.compHom (PO (m + 1) 1) Γ.subtype).toSMul _ volume ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper (m + 1), ElementaryGeometry (by omega)
      (Margulis.smallSubgroup (by omega) Γ ε x))
    {ξ : BoundaryH (m + 1)}
    (hξ : (thinRegion (by omega : 1 ≤ m + 1) Γ r {ξ}).Nonempty) :
    let P := endStabilizer (by omega : 1 ≤ m + 1) Γ {ξ}
    ∃ (a : PO (m + 1) 1) (D : Submodule ℤ (Horizontal m)) (hD : DiscreteTopology D),
      letI := hD
      (poBoundaryMulAction (by omega)).smul a ξ = ptInfty ∧ IsZLattice ℝ D ∧
        TranslationLattices.latticeGroup D ≤ P.map (MulAut.conj a).toMonoidHom ∧
        ((TranslationLattices.latticeGroup D).subgroupOf
          (P.map (MulAut.conj a).toMonoidHom)).FiniteIndex := by
  obtain ⟨a, ha, hfix, hco⟩ := @exists_cobounded_chart m hm Γ hΓ hfd hcov r ε hr hre hgeom ξ hξ
  obtain ⟨D, hD, hfull, hle, hindex⟩ :=
    HorosphereGroups.exists_full_translation_lattice_of_cobounded _ hfix
      (DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.isDiscrete_map_conj a (hΓ.mono inf_le_left)) hco
  exact ⟨a, D, hD, ha, hfull, hle, hindex⟩

theorem exists_virtual_translation_lattice (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [hfd : HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {r ε : ℝ} (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ : BoundaryH n} (hξ : (thinRegion hn Γ r {ξ}).Nonempty) :
    let P := endStabilizer hn Γ {ξ}
    ∃ (D : Submodule ℤ (Horizontal (n - 1))) (hD : DiscreteTopology D),
      letI := hD
      IsZLattice ℝ D ∧ ∃ H : Subgroup P, H.FiniteIndex ∧ Nonempty (Multiplicative D ≃* H) := by
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨a, D, hD, _, hfull, hle, hindex⟩ :=
      @exists_full_translation_chart m (by omega) Γ hΓ hfd hcov r ε hr hre hgeom ξ hξ
    let P := endStabilizer hn Γ {ξ}
    let e := (MulAut.conj a).subgroupMap P
    let T := (TranslationLattices.latticeGroup D).subgroupOf (P.map (MulAut.conj a).toMonoidHom)
    let H := T.map e.symm.toMonoidHom
    have hH : H.FiniteIndex := ⟨by
      rw [show H.index = T.index from T.index_map_equiv e.symm]
      exact hindex.index_ne_zero⟩
    exact ⟨D, hD, hfull, H, hH, ⟨((TranslationLattices.latticeEquiv D).trans
      (Subgroup.subgroupOfEquivOfLe hle).symm).trans (e.symm.subgroupMap T)⟩⟩

end DifferentialGeometry.CuspCharts
