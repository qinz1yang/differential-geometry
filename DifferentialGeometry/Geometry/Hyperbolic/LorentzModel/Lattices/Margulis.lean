/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.DirichletDomain
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.ThickPartCompactness
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.Zassenhaus
import DifferentialGeometry.Topology.Algebra.Group.CosetGrowth

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology Pointwise

namespace DifferentialGeometry.Margulis

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicTransitive

variable {n : ℕ}

def displacement (hn : 1 ≤ n) (g : PO n 1) : ℝ :=
  dist ((poMulAction hn).smul g basepointH) basepointH

theorem displacement_one (hn : 1 ≤ n) : displacement hn 1 = 0 := by
  have h : (poMulAction hn).smul (1 : PO n 1) (basepointH : HUpper n) = basepointH :=
    (poMulAction hn).one_smul _
  rw [displacement, h, dist_self]

theorem displacement_inv (hn : 1 ≤ n) (g : PO n 1) :
    displacement hn g⁻¹ = displacement hn g := by
  let := poMulAction hn
  change dist (g⁻¹ • (basepointH : HUpper n)) basepointH =
    dist (g • (basepointH : HUpper n)) basepointH
  calc
    dist (g⁻¹ • (basepointH : HUpper n)) basepointH
        = dist (g • (g⁻¹ • (basepointH : HUpper n))) (g • basepointH) :=
      (po_dist_smul hn g _ _).symm
    _ = dist basepointH (g • (basepointH : HUpper n)) := by rw [smul_inv_smul]
    _ = dist (g • (basepointH : HUpper n)) basepointH := dist_comm _ _

theorem displacement_mul_le (hn : 1 ≤ n) (g h : PO n 1) :
    displacement hn (g * h) ≤ displacement hn g + displacement hn h := by
  let := poMulAction hn
  change dist ((g * h) • (basepointH : HUpper n)) basepointH ≤
    dist (g • (basepointH : HUpper n)) basepointH +
      dist (h • (basepointH : HUpper n)) basepointH
  calc
    dist ((g * h) • (basepointH : HUpper n)) basepointH
        ≤ dist ((g * h) • (basepointH : HUpper n)) (g • basepointH) +
          dist (g • (basepointH : HUpper n)) basepointH := dist_triangle _ _ _
    _ = dist (h • (basepointH : HUpper n)) basepointH +
          dist (g • (basepointH : HUpper n)) basepointH := by
      rw [mul_smul, po_dist_smul hn g]
    _ = _ := add_comm _ _

theorem exists_displacement_cover (hn : 1 ≤ n) {U : Set (PO n 1)} (hU : U ∈ 𝓝 1) :
    ∃ (V : Set (PO n 1)) (F : Finset (PO n 1)), V⁻¹ * V ⊆ U ∧
      ∀ g : PO n 1, displacement hn g ≤ 1 → ∃ c ∈ F, g ∈ c • V := by
  obtain ⟨W, hW, _, hWinv, hWW⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  let V := interior W
  have hV1 : (1 : PO n 1) ∈ V := mem_interior_iff_mem_nhds.mpr hW
  have hVU : V⁻¹ * V ⊆ U := by
    apply (Set.mul_subset_mul ?_ (interior_subset (s := W))).trans hWW
    calc
      V⁻¹ ⊆ W⁻¹ := Set.inv_subset_inv.mpr interior_subset
      _ = W := hWinv
  have hC : IsCompact {g : PO n 1 | displacement hn g ≤ 1} :=
    DirichletDomain.isCompact_orbit_preimage hn 1
  have hcover : {g : PO n 1 | displacement hn g ≤ 1} ⊆ ⋃ c : PO n 1, c • V := by
    intro g _
    exact mem_iUnion.mpr ⟨g, 1, hV1, mul_one g⟩
  obtain ⟨F, hF⟩ := hC.elim_finite_subcover (fun c : PO n 1 => c • V)
    (fun c => isOpen_interior.smul c) hcover
  refine ⟨V, F, hVU, fun g hg => ?_⟩
  obtain ⟨c, hc⟩ := mem_iUnion.mp (hF hg)
  obtain ⟨hcF, hcg⟩ := mem_iUnion.mp hc
  exact ⟨c, hcF, hcg⟩

theorem inv_mul_mem_of_mem_translate {G : Type*} [Group G] {V : Set G} {a b c : G}
    (ha : a ∈ c • V) (hb : b ∈ c • V) : a⁻¹ * b ∈ V⁻¹ * V := by
  obtain ⟨v, hv, rfl⟩ := ha
  obtain ⟨w, hw, rfl⟩ := hb
  simpa only [smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left] using
    Set.mul_mem_mul (Set.inv_mem_inv.mpr hv) hw

def smallElements (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ) (x : HUpper n) :
    Set (PO n 1) :=
  {g | g ∈ Γ ∧ dist ((poMulAction hn).smul g x) x < ε}

def smallSubgroup (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ) (x : HUpper n) :
    Subgroup (PO n 1) :=
  Subgroup.closure (smallElements hn Γ ε x)

theorem smallSubgroup_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ) (x : HUpper n) :
    smallSubgroup hn Γ ε x ≤ Γ :=
  (Subgroup.closure_le Γ).mpr (fun _ hg => hg.1)

theorem mem_thickPart_iff_smallSubgroup_eq_bot (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (x : HUpper n) :
    x ∈ LatticeCompactness.thickPart hn Γ ε ↔ smallSubgroup hn Γ ε x = ⊥ := by
  constructor
  · intro hx
    apply le_antisymm _ bot_le
    apply (Subgroup.closure_le ⊥).mpr
    intro g hg
    change g = 1
    by_contra hne
    have hγ : (⟨g, hg.1⟩ : Γ) ≠ 1 :=
      fun h => hne (congrArg Subtype.val h)
    have hbound := hx ⟨g, hg.1⟩ hγ
    have hshort := hg.2
    rw [dist_comm] at hshort
    exact (not_lt_of_ge hbound) hshort
  · intro hbot γ hγ
    by_contra h
    have hmem : (γ : PO n 1) ∈ smallSubgroup hn Γ ε x :=
      Subgroup.subset_closure ⟨γ.property, by rw [dist_comm]; exact not_le.mp h⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hγ (Subtype.ext hmem)

theorem exists_margulis_at_basepoint (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Γ : Subgroup (PO n 1), IsDiscrete (SetLike.coe Γ) →
      Group.IsVirtuallyNilpotent (smallSubgroup hn Γ ε basepointH) := by
  let U := Zassenhaus.poNeighborhood n
  have hU : U ∈ 𝓝 (1 : PO n 1) :=
    Zassenhaus.isOpen_poNeighborhood.mem_nhds Zassenhaus.one_mem_poNeighborhood
  obtain ⟨V, F, hVU, hcover⟩ := exists_displacement_cover hn hU
  let ε : ℝ := 1 / ((F.card : ℝ) + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, fun Γ hΓ => ?_⟩
  let S := smallElements hn Γ ε basepointH
  let A := Subgroup.closure S
  have hAle : A ≤ Γ := smallSubgroup_le hn Γ ε basepointH
  have hAdisc : IsDiscrete (SetLike.coe A) := hΓ.mono hAle
  let H₀ := Subgroup.closure ((A : Set (PO n 1)) ∩ U)
  have hHle : H₀ ≤ A := (Subgroup.closure_le A).mpr inter_subset_left
  have hHnil : Group.IsNilpotent H₀ := Zassenhaus.isNilpotent_po_small hn A hAdisc
  let H := H₀.subgroupOf A
  have hHnil' : Group.IsNilpotent H :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hHle)).mpr hHnil
  refine ⟨H, hHnil', ?_⟩
  let T : Set A := A.subtype ⁻¹' S
  have hTinv : ∀ a ∈ T, a⁻¹ ∈ T := by
    intro a ha
    change (a : PO n 1) ∈ Γ ∧ displacement hn (a : PO n 1) < ε at ha
    change (a : PO n 1)⁻¹ ∈ Γ ∧ displacement hn (a : PO n 1)⁻¹ < ε
    exact ⟨Γ.inv_mem ha.1, by rw [displacement_inv]; exact ha.2⟩
  have hscale : (F.card : ℝ) * ε ≤ 1 := by
    change (F.card : ℝ) * (1 / ((F.card : ℝ) + 1)) ≤ 1
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (F.card : ℝ) + 1)).mpr
    linarith
  apply CosetGrowth.finiteIndex_of_cover T (Subgroup.closure_preimage_eq_top S)
    hTinv H (fun a : A => displacement hn a)
    (displacement_one hn) (fun a b => displacement_mul_le hn a b) hε.le
    (fun a ha => (show displacement hn (a : PO n 1) < ε from ha.2).le)
    F (fun c a => (a : PO n 1) ∈ c • V) hscale
    (fun a ha => hcover a ha)
  intro c a b ha hb
  change ((a⁻¹ * b : A) : PO n 1) ∈ H₀
  apply Subgroup.subset_closure
  exact ⟨(a⁻¹ * b : A).property, hVU (inv_mul_mem_of_mem_translate ha hb)⟩

theorem virtuallyNilpotent_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (hG : Group.IsVirtuallyNilpotent G) : Group.IsVirtuallyNilpotent G' := by
  obtain ⟨H, hHnil, hHfin⟩ := hG
  refine ⟨H.map e.toMonoidHom, (Group.isNilpotent_congr (e.subgroupMap H)).mp hHnil, ?_⟩
  refine ⟨?_⟩
  have he : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  rw [he]
  exact hHfin.index_ne_zero

theorem displacement_conj_basepoint (hn : 1 ≤ n) (g a : PO n 1) :
    displacement hn (g⁻¹ * a * g) =
      dist ((poMulAction hn).smul a ((poMulAction hn).smul g basepointH))
        ((poMulAction hn).smul g basepointH) := by
  have h := LatticeCompactness.displacement_conj hn g a basepointH
  calc
    displacement hn (g⁻¹ * a * g)
        = dist basepointH ((poMulAction hn).smul (g⁻¹ * a * g) basepointH) :=
      dist_comm _ _
    _ = dist ((poMulAction hn).smul g basepointH)
        ((poMulAction hn).smul a ((poMulAction hn).smul g basepointH)) := h.symm
    _ = _ := dist_comm _ _

theorem image_smallElements_conj (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ)
    (g : PO n 1) (x : HUpper n) (hx : (poMulAction hn).smul g basepointH = x) :
    (MulAut.conj g⁻¹) '' smallElements hn Γ ε x =
      smallElements hn (Γ.map (MulAut.conj g⁻¹).toMonoidHom) ε basepointH := by
  have hd (a : PO n 1) :
      displacement hn (MulAut.conj g⁻¹ a) = dist ((poMulAction hn).smul a x) x := by
    simpa only [MulAut.conj_apply, inv_inv, hx] using displacement_conj_basepoint hn g a
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Subgroup.mem_map.mpr ⟨a, ha.1, rfl⟩, ?_⟩
    change displacement hn (MulAut.conj g⁻¹ a) < ε
    rw [hd]
    exact ha.2
  · intro hb
    obtain ⟨a, haΓ, hab⟩ := Subgroup.mem_map.mp hb.1
    change MulAut.conj g⁻¹ a = b at hab
    refine ⟨a, ⟨haΓ, ?_⟩, hab⟩
    rw [← hd a, hab]
    exact hb.2

theorem exists_margulis_constant (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Γ : Subgroup (PO n 1), IsDiscrete (SetLike.coe Γ) →
      ∀ x : HUpper n, Group.IsVirtuallyNilpotent (smallSubgroup hn Γ ε x) := by
  obtain ⟨ε, hε, hbase⟩ := exists_margulis_at_basepoint hn
  refine ⟨ε, hε, fun Γ hΓ x => ?_⟩
  obtain ⟨g, hg⟩ := exists_po_smul_basepoint hn x
  let e := MulAut.conj g⁻¹
  let Γ' := Γ.map e.toMonoidHom
  have hΓ' : IsDiscrete (SetLike.coe Γ') := DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.isDiscrete_map_conj g⁻¹ hΓ
  have hmap : (smallSubgroup hn Γ ε x).map e.toMonoidHom =
      smallSubgroup hn Γ' ε basepointH := by
    simp only [smallSubgroup, MonoidHom.map_closure]
    exact congrArg Subgroup.closure (image_smallElements_conj hn Γ ε g x hg)
  have hvirt : Group.IsVirtuallyNilpotent ((smallSubgroup hn Γ ε x).map e.toMonoidHom) := by
    rw [hmap]
    exact hbase Γ' hΓ'
  exact virtuallyNilpotent_of_mulEquiv (e.subgroupMap (smallSubgroup hn Γ ε x)).symm hvirt

end DifferentialGeometry.Margulis
