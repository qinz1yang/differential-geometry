/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.GromovProduct
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.DirichletDomain
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.EquivariantMaps.Existence

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.UniformPseudoIsometry

open DifferentialGeometry.Hyperbolic DifferentialGeometry.HyperbolicFaithful DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.EquivariantMap DifferentialGeometry.PseudoIsometry

variable {n : ℕ}

def ActsCocompactly (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) : Prop :=
  letI := poMulAction hn
  ∃ D : ℝ, ∀ x : HUpper n, ∃ γ : Γ,
    dist x ((γ : PO n 1) • (basepointH : HUpper n)) ≤ D

section MilnorSvarc

variable (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1)) (f : Γ ≃* Λ)
  (disc_Γ : IsDiscrete (SetLike.coe Γ)) (hcoΓ : ActsCocompactly hn Γ)

noncomputable def covD : ℝ := Classical.choose hcoΓ

theorem covD_spec :
    letI := poMulAction hn
    ∀ x : HUpper n, ∃ γ : Γ,
      dist x ((γ : PO n 1) • (basepointH : HUpper n)) ≤ covD hn Γ hcoΓ := by
  let := poMulAction hn
  exact Classical.choose_spec hcoΓ

theorem covD_nonneg : 0 ≤ covD hn Γ hcoΓ := by
  let := poMulAction hn
  obtain ⟨γ, hγ⟩ := covD_spec hn Γ hcoΓ basepointH
  exact dist_nonneg.trans hγ

theorem dist_basepoint_inv_smul (γ : Γ) (y : HUpper n) :
    letI := poMulAction hn
    letI := subAction hn Γ
    dist basepointH ((γ⁻¹ : Γ) • y)
      = dist y ((γ : PO n 1) • (basepointH : HUpper n)) := by
  let := poMulAction hn
  let := subAction hn Γ
  rw [subAction_smul, Subgroup.coe_inv]
  have h4 := po_dist_smul hn (γ : PO n 1) (((γ : PO n 1)⁻¹) • y) basepointH
  rw [smul_smul, mul_inv_cancel, one_smul] at h4
  rw [dist_comm]
  exact h4.symm

theorem exists_bounded_rep :
    letI := poMulAction hn
    letI := subAction hn Γ
    ∀ q : MulAction.orbitRel.Quotient Γ (HUpper n),
      ∃ r : HUpper n, (⟦r⟧ : MulAction.orbitRel.Quotient Γ (HUpper n)) = q
        ∧ dist basepointH r ≤ covD hn Γ hcoΓ := by
  let := poMulAction hn
  let := subAction hn Γ
  intro q
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  obtain ⟨γ, hγ⟩ := covD_spec hn Γ hcoΓ y
  refine ⟨(γ⁻¹ : Γ) • y, ?_, ?_⟩
  · exact Quotient.eq'.mpr (MulAction.mem_orbit y (γ⁻¹))
  · rw [dist_basepoint_inv_smul hn Γ γ y]
    exact hγ

noncomputable def bRep (x : HUpper n) : HUpper n :=
  letI := poMulAction hn
  letI := subAction hn Γ
  Classical.choose (exists_bounded_rep hn Γ hcoΓ
    (⟦x⟧ : MulAction.orbitRel.Quotient Γ (HUpper n)))

theorem bRep_class (x : HUpper n) :
    letI := poMulAction hn
    letI := subAction hn Γ
    (⟦bRep hn Γ hcoΓ x⟧ : MulAction.orbitRel.Quotient Γ (HUpper n)) = ⟦x⟧ := by
  let := poMulAction hn
  let := subAction hn Γ
  exact (Classical.choose_spec (exists_bounded_rep hn Γ hcoΓ
    (⟦x⟧ : MulAction.orbitRel.Quotient Γ (HUpper n)))).1

theorem bRep_dist (x : HUpper n) :
    letI := poMulAction hn
    dist basepointH (bRep hn Γ hcoΓ x) ≤ covD hn Γ hcoΓ := by
  let := poMulAction hn
  let := subAction hn Γ
  exact (Classical.choose_spec (exists_bounded_rep hn Γ hcoΓ
    (⟦x⟧ : MulAction.orbitRel.Quotient Γ (HUpper n)))).2

theorem bRep_smul (δ : Γ) (x : HUpper n) :
    letI := poMulAction hn
    letI := subAction hn Γ
    bRep hn Γ hcoΓ (δ • x) = bRep hn Γ hcoΓ x := by
  let := poMulAction hn
  let := subAction hn Γ
  change Classical.choose (exists_bounded_rep hn Γ hcoΓ
      (⟦δ • x⟧ : MulAction.orbitRel.Quotient Γ (HUpper n)))
    = Classical.choose (exists_bounded_rep hn Γ hcoΓ
      (⟦x⟧ : MulAction.orbitRel.Quotient Γ (HUpper n)))
  have h : (⟦δ • x⟧ : MulAction.orbitRel.Quotient Γ (HUpper n)) = ⟦x⟧ :=
    Quotient.eq'.mpr (MulAction.mem_orbit x δ)
  rw [h]

theorem exists_smul_bRep (x : HUpper n) :
    letI := poMulAction hn
    letI := subAction hn Γ
    ∃ γ : Γ, γ • bRep hn Γ hcoΓ x = x := by
  let := poMulAction hn
  let := subAction hn Γ
  have h : bRep hn Γ hcoΓ x ∈ MulAction.orbit Γ x :=
    Quotient.eq'.mp (bRep_class hn Γ hcoΓ x)
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp h
  exact ⟨γ⁻¹, by rw [← hγ, smul_smul, inv_mul_cancel, one_smul]⟩

noncomputable def bGamma (x : HUpper n) : Γ :=
  letI := poMulAction hn
  letI := subAction hn Γ
  Classical.choose (exists_smul_bRep hn Γ hcoΓ x)

theorem bGamma_spec (x : HUpper n) :
    letI := poMulAction hn
    letI := subAction hn Γ
    bGamma hn Γ hcoΓ x • bRep hn Γ hcoΓ x = x := by
  let := poMulAction hn
  let := subAction hn Γ
  exact Classical.choose_spec (exists_smul_bRep hn Γ hcoΓ x)

noncomputable def shortFinset (R : ℝ) : Finset ↥Γ :=
  letI := poMulAction hn
  (DirichletDomain.finite_setOf_coe_le hn Γ disc_Γ R).toFinset

theorem mem_shortFinset (R : ℝ) (γ : Γ) :
    letI := poMulAction hn
    γ ∈ shortFinset hn Γ disc_Γ R ↔
      dist ((γ : PO n 1) • (basepointH : HUpper n)) basepointH ≤ R := by
  let := poMulAction hn
  exact Set.Finite.mem_toFinset _

noncomputable def RB : ℝ :=
  letI := poMulAction hn
  ∑ γ ∈ shortFinset hn Γ disc_Γ (2 * covD hn Γ hcoΓ),
    dist ((fpo Γ Λ f γ : PO n 1) • (basepointH : HUpper n)) basepointH

noncomputable def R1 : ℝ :=
  letI := poMulAction hn
  ∑ γ ∈ shortFinset hn Γ disc_Γ (2 * covD hn Γ hcoΓ + 1),
    dist ((fpo Γ Λ f γ : PO n 1) • (basepointH : HUpper n)) basepointH

theorem RB_nonneg : 0 ≤ RB hn Γ Λ f disc_Γ hcoΓ := by
  let := poMulAction hn
  exact Finset.sum_nonneg fun γ _ => dist_nonneg

theorem R1_nonneg : 0 ≤ R1 hn Γ Λ f disc_Γ hcoΓ := by
  let := poMulAction hn
  exact Finset.sum_nonneg fun γ _ => dist_nonneg

theorem dist_fpo_le_sum {R : ℝ} (γ : Γ) :
    letI := poMulAction hn
    dist ((γ : PO n 1) • (basepointH : HUpper n)) basepointH ≤ R →
      dist ((fpo Γ Λ f γ : PO n 1) • (basepointH : HUpper n)) basepointH
        ≤ ∑ δ ∈ shortFinset hn Γ disc_Γ R,
          dist ((fpo Γ Λ f δ : PO n 1) • (basepointH : HUpper n)) basepointH := by
  let := poMulAction hn
  intro hγ
  exact Finset.single_le_sum
    (s := shortFinset hn Γ disc_Γ R)
    (f := fun δ : ↥Γ => dist ((fpo Γ Λ f δ : PO n 1) • basepointH) basepointH)
    (fun δ _ => dist_nonneg) ((mem_shortFinset hn Γ disc_Γ R γ).mpr hγ)

theorem stabilizer_mem_shortFinset {r : HUpper n}
    (hr : dist basepointH r ≤ covD hn Γ hcoΓ) (s : Γ)
    (hs : s ∈ @MulAction.stabilizer Γ (HUpper n) _ (subAction hn Γ) r) :
    letI := poMulAction hn
    dist ((s : PO n 1) • (basepointH : HUpper n)) basepointH ≤ 2 * covD hn Γ hcoΓ := by
  let := poMulAction hn
  let := subAction hn Γ
  rw [MulAction.mem_stabilizer_iff] at hs
  have hsr : (s : PO n 1) • r = r := by rw [← subAction_smul hn Γ s r]; exact hs
  calc dist ((s : PO n 1) • basepointH) basepointH
      ≤ dist ((s : PO n 1) • basepointH) ((s : PO n 1) • r)
        + dist ((s : PO n 1) • r) basepointH := dist_triangle _ _ _
    _ = dist basepointH r + dist ((s : PO n 1) • r) basepointH := by
        rw [po_dist_smul hn (s : PO n 1) basepointH r]
    _ = dist basepointH r + dist r basepointH := by rw [hsr]
    _ ≤ covD hn Γ hcoΓ + covD hn Γ hcoΓ :=
        add_le_add hr (by rw [dist_comm]; exact hr)
    _ = 2 * covD hn Γ hcoΓ := by ring

noncomputable def bFix (r : HUpper n) : HUpper n :=
  letI := finite_stabImage hn Γ Λ f disc_Γ r
  letI := Fintype.ofFinite ↥(stabImage hn Γ Λ f r)
  Classical.choose
    (exists_fixed_point_of_finite_subgroup hn (stabImage hn Γ Λ f r))

theorem bFix_fixed (r : HUpper n) (s : Γ)
    (hs : s ∈ @MulAction.stabilizer Γ (HUpper n) _ (subAction hn Γ) r) :
    letI := poMulAction hn
    fpo Γ Λ f s • bFix hn Γ Λ f disc_Γ r = bFix hn Γ Λ f disc_Γ r := by
  let := poMulAction hn
  let := finite_stabImage hn Γ Λ f disc_Γ r
  let := Fintype.ofFinite ↥(stabImage hn Γ Λ f r)
  have hspec := (Classical.choose_spec
    (exists_fixed_point_of_finite_subgroup hn (stabImage hn Γ Λ f r))).1
  apply hspec
  change Λ.subtype (f s) ∈ stabImage hn Γ Λ f r
  exact Subgroup.mem_map.mpr ⟨f s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩, rfl⟩

theorem bFix_mem (r : HUpper n) (f₀ : ↥(stabImage hn Γ Λ f r)) :
    letI := poMulAction hn
    letI := finite_stabImage hn Γ Λ f disc_Γ r
    letI := Fintype.ofFinite ↥(stabImage hn Γ Λ f r)
    dist (bFix hn Γ Λ f disc_Γ r) ((f₀ : PO n 1) • (basepointH : HUpper n))
      ≤ orbitRadius hn (stabImage hn Γ Λ f r) := by
  let := poMulAction hn
  let := finite_stabImage hn Γ Λ f disc_Γ r
  let := Fintype.ofFinite ↥(stabImage hn Γ Λ f r)
  exact (Classical.choose_spec
    (exists_fixed_point_of_finite_subgroup hn (stabImage hn Γ Λ f r))).2 f₀

theorem dist_basepoint_le_RB_of_mem_stabImage (r : HUpper n)
    (hr : dist basepointH r ≤ covD hn Γ hcoΓ) (f₀ : ↥(stabImage hn Γ Λ f r)) :
    letI := poMulAction hn
    dist (basepointH : HUpper n) ((f₀ : PO n 1) • (basepointH : HUpper n))
      ≤ RB hn Γ Λ f disc_Γ hcoΓ := by
  let := poMulAction hn
  obtain ⟨x, hxM, hfp⟩ := Subgroup.mem_map.mp f₀.property
  obtain ⟨s, hsstab, hfs⟩ := Subgroup.mem_map.mp hxM
  have hmem := stabilizer_mem_shortFinset hn Γ hcoΓ hr s hsstab
  have hle := dist_fpo_le_sum hn Γ Λ f disc_Γ s hmem
  have h2 : (f₀ : PO n 1) = fpo Γ Λ f s := by
    rw [← hfp, ← hfs]
    rfl
  rw [h2, dist_comm]
  exact hle

theorem orbitRadius_stabImage_le (r : HUpper n)
    (hr : dist basepointH r ≤ covD hn Γ hcoΓ) :
    letI := poMulAction hn
    letI := finite_stabImage hn Γ Λ f disc_Γ r
    letI := Fintype.ofFinite ↥(stabImage hn Γ Λ f r)
    orbitRadius hn (stabImage hn Γ Λ f r) ≤ RB hn Γ Λ f disc_Γ hcoΓ := by
  let := poMulAction hn
  let := finite_stabImage hn Γ Λ f disc_Γ r
  let := Fintype.ofFinite ↥(stabImage hn Γ Λ f r)
  change Finset.univ.sup' ⟨1, Finset.mem_univ 1⟩
      (fun f₀ : ↥(stabImage hn Γ Λ f r) =>
        dist basepointH ((f₀ : PO n 1) • basepointH)) ≤ RB hn Γ Λ f disc_Γ hcoΓ
  exact Finset.sup'_le _ _
    (fun f₀ _ => dist_basepoint_le_RB_of_mem_stabImage hn Γ Λ f disc_Γ hcoΓ r hr f₀)

theorem bFix_dist_le (r : HUpper n) (hr : dist basepointH r ≤ covD hn Γ hcoΓ) :
    letI := poMulAction hn
    dist (bFix hn Γ Λ f disc_Γ r) basepointH ≤ RB hn Γ Λ f disc_Γ hcoΓ := by
  let := poMulAction hn
  have h := bFix_mem hn Γ Λ f disc_Γ r (1 : ↥(stabImage hn Γ Λ f r))
  rw [Subgroup.coe_one, one_smul] at h
  exact h.trans (orbitRadius_stabImage_le hn Γ Λ f disc_Γ hcoΓ r hr)

noncomputable def bPhi (x : HUpper n) : HUpper n :=
  letI := poMulAction hn
  fpo Γ Λ f (bGamma hn Γ hcoΓ x) • bFix hn Γ Λ f disc_Γ (bRep hn Γ hcoΓ x)

theorem bPhi_isFEquivariant :
    IsFEquivariant f hn (bPhi hn Γ Λ f disc_Γ hcoΓ) := by
  let := poMulAction hn
  let := subAction hn Γ
  intro δ x
  change bPhi hn Γ Λ f disc_Γ hcoΓ (δ • x)
    = ((f δ : Λ) : PO n 1) • bPhi hn Γ Λ f disc_Γ hcoΓ x
  set r : HUpper n := bRep hn Γ hcoΓ x with hrdef
  set γ₁ : Γ := bGamma hn Γ hcoΓ (δ • x)
  set γ₂ : Γ := bGamma hn Γ hcoΓ x
  have hγ₁ : γ₁ • r = δ • x := by
    have h := bGamma_spec hn Γ hcoΓ (δ • x)
    rw [bRep_smul hn Γ hcoΓ δ x] at h
    exact h
  have hγ₂ : γ₂ • r = x := bGamma_spec hn Γ hcoΓ x
  have hstab : ((δ * γ₂)⁻¹ * γ₁ : Γ) ∈ MulAction.stabilizer Γ r := by
    rw [MulAction.mem_stabilizer_iff]
    rw [subAction_smul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, mul_smul]
    have e2 : (γ₁ : PO n 1) • r = (δ : PO n 1) • x := by
      rw [← subAction_smul hn Γ γ₁ r, ← subAction_smul hn Γ δ x]
      exact hγ₁
    have hγ₂' : (γ₂ : PO n 1) • r = x := by
      rw [← subAction_smul]
      exact hγ₂
    have e3 : (δ : PO n 1) • x = ((δ : PO n 1) * (γ₂ : PO n 1)) • r := by
      rw [← hγ₂', smul_smul]
    rw [e2, e3, smul_smul, inv_mul_cancel, one_smul]
  have hfix := bFix_fixed hn Γ Λ f disc_Γ r _ hstab
  have hγ₁eq : fpo Γ Λ f γ₁ • bFix hn Γ Λ f disc_Γ r
      = fpo Γ Λ f (δ * γ₂) • bFix hn Γ Λ f disc_Γ r := by
    have h1 : fpo Γ Λ f (((δ * γ₂)⁻¹ * γ₁ : Γ)) • (bFix hn Γ Λ f disc_Γ r)
        = bFix hn Γ Λ f disc_Γ r := hfix
    rw [map_mul, map_inv] at h1
    have h2 : fpo Γ Λ f (δ * γ₂) •
        (((fpo Γ Λ f (δ * γ₂))⁻¹ * fpo Γ Λ f γ₁) • bFix hn Γ Λ f disc_Γ r)
        = fpo Γ Λ f γ₁ • bFix hn Γ Λ f disc_Γ r := by
      rw [smul_smul, mul_inv_cancel_left]
    rw [h1] at h2
    exact h2.symm
  change fpo Γ Λ f γ₁ • bFix hn Γ Λ f disc_Γ (bRep hn Γ hcoΓ (δ • x))
    = ((f δ : Λ) : PO n 1) • (fpo Γ Λ f γ₂ • bFix hn Γ Λ f disc_Γ (bRep hn Γ hcoΓ x))
  rw [bRep_smul hn Γ hcoΓ δ x, ← hrdef, hγ₁eq]
  show fpo Γ Λ f (δ * γ₂) • bFix hn Γ Λ f disc_Γ r
    = ((f δ : Λ) : PO n 1) • (fpo Γ Λ f γ₂ • bFix hn Γ Λ f disc_Γ r)
  rw [map_mul, mul_smul]
  rfl

noncomputable def C1 : ℝ := 2 * RB hn Γ Λ f disc_Γ hcoΓ + R1 hn Γ Λ f disc_Γ hcoΓ

theorem C1_nonneg : 0 ≤ C1 hn Γ Λ f disc_Γ hcoΓ := by
  let := poMulAction hn
  have h1 := RB_nonneg hn Γ Λ f disc_Γ hcoΓ
  have h2 := R1_nonneg hn Γ Λ f disc_Γ hcoΓ
  unfold C1
  linarith

theorem bGamma_ratio_mem (u v : HUpper n) :
    letI := poMulAction hn
    dist u v ≤ 1 →
      dist (((((bGamma hn Γ hcoΓ u)⁻¹ * bGamma hn Γ hcoΓ v) : Γ) : PO n 1)
        • (basepointH : HUpper n)) basepointH
      ≤ 2 * covD hn Γ hcoΓ + 1 := by
  let := poMulAction hn
  let := subAction hn Γ
  intro huv
  set γu : Γ := bGamma hn Γ hcoΓ u
  set γv : Γ := bGamma hn Γ hcoΓ v
  set ru : HUpper n := bRep hn Γ hcoΓ u
  set rv : HUpper n := bRep hn Γ hcoΓ v
  have hγu : (γu : PO n 1) • ru = u := by
    rw [← subAction_smul hn Γ γu ru]; exact bGamma_spec hn Γ hcoΓ u
  have hγv : (γv : PO n 1) • rv = v := by
    rw [← subAction_smul hn Γ γv rv]; exact bGamma_spec hn Γ hcoΓ v
  have hru : dist (basepointH : HUpper n) ru ≤ covD hn Γ hcoΓ := bRep_dist hn Γ hcoΓ u
  have hrv : dist (basepointH : HUpper n) rv ≤ covD hn Γ hcoΓ := bRep_dist hn Γ hcoΓ v
  have hcoe : (((γu⁻¹ * γv : Γ) : PO n 1)) = (γu : PO n 1)⁻¹ * (γv : PO n 1) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe]
  have hswap : dist (((γu : PO n 1)⁻¹ * (γv : PO n 1)) • (basepointH : HUpper n))
        (basepointH : HUpper n)
      = dist ((γv : PO n 1) • (basepointH : HUpper n)) ((γu : PO n 1) • basepointH) := by
    have h4 := po_dist_smul hn (γu : PO n 1)
      (((γu : PO n 1)⁻¹ * (γv : PO n 1)) • (basepointH : HUpper n)) basepointH
    rw [smul_smul, ← mul_assoc, mul_inv_cancel, one_mul] at h4
    exact h4.symm
  rw [hswap]
  have h1 : dist ((γv : PO n 1) • (basepointH : HUpper n)) v ≤ covD hn Γ hcoΓ := by
    have h := po_dist_smul hn (γv : PO n 1) (basepointH : HUpper n) rv
    rw [hγv] at h
    rw [h]; exact hrv
  have h2 : dist u ((γu : PO n 1) • (basepointH : HUpper n)) ≤ covD hn Γ hcoΓ := by
    have h := po_dist_smul hn (γu : PO n 1) ru (basepointH : HUpper n)
    rw [hγu] at h
    rw [h, dist_comm]; exact hru
  have h3 : dist v u ≤ 1 := by rw [dist_comm]; exact huv
  have htri := dist_triangle ((γv : PO n 1) • (basepointH : HUpper n)) v
    ((γu : PO n 1) • (basepointH : HUpper n))
  have htri2 := dist_triangle v u ((γu : PO n 1) • (basepointH : HUpper n))
  have hD := covD_nonneg hn Γ hcoΓ
  linarith [htri, htri2, h1, h3, h2]

theorem bPhi_one_close (u v : HUpper n) :
    letI := poMulAction hn
    dist u v ≤ 1 →
      dist (bPhi hn Γ Λ f disc_Γ hcoΓ u) (bPhi hn Γ Λ f disc_Γ hcoΓ v)
        ≤ C1 hn Γ Λ f disc_Γ hcoΓ := by
  let := poMulAction hn
  let := subAction hn Γ
  intro huv
  set ru : HUpper n := bRep hn Γ hcoΓ u
  set rv : HUpper n := bRep hn Γ hcoΓ v
  set γu : Γ := bGamma hn Γ hcoΓ u
  set γv : Γ := bGamma hn Γ hcoΓ v
  set σ : Γ := γu⁻¹ * γv
  have hσmem := bGamma_ratio_mem hn Γ hcoΓ u v huv
  have hσle0 := dist_fpo_le_sum hn Γ Λ f disc_Γ σ hσmem
  have hσle : dist ((fpo Γ Λ f σ : PO n 1) • basepointH) basepointH
      ≤ R1 hn Γ Λ f disc_Γ hcoΓ := hσle0
  have huru : dist (bFix hn Γ Λ f disc_Γ ru) basepointH ≤ RB hn Γ Λ f disc_Γ hcoΓ :=
    bFix_dist_le hn Γ Λ f disc_Γ hcoΓ ru (bRep_dist hn Γ hcoΓ u)
  have hvrv : dist (bFix hn Γ Λ f disc_Γ rv) basepointH ≤ RB hn Γ Λ f disc_Γ hcoΓ :=
    bFix_dist_le hn Γ Λ f disc_Γ hcoΓ rv (bRep_dist hn Γ hcoΓ v)
  change dist (fpo Γ Λ f γu • bFix hn Γ Λ f disc_Γ ru) (fpo Γ Λ f γv • bFix hn Γ Λ f disc_Γ rv)
    ≤ C1 hn Γ Λ f disc_Γ hcoΓ
  have hkey : dist (fpo Γ Λ f γu • bFix hn Γ Λ f disc_Γ ru)
      (fpo Γ Λ f γv • bFix hn Γ Λ f disc_Γ rv)
      = dist (bFix hn Γ Λ f disc_Γ ru)
        (fpo Γ Λ f σ • bFix hn Γ Λ f disc_Γ rv) := by
    have h4 := po_dist_smul hn (fpo Γ Λ f γu)⁻¹
      (fpo Γ Λ f γu • bFix hn Γ Λ f disc_Γ ru) (fpo Γ Λ f γv • bFix hn Γ Λ f disc_Γ rv)
    rw [smul_smul, inv_mul_cancel, one_smul] at h4
    rw [← h4, smul_smul]
    have hco : (fpo Γ Λ f γu)⁻¹ * fpo Γ Λ f γv = fpo Γ Λ f (γu⁻¹ * γv) := by
      rw [← map_inv, ← map_mul]
    rw [hco]
  rw [hkey]
  have hdist : dist basepointH (fpo Γ Λ f σ • bFix hn Γ Λ f disc_Γ rv)
      ≤ RB hn Γ Λ f disc_Γ hcoΓ + R1 hn Γ Λ f disc_Γ hcoΓ := by
    have h5 : dist basepointH (fpo Γ Λ f σ • bFix hn Γ Λ f disc_Γ rv)
        ≤ dist basepointH ((fpo Γ Λ f σ : PO n 1) • basepointH)
          + dist ((fpo Γ Λ f σ : PO n 1) • basepointH)
            (fpo Γ Λ f σ • bFix hn Γ Λ f disc_Γ rv) := dist_triangle _ _ _
    have h6 : dist ((fpo Γ Λ f σ : PO n 1) • basepointH)
        (fpo Γ Λ f σ • bFix hn Γ Λ f disc_Γ rv)
        = dist basepointH (bFix hn Γ Λ f disc_Γ rv) :=
      po_dist_smul hn (fpo Γ Λ f σ) basepointH (bFix hn Γ Λ f disc_Γ rv)
    have h7 : dist basepointH (bFix hn Γ Λ f disc_Γ rv) ≤ RB hn Γ Λ f disc_Γ hcoΓ := by
      rw [dist_comm]; exact hvrv
    have h8 : dist (basepointH : HUpper n) ((fpo Γ Λ f σ : PO n 1) • (basepointH : HUpper n))
        = dist ((fpo Γ Λ f σ : PO n 1) • basepointH) basepointH := dist_comm _ _
    linarith [h5, h6, h7, hσle, h8]
  have hfin := dist_triangle (bFix hn Γ Λ f disc_Γ ru) basepointH
    (fpo Γ Λ f σ • bFix hn Γ Λ f disc_Γ rv)
  have hC1eq : C1 hn Γ Λ f disc_Γ hcoΓ
      = 2 * RB hn Γ Λ f disc_Γ hcoΓ + R1 hn Γ Λ f disc_Γ hcoΓ := rfl
  linarith [hfin, huru, hdist, hC1eq]

theorem dist_le_sum_range (p : ℕ → HUpper n) (m : ℕ) :
    dist (p 0) (p m) ≤ ∑ i ∈ Finset.range m, dist (p i) (p (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc dist (p 0) (p (m + 1))
        ≤ dist (p 0) (p m) + dist (p m) (p (m + 1)) := dist_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.range m, dist (p i) (p (i + 1))) + dist (p m) (p (m + 1)) :=
          add_le_add ih (le_refl _)
      _ = ∑ i ∈ Finset.range (m + 1), dist (p i) (p (i + 1)) := by
          rw [Finset.sum_range_succ]

theorem bPhi_upper (x y : HUpper n) :
    letI := poMulAction hn
    dist (bPhi hn Γ Λ f disc_Γ hcoΓ x) (bPhi hn Γ Λ f disc_Γ hcoΓ y)
      ≤ C1 hn Γ Λ f disc_Γ hcoΓ * dist x y + C1 hn Γ Λ f disc_Γ hcoΓ := by
  let := poMulAction hn
  have hC0 : (0:ℝ) ≤ C1 hn Γ Λ f disc_Γ hcoΓ := C1_nonneg hn Γ Λ f disc_Γ hcoΓ
  by_cases hxy : x = y
  · subst hxy
    have h1 : dist (bPhi hn Γ Λ f disc_Γ hcoΓ x) (bPhi hn Γ Λ f disc_Γ hcoΓ x) = 0 :=
      dist_self _
    have h2 : dist x x = 0 := dist_self _
    rw [h1, h2, mul_zero, zero_add]
    exact hC0
  · set T : ℝ := dist x y with hTdef
    have hTpos : 0 < T := dist_pos.mpr hxy
    set m : ℕ := ⌈T⌉₊ with hmdef
    have hm1 : 1 ≤ m := Nat.ceil_pos.mpr hTpos
    have hmT : (T:ℝ) ≤ m := Nat.le_ceil T
    have hmlt : (m:ℝ) < T + 1 := Nat.ceil_lt_add_one hTpos.le
    have hmR : (0:ℝ) < m := by exact_mod_cast hm1
    have hm : (m:ℝ) ≠ 0 := ne_of_gt hmR
    set p : ℕ → HUpper n := fun i => HyperbolicConvexity.geodFromTo x y hxy ((i:ℝ)/m * T)
      with hpdef
    have hp0 : p 0 = x := by
      simp only [hpdef, Nat.cast_zero, zero_div, zero_mul]
      exact HyperbolicConvexity.geodFromTo_zero hxy
    have hpm : p m = y := by
      simp only [hpdef]
      rw [div_self hm, one_mul]
      exact HyperbolicConvexity.geodFromTo_dist hxy
    have hstep : ∀ i : ℕ, dist (p i) (p (i + 1)) ≤ 1 := by
      intro i
      simp only [hpdef]
      rw [HyperbolicConvexity.dist_geodFromTo hxy]
      have heq : ((i:ℝ)/m * T) - (((i+1:ℕ):ℝ)/m * T) = -(T/m) := by
        push_cast
        field_simp
        ring
      rw [heq, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ T/m)]
      rw [div_le_one hmR]
      exact hmT
    have hchain : dist (bPhi hn Γ Λ f disc_Γ hcoΓ (p 0)) (bPhi hn Γ Λ f disc_Γ hcoΓ (p m))
        ≤ m * C1 hn Γ Λ f disc_Γ hcoΓ := by
      calc dist (bPhi hn Γ Λ f disc_Γ hcoΓ (p 0)) (bPhi hn Γ Λ f disc_Γ hcoΓ (p m))
          ≤ ∑ i ∈ Finset.range m,
            dist (bPhi hn Γ Λ f disc_Γ hcoΓ (p i)) (bPhi hn Γ Λ f disc_Γ hcoΓ (p (i+1))) :=
            dist_le_sum_range (fun i => bPhi hn Γ Λ f disc_Γ hcoΓ (p i)) m
        _ ≤ ∑ i ∈ Finset.range m, C1 hn Γ Λ f disc_Γ hcoΓ :=
            Finset.sum_le_sum fun i _ => bPhi_one_close hn Γ Λ f disc_Γ hcoΓ (p i) (p (i+1))
              (hstep i)
        _ = m * C1 hn Γ Λ f disc_Γ hcoΓ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc dist (bPhi hn Γ Λ f disc_Γ hcoΓ x) (bPhi hn Γ Λ f disc_Γ hcoΓ y)
        = dist (bPhi hn Γ Λ f disc_Γ hcoΓ (p 0)) (bPhi hn Γ Λ f disc_Γ hcoΓ (p m)) := by
          rw [hp0, hpm]
      _ ≤ m * C1 hn Γ Λ f disc_Γ hcoΓ := hchain
      _ ≤ (T + 1) * C1 hn Γ Λ f disc_Γ hcoΓ :=
          mul_le_mul_of_nonneg_right (le_of_lt hmlt) hC0
      _ = C1 hn Γ Λ f disc_Γ hcoΓ * T + C1 hn Γ Λ f disc_Γ hcoΓ := by ring

end MilnorSvarc

theorem bPhi_comp_displacement (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    (hcoΓ : ActsCocompactly hn Γ) (hcoΛ : ActsCocompactly hn Λ) (f : Γ ≃* Λ)
    (x : HUpper n) :
    letI := poMulAction hn
    dist (bPhi hn Λ Γ f.symm disc_Λ hcoΛ (bPhi hn Γ Λ f disc_Γ hcoΓ x)) x
      ≤ C1 hn Λ Γ f.symm disc_Λ hcoΛ * RB hn Γ Λ f disc_Γ hcoΓ
        + C1 hn Λ Γ f.symm disc_Λ hcoΛ
        + dist (bPhi hn Λ Γ f.symm disc_Λ hcoΛ basepointH) basepointH
        + covD hn Γ hcoΓ := by
  let := poMulAction hn
  let := subAction hn Γ
  set Φ := bPhi hn Γ Λ f disc_Γ hcoΓ with hΦdef
  set Ψ := bPhi hn Λ Γ f.symm disc_Λ hcoΛ with hΨdef
  set γx : Γ := bGamma hn Γ hcoΓ x
  set rx : HUpper n := bRep hn Γ hcoΓ x
  have hγx : (γx : PO n 1) • rx = x := by
    rw [← subAction_smul hn Γ γx rx]; exact bGamma_spec hn Γ hcoΓ x
  have hrx : dist basepointH rx ≤ covD hn Γ hcoΓ := bRep_dist hn Γ hcoΓ x
  have hbFix : dist (bFix hn Γ Λ f disc_Γ rx) basepointH ≤ RB hn Γ Λ f disc_Γ hcoΓ :=
    bFix_dist_le hn Γ Λ f disc_Γ hcoΓ rx hrx
  have hΦx : Φ x = fpo Γ Λ f γx • bFix hn Γ Λ f disc_Γ rx := rfl
  have hΨeq : IsFEquivariant f.symm hn Ψ := bPhi_isFEquivariant hn Λ Γ f.symm disc_Λ hcoΛ
  have hΨup := bPhi_upper hn Λ Γ f.symm disc_Λ hcoΛ
  have ht2 : Ψ (fpo Γ Λ f γx • basepointH) = ((γx : Γ) : PO n 1) • Ψ basepointH := by
    have h := hΨeq (f γx) basepointH
    rw [MulEquiv.symm_apply_apply] at h
    exact h
  have hd1 : dist (Φ x) (fpo Γ Λ f γx • basepointH) ≤ RB hn Γ Λ f disc_Γ hcoΓ := by
    rw [hΦx]
    have h := po_dist_smul hn (fpo Γ Λ f γx) (bFix hn Γ Λ f disc_Γ rx) basepointH
    rw [h]; exact hbFix
  have ht1 : dist (Ψ (Φ x)) (Ψ (fpo Γ Λ f γx • basepointH))
      ≤ C1 hn Λ Γ f.symm disc_Λ hcoΛ * RB hn Γ Λ f disc_Γ hcoΓ
        + C1 hn Λ Γ f.symm disc_Λ hcoΛ := by
    have h := hΨup (Φ x) (fpo Γ Λ f γx • basepointH)
    have hC0 : 0 ≤ C1 hn Λ Γ f.symm disc_Λ hcoΛ := C1_nonneg hn Λ Γ f.symm disc_Λ hcoΛ
    have hmul := mul_le_mul_of_nonneg_left hd1 hC0
    linarith [h, hmul]
  have ht2d : dist (Ψ (fpo Γ Λ f γx • basepointH)) ((γx : PO n 1) • basepointH)
      = dist (Ψ basepointH) basepointH := by
    rw [ht2]
    exact po_dist_smul hn (γx : PO n 1) (Ψ basepointH) basepointH
  have ht3 : dist ((γx : PO n 1) • basepointH) x ≤ covD hn Γ hcoΓ := by
    have h := po_dist_smul hn (γx : PO n 1) basepointH rx
    rw [hγx] at h
    rw [h]; exact hrx
  have htri1 := dist_triangle (Ψ (Φ x)) (Ψ (fpo Γ Λ f γx • basepointH)) x
  have htri2 := dist_triangle (Ψ (fpo Γ Λ f γx • basepointH)) ((γx : PO n 1) • basepointH) x
  linarith [htri1, htri2, ht1, ht2d, ht3]

theorem bPhi_isPseudoIsometry (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    (hcoΓ : ActsCocompactly hn Γ) (hcoΛ : ActsCocompactly hn Λ) (f : Γ ≃* Λ) :
    PseudoIsometry.IsPseudoIsometry
      (max 1 (max (C1 hn Γ Λ f disc_Γ hcoΓ) (C1 hn Λ Γ f.symm disc_Λ hcoΛ)))
      (max 1 (max (C1 hn Γ Λ f disc_Γ hcoΓ) (C1 hn Λ Γ f.symm disc_Λ hcoΛ))
        + 2 * (C1 hn Λ Γ f.symm disc_Λ hcoΛ * RB hn Γ Λ f disc_Γ hcoΓ
            + C1 hn Λ Γ f.symm disc_Λ hcoΛ
            + dist (bPhi hn Λ Γ f.symm disc_Λ hcoΛ basepointH) basepointH
            + covD hn Γ hcoΓ))
      (bPhi hn Γ Λ f disc_Γ hcoΓ) := by
  let := poMulAction hn
  set Φ := bPhi hn Γ Λ f disc_Γ hcoΓ with hΦdef
  set Ψ := bPhi hn Λ Γ f.symm disc_Λ hcoΛ with hΨdef
  set C1Γ := C1 hn Γ Λ f disc_Γ hcoΓ with hC1Γdef
  set C1Λ := C1 hn Λ Γ f.symm disc_Λ hcoΛ with hC1Λdef
  set RBΓ := RB hn Γ Λ f disc_Γ hcoΓ with hRBΓdef
  set DΓ := covD hn Γ hcoΓ with hDΓdef
  set E0 := dist (Ψ basepointH) basepointH with hE0def
  set E := C1Λ * RBΓ + C1Λ + E0 + DΓ with hEdef
  set K := max 1 (max C1Γ C1Λ) with hKdef
  set C := K + 2 * E with hCdef
  have hΦup := bPhi_upper hn Γ Λ f disc_Γ hcoΓ
  have hΨup := bPhi_upper hn Λ Γ f.symm disc_Λ hcoΛ
  have hdispl : ∀ x : HUpper n, dist (Ψ (Φ x)) x ≤ E :=
    bPhi_comp_displacement hn Γ Λ disc_Γ disc_Λ hcoΓ hcoΛ f
  have hK1 : (1:ℝ) ≤ K := le_max_left _ _
  have hC1ΓK : C1Γ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hC1ΛK : C1Λ ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hE0nn : (0:ℝ) ≤ E0 := dist_nonneg
  have hC1Λnn : (0:ℝ) ≤ C1Λ := C1_nonneg hn Λ Γ f.symm disc_Λ hcoΛ
  have hRBΓnn : (0:ℝ) ≤ RBΓ := RB_nonneg hn Γ Λ f disc_Γ hcoΓ
  have hDΓnn : (0:ℝ) ≤ DΓ := covD_nonneg hn Γ hcoΓ
  have hEnn : (0:ℝ) ≤ E := by positivity
  have hKC : K ≤ C := by rw [hCdef]; linarith [hEnn]
  have hCnn : (0:ℝ) ≤ C := (zero_le_one.trans hK1).trans hKC
  constructor
  · exact hK1
  · exact hCnn
  · intro x y
    have h := hΦup x y
    have hmul := mul_le_mul_of_nonneg_right hC1ΓK (dist_nonneg : 0 ≤ dist x y)
    calc dist (Φ x) (Φ y) ≤ C1Γ * dist x y + C1Γ := h
      _ ≤ K * dist x y + K := by linarith [hmul, hC1ΓK]
      _ ≤ K * dist x y + C := by linarith [hKC]
  · intro x y
    have hKpos : (0:ℝ) < K := zero_lt_one.trans_le hK1
    have hKinv : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK1
    have hKinv0 : (0:ℝ) ≤ K⁻¹ := inv_nonneg.mpr hKpos.le
    have htri1 := dist_triangle x (Ψ (Φ x)) y
    have htri2 := dist_triangle (Ψ (Φ x)) (Ψ (Φ y)) y
    have hxE : dist x (Ψ (Φ x)) ≤ E := by rw [dist_comm]; exact hdispl x
    have hyE : dist (Ψ (Φ y)) y ≤ E := hdispl y
    have hmid : dist (Ψ (Φ x)) (Ψ (Φ y)) ≤ C1Λ * dist (Φ x) (Φ y) + C1Λ := hΨup _ _
    have hmulΛ := mul_le_mul_of_nonneg_right hC1ΛK (dist_nonneg : 0 ≤ dist (Φ x) (Φ y))
    have hkey : dist x y ≤ K * dist (Φ x) (Φ y) + C := by
      linarith [htri1, htri2, hxE, hyE, hmid, hmulΛ, hC1ΛK, hKC, hEnn]
    have h1 : dist x y - C ≤ K * dist (Φ x) (Φ y) := by linarith [hkey]
    have h2 : K⁻¹ * (dist x y - C) ≤ dist (Φ x) (Φ y) := by
      have h3 := mul_le_mul_of_nonneg_left h1 hKinv0
      have h4 : K⁻¹ * (K * dist (Φ x) (Φ y)) = dist (Φ x) (Φ y) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hKpos), one_mul]
      linarith [h3, h4]
    have h5 : K⁻¹ * C ≤ C := by
      calc K⁻¹ * C ≤ 1 * C := mul_le_mul_of_nonneg_right hKinv hCnn
        _ = C := one_mul _
    have h6 : K⁻¹ * dist x y - C = K⁻¹ * (dist x y - C) + (K⁻¹ * C - C) := by ring
    linarith [h2, h5, h6]

theorem exists_isPseudoIsometry_isFEquivariant_of_actsCocompactly
    (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    (hcoΓ : ActsCocompactly hn Γ) (hcoΛ : ActsCocompactly hn Λ) (f : Γ ≃* Λ) :
    ∃ (Φ : HUpper n → HUpper n) (K C : ℝ),
      PseudoIsometry.IsPseudoIsometry K C Φ ∧ PseudoIsometry.IsFEquivariant f hn Φ :=
  ⟨bPhi hn Γ Λ f disc_Γ hcoΓ, _, _,
    bPhi_isPseudoIsometry hn Γ Λ disc_Γ disc_Λ hcoΓ hcoΛ f,
    bPhi_isFEquivariant hn Γ Λ f disc_Γ hcoΓ⟩

theorem exists_twoSided_pseudoIsometry_of_actsCocompactly
    (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    (hcoΓ : ActsCocompactly hn Γ) (hcoΛ : ActsCocompactly hn Λ) (f : Γ ≃* Λ) :
    ∃ (Φ Ψ : HUpper n → HUpper n) (K C K' C' E E' : ℝ),
      PseudoIsometry.IsPseudoIsometry K C Φ
      ∧ PseudoIsometry.IsFEquivariant f hn Φ
      ∧ PseudoIsometry.IsPseudoIsometry K' C' Ψ
      ∧ PseudoIsometry.IsFEquivariant f.symm hn Ψ
      ∧ (∀ x : HUpper n, dist (Ψ (Φ x)) x ≤ E)
      ∧ (∀ y : HUpper n, dist (Φ (Ψ y)) y ≤ E') := by
  let := poMulAction hn
  refine ⟨bPhi hn Γ Λ f disc_Γ hcoΓ, bPhi hn Λ Γ f.symm disc_Λ hcoΛ, _, _, _, _,
    C1 hn Λ Γ f.symm disc_Λ hcoΛ * RB hn Γ Λ f disc_Γ hcoΓ
      + C1 hn Λ Γ f.symm disc_Λ hcoΛ
      + dist (bPhi hn Λ Γ f.symm disc_Λ hcoΛ basepointH) basepointH
      + covD hn Γ hcoΓ,
    C1 hn Γ Λ f disc_Γ hcoΓ * RB hn Λ Γ f.symm disc_Λ hcoΛ
      + C1 hn Γ Λ f disc_Γ hcoΓ
      + dist (bPhi hn Γ Λ f disc_Γ hcoΓ basepointH) basepointH
      + covD hn Λ hcoΛ,
    bPhi_isPseudoIsometry hn Γ Λ disc_Γ disc_Λ hcoΓ hcoΛ f,
    bPhi_isFEquivariant hn Γ Λ f disc_Γ hcoΓ,
    bPhi_isPseudoIsometry hn Λ Γ disc_Λ disc_Γ hcoΛ hcoΓ f.symm,
    bPhi_isFEquivariant hn Λ Γ f.symm disc_Λ hcoΛ,
    bPhi_comp_displacement hn Γ Λ disc_Γ disc_Λ hcoΓ hcoΛ f, ?_⟩
  have h := bPhi_comp_displacement hn Λ Γ disc_Λ disc_Γ hcoΛ hcoΓ f.symm
  rw [MulEquiv.symm_symm] at h
  exact h

end DifferentialGeometry.UniformPseudoIsometry
