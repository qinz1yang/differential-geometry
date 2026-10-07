/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.CoarseGeometry.PseudoIsometry
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.ContinuousAction
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Metric
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Transitivity

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.EquivariantMap

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicTransitive
open DifferentialGeometry.StabilizerCompact
open DifferentialGeometry.ContinuousAction
open Matrix

variable {n : ℕ}

@[instance_reducible]
noncomputable def subAction (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) : MulAction Γ (HUpper n) :=
  letI := poMulAction hn
  MulAction.compHom _ Γ.subtype

theorem subAction_smul (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (γ : Γ) (x : HUpper n) :
    let := subAction hn Γ
    let := poMulAction hn
    γ • x = (γ : PO n 1) • x := rfl

theorem isCompact_stabilizer (hn : 1 ≤ n) (x : HUpper n) :
    letI := poMulAction hn
    IsCompact {g : PO n 1 | g • x = x} := by
  let := poMulAction hn
  obtain ⟨g₀, hg₀⟩ := exists_po_smul_basepoint hn x
  have hg₀' : g₀ • (basepointH : HUpper n) = x := hg₀
  have hset : {g : PO n 1 | g • x = x}
      = (fun h => g₀ * h * g₀⁻¹) '' {h : PO n 1 | h • (basepointH : HUpper n) = basepointH} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hh
      refine ⟨g₀⁻¹ * h * g₀, ?_, by group⟩
      show (g₀⁻¹ * h * g₀) • (basepointH : HUpper n) = basepointH
      rw [mul_smul, mul_smul, hg₀', hh, ← hg₀', smul_smul, inv_mul_cancel, one_smul]
    · rintro ⟨h', hh', rfl⟩
      show (g₀ * h' * g₀⁻¹) • x = x
      rw [← hg₀']
      have e0 : g₀⁻¹ • (g₀ • (basepointH : HUpper n)) = basepointH := by
        rw [smul_smul, inv_mul_cancel, one_smul]
      rw [mul_smul, mul_smul, e0, hh']
  rw [hset]
  exact (isCompact_stabilizer_basepoint hn).image
    ((continuous_const_mul g₀).mul_const g₀⁻¹)

theorem finite_stabilizer (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) (x : HUpper n) :
    Finite ↥(@MulAction.stabilizer Γ (HUpper n) _ (subAction hn Γ) x) := by
  let := poMulAction hn
  let := subAction hn Γ
  have hSclosed : IsClosed {g : PO n 1 | g • x = x} := by
    have hcont : Continuous fun g : PO n 1 => g • x :=
      (continuous_po_smul hn).comp (Continuous.prodMk continuous_id continuous_const)
    exact isClosed_singleton.preimage hcont
  have hTcompact : IsCompact (SetLike.coe Γ ∩ {g : PO n 1 | g • x = x}) :=
    (isCompact_stabilizer hn x).of_isClosed_subset
      ((DifferentialGeometry.ProjectiveOrthogonalGroup.Center.isClosed_of_discrete hn Γ disc).inter hSclosed) Set.inter_subset_right
  have hTfin : (SetLike.coe Γ ∩ {g : PO n 1 | g • x = x} : Set (PO n 1)).Finite :=
    hTcompact.finite (disc.mono Set.inter_subset_left)
  have hrange : Set.range (fun γ : ↥(MulAction.stabilizer Γ x) => ((γ : Γ) : PO n 1))
      = (SetLike.coe Γ ∩ {g : PO n 1 | g • x = x}) := by
    ext g
    constructor
    · rintro ⟨γ, rfl⟩
      refine ⟨(γ : Γ).prop, ?_⟩
      have hγ := γ.prop
      rw [MulAction.mem_stabilizer_iff] at hγ
      rw [subAction_smul] at hγ
      exact hγ
    · rintro ⟨hgΓ, hgx⟩
      refine ⟨⟨⟨g, hgΓ⟩, ?_⟩, rfl⟩
      rw [MulAction.mem_stabilizer_iff, subAction_smul]
      exact hgx
  have : Finite (Set.range (fun γ : ↥(MulAction.stabilizer Γ x) => ((γ : Γ) : PO n 1))) := by
    rw [hrange]
    exact hTfin
  exact Finite.of_injective_finite_range (fun a b h => Subtype.ext (Subtype.ext h))

noncomputable def midPt (y y' : HUpper n) : HUpper n where
  val := (Real.sqrt (2 + 2 * (- lorB y.val y'.val)))⁻¹ • (y.val + y'.val)
  is_unit := by
    have h1 := HUpper.one_le_neg_lorB y y'
    have hpos : (0:ℝ) < 2 + 2 * (- lorB y.val y'.val) := by linarith
    have hne : (2:ℝ) + 2 * (- lorB y.val y'.val) ≠ 0 := ne_of_gt hpos
    have hexp : lorB (y.val + y'.val) (y.val + y'.val)
        = -(2 + 2 * (- lorB y.val y'.val)) := by
      rw [lorB_add_left, lorB_add_right, lorB_add_right, y.is_unit, y'.is_unit,
        lorB_comm y'.val y.val]
      ring
    rw [lorB_smul_left, lorB_smul_right, hexp, ← mul_assoc]
    have hs2 : (Real.sqrt (2 + 2 * (- lorB y.val y'.val)))⁻¹
        * (Real.sqrt (2 + 2 * (- lorB y.val y'.val)))⁻¹
        = (2 + 2 * (- lorB y.val y'.val))⁻¹ := by
      rw [← _root_.mul_inv_rev, Real.mul_self_sqrt hpos.le]
    rw [hs2, mul_neg, inv_mul_cancel₀ hne]
  future := by
    have h1 := HUpper.one_le_neg_lorB y y'
    have hpos : (0:ℝ) < 2 + 2 * (- lorB y.val y'.val) := by linarith
    rw [tc_smul, tc_add]
    have h2 := Real.sqrt_pos.mpr hpos
    have h3 := y.future
    have h4 := y'.future
    positivity

theorem neg_lorB_midPt (p y y' : HUpper n) :
    - lorB p.val (midPt y y').val
      = ((- lorB p.val y.val) + (- lorB p.val y'.val))
        / Real.sqrt (2 + 2 * (- lorB y.val y'.val)) := by
  change - lorB p.val ((Real.sqrt (2 + 2 * (- lorB y.val y'.val)))⁻¹ • (y.val + y'.val)) = _
  rw [lorB_smul_right, lorB_add_right, div_eq_mul_inv]
  ring

theorem cosh_dist_midPt (p y y' : HUpper n) :
    Real.cosh (dist p (midPt y y'))
      = (Real.cosh (dist p y) + Real.cosh (dist p y'))
        / Real.sqrt (2 + 2 * Real.cosh (dist y y')) := by
  have hc1 : ∀ a b : HUpper n, Real.cosh (dist a b) = - lorB a.val b.val := fun a b => by
    change Real.cosh (HUpper.hdist a b) = - lorB a.val b.val
    unfold HUpper.hdist
    rw [Real.cosh_arcosh (HUpper.one_le_neg_lorB a b)]
  rw [hc1 p (midPt y y'), neg_lorB_midPt, hc1 p y, hc1 p y', hc1 y y']

theorem continuous_sup' {ι : Type*} (φ : ι → HUpper n → ℝ) (hφ : ∀ i, Continuous (φ i))
    (T : Finset ι) (hT : T.Nonempty) :
    Continuous fun y => T.sup' hT (fun i => φ i y) := by
  classical
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a =>
    exact (hφ a).congr fun y => (Finset.sup'_singleton (f := fun i => φ i y)).symm
  | cons a s ha hs ih =>
    exact ((hφ a).max ih).congr fun y => (Finset.sup'_cons hs (fun i => φ i y)).symm

noncomputable def energy (hn : 1 ≤ n) (F : Subgroup (PO n 1)) [Fintype ↥F]
    (y : HUpper n) : ℝ :=
  letI := poMulAction hn
  Finset.univ.sup' ⟨1, Finset.mem_univ 1⟩
    (fun f : ↥F => Real.cosh (dist y ((f : PO n 1) • (basepointH : HUpper n))))

noncomputable def orbitRadius (hn : 1 ≤ n) (F : Subgroup (PO n 1)) [Fintype ↥F] : ℝ :=
  letI := poMulAction hn
  Finset.univ.sup' ⟨1, Finset.mem_univ 1⟩
    (fun f : ↥F => dist basepointH ((f : PO n 1) • (basepointH : HUpper n)))

theorem cosh_dist_le_energy (hn : 1 ≤ n) (F : Subgroup (PO n 1)) [Fintype ↥F] (f : ↥F)
    (y : HUpper n) :
    letI := poMulAction hn
    Real.cosh (dist y ((f : PO n 1) • (basepointH : HUpper n))) ≤ energy hn F y := by
  let := poMulAction hn
  exact Finset.le_sup'
    (fun f : ↥F => Real.cosh (dist y ((f : PO n 1) • (basepointH : HUpper n))))
    (Finset.mem_univ f)

theorem energy_le (hn : 1 ≤ n) (F : Subgroup (PO n 1)) [Fintype ↥F] (B : ℝ)
    (y : HUpper n) :
    letI := poMulAction hn
    (∀ f : ↥F, Real.cosh (dist y ((f : PO n 1) • (basepointH : HUpper n))) ≤ B)
      → energy hn F y ≤ B := by
  let := poMulAction hn
  intro h
  exact Finset.sup'_le _ _ (fun f _ => h f)

theorem dist_le_orbitRadius (hn : 1 ≤ n) (F : Subgroup (PO n 1)) [Fintype ↥F] (f : ↥F) :
    letI := poMulAction hn
    dist basepointH ((f : PO n 1) • (basepointH : HUpper n)) ≤ orbitRadius hn F := by
  let := poMulAction hn
  exact Finset.le_sup'
    (fun f : ↥F => dist basepointH ((f : PO n 1) • (basepointH : HUpper n))) (Finset.mem_univ f)

theorem orbitRadius_nonneg (hn : 1 ≤ n) (F : Subgroup (PO n 1)) [Fintype ↥F] :
    0 ≤ orbitRadius hn F := by
  let := poMulAction hn
  exact dist_nonneg.trans (dist_le_orbitRadius hn F 1)

theorem energy_basepoint_le (hn : 1 ≤ n) (F : Subgroup (PO n 1)) [Fintype ↥F] :
    energy hn F basepointH ≤ Real.cosh (orbitRadius hn F) := by
  let := poMulAction hn
  apply energy_le
  intro f
  exact Real.cosh_strictMonoOn.monotoneOn (Set.mem_Ici.mpr dist_nonneg)
    (Set.mem_Ici.mpr (orbitRadius_nonneg hn F)) (dist_le_orbitRadius hn F f)

theorem continuous_energy (hn : 1 ≤ n) (F : Subgroup (PO n 1)) [Fintype ↥F] :
    Continuous (energy hn F) := by
  let := poMulAction hn
  change Continuous fun y : HUpper n => (Finset.univ : Finset ↥F).sup' ⟨1, Finset.mem_univ 1⟩
    (fun f : ↥F => Real.cosh (dist y ((f : PO n 1) • (basepointH : HUpper n))))
  exact continuous_sup' _ (fun (f : ↥F) => Real.continuous_cosh.comp
    (Continuous.dist continuous_id
      (continuous_const (y := ((f : PO n 1) • (basepointH : HUpper n)))))) _ _

theorem one_le_energy (hn : 1 ≤ n) (F : Subgroup (PO n 1)) [Fintype ↥F] (y : HUpper n) :
    (1:ℝ) ≤ energy hn F y := by
  let := poMulAction hn
  exact (Real.one_le_cosh _).trans (cosh_dist_le_energy hn F 1 y)

theorem exists_fixed_point_of_finite_subgroup (hn : 1 ≤ n) (F : Subgroup (PO n 1))
    [Fintype ↥F] :
    letI := poMulAction hn
    ∃ y : HUpper n, (∀ g : PO n 1, g ∈ F → g • y = y)
      ∧ ∀ f₀ : ↥F, dist y ((f₀ : PO n 1) • (basepointH : HUpper n))
          ≤ orbitRadius hn F := by
  classical
  let := poMulAction hn
  set D : ℝ := orbitRadius hn F with hDdef
  set C : Set (HUpper n) :=
    {y | ∀ f : ↥F, dist y ((f : PO n 1) • (basepointH : HUpper n)) ≤ D} with hCdef
  have hbaseC : basepointH ∈ C := fun f => dist_le_orbitRadius hn F f
  have hCne : C.Nonempty := ⟨basepointH, hbaseC⟩
  have hCclosed : IsClosed C := by
    have heq : C = ⋂ f : ↥F,
        (fun y => dist y ((f : PO n 1) • (basepointH : HUpper n))) ⁻¹' Set.Iic D := by
      ext y
      simp [hCdef, Set.mem_iInter]
    rw [heq]
    apply isClosed_iInter
    intro f
    exact isClosed_Iic.preimage (Continuous.dist continuous_id continuous_const)
  have hCcompact : IsCompact C :=
    (isCompact_closedBall (((1 : ↥F) : PO n 1) • basepointH) D).of_isClosed_subset hCclosed
      (fun y hy => Metric.mem_closedBall.mpr (hy 1))
  obtain ⟨y, hyC, hymin⟩ := hCcompact.exists_isMinOn hCne (continuous_energy hn F).continuousOn
  have hymin' : ∀ z ∈ C, energy hn F y ≤ energy hn F z := isMinOn_iff.mp hymin
  have hyglobal : ∀ z : HUpper n, energy hn F y ≤ energy hn F z := by
    intro z
    by_cases hz : z ∈ C
    · exact hymin' z hz
    · have hz' : ∃ f : ↥F, D < dist z ((f : PO n 1) • basepointH) := by
        by_contra h
        exact hz fun f => le_of_not_gt (fun hf => h ⟨f, hf⟩)
      obtain ⟨f, hf⟩ := hz'
      have hle : energy hn F y < energy hn F z :=
        calc energy hn F y ≤ energy hn F basepointH := hymin' _ hbaseC
          _ ≤ Real.cosh D := energy_basepoint_le hn F
          _ < Real.cosh (dist z ((f : PO n 1) • basepointH)) :=
            (Real.cosh_strictMonoOn.lt_iff_lt
              (Set.mem_Ici.mpr (orbitRadius_nonneg hn F))
              (Set.mem_Ici.mpr dist_nonneg)).mpr hf
          _ ≤ energy hn F z := cosh_dist_le_energy hn F f z
      exact hle.le
  have huniq : ∀ a b : HUpper n, (∀ z, energy hn F a ≤ energy hn F z) →
      (∀ z, energy hn F b ≤ energy hn F z) → a = b := by
    intro a b ha hb
    by_contra hne
    have hdpos : 0 < dist a b := dist_pos.mpr hne
    have hρ : energy hn F a = energy hn F b := le_antisymm (ha b) (hb a)
    have hρ1 : (1:ℝ) ≤ energy hn F a := one_le_energy hn F a
    have hc1 : (1:ℝ) < Real.cosh (dist a b) := Real.one_lt_cosh.mpr (ne_of_gt hdpos)
    have hsqrt2 : (2:ℝ) < Real.sqrt (2 + 2 * Real.cosh (dist a b)) := by
      have h4 : (4:ℝ) < 2 + 2 * Real.cosh (dist a b) := by linarith
      have h := Real.sqrt_lt_sqrt (by norm_num) h4
      rwa [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
    have hspos : (0:ℝ) < Real.sqrt (2 + 2 * Real.cosh (dist a b)) := lt_trans (by norm_num) hsqrt2
    set m := midPt a b with hmdef
    have hterm : ∀ f : ↥F, Real.cosh (dist m ((f : PO n 1) • basepointH))
        ≤ (energy hn F a + energy hn F a) / Real.sqrt (2 + 2 * Real.cosh (dist a b)) := by
      intro f
      rw [dist_comm m, cosh_dist_midPt ((f : PO n 1) • basepointH) a b]
      rw [dist_comm ((f : PO n 1) • basepointH) a, dist_comm ((f : PO n 1) • basepointH) b]
      rw [div_le_iff₀ hspos]
      calc Real.cosh (dist a ((f : PO n 1) • basepointH))
            + Real.cosh (dist b ((f : PO n 1) • basepointH))
          ≤ energy hn F a + energy hn F b :=
            add_le_add (cosh_dist_le_energy hn F f a) (cosh_dist_le_energy hn F f b)
        _ = energy hn F a + energy hn F a := by rw [← hρ]
        _ ≤ (energy hn F a + energy hn F a) / Real.sqrt (2 + 2 * Real.cosh (dist a b))
              * Real.sqrt (2 + 2 * Real.cosh (dist a b)) := by
            rw [div_mul_cancel₀ _ (ne_of_gt hspos)]
    have hMm : energy hn F m
        ≤ (energy hn F a + energy hn F a) / Real.sqrt (2 + 2 * Real.cosh (dist a b)) :=
      energy_le hn F _ m (fun f => hterm f)
    have hcontra : (energy hn F a + energy hn F a) / Real.sqrt (2 + 2 * Real.cosh (dist a b))
        < energy hn F a := by
      rw [div_lt_iff₀ hspos]
      have hMa : (0:ℝ) < energy hn F a := lt_of_lt_of_le (by norm_num) hρ1
      calc energy hn F a + energy hn F a = energy hn F a * 2 := by ring
        _ < energy hn F a * Real.sqrt (2 + 2 * Real.cosh (dist a b)) :=
            mul_lt_mul_of_pos_left hsqrt2 hMa
    linarith [ha m, hMm, hcontra]
  have hinv : ∀ f₀ : ↥F, energy hn F ((f₀ : PO n 1) • y) = energy hn F y := by
    intro f₀
    apply le_antisymm
    · apply energy_le
      intro f
      have hd : dist (((f₀ : ↥F) : PO n 1) • y) (((f : ↥F) : PO n 1) • basepointH)
          = dist y ((((f₀ : ↥F) : PO n 1)⁻¹ * ((f : ↥F) : PO n 1)) • basepointH) := by
        have h2 := po_dist_smul hn (((f₀ : ↥F) : PO n 1)⁻¹)
          (((f₀ : ↥F) : PO n 1) • y) (((f : ↥F) : PO n 1) • basepointH)
        rw [smul_smul, smul_smul, inv_mul_cancel, one_smul] at h2
        exact h2.symm
      rw [hd, ← Subgroup.coe_inv, ← Subgroup.coe_mul]
      exact cosh_dist_le_energy hn F _ y
    · apply energy_le
      intro f
      have hd : dist (((f₀ : ↥F) : PO n 1) • y)
            (((((f₀ : ↥F) : PO n 1) * ((f : ↥F) : PO n 1))) • basepointH)
          = dist y (((f : ↥F) : PO n 1) • basepointH) := by
        have h2 := po_dist_smul hn ((f₀ : ↥F) : PO n 1) y
          (((f : ↥F) : PO n 1) • basepointH)
        rw [smul_smul] at h2
        exact h2
      rw [← hd, ← Subgroup.coe_mul]
      exact cosh_dist_le_energy hn F _ _
  have hfix : ∀ f₀ : ↥F, ((f₀ : PO n 1)) • y = y := fun f₀ =>
    huniq _ _ (fun z => (hinv f₀).symm ▸ hyglobal z) hyglobal
  exact ⟨y, fun g hg => hfix ⟨g, hg⟩, fun f₀ => by
    have h := hyC f₀
    rwa [hDdef] at h⟩

section EquivariantMap

variable (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1)) (f : Γ ≃* Λ)

def fpo : Γ →* PO n 1 := Λ.subtype.comp f.toMonoidHom

theorem fpo_apply (γ : Γ) : fpo Γ Λ f γ = ((f γ : Λ) : PO n 1) := rfl

noncomputable def orbRep (x : HUpper n) : HUpper n :=
  letI := subAction hn Γ
  Quotient.out (⟦x⟧ : MulAction.orbitRel.Quotient Γ (HUpper n))

theorem orbRep_spec (x : HUpper n) :
    letI := subAction hn Γ
    ∃ γ : Γ, γ • orbRep hn Γ x = x := by
  let := subAction hn Γ
  have h : (⟦orbRep hn Γ x⟧ : MulAction.orbitRel.Quotient Γ (HUpper n)) = ⟦x⟧ :=
    Quotient.out_eq' _
  have h2 : (orbRep hn Γ x) ∈ MulAction.orbit Γ x := Quotient.eq'.mp h
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp h2
  exact ⟨γ⁻¹, by rw [← hγ, smul_smul, inv_mul_cancel, one_smul]⟩

theorem orbRep_smul (δ : Γ) (x : HUpper n) :
    letI := subAction hn Γ
    orbRep hn Γ (δ • x) = orbRep hn Γ x := by
  let := subAction hn Γ
  change Quotient.out (⟦δ • x⟧ : MulAction.orbitRel.Quotient Γ (HUpper n)) = _
  congr 1
  exact Quotient.eq'.mpr (MulAction.mem_orbit x δ)

noncomputable def stabImage (r : HUpper n) : Subgroup (PO n 1) :=
  Subgroup.map Λ.subtype
    (Subgroup.map f.toMonoidHom (@MulAction.stabilizer Γ (HUpper n) _ (subAction hn Γ) r))

theorem finite_subgroupMap {G G' : Type*} [Group G] [Group G'] (φ : G →* G')
    (H : Subgroup G) [Finite ↥H] : Finite ↥(Subgroup.map φ H) := by
  have hsurj : Function.Surjective
      (fun x : ↥H => (⟨φ x, Subgroup.mem_map.mpr ⟨x, x.prop, rfl⟩⟩ : ↥(Subgroup.map φ H))) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact Finite.of_surjective _ hsurj

theorem finite_stabImage (disc_Γ : IsDiscrete (SetLike.coe Γ)) (r : HUpper n) :
    Finite ↥(stabImage hn Γ Λ f r) := by
  have := finite_stabilizer hn Γ disc_Γ r
  have := finite_subgroupMap f.toMonoidHom
    (@MulAction.stabilizer Γ (HUpper n) _ (subAction hn Γ) r)
  exact finite_subgroupMap Λ.subtype
    (Subgroup.map f.toMonoidHom (@MulAction.stabilizer Γ (HUpper n) _ (subAction hn Γ) r))

noncomputable def stabFix (disc_Γ : IsDiscrete (SetLike.coe Γ)) (r : HUpper n) : HUpper n :=
  letI := finite_stabImage hn Γ Λ f disc_Γ r
  letI := Fintype.ofFinite ↥(stabImage hn Γ Λ f r)
  Classical.choose (exists_fixed_point_of_finite_subgroup hn (stabImage hn Γ Λ f r))

theorem stabFix_spec (disc_Γ : IsDiscrete (SetLike.coe Γ)) (r : HUpper n) (s : Γ)
    (hs : s ∈ @MulAction.stabilizer Γ (HUpper n) _ (subAction hn Γ) r) :
    letI := poMulAction hn
    fpo Γ Λ f s • stabFix hn Γ Λ f disc_Γ r = stabFix hn Γ Λ f disc_Γ r := by
  let := poMulAction hn
  let := finite_stabImage hn Γ Λ f disc_Γ r
  let := Fintype.ofFinite ↥(stabImage hn Γ Λ f r)
  have hspec := (Classical.choose_spec
    (exists_fixed_point_of_finite_subgroup hn (stabImage hn Γ Λ f r))).1
  apply hspec
  change Λ.subtype (f s) ∈ stabImage hn Γ Λ f r
  exact Subgroup.mem_map.mpr ⟨f s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩, rfl⟩

noncomputable def equivMap (disc_Γ : IsDiscrete (SetLike.coe Γ)) (x : HUpper n) : HUpper n :=
  letI := poMulAction hn
  fpo Γ Λ f (Classical.choose (orbRep_spec hn Γ x)) • stabFix hn Γ Λ f disc_Γ (orbRep hn Γ x)

theorem equivMap_isFEquivariant (disc_Γ : IsDiscrete (SetLike.coe Γ)) :
    PseudoIsometry.IsFEquivariant f hn (equivMap hn Γ Λ f disc_Γ) := by
  let := poMulAction hn
  let := subAction hn Γ
  intro δ x
  change equivMap hn Γ Λ f disc_Γ (δ • x) = fpo Γ Λ f δ • equivMap hn Γ Λ f disc_Γ x
  set r : HUpper n := orbRep hn Γ x with hrdef
  set γ₁ : Γ := Classical.choose (orbRep_spec hn Γ (δ • x))
  set γ₂ : Γ := Classical.choose (orbRep_spec hn Γ x)
  have hγ₁ : γ₁ • r = δ • x := by
    have h := Classical.choose_spec (orbRep_spec hn Γ (δ • x))
    rw [← show γ₁ = Classical.choose (orbRep_spec hn Γ (δ • x)) from rfl] at h
    rw [orbRep_smul hn Γ δ x] at h
    exact h
  have hγ₂ : γ₂ • r = x := Classical.choose_spec (orbRep_spec hn Γ x)
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
  have hfix := stabFix_spec hn Γ Λ f disc_Γ r _ hstab
  have hγ₁eq : fpo Γ Λ f γ₁ • stabFix hn Γ Λ f disc_Γ r
      = fpo Γ Λ f (δ * γ₂) • stabFix hn Γ Λ f disc_Γ r := by
    have h1 : fpo Γ Λ f (((δ * γ₂)⁻¹ * γ₁ : Γ)) • (stabFix hn Γ Λ f disc_Γ r)
        = stabFix hn Γ Λ f disc_Γ r := hfix
    rw [map_mul, map_inv] at h1
    have h2 : fpo Γ Λ f (δ * γ₂) •
        (((fpo Γ Λ f (δ * γ₂))⁻¹ * fpo Γ Λ f γ₁) • stabFix hn Γ Λ f disc_Γ r)
        = fpo Γ Λ f γ₁ • stabFix hn Γ Λ f disc_Γ r := by
      rw [smul_smul, mul_inv_cancel_left]
    rw [h1] at h2
    exact h2.symm
  change fpo Γ Λ f γ₁ • stabFix hn Γ Λ f disc_Γ (orbRep hn Γ (δ • x))
    = fpo Γ Λ f δ • (fpo Γ Λ f γ₂ • stabFix hn Γ Λ f disc_Γ (orbRep hn Γ x))
  rw [orbRep_smul hn Γ δ x, ← hrdef, hγ₁eq, map_mul, mul_smul]

end EquivariantMap

theorem exists_fEquivariant (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (f : Γ ≃* Λ) :
    ∃ Φ : HUpper n → HUpper n, PseudoIsometry.IsFEquivariant f hn Φ :=
  ⟨equivMap hn Γ Λ f disc_Γ, equivMap_isFEquivariant hn Γ Λ f disc_Γ⟩

end DifferentialGeometry.EquivariantMap
