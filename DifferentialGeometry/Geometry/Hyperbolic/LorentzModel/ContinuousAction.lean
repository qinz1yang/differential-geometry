/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.StabilizerCompactness

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.ContinuousAction

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.Hyperbolic.HUpper
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary
open DifferentialGeometry.StabilizerCompact
open Matrix
open scoped Topology

variable {n : ℕ}

theorem continuous_matOf_mulVec_const (x₀ : HUpper n) :
    Continuous fun A : LorGrp n => matOf A *ᵥ x₀.val := by
  apply Continuous.matrix_mulVec _ continuous_const
  have h1 : Continuous (Subtype.val : LorGrp n → MatrixSum (Fin n) (Fin 1) ℝ) :=
    continuous_subtype_val
  have h2 : Continuous (MatrixSum.ofMatrix.symm :
      MatrixSum (Fin n) (Fin 1) ℝ → Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :=
    MatrixSum.continuous_ofMatrix_symm (Fin n) (Fin 1) ℝ
  exact h2.comp h1

theorem continuous_lorB_pair :
    Continuous fun p : LorVec n × LorVec n => lorB p.1 p.2 := by
  change Continuous fun p : LorVec n × LorVec n =>
    (∑ i : Fin n, p.1 (Sum.inl i) * p.2 (Sum.inl i)) - p.1 (Sum.inr 0) * p.2 (Sum.inr 0)
  fun_prop

theorem continuousAt_actH (x₀ : HUpper n) (A₀ : LorGrp n) :
    ContinuousAt (fun A : LorGrp n => actH A x₀) A₀ := by
  have hc₀ : tc (matOf A₀ *ᵥ x₀.val) ≠ 0 := matOf_mulVec_ne_tc A₀ x₀.is_unit
  have hcont := continuous_matOf_mulVec_const x₀
  have htccont : Continuous fun A : LorGrp n => tc (matOf A *ᵥ x₀.val) :=
    (continuous_apply (Sum.inr 0)).comp hcont
  set c₀ : ℝ := tc (matOf A₀ *ᵥ x₀.val) with hc₀def
  set W : Set (LorGrp n) := {A | 0 < tc (matOf A *ᵥ x₀.val) * c₀} with hWdef
  have hWmem : W ∈ nhds A₀ := by
    have hopen : IsOpen {A : LorGrp n | 0 < tc (matOf A *ᵥ x₀.val) * c₀} :=
      isOpen_lt continuous_const (htccont.mul continuous_const)
    rw [hWdef]
    apply hopen.mem_nhds
    change 0 < c₀ * c₀
    exact mul_self_pos.mpr hc₀
  set F : LorGrp n → ℝ := fun A => - lorB (matOf A *ᵥ x₀.val) (matOf A₀ *ᵥ x₀.val)
    with hFdef
  have hsign : ∀ A ∈ W, lorB ((actH A x₀).val) ((actH A₀ x₀).val)
      = lorB (matOf A *ᵥ x₀.val) (matOf A₀ *ᵥ x₀.val) := by
    intro A hA
    change lorB (upperize (matOf A *ᵥ x₀.val)) (upperize (matOf A₀ *ᵥ x₀.val)) = _
    have hA' : 0 < tc (matOf A *ᵥ x₀.val) * c₀ := hA
    by_cases hc : 0 < c₀
    · have h1 : 0 < tc (matOf A *ᵥ x₀.val) :=
        pos_of_mul_pos_left hA' (le_of_lt hc)
      unfold upperize
      rw [ite_eq_left h1, ite_eq_left hc]
    · have hc' : c₀ < 0 := lt_of_le_of_ne (le_of_not_gt hc) hc₀
      have h1 : tc (matOf A *ᵥ x₀.val) < 0 := neg_of_mul_pos_left hA' hc'.le
      unfold upperize
      rw [ite_eq_right (not_lt_of_gt h1), ite_eq_right (not_lt_of_gt hc')]
      rw [lorB_neg_left, lorB_neg_right, neg_neg]
  have hdist : ∀ A ∈ W, dist (actH A x₀) (actH A₀ x₀) = Real.arcosh (F A) := by
    intro A hA
    change HUpper.hdist (actH A x₀) (actH A₀ x₀) = Real.arcosh (F A)
    unfold HUpper.hdist
    rw [hsign A hA]
  have hF1 : ∀ A ∈ W, 1 ≤ F A := by
    intro A hA
    have h := one_le_neg_lorB (actH A x₀) (actH A₀ x₀)
    rw [hsign A hA] at h
    exact h
  have hFcont : Continuous F :=
    (continuous_lorB_pair.comp (hcont.prodMk continuous_const)).neg
  have hF0 : F A₀ = 1 := by
    change - lorB (matOf A₀ *ᵥ x₀.val) (matOf A₀ *ᵥ x₀.val) = 1
    rw [lorB_matOf_mulVec]
    have h := x₀.is_unit
    linarith
  have hlim : Filter.Tendsto (fun A => Real.arcosh (F A)) (nhdsWithin A₀ W) (nhds 0) := by
    have hac : Filter.Tendsto Real.arcosh (nhdsWithin 1 (Set.Ici 1))
        (nhds (Real.arcosh 1)) :=
      Real.continuousOn_arcosh 1 (Set.mem_Ici.mpr le_rfl)
    rw [Real.arcosh_zero] at hac
    have hg : Filter.Tendsto F (nhdsWithin A₀ W) (nhdsWithin (F A₀) (Set.Ici 1)) :=
      hFcont.continuousWithinAt.tendsto_nhdsWithin (fun A hA => Set.mem_Ici.mpr (hF1 A hA))
    rw [hF0] at hg
    exact hac.comp hg
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hev := hlim.eventually (Iio_mem_nhds hε)
  rw [nhdsWithin_eq_nhds.mpr hWmem] at hev
  filter_upwards [hev, hWmem] with A hAε hAW
  show dist (actH A x₀) (actH A₀ x₀) < ε
  rw [hdist A hAW]
  exact hAε

theorem continuous_actH :
    Continuous fun p : LorGrp n × HUpper n => actH p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro ⟨A₀, x₀⟩
  rw [ContinuousAt, nhds_prod_eq, Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hevA : ∀ᶠ A in nhds A₀, dist (actH A x₀) (actH A₀ x₀) < ε / 2 :=
    (Metric.tendsto_nhds.mp (continuousAt_actH x₀ A₀)) (ε / 2) hε2
  have hball : Metric.ball x₀ (ε / 2) ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ hε2
  have hmem : {A : LorGrp n | dist (actH A x₀) (actH A₀ x₀) < ε / 2} ×ˢ
      Metric.ball x₀ (ε / 2) ∈ 𝓝 A₀ ×ˢ 𝓝 x₀ :=
    Filter.prod_mem_prod hevA hball
  filter_upwards [hmem] with p hp
  show dist (actH p.1 p.2) (actH A₀ x₀) < ε
  have hp1 : dist (actH p.1 x₀) (actH A₀ x₀) < ε / 2 := hp.1
  have hp2 : dist p.2 x₀ < ε / 2 := by
    have h := hp.2
    rwa [Metric.mem_ball] at h
  calc dist (actH p.1 p.2) (actH A₀ x₀)
      ≤ dist (actH p.1 p.2) (actH p.1 x₀) + dist (actH p.1 x₀) (actH A₀ x₀) :=
        dist_triangle _ _ _
    _ = dist p.2 x₀ + dist (actH p.1 x₀) (actH A₀ x₀) := by
        rw [show dist (actH p.1 p.2) (actH p.1 x₀) = dist (p.1 • p.2) (p.1 • x₀) from rfl]
        rw [dist_smul]
    _ < ε / 2 + ε / 2 := add_lt_add hp2 hp1
    _ = ε := by ring

instance : ContinuousSMul (LorGrp n) (HUpper n) :=
  ⟨continuous_actH⟩

theorem continuous_po_smul (hn : 1 ≤ n) :
    Continuous fun p : PO n 1 × HUpper n => (poMulAction hn).smul p.1 p.2 := by
  let := poMulAction hn
  have hq : IsOpenQuotientMap (fun A : LorGrp n =>
      (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A
        : PO n 1)) :=
    QuotientGroup.isOpenQuotientMap_mk
  have hprod : IsOpenQuotientMap (Prod.map (fun A : LorGrp n =>
      (QuotientGroup.mk' (Subgroup.center ↥(unitary (MatrixSum (Fin n) (Fin 1) ℝ))) A
        : PO n 1)) id) :=
    hq.prodMap (IsOpenQuotientMap.id (X := HUpper n))
  rw [← hprod.continuous_comp_iff]
  change Continuous fun p : LorGrp n × HUpper n => actH p.1 p.2
  exact continuous_actH

end DifferentialGeometry.ContinuousAction
