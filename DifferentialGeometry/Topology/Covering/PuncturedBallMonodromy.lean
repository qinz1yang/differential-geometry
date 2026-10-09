import DifferentialGeometry.Topology.FundamentalGroup.Circle
import DifferentialGeometry.Topology.Covering.Fiber.Equivalence
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Set.Card

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology.Covering

/-- A connected finite covering of a punctured complex ball has a generator
whose monodromy is a single cycle, with period equal to the fiber cardinality. -/
theorem exists_cyclic_monodromy_puncturedBall
    {T : Type*} [TopologicalSpace T] [PathConnectedSpace T]
    {c : ℂ} {δ : ℝ}
    {p : T → ↥(Metric.ball c δ \ {c})}
    (hp : IsCoveringMap p)
    (y : ↥(Metric.ball c δ \ {c})) {n : ℕ}
    (hcard : (p ⁻¹' {y}).encard = (n : ℕ∞)) :
    ∃ γ : FundamentalGroup ↥(Metric.ball c δ \ {c}) y,
      Function.Surjective (fun k : ℤ => γ ^ k) ∧
      (hp.monodromyPerm y γ).IsCycleOn Set.univ ∧
      ∀ (e : p ⁻¹' {y}) (k : ℤ),
        ((hp.monodromyPerm y γ) ^ k) e = e ↔ (n : ℤ) ∣ k := by
  classical
  have hδ : 0 < δ := lt_of_le_of_lt dist_nonneg (mem_ball.mp y.property.1)
  let b : ℂ ≃ₜ ball c δ :=
    (Homeomorph.unitBall : ℂ ≃ₜ ball (0 : ℂ) 1).trans
      (OpenPartialHomeomorph.unitBallBall c δ hδ).toHomeomorphSourceTarget
  have hb : (b 0 : ℂ) = c := by
    change δ • (Homeomorph.unitBall (0 : ℂ) : ℂ) + c = c
    rw [Homeomorph.coe_unitBall_apply_zero, smul_zero, zero_add]
  let puncture : ({0}ᶜ : Set ℂ) ≃ₜ {z : ball c δ // (z : ℂ) ≠ c} :=
    b.subtype fun z => by
      change z ≠ 0 ↔ (b z : ℂ) ≠ c
      constructor
      · intro hz hzc
        apply hz
        apply b.injective
        exact Subtype.ext (hzc.trans hb.symm)
      · intro hz hzero
        apply hz
        rw [hzero]
        exact hb
  let flatten : {z : ball c δ // (z : ℂ) ≠ c} ≃ₜ ↥(ball c δ \ {c}) :=
    { toEquiv := Equiv.subtypeSubtypeEquivSubtypeInter
        (fun z : ℂ => z ∈ ball c δ) (fun z => z ≠ c)
      continuous_toFun := by
        change Continuous (fun z : {z : ball c δ // (z : ℂ) ≠ c} =>
          (⟨z.val.val, z.val.property, z.property⟩ : ↥(ball c δ \ {c})))
        fun_prop
      continuous_invFun := by
        change Continuous (fun z : ↥(ball c δ \ {c}) =>
          (⟨⟨z.val, z.property.1⟩, z.property.2⟩ :
            {z : ball c δ // (z : ℂ) ≠ c}))
        fun_prop }
  let polar : ({0}ᶜ : Set ℂ) ≃ₜ (Ioi (0 : ℝ) × Circle) :=
    (homeomorphUnitSphereProd ℂ).trans (Homeomorph.prodComm _ _)
  let e : ↥(ball c δ \ {c}) ≃ₜ (Ioi (0 : ℝ) × Circle) :=
    flatten.symm.trans (puncture.symm.trans polar)
  let : ContractibleSpace (Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace
      ⟨(1 : ℝ), Set.mem_Ioi.mpr (show (0 : ℝ) < 1 from zero_lt_one)⟩
  let : PathConnectedSpace ↥(ball c δ \ {c}) := e.symm.pathConnectedSpace
  let groupEquiv : FundamentalGroup ↥(ball c δ \ {c}) y ≃* Multiplicative ℤ :=
    (fundamentalGroupMulEquivOfHomotopyEquiv e.toHomotopyEquiv y (e y) rfl).trans
      ((fundamentalGroupProdRightEquivOfSimplyConnected (e y).1 (e y).2).trans
        ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
          (e y).2 (1 : Circle)).trans fundamentalGroupCircleEquivInt))
  let : IsCyclic (FundamentalGroup ↥(ball c δ \ {c}) y) :=
    groupEquiv.isCyclic.mpr inferInstance
  obtain ⟨γ, hγ⟩ := exists_zpow_surjective (FundamentalGroup ↥(ball c δ \ {c}) y)
  let : Fintype (p ⁻¹' {y}) := (Set.finite_of_encard_eq_coe hcard).fintype
  have hN : Fintype.card (p ⁻¹' {y}) = n := by
    have h := (Set.coe_fintypeCard (s := p ⁻¹' {y})).trans hcard
    exact_mod_cast h
  have hn : 0 < n := by
    obtain ⟨t, ht⟩ := hp.comp_subtypeVal_pathComponent_surjective
      (Classical.choice (inferInstance : Nonempty T)) y
    have hpos : 0 < (p ⁻¹' {y}).encard := Set.encard_pos.mpr ⟨t.val, ht⟩
    rw [hcard] at hpos
    exact_mod_cast hpos
  have hfiber : Nonempty (p ⁻¹' {y}) :=
    Fintype.card_pos_iff.mp (hN.symm ▸ hn)
  let e₀ : p ⁻¹' {y} := Classical.choice hfiber
  let σ := hp.monodromyPerm y γ
  have horbit (v : p ⁻¹' {y}) : σ.SameCycle e₀ v := by
    obtain ⟨η, hη⟩ :=
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.action_eval_surjective
        hp y e₀ v
    obtain ⟨k, hk⟩ := hγ η
    change γ ^ k = η at hk
    refine ⟨k, ?_⟩
    change ((hp.monodromyPerm y γ) ^ k) e₀ = v
    rw [← map_zpow, hk]
    exact hη
  have hcycle : σ.IsCycleOn Set.univ :=
    ⟨σ.bijective.bijOn_univ, fun v _ w _ => (horbit v).symm.trans (horbit w)⟩
  refine ⟨γ, hγ, hcycle, ?_⟩
  intro v k
  have hcycleFin : σ.IsCycleOn (↑(Finset.univ : Finset (p ⁻¹' {y})) : Set (p ⁻¹' {y})) := by
    simpa only [Finset.coe_univ] using hcycle
  simpa only [Finset.card_univ, hN] using
    (hcycleFin.zpow_apply_eq (Finset.mem_univ v) (n := k))

end DifferentialGeometry.Topology.Covering
