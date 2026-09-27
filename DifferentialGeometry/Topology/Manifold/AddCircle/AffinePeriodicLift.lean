import DifferentialGeometry.Topology.Covering.AddCircleLift
import DifferentialGeometry.Topology.Manifold.AddCircle.LocalLift

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace AddCircle

private theorem lift_eq_add_of_coe_eq
    {f : ℝ → ℝ} (hf : Continuous f)
    (hcoe : ∀ x, (f x : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ))) :
    ∀ x, f x = x + f 0 := by
  let d : ℝ → AddSubgroup.zmultiples (1 : ℝ) := fun x =>
    ⟨f x - x, by
      rw [← QuotientAddGroup.eq_iff_sub_mem]
      exact hcoe x⟩
  have hd : Continuous d :=
    (hf.sub continuous_id).subtype_mk (fun x => (d x).property)
  intro x
  have heq := congrArg Subtype.val
    (IsPreconnected.constant isPreconnected_univ hd.continuousOn
      (mem_univ (0 : ℝ)) (mem_univ x))
  change f 0 - 0 = f x - x at heq
  linarith

theorem exists_contDiffOn_affine_periodic_lift_of_initial_identity
    {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → AddCircle (1 : ℝ)}
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ f (univ ×ˢ Icc a b))
    (hperiodic : ∀ p : ℝ × ℝ, f (p.1 + 1, p.2) = f p)
    (hinitial : ∀ x : ℝ, f (x, a) = (x : AddCircle (1 : ℝ))) :
    ∃ g : ℝ × ℝ → ℝ,
      ContDiffOn ℝ ∞ g (univ ×ˢ Icc a b) ∧
      (∀ p ∈ univ ×ˢ Icc a b, (g p : AddCircle (1 : ℝ)) = f p) ∧
      (∀ p ∈ univ ×ˢ Icc a b, g (p.1 + 1, p.2) = g p + 1) ∧
      ∀ x, g (x, a) = x := by
  obtain ⟨g, d, hg, hlift, hdegree⟩ :=
    DifferentialGeometry.Topology.exists_contDiffOn_addCircle_lift_of_periodic
      (convex_Icc a b) ⟨a, le_rfl, hab⟩ f hperiodic
      (fun q hq => DifferentialGeometry.Topology.exists_contDiffWithinAt_addCircle_lift
        (hf q hq))
  have hslice : Continuous (fun x : ℝ => g (x, a)) := by
    apply continuousOn_univ.mp
    exact hg.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun x _ => ⟨mem_univ x, le_rfl, hab⟩)
  have hslice_eq : ∀ x : ℝ, g (x, a) = x + g (0, a) :=
    lift_eq_add_of_coe_eq hslice
      (fun x => (hlift (x, a) ⟨mem_univ x, le_rfl, hab⟩).trans (hinitial x))
  have hd : (d : ℝ) = 1 := by
    have h := hdegree (0, a) ⟨mem_univ 0, le_rfl, hab⟩
    rw [zero_add, hslice_eq 1] at h
    linarith
  have hzero : (g (0, a) : AddCircle (1 : ℝ)) = 0 := by
    exact (hlift (0, a) ⟨mem_univ 0, le_rfl, hab⟩).trans (hinitial 0)
  refine ⟨fun p => g p - g (0, a), hg.sub contDiffOn_const, ?_, ?_, ?_⟩
  · intro p hp
    rw [AddCircle.coe_sub, hzero, sub_zero]
    exact hlift p hp
  · intro p hp
    change g (p.1 + 1, p.2) - g (0, a) = g p - g (0, a) + 1
    rw [hdegree p hp, hd]
    ring
  · intro x
    change g (x, a) - g (0, a) = x
    linarith [hslice_eq x]

end AddCircle
