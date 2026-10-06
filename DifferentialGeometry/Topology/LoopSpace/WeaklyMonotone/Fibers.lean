import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section

open Set Function
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

private theorem surjective_and_connected_fibers_of_monotone_lift
    {σ : C(loopCircle, loopCircle)} (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (hlift : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle))
    (hmono : Monotone ψ) (hperiod : ∀ t, ψ (t + 1) = ψ t + 1) :
    Surjective σ ∧ ∀ θ : loopCircle, IsConnected (σ ⁻¹' {θ}) := by
  let f : CircleDeg1Lift := ⟨⟨ψ, hmono⟩, hperiod⟩
  have hf : Continuous f := hψ
  have hfsurj : Surjective f := f.continuous_iff_surjective.mp hf
  constructor
  · intro θ
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective θ
    obtain ⟨t, ht⟩ := hfsurj a
    refine ⟨(t : loopCircle), ?_⟩
    exact (hlift t).symm.trans (congrArg (fun x : ℝ => (x : loopCircle)) ht)
  · intro θ
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective θ
    have hreal : IsConnected (f ⁻¹' {a}) := by
      refine ⟨?_, (ordConnected_singleton.preimage_mono f.monotone).isPreconnected⟩
      obtain ⟨t, ht⟩ := hfsurj a
      exact ⟨t, ht⟩
    have himage : (fun t : ℝ => (t : loopCircle)) '' (f ⁻¹' {a}) =
        σ ⁻¹' {(a : loopCircle)} := by
      ext θ
      constructor
      · rintro ⟨t, ht, rfl⟩
        change σ (t : loopCircle) = (a : loopCircle)
        exact (hlift t).symm.trans (congrArg (fun x : ℝ => (x : loopCircle)) ht)
      · intro hθ
        obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
        change σ (t : loopCircle) = (a : loopCircle) at hθ
        have hzero : ((f t - a : ℝ) : loopCircle) = 0 := by
          rw [AddCircle.coe_sub]
          change (ψ t : loopCircle) - (a : loopCircle) = 0
          rw [hlift, hθ, sub_self]
        obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
        have hn' : (n : ℝ) = f t - a := by simpa using hn
        have hnzero : ((n : ℝ) : loopCircle) = 0 :=
          (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, by simp⟩
        refine ⟨t - (n : ℝ), ?_, ?_⟩
        · change f (t - (n : ℝ)) = a
          rw [f.map_sub_int]
          linarith
        · change ((t - (n : ℝ) : ℝ) : loopCircle) = (t : loopCircle)
          rw [AddCircle.coe_sub, hnzero, sub_zero]
    rw [← himage]
    exact hreal.image (fun t : ℝ => (t : loopCircle))
      (AddCircle.continuous_mk' (1 : ℝ)).continuousOn

private theorem IsWeaklyMonotoneOnce.surjective_and_connected_fibers
    {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ) :
    Surjective σ ∧ ∀ θ : loopCircle, IsConnected (σ ⁻¹' {θ}) := by
  obtain ⟨ψ, hψ, hlift, hsign⟩ := hσ
  rcases hsign with ⟨hmono, hperiod⟩ | ⟨hanti, hperiod⟩
  · exact surjective_and_connected_fibers_of_monotone_lift ψ hψ hlift hmono hperiod
  · let τ : C(loopCircle, loopCircle) := ⟨fun θ => -σ θ, σ.continuous.neg⟩
    have hτlift (t : ℝ) : ((-ψ t : ℝ) : loopCircle) = τ (t : loopCircle) := by
      change ((-ψ t : ℝ) : loopCircle) = -σ (t : loopCircle)
      rw [AddCircle.coe_neg, hlift]
    have hτperiod (t : ℝ) : -ψ (t + 1) = -ψ t + 1 := by rw [hperiod]; ring
    obtain ⟨hsurj, hconnected⟩ := surjective_and_connected_fibers_of_monotone_lift
      (fun t => -ψ t) hψ.neg hτlift hanti.neg hτperiod
    constructor
    · intro θ
      obtain ⟨x, hx⟩ := hsurj (-θ)
      refine ⟨x, ?_⟩
      change -σ x = -θ at hx
      exact neg_injective hx
    · intro θ
      have heq : τ ⁻¹' {-θ} = σ ⁻¹' {θ} := by
        ext x
        change (-σ x = -θ) ↔ σ x = θ
        exact neg_inj
      rw [← heq]
      exact hconnected (-θ)

/-- A weakly monotone circle phase of either signed degree one is surjective. -/
theorem IsWeaklyMonotoneOnce.surjective
    {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ) : Surjective σ :=
  hσ.surjective_and_connected_fibers.1

/-- Every fiber of the same weakly monotone phase is connected, including plateau
fibers and either signed orientation. -/
theorem IsWeaklyMonotoneOnce.isConnected_fiber
    {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ) (θ : loopCircle) :
    IsConnected (σ ⁻¹' {θ}) :=
  hσ.surjective_and_connected_fibers.2 θ

end DifferentialGeometry.Geometry
