import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Topology

namespace DifferentialGeometry.Topology.Covering

/-- A continuous real height on a path connected covering with a finite fiber
of size greater than one takes the same value at two distinct points of some fiber.
The collision fiber need not be the supplied basepoint fiber. -/
theorem exists_fiber_collision_of_finite_fiber
    {T Y : Type*} [TopologicalSpace T] [PathConnectedSpace T]
    [TopologicalSpace Y] {p : T → Y} (hp : IsCoveringMap p)
    {y₀ : Y} {n : ℕ} (hcard : (p ⁻¹' {y₀}).encard = (n : ℕ∞))
    (hn : 1 < n) (h : T → ℝ) (hh : Continuous h) :
    ∃ x₁ x₂ : T, x₁ ≠ x₂ ∧ p x₁ = p x₂ ∧ h x₁ = h x₂ := by
  classical
  by_contra hnone
  have hsep : Function.Injective (fun x : T => (p x, h x)) := by
    intro x y hxy
    by_contra hne
    exact hnone ⟨x, y, hne, congrArg Prod.fst hxy, congrArg Prod.snd hxy⟩
  have hlarge : 1 < (p ⁻¹' {y₀}).encard := by
    rw [hcard]
    exact ENat.natCast_lt_natCast.mpr hn
  obtain ⟨x₀, x₁, hx₀, hx₁, hne⟩ := Set.one_lt_encard_iff.mp hlarge
  obtain ⟨e₀, he₀, hmin⟩ := Set.exists_min_image (p ⁻¹' {y₀}) h
    (Set.finite_of_encard_eq_coe hcard) ⟨x₀, hx₀⟩
  have hle (x y : T) (hxy : p x = p y) : h x ≤ h y := by
    by_contra hnle
    have hlt : h y < h x := lt_of_not_ge hnle
    let γ : Path e₀ x := (PathConnectedSpace.joined e₀ x).somePath
    let β := γ.symm.map hp.continuous
    let δ := hp.liftPath β.toContinuousMap y (β.source.trans hxy)
    have hδ : p ∘ δ = β := hp.liftPath_lifts _ _ _
    have hδ₀ : δ 0 = y := hp.liftPath_zero _ _ _
    have hδ₁ : δ 1 ∈ p ⁻¹' {y₀} := by
      have hend : p (δ 1) = p e₀ := by
        simpa [β] using congrFun hδ 1
      exact hend.trans he₀
    let Γ : Path y (δ 1) := ⟨δ, hδ₀, rfl⟩
    have hbase : p ∘ γ = p ∘ Γ.symm := by
      funext t
      have ht := congrFun hδ (unitInterval.symm t)
      simpa [β, Γ] using ht.symm
    obtain ⟨t, ht⟩ := intermediate_value_univ₂
      (hh.comp γ.continuous) (hh.comp Γ.symm.continuous)
      (show h (γ 0) ≤ h (Γ.symm 0) by simpa using hmin (δ 1) hδ₁)
      (show h (Γ.symm 1) ≤ h (γ 1) by simpa using hlt.le)
    have hmeet : γ t = Γ.symm t := hsep (Prod.ext (congrFun hbase t) ht)
    have heq := hp.eq_of_comp_eq γ.continuous Γ.symm.continuous hbase t hmeet
    have hend : x = y := by simpa using congrFun heq 1
    exact hlt.ne (congrArg h hend).symm
  have hinj : Function.Injective p := by
    intro x y hxy
    exact hsep (Prod.ext hxy (le_antisymm (hle x y hxy) (hle y x hxy.symm)))
  exact hne (hinj ((show p x₀ = y₀ from hx₀).trans (show p x₁ = y₀ from hx₁).symm))

end DifferentialGeometry.Topology.Covering
