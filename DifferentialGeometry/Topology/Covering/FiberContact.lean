import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology

namespace DifferentialGeometry.Topology.Covering

private theorem eq_of_contact_germs_along_lifts
    {S T Y : Type*} [TopologicalSpace S] [PreconnectedSpace S]
    [TopologicalSpace T] {p : T → Y} {h : T → ℝ}
    (hh : Continuous h)
    (hcontact : ∀ x y : T, p x = p y → h x = h y →
      ∀ᶠ xy : T × T in 𝓝 (x, y), p xy.1 = p xy.2 → h xy.1 = h xy.2)
    {α β : S → T} (hα : Continuous α) (hβ : Continuous β)
    (hbase : ∀ t, p (α t) = p (β t))
    {s : S} (hs : h (α s) = h (β s)) : ∀ t, h (α t) = h (β t) := by
  have hclosed : IsClosed {t | h (α t) = h (β t)} :=
    isClosed_eq (hh.comp hα) (hh.comp hβ)
  have hopen : IsOpen {t | h (α t) = h (β t)} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hnear : ∀ᶠ t' in 𝓝 t,
        p (α t') = p (β t') → h (α t') = h (β t') :=
      (hα.prodMk hβ).continuousAt.eventually (hcontact (α t) (β t) (hbase t) ht)
    filter_upwards [hnear] with t' ht'
    exact ht' (hbase t')
  have hall : {t | h (α t) = h (β t)} = univ :=
    (show IsClopen {t | h (α t) = h (β t)} from ⟨hclosed, hopen⟩).eq_univ ⟨s, hs⟩
  intro t
  exact Set.eq_univ_iff_forall.mp hall t

/-- On a path connected covering with a finite fiber, a continuous real height
is constant on each fiber if equal-height contacts persist in local sheet germs.
The hypothesis concerns only contacts, not arbitrary pairs in a fiber. -/
theorem factorsThrough_of_finite_fiber_of_contact_germs
    {T Y : Type*} [TopologicalSpace T] [PathConnectedSpace T]
    [TopologicalSpace Y] {p : T → Y} (hp : IsCoveringMap p)
    (x₀ : T) (hfinite : (p ⁻¹' {p x₀}).Finite)
    (h : T → ℝ) (hh : Continuous h)
    (hcontact : ∀ x y : T, p x = p y → h x = h y →
      ∀ᶠ xy : T × T in 𝓝 (x, y), p xy.1 = p xy.2 → h xy.1 = h xy.2) :
    Function.FactorsThrough h p := by
  obtain ⟨e₀, he₀, hmin⟩ := Set.exists_min_image (p ⁻¹' {p x₀}) h
    hfinite ⟨x₀, rfl⟩
  have hle (x y : T) (hxy : p x = p y) : h x ≤ h y := by
    by_contra hnle
    have hlt : h y < h x := lt_of_not_ge hnle
    let γ : Path e₀ x := (PathConnectedSpace.joined e₀ x).somePath
    let β := γ.symm.map hp.continuous
    let δ := hp.liftPath β.toContinuousMap y (β.source.trans hxy)
    have hδ : p ∘ δ = β := hp.liftPath_lifts _ _ _
    have hδ₀ : δ 0 = y := hp.liftPath_zero _ _ _
    have hδ₁ : δ 1 ∈ p ⁻¹' {p x₀} := by
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
    have heq := eq_of_contact_germs_along_lifts hh hcontact
      γ.continuous Γ.symm.continuous (congrFun hbase) ht
    have hend : h x = h y := by simpa using heq 1
    exact hlt.ne hend.symm
  intro x y hxy
  exact le_antisymm (hle x y hxy) (hle y x hxy.symm)

end DifferentialGeometry.Topology.Covering
