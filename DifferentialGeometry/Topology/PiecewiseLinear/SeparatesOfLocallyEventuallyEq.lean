/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.LimitSeparation
import Mathlib.Topology.Connected.LocallyPathConnected

open Filter Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem separates_of_locally_eventually_eq {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {M : ℕ → Set X} {L H K : Set X} {p : X}
    (hM : ∀ n, IsClosed (M n)) (hsep : ∀ n, Separates (M n) H K) (hp : ∀ n, p ∈ M n)
    (hH : IsPreconnected H) (hK : IsPreconnected K) (hL : IsClosed L) (hpL : p ∈ L)
    (hloc : ∀ x, x ≠ p → ∃ U ∈ 𝓝 x, ∃ n₀ : ℕ, ∀ n ≥ n₀, M n ∩ U = L ∩ U) :
    Separates L H K := by
  let Z : Set X := closure {p}
  have hpZ : p ∈ Z := subset_closure (mem_singleton p)
  have hZM : ∀ n, Z ⊆ M n := fun n =>
    closure_minimal (singleton_subset_iff.mpr (hp n)) (hM n)
  have hZL : Z ⊆ L := closure_minimal (singleton_subset_iff.mpr hpL) hL
  have hstable : ∀ x ∈ Zᶜ, ∃ U ∈ 𝓝 x, ∃ N : ℕ,
      ∀ n ≥ N, ∀ y ∈ U, (y ∈ M n ↔ y ∈ M N) := by
    intro x hx
    have hxne : x ≠ p := by
      rintro rfl
      exact hx hpZ
    obtain ⟨U, hU, N, hN⟩ := hloc x hxne
    refine ⟨U, hU, N, fun n hn y hy => ?_⟩
    have heq := Set.ext_iff.mp ((hN n hn).trans (hN N le_rfl).symm) y
    simpa only [mem_inter_iff, hy, and_true] using heq
  have hopenPath : ∀ V : Set X, IsOpen V → IsConnected V → IsPathConnected V :=
    fun V hV hVconn => hV.isConnected_iff_isPathConnected.mp hVconn
  obtain ⟨Clim, -, hZlim, hcompact, hseplim⟩ :=
    exists_isClosed_separating_limit_of_locally_eventually_constant
      hopenPath M hM isClosed_closure hZM hstable hH hK hsep
  have hlim : Clim = L := by
    ext x
    by_cases hxZ : x ∈ Z
    · exact iff_of_true (hZlim hxZ) (hZL hxZ)
    · have hxne : x ≠ p := by
        rintro rfl
        exact hxZ hpZ
      obtain ⟨U, hU, N, hN⟩ := hloc x hxne
      obtain ⟨n, hn, hnN⟩ := ((hcompact {x} isCompact_singleton
        (singleton_subset_iff.mpr hxZ)).and (eventually_ge_atTop N)).exists
      have hxU : x ∈ U := mem_of_mem_nhds hU
      have hMlim : x ∈ M n ↔ x ∈ Clim := by
        simpa only [mem_inter_iff, mem_singleton_iff, and_true] using Set.ext_iff.mp hn x
      have hML : x ∈ M n ↔ x ∈ L := by
        simpa only [mem_inter_iff, hxU, and_true] using Set.ext_iff.mp (hN n hnN) x
      exact hMlim.symm.trans hML
  exact hlim ▸ hseplim

end DifferentialGeometry.Topology.PiecewiseLinear
