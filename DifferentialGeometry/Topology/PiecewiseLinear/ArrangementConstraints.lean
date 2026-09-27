/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeNormalForm

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsVertexMapGeneralInArrangement.card_le_finrank_of_zero
    {κ ι η ζ : Type*} {l : κ → E →ᵃ[ℝ] ℝ} {V B : Finset ι} {φ₀ φ : ι → E}
    {c : η → Finset ι} {s t : ζ → Finset ι}
    (h : IsVertexMapGeneralInArrangement l V B φ₀ φ c s t)
    (hfix : EqOn φ φ₀ (B : Set ι)) (j : η) (k : κ) (hk : (l k).linear ≠ 0)
    (hzero : ∀ v ∈ c j ∩ (B ∪ V), l k (φ₀ v) = 0) :
    (c j ∩ (B ∪ V)).card ≤ Module.finrank ℝ E := by
  let p : (c j ∩ (B ∪ V) : Finset ι) → E := fun v => φ v
  have hpzero : EqOn (l k) (fun _ => 0) (Set.range p) := by
    rintro _ ⟨v, rfl⟩
    rcases Finset.mem_union.mp (Finset.mem_inter.mp v.property).2 with hvB | hvV
    · change l k (φ v) = 0
      rw [hfix hvB]
      exact hzero v v.property
    · have hsign := congrFun (h.1 v hvV) k
      exact sign_eq_zero_iff.mp (hsign.trans (sign_eq_zero_iff.mpr (hzero v v.property)))
  have hle : vectorSpan ℝ (Set.range p) ≤ LinearMap.ker (l k).linear := by
    intro v hv
    exact AffineMap.linear_eqOn_vectorSpan (g := AffineMap.const ℝ E 0) hpzero hv
  calc
    (c j ∩ (B ∪ V)).card ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range p)) + 1 := by
      simpa only [Fintype.card_coe] using (h.2.1 j).card_le_finrank_succ
    _ ≤ Module.finrank ℝ (LinearMap.ker (l k).linear) + 1 :=
      Nat.add_le_add_right (Submodule.finrank_mono hle) 1
    _ = Module.finrank ℝ E := Module.Dual.finrank_ker_add_one_of_ne_zero hk

open Classical in
theorem IsVertexMapGeneralInArrangement.card_le_finrank_of_complete_zero
    {κ ι η ζ : Type*} {l : κ → E →ᵃ[ℝ] ℝ} {V B : Finset ι} {φ₀ φ : ι → E}
    {c : η → Finset ι} {s t : ζ → Finset ι}
    (h : IsVertexMapGeneralInArrangement l V B φ₀ φ c s t)
    (hfix : EqOn φ φ₀ (B : Set ι)) (q : ζ)
    (hcover : s q ∪ t q ⊆ B ∪ V)
    (hcomplete : ∀ u : Finset ι, u ⊆ s q ∪ t q →
      u.card ≤ Module.finrank ℝ (arrangementEnvelope l φ₀ (s q ∪ t q)).direction + 1 →
        ∃ j, c j = u)
    (u : Finset ι) (hu : u ⊆ s q ∪ t q)
    (hcard : u.card ≤ Module.finrank ℝ (arrangementEnvelope l φ₀ (s q ∪ t q)).direction + 1)
    (k : κ) (hk : (l k).linear ≠ 0) (hzero : ∀ v ∈ u, l k (φ₀ v) = 0) :
    u.card ≤ Module.finrank ℝ E := by
  obtain ⟨j, hj⟩ := hcomplete u hu hcard
  have hinter : c j ∩ (B ∪ V) = u := by
    rw [hj, Finset.inter_eq_left.mpr (hu.trans hcover)]
  have hz : ∀ v ∈ c j ∩ (B ∪ V), l k (φ₀ v) = 0 := by
    simpa only [hinter] using hzero
  simpa only [hinter] using h.card_le_finrank_of_zero hfix j k hk hz

open Classical in
theorem not_isVertexMapGeneralInArrangement_of_complete_hyperplane
    {κ ι η ζ : Type*} {l : κ → E →ᵃ[ℝ] ℝ} {V B : Finset ι} {φ₀ φ : ι → E}
    {c : η → Finset ι} {s t : ζ → Finset ι}
    (hfix : EqOn φ φ₀ (B : Set ι)) (q : ζ)
    (hcover : s q ∪ t q ⊆ B ∪ V)
    (hcomplete : ∀ u : Finset ι, u ⊆ s q ∪ t q →
      u.card ≤ Module.finrank ℝ (arrangementEnvelope l φ₀ (s q ∪ t q)).direction + 1 →
        ∃ j, c j = u)
    (henv : (arrangementEnvelope l φ₀ (s q ∪ t q)).direction = ⊤)
    (u : Finset ι) (hu : u ⊆ s q ∪ t q) (hcard : u.card = Module.finrank ℝ E + 1)
    (k : κ) (hk : (l k).linear ≠ 0) (hzero : ∀ v ∈ u, l k (φ₀ v) = 0) :
    ¬ IsVertexMapGeneralInArrangement l V B φ₀ φ c s t := by
  intro h
  have hcard' : u.card ≤
      Module.finrank ℝ (arrangementEnvelope l φ₀ (s q ∪ t q)).direction + 1 := by
    rw [henv, finrank_top, hcard]
  have hbound := h.card_le_finrank_of_complete_zero hfix q hcover hcomplete u hu hcard' k hk hzero
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
