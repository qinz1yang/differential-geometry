/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringLift
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.ZMultiples
import Mathlib.Topology.UrysohnsLemma

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPreconnected.eq_of_forall_eq_intCast {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {f : X → ℝ} (hf : ContinuousOn f S)
    (hint : ∀ x ∈ S, ∃ n : ℤ, f x = n) {x y : X} (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  have hI := hS.image f hf
  have key : ∀ a ∈ S, ∀ b ∈ S, ¬ f a < f b := by
    intro a ha b hb hab
    obtain ⟨m, hm⟩ := hint a ha
    obtain ⟨k, hk⟩ := hint b hb
    have hmk : m < k := by
      rw [hm, hk] at hab
      exact_mod_cast hab
    have hmk' : (m : ℝ) + 1 ≤ k := by exact_mod_cast Int.add_one_le_iff.mpr hmk
    obtain ⟨z, hz, hfz⟩ := hI.Icc_subset (mem_image_of_mem f ha) (mem_image_of_mem f hb)
      (show f a + 1 / 2 ∈ Icc (f a) (f b) from ⟨by linarith, by rw [hm, hk]; linarith⟩)
    obtain ⟨l, hl⟩ := hint z hz
    have h2 : ((2 * (l - m) : ℤ) : ℝ) = 1 := by
      push_cast
      linarith
    have h3 : 2 * (l - m) = 1 := by exact_mod_cast h2
    omega
  rcases lt_trichotomy (f x) (f y) with h | h | h
  · exact absurd h (key x hx y hy)
  · exact h
  · exact absurd h (key y hy x hx)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLBall.not_subset_union_of_joined_twice {n : ℕ} {D V T E₀ E₁ A B : Set E}
    (hD : IsPLBall n D) (hV : IsClosed V) (hT : IsClosed T) (hE₀ : IsClosed E₀)
    (hE₁ : IsClosed E₁) (hE : Disjoint E₀ E₁) (hVT : V ∩ T ⊆ E₀ ∪ E₁)
    (hA : IsPreconnected A) (hAV : A ⊆ V) (hAD : A ⊆ D)
    (hB : IsPreconnected B) (hBT : B ⊆ T) (hBD : B ⊆ D) {p₀ p₁ : E}
    (hp₀ : p₀ ∈ A ∩ B ∩ E₀) (hp₁ : p₁ ∈ A ∩ B ∩ E₁) : ¬ D ⊆ V ∪ T := by
  classical
  intro hDVT
  obtain ⟨φ, hφ₀, hφ₁, -⟩ := exists_continuous_zero_one_of_isClosed hE₀ hE₁ hE
  have hcov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let g : E → AddCircle (1 : ℝ) := fun x => if x ∈ V then (φ x : AddCircle (1 : ℝ)) else 0
  have hgV : ∀ x ∈ V, g x = (φ x : AddCircle (1 : ℝ)) := fun x hx => ite_eq_left hx
  have hgT : ∀ x ∈ T, g x = 0 := by
    intro x hx
    by_cases hxV : x ∈ V
    · rw [hgV x hxV]
      rcases hVT ⟨hxV, hx⟩ with h | h
      · rw [hφ₀ h]
        exact AddCircle.coe_zero (1 : ℝ)
      · rw [hφ₁ h]
        exact AddCircle.coe_period (1 : ℝ)
    · exact ite_eq_right hxV
  have hgc : ContinuousOn g (V ∪ T) := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ hV hT
    · exact (hcov.continuous.comp φ.continuous).continuousOn.congr hgV
    · exact continuousOn_const.congr hgT
  let F : C(D, AddCircle (1 : ℝ)) :=
    ⟨fun y => g y, (hgc.mono hDVT).comp_continuous continuous_subtype_val fun y => y.2⟩
  have hp₀D : p₀ ∈ D := hAD hp₀.1.1
  obtain ⟨G, ⟨hGF, -⟩, -⟩ := hcov.exists_unique_lift_of_isPLBall hD F ⟨p₀, hp₀D⟩ 0
    ((AddCircle.coe_zero (1 : ℝ)).trans (hgT p₀ (hBT hp₀.1.2)).symm)
  let Gt : E → ℝ := fun x => if hx : x ∈ D then G ⟨x, hx⟩ else 0
  have hGt : ∀ x (hx : x ∈ D), Gt x = G ⟨x, hx⟩ := fun x hx => dite_eq_left hx
  have hGtc : ContinuousOn Gt D := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hres : D.domRestrict Gt = G := funext fun y => hGt y y.2
    rw [hres]
    exact G.continuous
  have hlift : ∀ x ∈ D, (Gt x : AddCircle (1 : ℝ)) = g x := by
    intro x hx
    rw [hGt x hx]
    exact congrFun hGF ⟨x, hx⟩
  have hB' : Gt p₀ = Gt p₁ := by
    refine IsPreconnected.eq_of_forall_eq_intCast hB (hGtc.mono hBD) (fun x hx => ?_)
      hp₀.1.2 hp₁.1.2
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp
      ((hlift x (hBD hx)).trans (hgT x (hBT hx)))
    exact ⟨k, by rw [← hk, zsmul_eq_mul, mul_one]⟩
  have hA' : Gt p₀ - φ p₀ = Gt p₁ - φ p₁ := by
    refine IsPreconnected.eq_of_forall_eq_intCast hA (f := fun x => Gt x - φ x)
      ((hGtc.mono hAD).sub φ.continuous.continuousOn) (fun x hx => ?_) hp₀.1.1 hp₁.1.1
    have hz : ((Gt x - φ x : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, hlift x (hAD hx), hgV x (hAV hx), sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    exact ⟨k, by rw [← hk, zsmul_eq_mul, mul_one]⟩
  have h0 : φ p₀ = 0 := hφ₀ hp₀.2
  have h1 : φ p₁ = 1 := hφ₁ hp₁.2
  rw [h0, h1] at hA'
  linarith

end DifferentialGeometry.Topology.PiecewiseLinear
