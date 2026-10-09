/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import Mathlib.LinearAlgebra.Dual.Lemmas

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem hasPLCrossingAt_affineSubspace_fiber (P : Submodule ℝ E)
    (hP : Module.finrank ℝ P = 2) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) {d : E} (hd : d ∈ P) (hℓd : ℓ d ≠ 0) (x : E) :
    HasPLCrossingAt {y | y - x ∈ P} {y | ℓ y = ℓ x} x := by
  have hℓ : ℓ ≠ 0 := fun hz => hℓd (by rw [hz, LinearMap.zero_apply])
  have hker : Module.finrank ℝ (LinearMap.ker ℓ) = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hℓ
    omega
  have hsup : P ⊔ LinearMap.ker ℓ = ⊤ := sup_ker_eq_top_of_apply_ne_zero P ℓ hd hℓd
  have hinf : Module.finrank ℝ (P ⊓ LinearMap.ker ℓ : Submodule ℝ E) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P (LinearMap.ker ℓ)
    rw [hsup, finrank_top, hdimE, hP, hker] at h
    omega
  have hh : IsPLHomeomorphOn (fun y : E => y - x) univ univ := by
    simpa only [sub_eq_add_neg] using isPLHomeomorphOn_add_const (-x)
  refine ⟨univ, univ, fun y => y - x, P, LinearMap.ker ℓ, 0, 0,
    isOpen_univ, isOpen_univ, mem_univ x, hh, sub_self x, hP, hker, hinf, hsup,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Filter.Eventually.of_forall fun y => ?_⟩
  constructor
  · simp only [LinearMap.zero_apply, le_refl, and_true, mem_ofPred_eq]
  · simp only [LinearMap.zero_apply, le_refl, and_true, mem_ofPred_eq, LinearMap.mem_ker, map_sub,
      sub_eq_zero, sub_self]

theorem hasPLCrossingAt_fiber_of_transverse_face (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) {s : Finset E} (hs : s ∈ K.faces)
    {x d : E} (hx : x ∈ openSimplex s) (hd : d ∈ vectorSpan ℝ (s : Set E)) (hℓd : ℓ d ≠ 0) :
    HasPLCrossingAt K.space {y | ℓ y = ℓ x} x := by
  classical
  have hℓ : ℓ ≠ 0 := fun hz => hℓd (by rw [hz, LinearMap.zero_apply])
  obtain ⟨T, hT, hTcard, -, hKT, -, hspan⟩ := exists_simplex_containing_fiber K hdimE ℓ hℓ (ℓ x)
  let L := simplexComplex T hT
  let _ : Finite L.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have ht : T ∈ L.faces := ⟨hTne, Finset.Subset.refl T⟩
  have hLspace : L.space = convexHull ℝ (T : Set E) := simplexComplex_space T hT hTne
  have hLball : IsPLBall 2 L.space := by
    rw [hLspace]
    exact isPLBall_convexHull_of_affineIndependent _ hT hTcard
  have hxt := hKT ⟨K.convexHull_subset_space hs (openSimplex_subset_convexHull s hx), rfl⟩
  have hst : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (T : Set E) = ⊤ := by
    rw [hspan]
    exact sup_ker_eq_top_of_apply_ne_zero _ ℓ hd hℓd
  have hcross := hasPLCrossingAt_of_transverse_face K L hK
      hLball.isCombinatorialManifoldWithBoundary
    hdimE hs ht hx hxt hst
  apply hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
  filter_upwards [eventually_mem_convexHull_iff_sub_mem_vectorSpan hT hxt] with y hy
  rw [hLspace]
  refine hy.trans ?_
  rw [hspan]
  change ℓ (y - x) = 0 ↔ ℓ y = ℓ x
  rw [map_sub, sub_eq_zero]

theorem eventually_hasPLCrossingAt_fiber_of_transverse_face
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) {s : Finset E} (hs : s ∈ K.faces) {x d : E}
    (hx : x ∈ openSimplex s) (hd : d ∈ vectorSpan ℝ (s : Set E)) (hℓd : ℓ d ≠ 0) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, HasPLCrossingAt K.space {y | f y = f x} x := by
  have hne : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f d ≠ 0 :=
    (ContinuousLinearMap.apply ℝ ℝ d).continuous.continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hℓd)
  exact hne.mono fun f hf => hasPLCrossingAt_fiber_of_transverse_face K hK hdimE f.toLinearMap hs hx
      hd hf

theorem eventually_hasPLCrossingAt_fiber_of_affineSubspace_germ (P : Submodule ℝ E)
    (hP : Module.finrank ℝ P = 2) (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ)
    {d x : E} (hd : d ∈ P) (hℓd : ℓ d ≠ 0) {S : Set E}
    (hS : ∀ᶠ y in 𝓝 x, y ∈ S ↔ y - x ∈ P) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, HasPLCrossingAt S {y | f y = f x} x := by
  have hne : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f d ≠ 0 :=
    (ContinuousLinearMap.apply ℝ ℝ d).continuous.continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hℓd)
  filter_upwards [hne] with f hf
  exact (hasPLCrossingAt_affineSubspace_fiber P hP hdimE f.toLinearMap hd hf x).congr
    (hS.mono fun _ hy => hy.symm) (Filter.Eventually.of_forall fun _ => Iff.rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
