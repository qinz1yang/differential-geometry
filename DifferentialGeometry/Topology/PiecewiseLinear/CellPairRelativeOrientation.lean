/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairComparison
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellMapInterior
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellRelativeOrientation
import DifferentialGeometry.Topology.LocalDegree.ChartComparison

open Set Filter
open scoped Topology Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.LocalDegree

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem relative_parity_eq_of_open_restriction
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {A W : Set M} (hA : IsPreconnected A) (hW : IsOpen W) (hne : W.Nonempty) (hWA : W ⊆ A)
    (H T R F : OpenPartialHomeomorph M N) (c : OpenPartialHomeomorph N E3)
    (hAH : A ⊆ H.source) (hAT : A ⊆ T.source)
    (hHc : MapsTo H A c.source) (hTc : MapsTo T A c.source)
    (hWR : W ⊆ R.source) (hWF : W ⊆ F.source)
    (hHR : EqOn H R W) (hTF : EqOn T F W) {σ : ZMod 2}
    (hσ : ∀ x (hxR : x ∈ R.source) (hxF : x ∈ F.source)
      (hRc : R x ∈ c.source) (hFc : F x ∈ c.source),
      chartOrientationParity (R ≫ₕ c) (F ≫ₕ c) x ⟨hxR, hRc⟩ ⟨hxF, hFc⟩ = σ) :
    ∀ x (hx : x ∈ A), chartOrientationParity (H ≫ₕ c) (T ≫ₕ c) x
      ⟨hAH hx, hHc hx⟩ ⟨hAT hx, hTc hx⟩ = σ := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hRc : R x₀ ∈ c.source := (hHR hx₀) ▸ hHc (hWA hx₀)
  have hFc : F x₀ ∈ c.source := (hTF hx₀) ▸ hTc (hWA hx₀)
  have hHRg : (H ≫ₕ c) =ᶠ[𝓝 x₀] (R ≫ₕ c) := by
    filter_upwards [hW.mem_nhds hx₀] with y hy
    exact congrArg c (hHR hy)
  have hTFg : (T ≫ₕ c) =ᶠ[𝓝 x₀] (F ≫ₕ c) := by
    filter_upwards [hW.mem_nhds hx₀] with y hy
    exact congrArg c (hTF hy)
  have hg := chartOrientationParity_congr (H ≫ₕ c) (T ≫ₕ c) (R ≫ₕ c) (F ≫ₕ c) x₀
    ⟨hAH (hWA hx₀), hHc (hWA hx₀)⟩ ⟨hAT (hWA hx₀), hTc (hWA hx₀)⟩
    ⟨hWR hx₀, hRc⟩ ⟨hWF hx₀, hFc⟩ hHRg hTFg
  intro x hx
  exact (chartOrientationParity_eq_of_isPreconnected (H ≫ₕ c) (T ≫ₕ c) hA
    (fun _ hy => ⟨hAH hy, hHc hy⟩) (fun _ hy => ⟨hAT hy, hTc hy⟩) hx (hWA hx₀)).trans
      (hg.trans (hσ x₀ (hWR hx₀) (hWF hx₀) hRc hFc))

variable {M N : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
  [MetricSpace N] [ChartedSpace E3 N]

theorem exists_comparison_map_with_orientation_of_cell_pair
    {P PB Q QB D J : Set M} {P' PB' Q' QB' D' : Set N}
    (hP : IsPLCellOn 3 P PB) (hQ : IsPLCellOn 3 Q QB)
    (hP' : IsPLCellOn 3 P' PB') (hQ' : IsPLCellOn 3 Q' QB')
    (hD : IsPLCellOn 2 D J) (hPQ : P ∩ Q = D) (hP'Q' : P' ∩ Q' = D')
    (hDP : D ⊆ PB) (hDQ : D ⊆ QB) (hDP' : D' ⊆ PB') (hDQ' : D' ⊆ QB')
    {f g h : M → N} (hf : IsPLHomeomorphInto 3 f P) (hfim : f '' P = P')
    (hg : IsPLHomeomorphInto 3 g Q) (hgim : g '' Q = Q')
    (hfD : f '' D = D') (hgD : g '' D = D')
    (hh : ContinuousOn h (P ∪ Q)) (hhi : InjOn h (P ∪ Q))
    (HP FP HQ FQ : OpenPartialHomeomorph M N)
    (hHPs : HP.source = interior P) (hFPs : FP.source = interior P)
    (hHQs : HQ.source = interior Q) (hFQs : FQ.source = interior Q)
    (hHP : ∀ x, HP x = h x) (hFP : ∀ x, FP x = f x)
    (hHQ : ∀ x, HQ x = h x) (hFQ : ∀ x, FQ x = g x)
    (c : OpenPartialHomeomorph N E3) (hcH : h '' (P ∪ Q) ⊆ c.source)
    (hcT : P' ∪ Q' ⊆ c.source) {σP σQ : ZMod 2}
    (hσP : ∀ x (hxH : x ∈ HP.source) (hxF : x ∈ FP.source)
      (hxc : HP x ∈ c.source) (hxfc : FP x ∈ c.source),
      chartOrientationParity (HP ≫ₕ c) (FP ≫ₕ c) x ⟨hxH, hxc⟩ ⟨hxF, hxfc⟩ = σP)
    (hσQ : ∀ x (hxH : x ∈ HQ.source) (hxF : x ∈ FQ.source)
      (hxc : HQ x ∈ c.source) (hxfc : FQ x ∈ c.source),
      chartOrientationParity (HQ ≫ₕ c) (FQ ≫ₕ c) x ⟨hxH, hxc⟩ ⟨hxF, hxfc⟩ = σQ) :
    ∃ (K : N → N) (L : OpenPartialHomeomorph N N),
      IsPLHomeomorphInto 3 K (P' ∪ Q') ∧ K '' (P' ∪ Q') = P' ∪ Q' ∧
      K '' P' = P' ∧ K '' Q' = Q' ∧ EqOn (K ∘ g) f D ∧
      L.source = interior (P' ∪ Q') ∧ L.target = interior (P' ∪ Q') ∧
      (∀ y, L y = K y) ∧
      ∀ y (hy : y ∈ L.source) (hyc : y ∈ c.source) (hLyc : L y ∈ c.source),
        chartOrientationParity c (L ≫ₕ c) y hyc ⟨hy, hLyc⟩ = σP + σQ := by
  have : Nonempty M := ⟨hP.nonempty.choose⟩
  obtain ⟨T₁, T₂, K, hT₁, hT₂, hT₁P, hT₁Q, hT₂P, hT₂Q, hT₁f, hT₂g,
    hK, hKim, hKP, hKQ, hKT, hKgf⟩ := exists_comparison_map_of_cell_pair
      hP hQ hP' hQ' hD hPQ hP'Q' hDP hDQ hDP' hDQ' hf hfim hg hgim hfD hgD
  have hS := isPLCellOn_union_of_inter_eq_disk hP hQ hD hPQ hDP hDQ
  have hD' := hD.image (hf.mono_of_isPLCellOn hD (hDP.trans hP.boundary_subset))
  rw [hfD] at hD'
  have hS' := isPLCellOn_union_of_inter_eq_disk hP' hQ' hD' hP'Q' hDP' hDQ'
  have hT₁im : T₁ '' (P ∪ Q) = P' ∪ Q' := by rw [image_union, hT₁P, hT₁Q]
  have hT₂im : T₂ '' (P ∪ Q) = P' ∪ Q' := by rw [image_union, hT₂P, hT₂Q]
  obtain ⟨H, hHs, -, hH⟩ := exists_openPartialHomeomorph_of_continuousOn_injOn
    (E := E3) isOpen_interior (hh.mono interior_subset) (hhi.mono interior_subset)
  obtain ⟨T₁o, hT₁s, hT₁t, hT₁v⟩ := hS.exists_openPartialHomeomorph_of_map hT₁
  obtain ⟨T₂o, hT₂s, hT₂t, hT₂v⟩ := hS.exists_openPartialHomeomorph_of_map hT₂
  obtain ⟨L, hLs, hLt, hL⟩ := hS'.exists_openPartialHomeomorph_of_map hK
  rw [hT₁im] at hT₁t
  rw [hT₂im] at hT₂t
  rw [hKim] at hLt
  have hAH : interior (P ∪ Q) ⊆ H.source := hHs ▸ Subset.rfl
  have hAT₁ : interior (P ∪ Q) ⊆ T₁o.source := hT₁s ▸ Subset.rfl
  have hAT₂ : interior (P ∪ Q) ⊆ T₂o.source := hT₂s ▸ Subset.rfl
  have hHc : MapsTo H (interior (P ∪ Q)) c.source := by
    intro x hx
    rw [hH]
    exact hcH ⟨x, interior_subset hx, rfl⟩
  have hT₁c : MapsTo T₁o (interior (P ∪ Q)) c.source := by
    intro x hx
    exact hcT (interior_subset (hT₁t ▸ T₁o.map_source (hAT₁ hx)))
  have hT₂c : MapsTo T₂o (interior (P ∪ Q)) c.source := by
    intro x hx
    exact hcT (interior_subset (hT₂t ▸ T₂o.map_source (hAT₂ hx)))
  have hPsign := relative_parity_eq_of_open_restriction hS.isConnected_interior.isPreconnected
    isOpen_interior hP.isConnected_interior.nonempty (interior_mono subset_union_left)
    H T₁o HP FP c hAH hAT₁ hHc hT₁c (hHPs ▸ Subset.rfl) (hFPs ▸ Subset.rfl)
    (fun x _ => (hH x).trans (hHP x).symm)
    (fun x hx => (hT₁v x).trans ((hT₁f (interior_subset hx)).trans (hFP x).symm)) hσP
  have hQsign := relative_parity_eq_of_open_restriction hS.isConnected_interior.isPreconnected
    isOpen_interior hQ.isConnected_interior.nonempty (interior_mono subset_union_right)
    H T₂o HQ FQ c hAH hAT₂ hHc hT₂c (hHQs ▸ Subset.rfl) (hFQs ▸ Subset.rfl)
    (fun x _ => (hH x).trans (hHQ x).symm)
    (fun x hx => (hT₂v x).trans ((hT₂g (interior_subset hx)).trans (hFQ x).symm)) hσQ
  obtain ⟨x, hx⟩ := hS.isConnected_interior.nonempty
  have hxL : T₂o x ∈ L.source := hLs ▸ (hT₂t ▸ T₂o.map_source (hAT₂ hx))
  have hcomp : (L ∘ T₂o) =ᶠ[𝓝 x] T₁o := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    change L (T₂o y) = T₁o y
    rw [hT₂v, hL, hT₁v]
    exact hKT y (interior_subset hy)
  have hcmp := chartOrientationParity_comparison H T₁o T₂o L c x
    (hAH hx) (hAT₁ hx) (hAT₂ hx) hxL (hHc hx) (hT₁c hx) (hT₂c hx) hcomp
  rw [hPsign x hx, hQsign x hx] at hcmp
  have hAL : interior (P' ∪ Q') ⊆ L.source := hLs ▸ Subset.rfl
  have hAc : interior (P' ∪ Q') ⊆ c.source := interior_subset.trans hcT
  have hALc : MapsTo L (interior (P' ∪ Q')) c.source := fun _ hy =>
    hcT (interior_subset (hLt ▸ L.map_source (hAL hy)))
  refine ⟨K, L, hK, hKim, hKP, hKQ, hKgf, hLs, hLt, hL, ?_⟩
  intro y hy hyc hLyc
  have hy' : y ∈ interior (P' ∪ Q') := hLs ▸ hy
  have hx' : T₂o x ∈ interior (P' ∪ Q') := hLs ▸ hxL
  exact (chartOrientationParity_eq_of_isPreconnected c (L ≫ₕ c)
    hS'.isConnected_interior.isPreconnected hAc (fun _ ht => ⟨hAL ht, hALc ht⟩)
    hy' hx').trans hcmp

end DifferentialGeometry.Topology.PiecewiseLinear
