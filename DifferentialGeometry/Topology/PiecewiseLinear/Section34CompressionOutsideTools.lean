/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionTools

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Exterior

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] {U : Set M₁} {h : M₁ → M₂} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

omit [MetricSpace M₂] in
open Classical in
theorem section34TetraObstacle_update_subset {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂} {s : Section34SimplexIndex 𝒦 3} {F Z : Set M₂}
    (hFZ : F ⊆ fbl s ∪ Z) (t : Section34SimplexIndex 𝒦 4) :
    section34TetraObstacle tgtV (Function.update fbl s F) t ⊆
      section34TetraObstacle tgtV fbl t ∪ Z := by
  classical
  rintro x (hx | hx)
  · exact Or.inl (Or.inl hx)
  · obtain ⟨s', hs', hx'⟩ := mem_iUnion₂.mp hx
    by_cases hne : s' = s
    · rw [hne, Function.update_self] at hx'
      rcases hFZ hx' with hx'' | hx''
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨s, hne ▸ hs', hx''⟩))
      · exact Or.inr hx''
    · rw [Function.update_of_ne hne] at hx'
      exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨s', hs', hx'⟩))

omit [MetricSpace M₂] in
open Classical in
theorem section34TetraObstacle_update_of_not_incident
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂} {fbl : Section34SimplexIndex 𝒦 3 → Set M₂}
    {s : Section34SimplexIndex 𝒦 3} (F : Set M₂) {t : Section34SimplexIndex 𝒦 4}
    (hst : ¬ Section34Incident s.1 t.1) :
    section34TetraObstacle tgtV (Function.update fbl s F) t =
      section34TetraObstacle tgtV fbl t := by
  classical
  simp only [section34TetraObstacle]
  congr 1
  refine iUnion₂_congr fun s' hs' => ?_
  have hne : s' ≠ s := by
    rintro rfl
    exact hst hs'
  rw [Function.update_of_ne hne]

open Classical in
theorem Section34Exterior.update_of_subset_union {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂} (hext : Section34Exterior 𝒦 𝒦' h H tgtV fbl)
    {s : Section34SimplexIndex 𝒦 3} {F Z : Set M₂} (hFZ : F ⊆ fbl s ∪ Z)
    (hZH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → Z ⊆ interior (H t.1))
    (hr : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → ∃ r : M₂ → M₂,
      ContinuousOn r (H t.1 \ section34TetraObstacle tgtV fbl t) ∧
      MapsTo r (H t.1 \ section34TetraObstacle tgtV fbl t)
        (H t.1 \ (section34TetraObstacle tgtV fbl t ∪ Z)) ∧
      (∀ z ∈ frontier (H t.1), r z = z) ∧
      ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
        ∀ y ∈ h '' simplexBody 𝒦' w.1, r y = y) :
    Section34Exterior 𝒦 𝒦' h H tgtV (Function.update fbl s F) := by
  classical
  obtain ⟨h1, h2, h3⟩ := hext
  refine ⟨fun t => ?_, h2, fun t w hw y hy hyH => ?_⟩
  · by_cases hst : Section34Incident s.1 t.1
    · exact (section34TetraObstacle_update_subset hFZ t).trans (union_subset (h1 t) (hZH t hst))
    · rw [section34TetraObstacle_update_of_not_incident F hst]
      exact h1 t
  · by_cases hst : Section34Incident s.1 t.1
    · obtain ⟨r, hrc, hrm, hrfr, hrw⟩ := hr t hst
      obtain ⟨hyo, z, hzC, hzfr⟩ := h3 t w hw y hy hyH
      have hyC : y ∈ H t.1 \ section34TetraObstacle tgtV fbl t := ⟨hyH, hyo⟩
      have hyr := hrw w hw y hy
      have hmem := hrm hyC
      rw [hyr] at hmem
      have hobs := section34TetraObstacle_update_subset (tgtV := tgtV) hFZ t
      refine ⟨fun hyo' => hmem.2 (hobs hyo'), ?_⟩
      have hCsub : connectedComponentIn (H t.1 \ section34TetraObstacle tgtV fbl t) y ⊆
          H t.1 \ section34TetraObstacle tgtV fbl t := connectedComponentIn_subset _ _
      have hpc : IsPreconnected
          (r '' connectedComponentIn (H t.1 \ section34TetraObstacle tgtV fbl t) y) :=
        isPreconnected_connectedComponentIn.image r (hrc.mono hCsub)
      have hsub : r '' connectedComponentIn (H t.1 \ section34TetraObstacle tgtV fbl t) y ⊆
          H t.1 \ section34TetraObstacle tgtV (Function.update fbl s F) t := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' := hrm (hCsub hx)
        exact ⟨hx'.1, fun hxo => hx'.2 (hobs hxo)⟩
      have hyimg : y ∈ r '' connectedComponentIn (H t.1 \ section34TetraObstacle tgtV fbl t) y :=
        ⟨y, mem_connectedComponentIn hyC, hyr⟩
      exact ⟨z, hpc.subset_connectedComponentIn hyimg hsub ⟨z, hzC, hrfr z hzfr⟩, hzfr⟩
    · rw [section34TetraObstacle_update_of_not_incident F hst]
      exact h3 t w hw y hy hyH

end Exterior

section Invariants

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

open Classical in
theorem section34FaceBallInvariants_update_of_subset_union
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂} {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl fblBd)
    {s : Section34SimplexIndex 𝒦 3} {F Fb Z : Set M₂} (hF : IsPLCellOn 3 F Fb)
    (hrim : h '' simplexRim 𝒦 s.1 ⊆ interior F) (hFZ : F ⊆ fbl s ∪ Z)
    (hZV : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 s.1 → Disjoint Z (tgtV w))
    (hZs : ∀ s', s' ≠ s → Disjoint Z (fbl s'))
    (hZH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → Z ⊆ interior (H t.1))
    (hr : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → ∃ r : M₂ → M₂,
      ContinuousOn r (H t.1 \ section34TetraObstacle tgtV fbl t) ∧
      MapsTo r (H t.1 \ section34TetraObstacle tgtV fbl t)
        (H t.1 \ (section34TetraObstacle tgtV fbl t ∪ Z)) ∧
      (∀ z ∈ frontier (H t.1), r z = z) ∧
      ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
        ∀ y ∈ h '' simplexBody 𝒦' w.1, r y = y)
    (h5 : ∀ y ∈ Fb ∩ frontier (⋃ w, tgtV w), ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
      y ∈ c.source ∧ HasPLCrossingAt (c '' (Fb ∩ c.source))
        (c '' (frontier (⋃ w, tgtV w) ∩ c.source)) (c y))
    (h6 : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∀ y ∈ Fb ∩ tgtEBd e,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCurveCrossingOnAt (c '' (frontier (⋃ w, tgtV w) ∩ c.source))
          (c '' (Fb ∩ frontier (⋃ w, tgtV w) ∩ c.source)) (c '' (tgtEBd e ∩ c.source)) (c y))
    (h7 : CarriesFirstHomologyOnto (Fb ∩ frontier (section34FaceTorus tgtV s))
      (section34FaceTorus tgtV s))
    (h8 : (Fb ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).Finite)
    (h9 : ((fun y => connectedComponentIn (Fb ∩ frontier (⋃ w, tgtV w)) y) ''
      (Fb ∩ frontier (⋃ w, tgtV w))).Finite) :
    Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd (Function.update fbl s F)
      (Function.update fblBd s Fb) := by
  classical
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩ := hinv
  have hFs : ∀ s', s' ≠ s → F ∩ fbl s' ⊆ fbl s ∩ fbl s' := by
    rintro s' hs' x ⟨hxF, hx'⟩
    rcases hFZ hxF with hx | hx
    · exact ⟨hx, hx'⟩
    · exact absurd hx' (Set.disjoint_left.mp (hZs s' hs') hx)
  refine ⟨fun s' => ?_, fun s' => ?_, fun s' w hw => ?_, fun s₁ s₂ hne => ?_, fun s' => ?_,
    fun s' e => ?_, fun s' => ?_, fun s' => ?_, fun s' => ?_,
    hc10.update_of_subset_union hFZ hZH hr⟩
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using hF
    · simpa only [Function.update_of_ne hs] using hc1 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using hrim
    · simpa only [Function.update_of_ne hs] using hc2 s'
  · by_cases hs : s' = s
    · have hw' : ¬ Section34Incident w.1 s.1 := by rwa [hs] at hw
      rw [hs, Function.update_self]
      refine eq_empty_iff_forall_notMem.mpr fun x ⟨hxF, hxw⟩ => ?_
      rcases hFZ hxF with hx | hx
      · have hmem : x ∈ fbl s ∩ tgtV w := ⟨hx, hxw⟩
        rw [hc3 s w hw'] at hmem
        exact hmem
      · exact Set.disjoint_left.mp (hZV w hw') hx hxw
    · rw [Function.update_of_ne hs]
      exact hc3 s' w hw
  · by_cases hs₁ : s₁ = s
    · have hs₂ : s₂ ≠ s := fun h => hne (hs₁.trans h.symm)
      rw [hs₁, Function.update_self, Function.update_of_ne hs₂]
      exact (hFs s₂ hs₂).trans (hc4 s s₂ fun h => hne (hs₁.trans h))
    · by_cases hs₂ : s₂ = s
      · rw [hs₂, Function.update_self, Function.update_of_ne hs₁, inter_comm]
        exact (hFs s₁ hs₁).trans ((inter_comm _ _).subset.trans
          (hc4 s₁ s fun h => hne (h.trans hs₂.symm)))
      · rw [Function.update_of_ne hs₁, Function.update_of_ne hs₂]
        exact hc4 s₁ s₂ hne
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h5
    · simpa only [Function.update_of_ne hs] using hc5 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h6 e
    · simpa only [Function.update_of_ne hs] using hc6 s' e
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h7
    · simpa only [Function.update_of_ne hs] using hc7 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h8
    · simpa only [Function.update_of_ne hs] using hc8 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [section34TraceComponents, Function.update_self] using h9
    · simpa only [section34TraceComponents, Function.update_of_ne hs] using hc9 s'

end Invariants

section Torus

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] {φ : E3 → Y} {S : Set Y}

theorem IsPLTorus.carriesFirstHomologyOnto_image_iUnion_ne_of_not_isPreconnected {ι : Type*}
    [Finite ι] {Θ : Set E3} {C : ι → Set E3} (hΘ : IsPLTorus Θ) (hC : ∀ i, IsPLSphere 1 (C i))
    (hCΘ : ∀ i, C i ⊆ Θ) (hCd : Pairwise fun i j => Disjoint (C i) (C j))
    (hφ : ContinuousOn φ Θ) (hφi : InjOn φ Θ) (hS : φ '' Θ ⊆ S)
    (hZ : CarriesFirstHomologyOnto (φ '' ⋃ i, C i) S) {i₀ : ι}
    (hsep : ¬ IsPreconnected (Θ \ C i₀)) :
    CarriesFirstHomologyOnto (φ '' ⋃ (i) (_ : i ≠ i₀), C i) S := by
  have hsub : φ '' ⋃ (i) (_ : i ≠ i₀), C i ⊆ S :=
    (image_mono (iUnion₂_subset fun i _ => hCΘ i)).trans hS
  rcases hΘ.carriesFirstHomologyOnto_or_subsingleton_of_iUnion hC hCΘ hCd hφ hφi hS hZ with
    ⟨i, hisep, hcarry⟩ | hsing
  · have hi : i ≠ i₀ := by
      rintro rfl
      exact hsep hisep
    exact hcarry.mono (image_mono (subset_iUnion₂ (s := fun i (_ : i ≠ i₀) => C i) i hi)) hsub
  · exact carriesFirstHomologyOnto_of_subsingleton hsub hsing

end Torus

end DifferentialGeometry.Topology.PiecewiseLinear
