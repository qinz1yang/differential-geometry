/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ} {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem piercing_conditions_of_crossings_and_margins
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hQlfU : LocallyFinite fun w => {y : h '' U | (y : M₂) ∈ Q w})
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (Cc w))
    (hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w)
    (himages : ∀ e, Sp e = G (ends e).1 '' Sn e ∧ Tp e = G (ends e).1 '' Tn e)
    (htraceInside : ∀ e,
      G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
        interior (Tp e))
    (hAb₀Inside : ∀ e, G (ends e).1 '' Ab₀ e ⊆ interior (G (ends e).2 '' Cp (ends e).2))
    (hBbInside : ∀ e, G (ends e).2 '' Bb e ⊆ interior (Sp e))
    (hcomponentInside : ∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
        z ∈ connectedComponentIn
          (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y₀)
    (hcomponentOutside : ∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
      ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
        z ∈ connectedComponentIn
          (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y₀)
    (hcircles : ∀ e, 0 < cnt e ∧
      G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e = ⋃ i < cnt e, Pg e i)
    (hcirclesPoly : ∀ e, ∀ i < cnt e, IsPolyhedralSphere (n := 3) 1 (Pg e i) ∧
      Pg e i ⊆ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e)
    (hcirclesDisjoint : ∀ e, ∀ i < cnt e, ∀ j < cnt e, i ≠ j → Disjoint (Pg e i) (Pg e j))
    (hcrossing : ∀ e, ∀ y ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCrossingAt (c '' (G (ends e).1 '' Aa e ∩ c.source))
          (c '' (G (ends e).2 '' Bb e ∩ c.source)) (c y)) :
    Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
      Sp Tp cnt Pg G := by
  obtain ⟨-, -, hsubs, -, hcpcell, -, -, -, hends, -, -, -, hsncc, -, hAa, hBb, -⟩ := id hprep
  have hCpCc : ∀ w, Cp w ⊆ Cc w := fun w => (hsubs w).2.1
  have hGp : ∀ w, IsPLHomeomorphInto 3 (G w) (Cp w) := fun w =>
    (hG w).mono_of_isPLCellOn (hcpcell w) (hCpCc w)
  obtain ⟨hcellQ, htubeQ, hBbDisjoint, hgraph, htubes, hannuli, hAb₁Disjoint,
    hmarkers, hforeign, hcells⟩ := section34MarginConditions hprep hGdist
  have hSpQ : ∀ e, Sp e ⊆ Q (ends e).1 := by
    intro e
    rw [(himages e).1]
    exact (image_mono (hsncc e _ (Or.inl rfl))).trans (hcellQ _)
  have hlocal : LocallyFinite fun e => {y : h '' U | (y : M₂) ∈ Sp e} :=
    locallyFinite_support_of_section34CutFrame Sp hframe (fun e => (hends e).2.2)
      hSpQ hQlfU
  have hoverlap := section34OverlapConditions hprep (G := G) (fun w z hz => by
    rw [dist_comm]
    exact hGdist w z (hCpCc w hz))
  have hmarker := (section34MarkerConditions hprep hGp hGdist).2.2
  refine ⟨hG, hcellQ, htubeQ, himages, hlocal, ?_, ?_, ?_, ?_, ?_, hGp, ?_, ?_, hcells,
    hcomponentInside, hcomponentOutside, hcircles, ?_, hcirclesDisjoint,
    hcrossing, hoverlap, hmarker⟩
  · intro e d hed
    rw [(himages e).1, (himages d).1]
    exact htubes e d hed
  · intro e
    exact subset_inter (hannuli e) (htraceInside e)
  · exact fun e => ⟨hAb₀Inside e, hAb₁Disjoint e⟩
  · intro e
    refine ⟨hBbInside e, ?_⟩
    rw [(himages e).2]
    exact hBbDisjoint e
  · intro e
    rw [(himages e).1]
    exact hgraph e
  · intro w e
    rw [(himages e).1]
    exact hmarkers w e
  · intro e w hwa hwb
    rw [(himages e).1]
    exact hforeign e w hwa hwb
  · intro e i hi
    refine ⟨(hcirclesPoly e i hi).1, ((hcirclesPoly e i hi).2.trans ?_).trans (hannuli e)⟩
    have hAaBd : Aa e ⊆ CpBd (ends e).1 := by
      rw [(hAa e).1]
      exact inter_subset_left
    exact inter_subset_inter (image_mono hAaBd) (image_mono (hBb e).1)

end DifferentialGeometry.Topology.PiecewiseLinear
