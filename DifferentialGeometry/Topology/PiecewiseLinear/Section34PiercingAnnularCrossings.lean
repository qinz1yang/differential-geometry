/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallUpdate
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSurfaceCharts
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingSurfaceLineChart
import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_piercing_annular_crossings
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (Cc w))
    (hleft : ∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
      interior (G (ends e).1 '' Tn e))
    (hright : ∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
      interior (G (ends e).2 '' Tn e))
    (c : Section34EdgeIndex 𝒦 𝒦' → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3)))
    (hcross : ∀ e, ∀ y ∈ G (ends e).1 '' CpBd (ends e).1 ∩
      G (ends e).2 '' CpBd (ends e).2, y ∈ (c e).source →
      HasPLCrossingAt (c e '' ((G (ends e).1 '' CpBd (ends e).1) ∩ (c e).source))
        (c e '' ((G (ends e).2 '' CpBd (ends e).2) ∩ (c e).source)) (c e y)) :
    ∀ e, ∀ x ∈ c e '' ((G (ends e).1 '' Aa e) ∩ (c e).source) ∩
      c e '' ((G (ends e).2 '' Bb e) ∩ (c e).source),
      HasPLCrossingAt (c e '' ((G (ends e).1 '' Aa e) ∩ (c e).source))
        (c e '' ((G (ends e).2 '' Bb e) ∩ (c e).source)) x ∧
      ∃ (V : Set (EuclideanSpace ℝ (Fin 3)))
        (φ : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ × ℝ) (ρ : ℝ),
        IsOpen V ∧ x ∈ V ∧ 0 < ρ ∧ IsPLHomeomorphOn φ V (Metric.ball 0 ρ) ∧ φ x = 0 ∧
        ∀ z ∈ V, (z ∈ c e '' ((G (ends e).1 '' Aa e) ∩ (c e).source) ↔
          (φ z).2.2 = 0) ∧ (z ∈ c e '' ((G (ends e).2 '' Bb e) ∩ (c e).source) ↔
          (φ z).2.1 = 0) := by
  obtain ⟨-, -, hsubs, -, hcp, -, -, -, -, -, -, htn, hsncc, -, haa, hbb, htb, -⟩ :=
    id hprep
  have hbd (w : Section34VertexIndex 𝒦 𝒦') : CpBd w ⊆ Cc w :=
    (hcp w).boundary_subset.trans (hsubs w).2.1
  have hT (e : Section34EdgeIndex 𝒦 𝒦') (w) (hw : w = (ends e).1 ∨ w = (ends e).2) :
      Tn e ⊆ Cc w := ((htn e).1.trans interior_subset).trans (hsncc e w hw)
  have hcell (w : Section34VertexIndex 𝒦 𝒦') :
      IsPLCellOn 3 (G w '' Cp w) (G w '' CpBd w) :=
    (hcp w).image ((hG w).mono_of_isPLCellOn (hcp w) (hsubs w).2.1)
  intro e x hx
  obtain ⟨y, ⟨hyA, hyc⟩, rfl⟩ := hx.1
  obtain ⟨z, ⟨hzB, hzc⟩, hzy⟩ := hx.2
  have hzy' : z = y := (c e).injOn hzc hyc hzy
  subst z
  have hAa : Aa e ⊆ CpBd (ends e).1 := by rw [(haa e).1]; exact inter_subset_left
  have hy : y ∈ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 :=
    ⟨image_mono hAa hyA, image_mono (hbb e).1 hzB⟩
  have heqA : (G (ends e).1 '' CpBd (ends e).1) ∩ interior (G (ends e).1 '' Tn e) =
      (G (ends e).1 '' Aa e) ∩ interior (G (ends e).1 '' Tn e) := by
    apply Subset.antisymm
    · rintro y ⟨⟨a, ha, rfl⟩, hyT⟩
      obtain ⟨b, hb, hba⟩ := interior_subset hyT
      have hba' : b = a := (hG _).injOn (hT e _ (Or.inl rfl) hb) (hbd _ ha) hba
      subst b
      refine ⟨mem_image_of_mem _ ?_, hyT⟩
      rw [(haa e).1]
      exact ⟨ha, hb⟩
    · exact inter_subset_inter_left _ (image_mono hAa)
  have heqB : (G (ends e).2 '' CpBd (ends e).2) ∩ interior (G (ends e).2 '' Tn e) =
      (G (ends e).2 '' Bb e) ∩ interior (G (ends e).2 '' Tn e) := by
    apply Subset.antisymm
    · rintro y ⟨⟨a, ha, rfl⟩, hyT⟩
      obtain ⟨b, hb, hba⟩ := interior_subset hyT
      have hba' : b = a := (hG _).injOn (hT e _ (Or.inr rfl) hb) (hbd _ ha) hba
      subst b
      exact ⟨mem_image_of_mem _ (htb e ⟨hb, ha⟩).1, hyT⟩
    · exact inter_subset_inter_left _ (image_mono (hbb e).1)
  have hAe := eventually_mem_image_inter_source_iff isOpen_interior heqA (hleft e hy) hyc
  have hBe := eventually_mem_image_inter_source_iff isOpen_interior heqB (hright e hy) hyc
  have hc := hcross e y hy hyc
  refine ⟨hc.congr hAe hBe, ?_⟩
  exact hc.exists_lineChart_of_eventuallyEq_surface_charts
    ⟨mem_image_of_mem _ ⟨hy.1, hyc⟩, mem_image_of_mem _ ⟨hy.2, hyc⟩⟩
    ((hcell _).exists_isOpen_inter_boundary_chart_image_homeomorph (c e) ⟨hy.1, hyc⟩)
    ((hcell _).exists_isOpen_inter_boundary_chart_image_homeomorph (c e) ⟨hy.2, hyc⟩)
    hAe hBe

end DifferentialGeometry.Topology.PiecewiseLinear
