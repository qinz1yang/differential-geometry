/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

def Section34ConfinedTubePiercingConditions (U : Set M₁)
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (h : M₁ → M₂) (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (Cp CpBd Cc : Section34VertexIndex 𝒦 𝒦' → Set M₁)
    (Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁)
    (Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂) (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ)
    (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂)
    (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) : Prop :=
  (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) ∧
  (∀ w, G w '' Cc w ⊆ Q w) ∧
  (∀ e, Sp e ⊆ Q (ends e).1 ∩ Q (ends e).2) ∧
  (∀ e, Sp e = G (ends e).1 '' Sn e ∧ Tp e = G (ends e).1 '' Tn e) ∧
  LocallyFinite (fun e => {y : h '' U | (y : M₂) ∈ Sp e}) ∧
  (∀ e d, e ≠ d → Disjoint (Sp e) (Sp d)) ∧
  (∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
    G (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
      G (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)) ∩ interior (Tp e)) ∧
  (∀ e, G (ends e).1 '' Ab₀ e ⊆ interior (G (ends e).2 '' Cp (ends e).2) ∧
    Disjoint (G (ends e).1 '' Ab₁ e) (G (ends e).2 '' Cp (ends e).2)) ∧
  (∀ e, G (ends e).2 '' Bb e ⊆ interior (Sp e) ∧
    Disjoint (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) (Tp e)) ∧
  (∀ e, Disjoint (Sp e) (h '' graphSkeletonSpace 𝒦)) ∧
  (∀ w, IsPLHomeomorphInto 3 (G w) (Cp w)) ∧
  (∀ w e, Disjoint (G w '' simplexBody 𝒦' w.1) (Sp e)) ∧
  (∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → Disjoint (Sp e) (G w '' CpBd w)) ∧
  (∀ w w', Disjoint (Cp w) (Cp w') → Disjoint (G w '' Cp w) (G w' '' Cp w')) ∧
  (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
    ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y₀) ∧
  (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
    ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y₀) ∧
  (∀ e, 0 < cnt e ∧
    G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e = ⋃ i < cnt e, Pg e i) ∧
  (∀ e, ∀ i < cnt e, IsPolyhedralSphere (n := 3) 1 (Pg e i) ∧
    Pg e i ⊆ G (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
      G (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e))) ∧
  (∀ e, ∀ i < cnt e, ∀ j < cnt e, i ≠ j → Disjoint (Pg e i) (Pg e j)) ∧
  (∀ e, ∀ y ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e,
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
      HasPLCrossingAt (c '' (G (ends e).1 '' Aa e ∩ c.source))
        (c '' (G (ends e).2 '' Bb e ∩ c.source)) (c y)) ∧
  (∀ e d, e ≠ d →
    Disjoint (G (ends e).1 '' Cp (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2)
      (G (ends d).1 '' Cp (ends d).1 ∩ G (ends d).2 '' Cp (ends d).2)) ∧
  ∀ w w', w ≠ w' → Disjoint (h '' simplexBody 𝒦' w.1) (G w' '' Cp w')

variable {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {h : M₁ → M₂}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem Section34PiercingConditions.confinedTube
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) :
    Section34ConfinedTubePiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hSnCc, -⟩ := hprep
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19,
    p20, p21, p22⟩ := hpack
  refine ⟨p1, p2, fun e => ?_, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17,
    p18, p19, p20, p21, p22⟩
  rw [(p4 e).1]
  exact subset_inter ((image_mono (hSnCc e _ (Or.inl rfl))).trans (p2 _)) (p3 e).2

end DifferentialGeometry.Topology.PiecewiseLinear
