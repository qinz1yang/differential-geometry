/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section CurveCrossing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasPLCurveCrossingOnAt (S A B : Set E) (x : E) : Prop :=
  ∃ (U V : Set E) (φ : E → E) (T P Q : Submodule ℝ E),
    IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ IsPLHomeomorphOn φ U V ∧ φ x = 0 ∧
      Module.finrank ℝ T = 2 ∧ Module.finrank ℝ P = 1 ∧ Module.finrank ℝ Q = 1 ∧
      P ≤ T ∧ Q ≤ T ∧ P ⊓ Q = ⊥ ∧ ∀ᶠ y in 𝓝 x,
        (y ∈ S ↔ φ y ∈ T) ∧ (y ∈ A ↔ φ y ∈ P) ∧ (y ∈ B ↔ φ y ∈ Q)

end CurveCrossing

section FirstHomology

variable {Y : Type u} [TopologicalSpace Y]

def CarriesFirstHomologyOnto (J T : Set Y) : Prop :=
  J ⊆ T ∧ ∀ hJT : J ⊆ T,
    Function.Surjective
      (integralSingularHomologyMap 1 (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)))

theorem carriesFirstHomologyOnto_self (T : Set Y) : CarriesFirstHomologyOnto T T := by
  refine ⟨Subset.rfl, fun hJT => ?_⟩
  have hid : (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(T, T)) = ContinuousMap.id T :=
    ContinuousMap.ext fun _ => rfl
  rw [hid, integralSingularHomologyMap_id]
  exact fun x => ⟨x, rfl⟩

end FirstHomology

section Vocabulary

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁}

def section34VertexBallImage {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (c : Section34CutLabelOf 𝒦 𝒦' → Set M₁) (g : M₁ → M₂)
    (w : Section34VertexIndex 𝒦 𝒦') : Set M₂ :=
  g '' c (Section34Label.vertexBall w)

def section34SplitDiskImage {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (c : Section34CutLabelOf 𝒦 𝒦' → Set M₁) (g : M₁ → M₂)
    (e : Section34EdgeIndex 𝒦 𝒦') : Set M₂ :=
  g '' c (Section34Label.splitDisk e)

def section34TraceComponents {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) :
    Set (Set M₂) :=
  (fun y => connectedComponentIn (fblBd s ∩ frontier (⋃ w, tgtV w)) y) ''
    (fblBd s ∩ frontier (⋃ w, tgtV w))

noncomputable def section34TraceCount {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : ℕ :=
  (section34TraceComponents tgtV fblBd s).ncard

noncomputable def section34CrossingCount {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : ℕ :=
  (fblBd s ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).ncard

noncomputable def section34FaceBallRank {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : ℕ :=
  section34TraceCount tgtV fblBd s + section34CrossingCount tgtEBd fblBd s

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem section34FaceBallRank_congr {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fblBd fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂} {s : Section34SimplexIndex 𝒦 3}
    (hs : fblBd s = fblBd' s) :
    section34FaceBallRank tgtV tgtEBd fblBd s = section34FaceBallRank tgtV tgtEBd fblBd' s := by
  simp only [section34FaceBallRank, section34TraceCount, section34CrossingCount,
    section34TraceComponents, hs]

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem section34FaceBallRank_lt_of_compression {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fblBd fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂} {s : Section34SimplexIndex 𝒦 3}
    (hc : section34TraceCount tgtV fblBd' s + 1 ≤ section34TraceCount tgtV fblBd s)
    (hp : section34CrossingCount tgtEBd fblBd' s ≤ section34CrossingCount tgtEBd fblBd s) :
    section34FaceBallRank tgtV tgtEBd fblBd' s < section34FaceBallRank tgtV tgtEBd fblBd s := by
  simp only [section34FaceBallRank]
  omega

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem section34FaceBallRank_lt_of_bigonSlide {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fblBd fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂} {s : Section34SimplexIndex 𝒦 3}
    (hc : section34TraceCount tgtV fblBd' s = section34TraceCount tgtV fblBd s)
    (hp : section34CrossingCount tgtEBd fblBd' s + 2 = section34CrossingCount tgtEBd fblBd s) :
    section34FaceBallRank tgtV tgtEBd fblBd' s < section34FaceBallRank tgtV tgtEBd fblBd s := by
  simp only [section34FaceBallRank]
  omega

def Section34FaceBallInvariants (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U) (h : M₁ → M₂)
    (H : Finset Ea → Set M₂) (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) : Prop :=
  (∀ s, IsPLCellOn 3 (fbl s) (fblBd s)) ∧
  (∀ s : Section34SimplexIndex 𝒦 3, h '' simplexRim 𝒦 s.1 ⊆ interior (fbl s)) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
    ¬ Section34Incident w.1 s.1 → fbl s ∩ tgtV w = ∅) ∧
  (∀ s s', s ≠ s' → fbl s ∩ fbl s' ⊆ interior (⋃ w, tgtV w)) ∧
  (∀ s, ∀ y ∈ fblBd s ∩ frontier (⋃ w, tgtV w),
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
      HasPLCrossingAt (c '' (fblBd s ∩ c.source))
        (c '' (frontier (⋃ w, tgtV w) ∩ c.source)) (c y)) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦'),
    ∀ y ∈ fblBd s ∩ tgtEBd e,
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
      HasPLCurveCrossingOnAt (c '' (frontier (⋃ w, tgtV w) ∩ c.source))
        (c '' (fblBd s ∩ frontier (⋃ w, tgtV w) ∩ c.source))
        (c '' (tgtEBd e ∩ c.source)) (c y)) ∧
  (∀ s, CarriesFirstHomologyOnto (fblBd s ∩ frontier (section34FaceTorus tgtV s))
    (section34FaceTorus tgtV s)) ∧
  (∀ s, (fblBd s ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).Finite) ∧
  (∀ s, (section34TraceComponents tgtV fblBd s).Finite) ∧
  Section34Exterior 𝒦 𝒦' h H tgtV fbl

def Section34Compression (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtE : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : Prop :=
  ∃ (w : Section34VertexIndex 𝒦 𝒦') (Dj Jd : Set M₂),
    IsPLCellOn 2 Dj Jd ∧ Dj ⊆ tgtVBd w ∧ Jd ⊆ fblBd s ∧ Dj ∩ fblBd s = Jd ∧
      (∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint Dj (tgtE e)) ∧
      ∀ s' : Section34SimplexIndex 𝒦 3, s' ≠ s → Disjoint (Dj \ Jd) (fbl s')

def Section34BigonSlide (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : Prop :=
  ∃ (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') (B B' Bb Dj Jd : Set M₂),
    IsPLCellOn 1 B Bb ∧ B ⊆ fblBd s ∧ B ⊆ tgtVBd w ∧ Bb ⊆ tgtEBd e ∧
      B ∩ (⋃ e' : Section34EdgeIndex 𝒦 𝒦', tgtE e') = Bb ∧
      IsPLCellOn 1 B' Bb ∧ B' ⊆ tgtEBd e ∧ B ∩ B' = Bb ∧
      IsPLCellOn 2 Dj Jd ∧ Dj ⊆ tgtVBd w ∩ frontier (⋃ w, tgtV w) ∧ Jd = B ∪ B' ∧
      ∀ s' : Section34SimplexIndex 𝒦 3, Disjoint (Dj \ Jd) (fblBd s')

end Vocabulary

end DifferentialGeometry.Topology.PiecewiseLinear
