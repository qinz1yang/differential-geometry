import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import DifferentialGeometry.Topology.PiecewiseLinear.Product

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def lateralBandReverse {X Y : Type*} (f : X × ℝ → Y) : X × ℝ → Y :=
  fun p => f (p.1, 1 - p.2)

theorem lateralBandReverse_image_Icc {X Y : Type*} (f : X × ℝ → Y) (S : Set X) :
    lateralBandReverse f '' (S ×ˢ Icc (0 : ℝ) 1) = f '' (S ×ˢ Icc (0 : ℝ) 1) := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨(p.1, 1 - p.2), ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨(p.1, 1 - p.2), ⟨hp.1, ?_⟩, ?_⟩
    · constructor <;> linarith [hp.2.1, hp.2.2]
    · simp [lateralBandReverse]

theorem lateralBandReverse_image_Ioo {X Y : Type*} (f : X × ℝ → Y) (S : Set X) :
    lateralBandReverse f '' (S ×ˢ Ioo (0 : ℝ) 1) = f '' (S ×ˢ Ioo (0 : ℝ) 1) := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨(p.1, 1 - p.2), ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨(p.1, 1 - p.2), ⟨hp.1, ?_⟩, ?_⟩
    · constructor <;> linarith [hp.2.1, hp.2.2]
    · simp [lateralBandReverse]

theorem lateralBandReverse_image_zero {X Y : Type*} (f : X × ℝ → Y) (S : Set X) :
    lateralBandReverse f '' (S ×ˢ {(0 : ℝ)}) = f '' (S ×ˢ {(1 : ℝ)}) := by
  ext y
  simp [lateralBandReverse, mem_image, Prod.exists]

theorem lateralBandReverse_image_one {X Y : Type*} (f : X × ℝ → Y) (S : Set X) :
    lateralBandReverse f '' (S ×ˢ {(1 : ℝ)}) = f '' (S ×ˢ {(0 : ℝ)}) := by
  ext y
  simp [lateralBandReverse, mem_image, Prod.exists]

theorem continuousOn_lateralBandReverse {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X × ℝ → Y} {S : Set X}
    (hf : ContinuousOn f (S ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (lateralBandReverse f) (S ×ˢ Icc (0 : ℝ) 1) := by
  apply hf.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd)).continuousOn
  intro p hp
  change (p.1, 1 - p.2) ∈ S ×ˢ Icc (0 : ℝ) 1
  exact ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩

theorem injOn_lateralBandReverse {X Y : Type*} {f : X × ℝ → Y} {S : Set X}
    (hf : InjOn f (S ×ˢ Icc (0 : ℝ) 1)) :
    InjOn (lateralBandReverse f) (S ×ˢ Icc (0 : ℝ) 1) := by
  intro p hp q hq hpq
  have heq := hf (x₁ := (p.1, 1 - p.2)) (x₂ := (q.1, 1 - q.2))
    ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
    ⟨hq.1, by constructor <;> linarith [hq.2.1, hq.2.2]⟩ hpq
  have hfst := congrArg Prod.fst heq
  exact Prod.ext hfst
    (by have hh := congrArg Prod.snd heq; dsimp at hh; linarith)

theorem exists_lateral_band_reversal {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X × ℝ → Y} {S : Set X}
    (hf : ContinuousOn f (S ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (S ×ˢ Icc (0 : ℝ) 1)) :
    ∃ g : X × ℝ → Y, ContinuousOn g (S ×ˢ Icc (0 : ℝ) 1) ∧
      InjOn g (S ×ˢ Icc (0 : ℝ) 1) ∧
      g '' (S ×ˢ Icc (0 : ℝ) 1) = f '' (S ×ˢ Icc (0 : ℝ) 1) ∧
      g '' (S ×ˢ Ioo (0 : ℝ) 1) = f '' (S ×ˢ Ioo (0 : ℝ) 1) ∧
      g '' (S ×ˢ {(0 : ℝ)}) = f '' (S ×ˢ {(1 : ℝ)}) ∧
      g '' (S ×ˢ {(1 : ℝ)}) = f '' (S ×ˢ {(0 : ℝ)}) :=
  ⟨lateralBandReverse f, continuousOn_lateralBandReverse hf, injOn_lateralBandReverse hfi,
    lateralBandReverse_image_Icc f S, lateralBandReverse_image_Ioo f S,
    lateralBandReverse_image_zero f S, lateralBandReverse_image_one f S⟩

theorem IsPLHomeomorphOn.lateralBandReverse {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {g : (Fin 3 → ℝ) × ℝ → E} {R : Set E}
    (hg : IsPLHomeomorphOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) R) :
    IsPLHomeomorphOn (lateralBandReverse g) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) R := by
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  exact (hpoly.isPLHomeomorphOn_id.prodMap isPLHomeomorphOn_one_sub_Icc).trans hg

theorem exists_lateral_PL_band_reversal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (u : E → M) {P : Set E}
    {g : (Fin 3 → ℝ) × ℝ → E}
    (hg : IsPLHomeomorphOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
      (g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)))
    (hgP : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P) :
    ∃ g' : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn g' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (g' '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      g' '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ P ∧
      (u ∘ g') '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      (u ∘ g') '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) =
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ∧
      (u ∘ g') '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) =
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {(1 : ℝ)}) ∧
      (u ∘ g') '' (stdSimplexBoundary 2 ×ˢ {(1 : ℝ)}) =
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) := by
  refine ⟨lateralBandReverse g, ?_, ?_, lateralBandReverse_image_Icc (u ∘ g) _,
    lateralBandReverse_image_Ioo (u ∘ g) _, lateralBandReverse_image_zero (u ∘ g) _,
    lateralBandReverse_image_one (u ∘ g) _⟩
  · rw [lateralBandReverse_image_Icc]
    exact hg.lateralBandReverse
  · rw [lateralBandReverse_image_Icc]
    exact hgP

end DifferentialGeometry.Topology.PiecewiseLinear
