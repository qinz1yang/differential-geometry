import DifferentialGeometry.Topology.Morse.RegularSublevel
import DifferentialGeometry.Geometry.Boundary.BoundaryManifold

namespace DifferentialGeometry.Topology.Morse

open scoped Manifold

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]

theorem manifoldSublevel_isBoundaryPoint_iff (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    (morseModelWithCornersHalfSpace m).IsBoundaryPoint x ↔ f x.1 = a := by
  classical
  let := manifoldSublevelChartedSpace I f a hf hreg
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_morseHalfSpace_range]
  change (chartAt (MorseHalfSpace m) x x : MorseModel (m + 1)) (Fin.last m) = 0 ↔
    f x.1 = a
  by_cases hx : f x.1 = a
  · have hchart : chartAt (MorseHalfSpace m) x =
        manifoldSublevelBoundaryChart I f a x hx hf hreg := by
      change (if h : f x.1 = a then manifoldSublevelBoundaryChart I f a x h hf hreg
        else manifoldSublevelInteriorChart I f a x
          (lt_of_le_of_ne (show f x.1 ≤ a from x.2) h) hf) = _
      rw [dif_pos hx]
    rw [hchart]
    exact iff_of_true (manifoldSublevelBoundaryChart_extend_last_zero I f a hf hreg x hx) hx
  · have hlt : f x.1 < a := lt_of_le_of_ne x.2 hx
    have hchart : chartAt (MorseHalfSpace m) x =
        manifoldSublevelInteriorChart I f a x hlt hf := by
      change (if h : f x.1 = a then manifoldSublevelBoundaryChart I f a x h hf hreg
        else manifoldSublevelInteriorChart I f a x
          (lt_of_le_of_ne (show f x.1 ≤ a from x.2) h) hf) = _
      rw [dif_neg hx]
    rw [hchart]
    exact iff_of_false (ne_of_gt
      (manifoldSublevelInteriorChart_extend_last_pos I f a hf x hlt)) hx

theorem manifoldSublevel_isInteriorPoint_iff (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    (morseModelWithCornersHalfSpace m).IsInteriorPoint x ↔ f x.1 < a := by
  let := manifoldSublevelChartedSpace I f a hf hreg
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint,
    manifoldSublevel_isBoundaryPoint_iff I f a hf hreg]
  exact ⟨lt_of_le_of_ne x.2, ne_of_lt⟩

def manifoldSublevelBoundaryHomeomorph (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    Integral.DivergenceTheorem.WithBoundary.BoundaryManifold
      (morseModelWithCornersHalfSpace m) (SublevelSpace f a) ≃ₜ LevelSetSpace f a := by
  letI := manifoldSublevelChartedSpace I f a hf hreg
  exact
    { toFun := fun x => ⟨x.1.1, (manifoldSublevel_isBoundaryPoint_iff I f a hf hreg x.1).mp x.2⟩
      invFun := fun y => ⟨⟨y.1, le_of_eq y.2⟩,
        (manifoldSublevel_isBoundaryPoint_iff I f a hf hreg _).mpr y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

@[simp]
theorem manifoldSublevelBoundaryHomeomorph_apply_val (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    ∀ x, (manifoldSublevelBoundaryHomeomorph I f a hf hreg x).1 = x.1.1 := fun _ => rfl

@[simp]
theorem manifoldSublevelBoundaryHomeomorph_symm_apply_val (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (y : LevelSetSpace f a) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    ((manifoldSublevelBoundaryHomeomorph I f a hf hreg).symm y).1.1 = y.1 := rfl

end

end DifferentialGeometry.Topology.Morse
