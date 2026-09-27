import DifferentialGeometry.Topology.Morse.HalfSpaceModel
import DifferentialGeometry.Topology.Morse.SublevelInclusion
import DifferentialGeometry.Topology.Morse.RegularSublevelBoundary
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]

@[instance_reducible]
def manifoldSublevelEuclideanChartedSpace (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (SublevelSpace f a) :=
  letI := manifoldSublevelChartedSpace I f a hf hreg
  ChartedSpace.transHomeomorph (morseHalfSpaceEuclideanHomeomorph m)

theorem manifoldSublevelEuclidean_isManifold (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) (⊤ : ℕ∞)
      (SublevelSpace f a) := by
  let := manifoldSublevelChartedSpace I f a hf hreg
  let : IsManifold (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞) (SublevelSpace f a) :=
    manifoldSublevelIsManifold I f a hf hreg
  exact morseHalfSpaceEuclideanHomeomorph_isManifold

def manifoldSublevelEuclideanDiffeomorph (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    SublevelSpace f a ≃ₘ⟮morseModelWithCornersHalfSpace m,
      modelWithCornersEuclideanHalfSpace (m + 1)⟯ SublevelSpace f a := by
  letI := manifoldSublevelChartedSpace I f a hf hreg
  letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  exact (ContinuousLinearEquiv.toTransContinuousLinearEquiv
    (morseModelWithCornersHalfSpace m) (SublevelSpace f a) (morseModelEuclideanEquiv m)).trans
    (ChartedSpace.transHomeomorphDiffeomorph
      ((morseModelWithCornersHalfSpace m).transContinuousLinearEquiv (morseModelEuclideanEquiv m))
      (modelWithCornersEuclideanHalfSpace (m + 1))
      (morseHalfSpaceEuclideanHomeomorph m) (fun _ => rfl) ∞)

theorem contMDiff_manifoldSublevelEuclideanInclusion (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    ContMDiff (modelWithCornersEuclideanHalfSpace (m + 1)) I (⊤ : ℕ∞)
      (fun x : SublevelSpace f a => x.1) := by
  let := manifoldSublevelChartedSpace I f a hf hreg
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  exact (contMDiff_manifoldSublevelInclusion I f a hf hreg).comp
    (manifoldSublevelEuclideanDiffeomorph I f a hf hreg).symm.contMDiff

theorem mfderiv_manifoldSublevelEuclideanInclusion_bijective (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    Function.Bijective (mfderiv (modelWithCornersEuclideanHalfSpace (m + 1)) I
      (fun y : SublevelSpace f a => y.1) x) := by
  let := manifoldSublevelChartedSpace I f a hf hreg
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let Φ := (manifoldSublevelEuclideanDiffeomorph I f a hf hreg).symm
  let hd := Φ.mfderivToContinuousLinearEquiv (by simp) x
  have hb := (mfderiv_manifoldSublevelInclusion_bijective I f a hf hreg (Φ x)).comp hd.bijective
  change Function.Bijective
    (⇑(mfderiv (morseModelWithCornersHalfSpace m) I (fun y => y.1) (Φ x)) ∘
      ⇑(mfderiv (modelWithCornersEuclideanHalfSpace (m + 1))
        (morseModelWithCornersHalfSpace m) Φ x)) at hb
  have hi := (contMDiff_manifoldSublevelInclusion I f a hf hreg (Φ x)).mdifferentiableAt (by simp)
  have hΦ := (Φ.contMDiff x).mdifferentiableAt (by simp)
  rwa [← ContinuousLinearMap.coe_comp, ← mfderiv_comp x hi hΦ] at hb

end

end DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.Morse

open scoped Manifold ContDiff

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

theorem manifoldSublevelEuclidean_isBoundaryPoint_iff (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔ f x.1 = a := by
  let := manifoldSublevelChartedSpace I f a hf hreg
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  let : IsManifold (morseModelWithCornersHalfSpace m) ∞ (SublevelSpace f a) :=
    manifoldSublevelIsManifold I f a hf hreg
  let : IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞ (SublevelSpace f a) :=
    manifoldSublevelEuclidean_isManifold I f a hf hreg
  have h := ((manifoldSublevelEuclideanDiffeomorph I f a hf hreg).isLocalDiffeomorph x)
    |>.isBoundaryPoint_iff (by simp)
  exact h.symm.trans (manifoldSublevel_isBoundaryPoint_iff I f a hf hreg x)

theorem manifoldSublevelEuclidean_isInteriorPoint_iff (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    (modelWithCornersEuclideanHalfSpace (m + 1)).IsInteriorPoint x ↔ f x.1 < a := by
  let := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint,
    manifoldSublevelEuclidean_isBoundaryPoint_iff I f a hf hreg]
  exact ⟨lt_of_le_of_ne x.2, ne_of_lt⟩

def manifoldSublevelEuclideanBoundaryHomeomorph (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    Integral.DivergenceTheorem.WithBoundary.BoundaryManifold
      (modelWithCornersEuclideanHalfSpace (m + 1)) (SublevelSpace f a) ≃ₜ LevelSetSpace f a := by
  letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
  exact
    { toFun := fun x =>
        ⟨x.1.1, (manifoldSublevelEuclidean_isBoundaryPoint_iff I f a hf hreg x.1).mp x.2⟩
      invFun := fun y => ⟨⟨y.1, le_of_eq y.2⟩,
        (manifoldSublevelEuclidean_isBoundaryPoint_iff I f a hf hreg _).mpr y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

@[simp]
theorem manifoldSublevelEuclideanBoundaryHomeomorph_apply_val (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    ∀ x, (manifoldSublevelEuclideanBoundaryHomeomorph I f a hf hreg x).1 = x.1.1 := fun _ => rfl

@[simp]
theorem manifoldSublevelEuclideanBoundaryHomeomorph_symm_apply_val (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (y : LevelSetSpace f a) :
    letI := manifoldSublevelEuclideanChartedSpace I f a hf hreg
    ((manifoldSublevelEuclideanBoundaryHomeomorph I f a hf hreg).symm y).1.1 = y.1 := rfl

end

end DifferentialGeometry.Topology.Morse
