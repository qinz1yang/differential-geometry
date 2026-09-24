import DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import DifferentialGeometry.Topology.Morse.NormalForm.Local
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

noncomputable def morseModelEuclideanModelEquiv (n : ℕ) :
    MorseModel n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

theorem morseModelEuclideanModelCompat (n : ℕ) (y : MorseModel n) :
    (𝓡 n) (morseModelEuclideanModelEquiv n y) =
      morseModelEuclideanModelEquiv n ((𝓘(ℝ, MorseModel n)) y) := rfl

@[instance_reducible]
noncomputable def morseModelEuclideanModelChartedSpace (n : ℕ) (M : Type*)
    [TopologicalSpace M] [ChartedSpace (MorseModel n) M] :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
  DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := M)
    (morseModelEuclideanModelEquiv n).toHomeomorph

theorem isManifold_morseModelEuclideanModel {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (MorseModel n) M] [IsManifold (𝓘(ℝ, MorseModel n)) ∞ M] :
    letI := morseModelEuclideanModelChartedSpace n M
    IsManifold (𝓡 n) ∞ M :=
  DifferentialGeometry.Manifold.isManifold_transHomeomorph (M := M)
    (𝓘(ℝ, MorseModel n)) (𝓡 n) (morseModelEuclideanModelEquiv n).toHomeomorph
    (morseModelEuclideanModelEquiv n) (morseModelEuclideanModelCompat n)

noncomputable def diffeomorph_morseModelEuclideanModel {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (MorseModel n) M] [IsManifold (𝓘(ℝ, MorseModel n)) ∞ M] :
    letI := morseModelEuclideanModelChartedSpace n M
    M ≃ₘ⟮𝓡 n, 𝓘(ℝ, MorseModel n)⟯ M := by
  letI := morseModelEuclideanModelChartedSpace n M
  letI := isManifold_morseModelEuclideanModel (n := n) (M := M)
  refine ⟨Equiv.refl M, ?_, ?_⟩
  · change ContMDiff (𝓡 n) (𝓘(ℝ, MorseModel n)) ∞ (id : M → M)
    exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (𝓘(ℝ, MorseModel n)) (𝓡 n) (morseModelEuclideanModelEquiv n).toHomeomorph
      (morseModelEuclideanModelEquiv n) (morseModelEuclideanModelCompat n)
      (I₀ := 𝓡 n) (f := id)).mp contMDiff_id
  · change ContMDiff (𝓘(ℝ, MorseModel n)) (𝓡 n) ∞ (id : M → M)
    exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (𝓘(ℝ, MorseModel n)) (𝓡 n) (morseModelEuclideanModelEquiv n).toHomeomorph
      (morseModelEuclideanModelEquiv n) (morseModelEuclideanModelCompat n)
      (I₀ := 𝓘(ℝ, MorseModel n)) (f := id)).mpr contMDiff_id

theorem diffeomorph_morseModelEuclideanModel_apply {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (MorseModel n) M] [IsManifold (𝓘(ℝ, MorseModel n)) ∞ M] (x : M) :
    letI := morseModelEuclideanModelChartedSpace n M
    (diffeomorph_morseModelEuclideanModel (n := n) (M := M) : M → M) x = x := rfl

theorem nonempty_diffeomorph_morseModelEuclideanModel_self (n : ℕ) :
    letI := morseModelEuclideanModelChartedSpace n (MorseModel n)
    ∃ f : MorseModel n ≃ₘ⟮𝓡 n, 𝓘(ℝ, MorseModel n)⟯ MorseModel n, f 0 = 0 :=
  ⟨diffeomorph_morseModelEuclideanModel, rfl⟩

end DifferentialGeometry.Topology.Morse
