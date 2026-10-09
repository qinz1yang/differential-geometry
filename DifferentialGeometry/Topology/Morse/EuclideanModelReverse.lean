import DifferentialGeometry.Topology.Morse.EuclideanModel

/-!
# Morse-model charts on a Euclidean-model manifold

The reverse of `Topology/Morse/EuclideanModel.lean`: a smooth manifold modelled on
`EuclideanSpace ℝ (Fin n)` also carries charts in `MorseModel n = Fin n → ℝ`
(`euclideanModelMorseModelChartedSpace`, the charts composed with the linear equivalence), it is a
smooth manifold for `𝓘(ℝ, MorseModel n)` (`isManifold_euclideanModelMorseModel`), and the
identity is a diffeomorphism between the two structures (`euclideanModelMorseModelDiffeomorph`).
Results stated for `MorseModel n` charts (such as the surface Ricci flow theorem
`GC.Geometry.exists_isometryInvariant_roundMetric_proved`) thus apply to `𝓡 n`-manifolds.
-/

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

theorem euclideanModelMorseModelCompat (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    (𝓘(ℝ, MorseModel n)) ((morseModelEuclideanModelEquiv n).symm y) =
      (morseModelEuclideanModelEquiv n).symm ((𝓡 n) y) := rfl

/-- Charts in `MorseModel n` on a manifold modelled on `EuclideanSpace ℝ (Fin n)`. -/
@[instance_reducible]
noncomputable def euclideanModelMorseModelChartedSpace (n : ℕ) (M : Type*)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ChartedSpace (MorseModel n) M :=
  DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := M)
    (morseModelEuclideanModelEquiv n).symm.toHomeomorph

theorem isManifold_euclideanModelMorseModel {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] :
    letI := euclideanModelMorseModelChartedSpace n M
    IsManifold (𝓘(ℝ, MorseModel n)) ∞ M :=
  DifferentialGeometry.Manifold.isManifold_transHomeomorph (M := M)
    (𝓡 n) (𝓘(ℝ, MorseModel n)) (morseModelEuclideanModelEquiv n).symm.toHomeomorph
    (morseModelEuclideanModelEquiv n).symm (euclideanModelMorseModelCompat n)

/-- The identity, from the Morse-model charts to the Euclidean-model charts, is a
diffeomorphism. -/
noncomputable def euclideanModelMorseModelDiffeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    letI := euclideanModelMorseModelChartedSpace n M
    M ≃ₘ⟮𝓘(ℝ, MorseModel n), 𝓡 n⟯ M := by
  letI := euclideanModelMorseModelChartedSpace n M
  refine ⟨Equiv.refl M, ?_, ?_⟩
  · change ContMDiff (𝓘(ℝ, MorseModel n)) (𝓡 n) ∞ (id : M → M)
    exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (𝓡 n) (𝓘(ℝ, MorseModel n)) (morseModelEuclideanModelEquiv n).symm.toHomeomorph
      (morseModelEuclideanModelEquiv n).symm (euclideanModelMorseModelCompat n)
      (I₀ := 𝓘(ℝ, MorseModel n)) (f := id)).mp contMDiff_id
  · change ContMDiff (𝓡 n) (𝓘(ℝ, MorseModel n)) ∞ (id : M → M)
    exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (𝓡 n) (𝓘(ℝ, MorseModel n)) (morseModelEuclideanModelEquiv n).symm.toHomeomorph
      (morseModelEuclideanModelEquiv n).symm (euclideanModelMorseModelCompat n)
      (I₀ := 𝓡 n) (f := id)).mpr contMDiff_id

theorem euclideanModelMorseModelDiffeomorph_apply {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    letI := euclideanModelMorseModelChartedSpace n M
    (euclideanModelMorseModelDiffeomorph (n := n) (M := M) : M → M) x = x := rfl

end DifferentialGeometry.Topology.Morse
