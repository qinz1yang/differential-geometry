import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskBundleTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskSmaleApplications

/-!
# Chapter-14 assembly, D2S1 consumer: SM-D + the mapping-torus lemma

Consumer of `AssemblyDiskBundleTorus.lean` and `AssemblyDiskSmaleApplications.lean` (lane ASM-D2S1).
D2S1 with the rim normalization already done: if a lift flow of the rotation has a fibre disk over
`1` whose inverse monodromy is the identity near the rim, the total space is the standard solid
torus. The remaining inputs of the frozen D2S1 are the lift flow itself and the rim normalization
of the monodromy (`build-logs/scratch/ASM-D2S1/D2S1Inputs.lean`, items (a), (b), (c)).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsTorusApp_ASMD2S1 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothTorusApp_ASMD2S1 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- **D2S1 after rim normalization.** A lift flow of the rotation with a fibre disk over `1` whose
inverse monodromy `μ` (`Φ (2π) ∘ fibre ∘ μ = fibre`) is the identity on an open neighbourhood of the
rim: the total space is the standard solid torus. SM-D supplies the isotopy from the identity to
`μ`; the mapping-torus lemma descends it. -/
theorem nonempty_solidTorus_diffeomorph_of_liftFlow_of_rim_identity {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M))
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    (fibre : ClosedCell 2 → M) (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hrange : range fibre = p ⁻¹' {1})
    (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)
    (hμ : ∀ x, Φ (2 * Real.pi) (fibre (μ x)) = fibre x)
    (N : Set (ClosedCell 2)) (hN : IsOpen N) (hrim : diskRim ⊆ N) (hμN : ∀ x ∈ N, μ x = x) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯ M) := by
  obtain ⟨K, hK, hKi, -, ε, hε, hlo, hhi⟩ :=
    exists_diskIsotopy_from_refl_fixing_rim μ N hN hrim hμN
  exact nonempty_solidTorus_diffeomorph_of_liftFlow p hp Φ hΦ hΦadd hΦp fibre hfibre hrange K hK
    hKi hε hlo (fun t x ht => by rw [hhi t x ht]; exact hμ x)

end GC.GraphManifold.Assembly
