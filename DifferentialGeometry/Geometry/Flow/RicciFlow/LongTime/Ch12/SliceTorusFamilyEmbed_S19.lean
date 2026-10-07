import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutAlongTori
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.LongTime.Ch12

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N]

theorem exists_openEmbChart_S19 (U : Opens M) (hU : Nonempty U) (f : M → N)
    (hf : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x)) :
    ∃ φ : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞,
      φ.source = (U : Set M) ∧ (∀ x ∈ U, φ x = f x) ∧ φ.target = f '' (U : Set M) := by
  obtain ⟨Q', hQng, hQns, hQimm⟩ := hf.isImmersion
  have himm : ∀ x : U, Injective (mfderiv (𝓡 3) (𝓡 3) (fun x : U => f x) x) := fun x =>
    DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
      (𝓡 3) (𝓡 3) _ x ⟨Q', hQng, hQns, hQimm x⟩
  obtain ⟨V, Φ, hV, hΦ, -⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      (I := 𝓡 3) (J := 𝓡 3) (fun x : U => f x) hf.contMDiff hf.isEmbedding.injective himm rfl
  obtain ⟨x0⟩ := hU
  have : Nonempty V := ⟨Φ x0⟩
  refine ⟨((PartialDiffeomorph.subtypeVal U ⟨x0⟩).symm).trans
    (Φ.toPartialDiffeomorph.trans (PartialDiffeomorph.subtypeVal V ⟨Φ x0⟩)), ?_, ?_, ?_⟩
  · simp [PartialDiffeomorph.trans_toPartialEquiv, PartialDiffeomorph.symm_toPartialEquiv,
      PartialDiffeomorph.subtypeVal, Diffeomorph.toPartialDiffeomorph]
  · intro x hx
    simp [PartialDiffeomorph.trans_toPartialEquiv, PartialDiffeomorph.symm_toPartialEquiv,
      PartialDiffeomorph.subtypeVal, Diffeomorph.toPartialDiffeomorph]
    have h : ((U.openPartialHomeomorphSubtypeCoe ⟨x0⟩).symm x) = ⟨x, hx⟩ := by
      apply Subtype.ext
      have := (U.openPartialHomeomorphSubtypeCoe ⟨x0⟩).right_inv
        (show x ∈ (U.openPartialHomeomorphSubtypeCoe ⟨x0⟩).target by simpa using hx)
      simpa using this
    rw [h, hΦ]
  · simp [PartialDiffeomorph.trans_toPartialEquiv, PartialDiffeomorph.symm_toPartialEquiv,
      PartialDiffeomorph.subtypeVal, Diffeomorph.toPartialDiffeomorph]
    rw [hV]
    ext y
    simp

end GC.LongTime.Ch12
