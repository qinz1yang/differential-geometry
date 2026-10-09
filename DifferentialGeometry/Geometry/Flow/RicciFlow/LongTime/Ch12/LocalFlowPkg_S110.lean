import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StageGlue_S110
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PullbackFlowOnU_S67
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryNaturalityRaw
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding

set_option autoImplicit false

/-!
# CH12-S110 / G2a: the `hLocalFlow` package of `wbN_S98` from a smooth flow on the survivor domain

`localFlow_package_S110`: given a Ricci flow `G` on an `N`-level manifold (`IsSolutionOn`, `Icc t (2t) ⊆ D.regular`,
joint smoothness of `(r, x) ↦ (G r).inner x` on `Icc t (2t) × N`) with `G r = g r` on `Icc t (2t)`, and `φ` an
injective map smooth on `ball(2R)` with injective differential, the pull-back flow `S'` on `↥ball(2R)` has exactly
the four clauses of the first premise of `wbN_S98` (`IsSolutionOn`, regular, `hgram`, metric identification).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter TopologicalSpace Bundle
open DifferentialGeometry.Topology.Manifold Manifold GC.LongTime GC.LongTime.Ch12
open scoped Manifold ContDiff ENNReal Topology
universe u

namespace GC.LongTime.Ch12

/-- `φ|_U` is a smooth embedding: smooth, injective differential (equal dimensions) and injective. -/
theorem isSmoothEmbedding_phi_S110 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (φ : H.Carrier → N) (U : Opens H.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y)) (hφinj : Set.InjOn φ U) :
    Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) := by
  have hsm : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) := contMDiff_restrict_C4 φ U hF
  have hld : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) :=
    isLocalDiffeomorph_of_injective_mfderiv _ hsm
      (fun x v w hvw => hinj x x.2 (by
        rw [← mfderiv_comp_val_C4 φ U hF x v, ← mfderiv_comp_val_C4 φ U hF x w]; exact hvw)) rfl
  exact DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hld (fun x y hxy =>
    Subtype.ext (hφinj x.2 y.2 hxy))

theorem localFlow_package_S110 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T2Space N] [SigmaCompactSpace N]
    (φ : H.Carrier → N) (U : Opens H.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y)) (hφinj : Set.InjOn φ U)
    (t : ℝ) (D : RealTimeInterval) (G : SolutionOn (I := 𝓡 3) (M := N) D) (hG : IsSolutionOn (I := 𝓡 3) G)
    (hreg : Icc t (2 * t) ⊆ D.regular)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3))
      ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)) ∞
      (fun q : ℝ × N => (⟨q.2, (G.base.metric q.1).inner q.2⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ)))
      (Icc t (2 * t) ×ˢ (Set.univ : Set N)))
    (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) (hgG : ∀ r ∈ Icc t (2 * t), G.base.metric r = g r) :
    ∃ (D' : RealTimeInterval) (S' : SolutionOn (I := 𝓡 3) (M := U) D'),
      IsSolutionOn (I := 𝓡 3) S' ∧ Icc t (2 * t) ⊆ D'.regular ∧
      (∀ (x₀ : U) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × U => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S'.base.metric p.1) x₀ p.2 i j)
          (Icc t (2 * t) ×ˢ
            (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
      (∀ r ∈ Icc t (2 * t),
        S'.base.metric r = pullbackRestrict_S57 H (g r) φ U hF hinj) := by
  have hemb := isSmoothEmbedding_phi_S110 H φ U hF hinj hφinj
  obtain ⟨S', hS', hmet⟩ := exists_solutionOn_pullbackRestrict_S67 H G hG φ U hF hemb
  refine ⟨D, S', hS', hreg, ?_, ?_⟩
  · intro x₀ i j
    refine chartGramMatrix_joint_contMDiffOn_of_pullback G.base.metric (Icc t (2 * t)) hjoint
      S'.base.metric (fun x : U => φ x) (contMDiff_restrict_C4 φ U hF) ?_ x₀ i j
    intro r _ x u v
    rw [hmet r]
    simp only [pullbackRestrict_S57, SmoothRiemannianMetric.pullbackOfImmersion_inner]
  · intro r hr
    rw [hmet r, hgG r hr]

end GC.LongTime.Ch12

end
