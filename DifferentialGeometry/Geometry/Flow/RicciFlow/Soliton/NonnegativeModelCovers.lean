import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.NonnegativeCurvature
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CompleteTrichotomy
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ProductCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PositiveModelCoverRankThree
import DifferentialGeometry.Geometry.Metric.RicciSoliton.MunteanuWangCompactness
import DifferentialGeometry.Geometry.Curvature.ModelChange
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality
import DifferentialGeometry.Geometry.Operator.ModelChange
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry
open Curvature Operator Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Soliton
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners Real (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]

theorem gradientRicciSoliton_hasCurvatureSurfaceProductSplitting_of_nonnegative_of_rank_one
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (σ : Real)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {x₀ : M} (hrank : metricCurvatureOperatorRankAt g x₀ (by change Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3; simp [DifferentialGeometry.Topology.Morse.MorseModel]) = 1)
    :
    HasCurvatureSurfaceProductSplitting (I := I) (M := M) g := by
  have hkern := gradientRicciSoliton_curvatureOperatorKernelAt_parallel_of_nonnegative g f σ hcomplete hsol
    (by simp [DifferentialGeometry.Topology.Morse.MorseModel]) hcone
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  have hdim : Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hrank' : Module.finrank Real (curvatureOperatorImageAt g x₀
      ⟨metricRm04At g x₀, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x₀⟩) = 1 := by
    rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank]
    exact hrank
  have hrankall : ∀ x, Module.finrank Real (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) = 1 := by
    intro x
    exact (gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq_of_nonnegative g f σ hcomplete hsol hdim hcone x x₀).trans hrank'
  have hscalar : ∀ x, 0 < metricScalarAt g x := by
    intro x
    exact metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      hdim g x (hcone x) (hrankall x)
  obtain ⟨S, hSrank, hSfiber, hSparallel⟩ := exists_smooth_parallel_curvatureOperatorImageLine
    hdim g (metricRm04 g) (fun x => metricRm04At_mem_algebraicCurvatureTensorSubmodule g x) hrankall hkern
  obtain ⟨N, topologyN, hcs, hmanifold, ht2, hσN, h,
      hconnected, hsimplyConnected, hhcomplete, F, hF, hmetric⟩ :=
    exists_global_product_diffeomorph_of_parallel_line (I := I) (M := M) (m := 2) g hcomplete S hSrank hSparallel
  let _ : TopologicalSpace N := topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N := hcs
  let _ : IsManifold (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) (∞ : WithTop ℕ∞) N := hmanifold
  let _ : T2Space N := ht2
  let _ : SigmaCompactSpace N := hσN
  let P : GlobalSurfaceProductSplitting (I := I) (M := M) g := {
    N := N
    metricN := h
    connectedN := hconnected
    simplyConnectedN := hsimplyConnected
    completeN := hhcomplete
    F := F
    line := liftTangentSubbundle (I := I) (M := M) S
    line_rank := by simpa using hSrank
    line_parallel := liftTangentSubbundle_isParallel_of_rank_eq_one g S hSrank hSparallel
    line_compatibility := hF
    isometry := hmetric
  }
  refine ⟨S, P, hSrank, hSfiber, ?_, ?_⟩
  · intro y
    rw [liftTangentSubbundle_fiber]
  · intro y
    have hprod := metricScalarAt_prod_flat P.metricN y (0 : Real)
    have hpull := DifferentialGeometry.HCGCompactness.metricScalar_cross
      (I := (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(Real, Real))
      (J := I) (g := liftedMetric (I := I) g) (Phi := P.F) (x := (y, 0))
    have heqscalar := congrArg
      (fun q : SmoothRiemannianMetric
        ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(Real, Real))
        (P.N × Real) => metricScalarAt q (y, 0)) (P.pullbackMetric_eq_prod g)
    rw [hprod] at heqscalar
    rw [← heqscalar, hpull, metricScalarAt_lifted]
    exact hscalar _
end DifferentialGeometry.Geometry


set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature
open Curvature.DimensionThree
open Riemannian.Topology.UniversalCover

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners Real (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]

private theorem cylinder_cover_of_nonnegative_of_rank_one_morseModel
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {x₀ : M} (hrank : metricCurvatureOperatorRankAt g x₀
      (by change Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3
          simp [DifferentialGeometry.Topology.Morse.MorseModel]) = 1) :
    ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric
        roundThreeCylinderShrinkerPotential g f cover := by
  have hsplit := gradientRicciSoliton_hasCurvatureSurfaceProductSplitting_of_nonnegative_of_rank_one
    g f 1 h.1 h.2.1 hcone hrank
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  obtain ⟨_, P, -, -, -, hpositive⟩ := hsplit
  let _ : TopologicalSpace P.N := P.topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
  let _ : IsManifold (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) ∞ P.N :=
    P.manifoldN
  let _ : T2Space P.N := P.t2N
  let _ : SigmaCompactSpace P.N := P.sigmaN
  let _ : SimplyConnectedSpace P.N := P.simplyConnectedN
  let k : SmoothRiemannianMetric
      (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) P.N := P.metricN
  let Phi := P.F
  have hdim : Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 2) = 2 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hpull : Diffeomorph.pullbackMetricCross (liftedMetric (I := I) g) Phi =
      k.prod (euclideanMetric (E := Real)) := by
    simpa only [k, Phi, flatModelMetric] using P.pullbackMetric_eq_prod g
  have hpos : ∃ x : P.N, 0 < metricScalarAt
      (I := 𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) k x := by
    exact ⟨Classical.choice (inferInstance : Nonempty P.N), by simpa [k] using hpositive _⟩
  apply exists_roundThreeCylinder_solitonModelCovering_of_product_diffeomorph
    (E₂ := DifferentialGeometry.Topology.Morse.MorseModel 2)
    (J := 𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2))
    (N := P.N) (g := g) (f := f) (k := k) (Phi := Phi)
    (h := h) (hk := P.completeN) (hpull := hpull) hdim hpos

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

open Curvature Curvature.DimensionThree Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [ConnectedSpace M]

omit [ConnectedSpace M] in
private theorem normalized_morse_model_change
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (L : E ≃L[ℝ] DifferentialGeometry.Topology.Morse.MorseModel 3) :
    normalizedGradientRicciSoliton (g.transContinuousLinearEquiv L)
      (f.comp (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M L).symm.toContMDiffMap) := by
  let Phi := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M L).symm
  refine ⟨RiemannianMetricComplete.pullbackCross g Phi h.1,
    gradientRicciSoliton_pullbackCross h.2.1 Phi, ?_⟩
  intro x
  change metricScalarAt (g.transContinuousLinearEquiv L) x +
    normGradSqFun (g.transContinuousLinearEquiv L) f x = f x
  rw [metricScalarAt_transContinuousLinearEquiv,
    normGradSqFun_transContinuousLinearEquiv g L f x (f.contMDiff.mdifferentiableAt (by simp))]
  exact h.2.2 x

theorem exists_roundThreeCylinder_solitonModelCovering_of_nonnegative_of_rank_one
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) {x₀ : M}
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : metricCurvatureOperatorRankAt g x₀ hdim = 1) :
    ∃ cover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L : E ≃L[ℝ] DifferentialGeometry.Topology.Morse.MorseModel 3 :=
    (toEuclidean (E := E)).trans
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim)).toContinuousLinearEquiv.trans
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)))
  let J := I.transContinuousLinearEquiv L
  let Phi : M ≃ₘ⟮I, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I M L
  let k : SmoothRiemannianMetric J M := g.transContinuousLinearEquiv L
  let u : C^∞⟮J, M; ℝ⟯ := f.comp Phi.symm.toContMDiffMap
  have hu : normalizedGradientRicciSoliton k u := normalized_morse_model_change h L
  have hrankk : metricCurvatureOperatorRankAt k x₀ (by
      change Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3
      simp [DifferentialGeometry.Topology.Morse.MorseModel]) = 1 := by
    change metricCurvatureOperatorRankAt (Diffeomorph.pullbackMetricCross g Phi.symm) x₀ _ = 1
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      metricCurvatureOperatorRankAt_localPull g Phi.symm Phi.symm.isLocalDiffeomorph x₀
        (by change Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3
            simp [DifferentialGeometry.Topology.Morse.MorseModel]) hdim]
    exact hrank
  have hconek : ∀ x : M, metricAlgebraicCurvatureTensorAt k x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := J) (M := M) := by
    intro x
    rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
    intro n c v w
    have hg := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      g (Phi.symm x)).mp (hcone (Phi.symm x)) n c
      (fun i => mfderiv J I Phi.symm x (v i)) (fun i => mfderiv J I Phi.symm x (w i))
    change 0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StdAt
      (Diffeomorph.pullbackMetricCross g Phi.symm) x (v i) (w i) (w j) (v j)
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric]
    simp_rw [DifferentialGeometry.Integral.Connection.rm04_localPull]
    exact hg
  obtain ⟨cover, hcover⟩ := cylinder_cover_of_nonnegative_of_rank_one_morseModel hu hconek hrankk
  refine ⟨cover, hcover.1, h, ?_, hcover.2.2.2.1, hcover.2.2.2.2.1, ?_, ?_⟩
  · change IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) I ∞ ((Phi.symm : M → M) ∘ cover)
    exact isLocalDiffeomorph_comp Phi.symm.isLocalDiffeomorph hcover.2.2.1
  · intro x v w
    have hm := solitonModelCovering_metric hcover x v w
    rw [show k = g.transContinuousLinearEquiv L from rfl,
      SmoothRiemannianMetric.transContinuousLinearEquiv_inner] at hm
    have hchain := mfderiv_comp x
      (Phi.symm.contMDiff.mdifferentiableAt (by simp))
      ((solitonModelCovering_contMDiff hcover).mdifferentiableAt (by simp))
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I cover x =
      (mfderiv J I id (cover x)).comp (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) J cover x) at hchain
    rw [hchain]
    exact hm
  · intro x
    exact solitonModelCovering_potential hcover x

end DifferentialGeometry.Geometry

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Curvature.DimensionThree Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [ConnectedSpace M]

omit [ConnectedSpace M] in
private theorem normalized_euclidean_model_change
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    normalizedGradientRicciSoliton (g.transContinuousLinearEquiv L)
      (f.comp (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M L).symm.toContMDiffMap) := by
  let Phi := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M L).symm
  refine ⟨RiemannianMetricComplete.pullbackCross g Phi h.1,
    gradientRicciSoliton_pullbackCross h.2.1 Phi, ?_⟩
  intro x
  change metricScalarAt (g.transContinuousLinearEquiv L) x +
    normGradSqFun (g.transContinuousLinearEquiv L) f x = f x
  rw [metricScalarAt_transContinuousLinearEquiv,
    normGradSqFun_transContinuousLinearEquiv g L f x (f.contMDiff.mdifferentiableAt (by simp))]
  exact h.2.2 x

theorem exists_roundThreeSphere_solitonModelCovering_of_rank_three_of_nonnegative
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) {x₀ : M}
    (hrank : metricCurvatureOperatorRankAt g x₀ hdim = 3)
    (hcone : ∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := (toEuclidean (E := E)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim)).toContinuousLinearEquiv
  let J := I.transContinuousLinearEquiv L
  let Phi : M ≃ₘ⟮I, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I M L
  let k : SmoothRiemannianMetric J M := g.transContinuousLinearEquiv L
  let u : C^∞⟮J, M; ℝ⟯ := f.comp Phi.symm.toContMDiffMap
  have hu : normalizedGradientRicciSoliton k u := normalized_euclidean_model_change h L
  have hrankk : ∀ x : M, metricCurvatureOperatorRankAt k x (by change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3; simp) = 3 := by
    intro x
    have hrankg := (gradientRicciSoliton_metricCurvatureOperatorRankAt_eq_of_nonnegative g f 1
      h.1 h.2.1 hdim hcone x x₀).trans hrank
    change metricCurvatureOperatorRankAt (Diffeomorph.pullbackMetricCross g Phi.symm) x _ = 3
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      metricCurvatureOperatorRankAt_localPull g Phi.symm Phi.symm.isLocalDiffeomorph x (by change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3; simp) hdim]
    exact hrankg
  have hconek : ∀ x : M, metricAlgebraicCurvatureTensorAt k x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := J) (M := M) := by
    intro x
    rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
    intro n c v w
    change 0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StdAt
      (Diffeomorph.pullbackMetricCross g Phi.symm) x (v i) (w i) (w j) (v j)
    simp_rw [metricRm04Std_pullbackCross]
    exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      g (Phi.symm x)).mp (hcone (Phi.symm x)) n c
      (fun i => mfderiv J I Phi.symm x (v i)) (fun i => mfderiv J I Phi.symm x (w i))
  have hsec : ∀ (x : M) (v w : TangentSpace J x),
      LinearIndependent ℝ (vec2 (I := J) v w) →
        0 < metricRm04StdAt k x v w w v := by
    intro x v w hlin
    exact metricRm04StdAt_pos_of_metricCurvatureOperatorRankAt_eq_three_of_nonnegative
      k x (by change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3; simp) (hrankk x) (hconek x) v w hlin
  let _ : CompactSpace M := positive_sectional_gradientRicciSoliton_compactness
    (by simp : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) hu.1 hu.2.1 zero_lt_one hsec
  obtain ⟨cover, hcover⟩ :=
    exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_sectional_pos
      hu (by simp) hsec
  refine ⟨cover, hcover.1, h, ?_, hcover.2.2.2.1, hcover.2.2.2.2.1, ?_, ?_⟩
  · change IsLocalDiffeomorph (𝓡 3) I ∞ ((Phi.symm : M → M) ∘ cover)
    exact isLocalDiffeomorph_comp Phi.symm.isLocalDiffeomorph hcover.2.2.1
  · intro x v w
    have hm := solitonModelCovering_metric hcover x v w
    rw [show k = g.transContinuousLinearEquiv L from rfl,
      SmoothRiemannianMetric.transContinuousLinearEquiv_inner] at hm
    have hchain := mfderiv_comp x
      (Phi.symm.contMDiff.mdifferentiableAt (by simp))
      ((solitonModelCovering_contMDiff hcover).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) I cover x =
      (mfderiv J I id (cover x)).comp (mfderiv (𝓡 3) J cover x) at hchain
    rw [hchain]
    exact hm
  · intro x
    exact solitonModelCovering_potential hcover x

end DifferentialGeometry.Geometry
