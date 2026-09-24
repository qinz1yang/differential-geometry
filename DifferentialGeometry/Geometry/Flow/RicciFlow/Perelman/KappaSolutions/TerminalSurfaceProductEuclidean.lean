import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProduct
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CompleteTrichotomy
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorPositiveSectional
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorVanishing
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.PositiveSectional
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureTrichotomy
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Pullback.Product
import DifferentialGeometry.Geometry.Metric.CompletenessPullback
import DifferentialGeometry.Geometry.Curvature.ModelChange
import DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import DifferentialGeometry.Topology.Morse.HalfSpaceModel

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem hasPositiveSectionalCurvature_of_forall_metricScalarAt_pos_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x : M, 0 < DifferentialGeometry.Geometry.Curvature.metricScalarAt (I := I) g x) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) g := by
  intro x v w hvw
  have hpos := sectionalCurvature_pos_of_metricScalarAt_pos_of_finrank_eq_two
    (I := I) g hdim x (hscalar x) v w hvw
  rw [sectionalCurvature_eq_metricRm04StandardAt_div (I := I) g x v w] at hpos
  exact (div_pos_iff_of_pos_right
    (DifferentialGeometry.Geometry.gram_determinant_pos (I := I) g x v w hvw)).mp hpos

end DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Manifold

variable {E F H H' M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace M]

noncomputable def diffeomorph_chartedSpaceTransHomeomorph
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
    (e : H ≃ₜ H') (L : E ≃L[ℝ] F) (hcompat : ∀ y, J (e y) = L (I y))
    [ChartedSpace H M] [IsManifold I ∞ M] :
    let _ : ChartedSpace H' M := chartedSpaceTransHomeomorph (M := M) e
    let _ : IsManifold J ∞ M := isManifold_transHomeomorph (M := M) I J e L hcompat
    M ≃ₘ⟮J, I⟯ M := by
  let _ : ChartedSpace H' M := chartedSpaceTransHomeomorph (M := M) e
  let _ : IsManifold J ∞ M := isManifold_transHomeomorph (M := M) I J e L hcompat
  refine ⟨Equiv.refl M, ?_, ?_⟩
  · change ContMDiff J I ∞ (id : M → M)
    exact (contMDiff_chartedSpaceTransHomeomorph_iff I J e L hcompat (I₀ := J) (f := id)).mp
      contMDiff_id
  · change ContMDiff I J ∞ (id : M → M)
    exact (contMDiff_chartedSpaceTransHomeomorph_iff I J e L hcompat (I₀ := I) (f := id)).mpr
      contMDiff_id

end DifferentialGeometry.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

noncomputable def morseModelEuclideanModelEquiv (n : ℕ) :
    MorseModel n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

theorem nonempty_terminalSurfaceProduct_of_hasCurvatureSurfaceProductSplitting
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    (g : SmoothRiemannianMetric I M)
    (hS : DifferentialGeometry.Geometry.Curvature.DimensionThree.HasCurvatureSurfaceProductSplitting
      (I := I) (M := M) g) :
    let _ : LocallyPathConnectedSpace H :=
      I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    let _ : SemilocallySimplyConnectedSpace M :=
      manifold_semilocallySimplyConnectedSpace (I := I)
    let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
    Nonempty (TerminalSurfaceProduct (I := I) g) := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M :=
    manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  obtain ⟨S, P, hSrank, hSfiber, hSline, hscalar⟩ := hS
  let _ : TopologicalSpace P.N := P.topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
  let _ : IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) ∞ P.N :=
    P.manifoldN
  let _ : T2Space P.N := P.t2N
  let _ : SigmaCompactSpace P.N := P.sigmaN
  let e : DifferentialGeometry.Topology.Morse.MorseModel 2 ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    (morseModelEuclideanModelEquiv 2).toHomeomorph
  let L : DifferentialGeometry.Topology.Morse.MorseModel 2 ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    morseModelEuclideanModelEquiv 2
  have hcompat : ∀ y : MorseModel 2,
      (𝓡 2) (e y) = L (𝓘(ℝ, MorseModel 2) y) :=
    fun _ => rfl
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) P.N :=
    DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := P.N) e
  let _ : IsManifold (𝓡 2) ∞ P.N :=
    DifferentialGeometry.Manifold.isManifold_transHomeomorph (M := P.N)
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (𝓡 2) e L hcompat
  let Ψ : P.N ≃ₘ⟮𝓡 2, 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)⟯ P.N :=
    DifferentialGeometry.Manifold.diffeomorph_chartedSpaceTransHomeomorph (M := P.N)
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (𝓡 2) e L hcompat
  let hmetric : SmoothRiemannianMetric (𝓡 2) P.N :=
    DifferentialGeometry.Diffeomorph.pullbackMetricCross P.metricN Ψ
  let Φ : (P.N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover M :=
    (Ψ.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).trans P.F
  have hscalar' : ∀ y : P.N,
      0 < DifferentialGeometry.Geometry.Curvature.metricScalarAt (I := 𝓡 2) hmetric y := by
    intro y
    change 0 < DifferentialGeometry.Geometry.Curvature.metricScalarAt (I := 𝓡 2)
      (DifferentialGeometry.Diffeomorph.pullbackMetricCross P.metricN Ψ) y
    rw [DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      DifferentialGeometry.Geometry.Curvature.metricScalarAt_localPull]
    have hΨy : (Ψ : P.N → P.N) y = y := rfl
    rw [hΨy]
    exact hscalar y
  have hproduct : ∀ (y : P.N) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
          (I := I) g).inner (Φ (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (Φ : P.N × ℝ → UniversalCover M) (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (Φ : P.N × ℝ → UniversalCover M) (y, s)
            (w, c)) =
        hmetric.inner y v w + a * c := by
    have hΨp_metric : DifferentialGeometry.Diffeomorph.pullbackMetricCross
          (P.metricN.prod (flatModelMetric ℝ))
          (Ψ.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)) =
        hmetric.prod (flatModelMetric ℝ) := by
      rw [show hmetric = DifferentialGeometry.Diffeomorph.pullbackMetricCross P.metricN Ψ from rfl,
        DifferentialGeometry.Diffeomorph.pullbackMetricCross_prodCongr,
        DifferentialGeometry.Diffeomorph.pullbackMetricCross_refl]
    have hΦ_metric : DifferentialGeometry.Diffeomorph.pullbackMetricCross
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
            (I := I) g) Φ =
        hmetric.prod (flatModelMetric ℝ) := by
      rw [show Φ = (Ψ.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).trans P.F from rfl,
        ← DifferentialGeometry.Diffeomorph.pullbackMetricCross_trans]
      rw [P.pullbackMetric_eq_prod g, hΨp_metric]
    intro y s v w a c
    have hflat : (flatModelMetric ℝ).inner s a c = a * c := by
      change inner ℝ a c = a * c
      rw [RCLike.inner_apply]
      simp
      ring
    have hpb : (DifferentialGeometry.Diffeomorph.pullbackMetricCross
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
            (I := I) g) Φ).inner (y, s) (v, a) (w, c) =
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
          (I := I) g).inner (Φ (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (Φ : P.N × ℝ → UniversalCover M) (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (Φ : P.N × ℝ → UniversalCover M) (y, s)
            (w, c)) :=
      DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
          (I := I) g) Φ (y, s) (v, a) (w, c)
    have hprod : (hmetric.prod (flatModelMetric ℝ)).inner (y, s) (v, a) (w, c) =
        hmetric.inner y v w + a * c := by
      have hsplit := SmoothRiemannianMetric.prod_inner hmetric (flatModelMetric ℝ)
        (y, s) (v, a) (w, c)
      rw [hsplit, hflat]
    have hbridge := congrArg (fun q : SmoothRiemannianMetric
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) (P.N × ℝ) => q.inner (y, s) (v, a) (w, c)) hΦ_metric
    exact hpb.symm.trans (hbridge.trans hprod)
  exact ⟨{
    S := P.N
    topology := P.topologyN
    charted := inferInstance
    smooth := inferInstance
    t2 := P.t2N
    sigmaCompact := P.sigmaN
    connected := P.connectedN
    h := hmetric
    Phi := Φ
    product := hproduct
    complete := DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
      P.completeN Ψ
    positive := hasPositiveSectionalCurvature_of_forall_metricScalarAt_pos_of_finrank_eq_two
      hmetric (by simp) hscalar' }⟩


section TerminalTrichotomyAssembly

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Connection

variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (MorseModel 3) H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]

theorem flat_or_curvatureSurfaceProductSplitting_or_operatorPositive_of_derived_data
    (g : SmoothRiemannianMetric I M)
    (hg : DifferentialGeometry.RiemannianMetricComplete (I := I) g)
    (hpositive : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
        0 ≤ (twoFormMetricData (I := I) g x).inner
          (curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ a) a)
    (hnull : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
        curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ a = 0 →
          curvatureOperatorReactionEndomorphism3
            (curvatureOperatorEndomorphismAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩).toLinearMap a = 0)
    (hrank : ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩) =
      Module.finrank ℝ (curvatureOperatorImageAt (I := I) g y
        ⟨metricRm04 (I := I) g y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g y⟩))
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩)) :
    (∀ x : M, metricRm04 (I := I) g x = 0) ∨
      DifferentialGeometry.Geometry.Curvature.DimensionThree.HasCurvatureSurfaceProductSplitting
        (I := I) (M := M) g ∨
      (∀ x, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ, a ≠ 0 →
        0 < (twoFormMetricData (I := I) g x).inner
          (curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ a) a) := by
  have hdim : Module.finrank ℝ (MorseModel 3) = 3 := by simp [MorseModel]
  rcases DifferentialGeometry.PDE.RicciFlow.DimensionThree.curvature_time_slice_global_trichotomy_of_derived_data
      (I := I) g hg hpositive hnull hrank hkernel with
    ⟨hzero, _⟩ | ⟨_, hproduct⟩ | ⟨_, hpositiveRank⟩
  · refine Or.inl ?_
    intro x
    rw [metricRm04_apply]
    have hsub : (⟨metricRm04At (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) =
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ :=
      Subtype.ext (metricRm04_apply (I := I) (M := M) g x).symm
    exact DifferentialGeometry.Geometry.Curvature.DimensionThree.metricRm04At_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
      (I := I) g x hdim (by rw [hsub]; exact hzero x)
  · exact Or.inr (Or.inl hproduct)
  · exact Or.inr (Or.inr hpositiveRank)

end TerminalTrichotomyAssembly

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
