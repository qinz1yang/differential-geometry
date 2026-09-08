import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PositiveSystem
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CompleteTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorKernel

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.DimensionThree

open Bundle Set
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open CovariantDerivative
open PositiveSystem
open scoped ContDiff Manifold InnerProductSpace BigOperators

universe uE uH uM uF uV

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

noncomputable local instance twoFormFiniteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {V : M → Type uV} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace Real (V x)]
  [∀ x, FiniteDimensional Real (V x)]
  [FiberBundle F V] [VectorBundle Real F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

omit [CompleteSpace E] in
theorem positive_time_rank_spreading
    [I.Boundaryless] [ConnectedSpace M] [Nonempty M]
    [NeZero (Module.finrank Real E)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (cov : Real → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    {T : Real} (hT : 0 < T)
    (A : Real → Cₛ^∞⟮I; F →L[Real] F, (fun x : M => V x →L[Real] V x)⟯)
    (hAsymm : ∀ t x,
      ((A t x : V x →L[Real] V x) : V x →ₗ[Real] V x).IsSymmetric)
    (hApos : ∀ t ∈ Icc 0 T, ∀ x, (A t x).IsPositive)
    (hphiCont : ∀ k, k ≤ Module.finrank Real F →
      ContinuousOn (fun p : Real × M =>
        (hAsymm p.1 p.2).lowerKyFanSum k)
        (Set.prod (Icc 0 T) (Set.univ : Set M)))
    (hA_bound : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : Real → (x : M) → TangentSpace I x)
    (reaction : Real → (x : M) →
      (V x →L[Real] V x) → V x →L[Real] V x)
    (hreactionNull : ∀ t x, satisfiesNullEigenvectorCondition (reaction t x))
    (hreactionLip : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[Real] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (hdirichlet : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset →
        IsConnected (interior Kset) →
        HasLocalScalarDirichletSolution (I := I) G T X s t Kset)
    (hGconn : ∀ q ∈ Ioc 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ t ∈ Ioc 0 T, ∀ x,
      DifferentiableAt Real (fun s => A s x) t)
    (hevolution : ∀ t ∈ Ioc 0 T, ∀ x,
      deriv (fun s => A s x) t =
        rawBundleEndomorphismConnLap (I := I) (G.metric t) (cov t)
            (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y => A t y) x (X t x) +
          reaction t x (A t x)) :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank Real (A t x).range =
        Module.finrank Real (A t y).range) ∧
      (∀ x, MonotoneOn
        (fun t => Module.finrank Real (A t x).range) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
          Module.finrank Real (A s x).range =
            Module.finrank Real (A t x).range) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : Nat, ∀ t ∈ Ioc 0 δ, ∀ x,
        Module.finrank Real (A t x).range = q := by
  exact PositiveSystem.finrank_range_spatially_constant_and_locally_constant_of_local_dirichlet_solution_exists
    (I := I) G cov hcov hT A hAsymm hApos hphiCont hA_bound X reaction
    hreactionNull hreactionLip hdirichlet hGconn hAt hevolution

omit [CompleteSpace E] [∀ x, FiniteDimensional Real (V x)] in
theorem positive_time_kernel_rigidity
    (g : Real → SmoothRiemannianMetric I M)
    (cov : Real → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    (A : Real → Cₛ^∞⟮I; F →L[Real] F, (fun x : M => V x →L[Real] V x)⟯)
    {a b : Real}
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x => A t x) (Set.prod (Ioo a b) (Set.univ : Set M)))
    (q : Nat) (hrange : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank Real (A t x).range = q)
    (hAsymm : ∀ t ∈ Ioo a b, ∀ x,
      ((A t x : V x →L[Real] V x) : V x →ₗ[Real] V x).IsSymmetric)
    (hApos : ∀ t ∈ Ioo a b, ∀ x, (A t x).IsPositive)
    (X : Real → (x : M) → TangentSpace I x)
    (reaction : Real → (x : M) →
      (V x →L[Real] V x) → V x →L[Real] V x)
    (hreactionNull : ∀ t x, satisfiesNullEigenvectorCondition (reaction t x))
    (hAt : ∀ t ∈ Ioo a b, ∀ x,
      DifferentiableAt Real (fun s => A s x) t)
    (hevolution : ∀ t ∈ Ioo a b, ∀ x,
      deriv (fun s => A s x) t =
        rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y => A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y => A t y) x (X t x) +
          reaction t x (A t x)) :
    And
      (∀ p ∈ Set.prod (Ioo a b) (Set.univ : Set M),
        ∃ (U : Set (Real × M)) (w : Fin (Module.finrank Real F - q) →
          (p : Real × M) → V p.2),
          And (IsOpen U)
            (And (p ∈ U)
              (And (U ⊆ Set.prod (Ioo a b) (Set.univ : Set M))
                (And (∀ z ∈ U, LinearIndependent Real (w · z))
                  (And (∀ z ∈ U,
                    Submodule.span Real (Set.range (w · z)) = (A z.1 z.2).ker)
                    (∀ i, ContMDiffOn (𝓘(Real, Real).prod I)
                      ((𝓘(Real, Real).prod I).prod 𝓘(Real, F)) ∞
                      (fun z => TotalSpace.mk' F z (w i z) : Real × M →
                        TotalSpace F ((ContMDiffMap.snd :
                          C^∞⟮𝓘(Real, Real).prod I, Real × M; I, M⟯) *ᵖ V)) U))))))
      (And
        (∀ t ∈ Ioo a b,
          IsCovariantlyInvariantSubmoduleFamily (cov t)
            (fun x => (A t x).ker))
        (And
          (∀ t ∈ Ioo a b, ∀ x v, A t x v = 0 →
            inner Real (reaction t x (A t x) v) v = 0)
          (And
            (∀ t ∈ Ioo a b, ∀ x v, A t x v = 0 →
              deriv (fun s => A s x) t v = reaction t x (A t x) v)
            (∀ t ∈ Ioo a b,
              ∀ (w : (p : Real × M) → V p.2) {U : Set (Real × M)},
                IsOpen U → ∀ {x}, (t, x) ∈ U →
                ContMDiffOn (𝓘(Real, Real).prod I)
                  ((𝓘(Real, Real).prod I).prod 𝓘(Real, F)) ∞
                  (fun p => TotalSpace.mk' F p (w p) : Real × M →
                    TotalSpace F ((ContMDiffMap.snd :
                      C^∞⟮𝓘(Real, Real).prod I, Real × M; I, M⟯) *ᵖ V)) U →
                (∀ p ∈ U, A p.1 p.2 (w p) = 0) →
                And (A t x (deriv (fun s => w (s, x)) t) =
                    -reaction t x (A t x) (w (t, x)))
                  (deriv (fun s => A s x) t (w (t, x)) =
                    reaction t x (A t x) (w (t, x))))))) := by
  exact PositiveSystem.kernel_rigidity_of_constant_range_rank
    (I := I) g cov hcov A hAspace q hrange hAsymm hApos X reaction
      hreactionNull hAt hevolution

theorem curvature_time_slice_trichotomy_of_derived_data
    [I.Boundaryless] [Nonempty M]
    (hE : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M)
    (hpositive : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        0 ≤ (twoFormMetricData (I := I) g x).inner
          (curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩ a) a)
    (hnull : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩ a = 0 →
          curvatureOperatorReactionEndomorphism3
            (curvatureOperatorEndomorphismAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩).toLinearMap a = 0)
    (hrank : ∀ x y,
      Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩) =
        Module.finrank Real
          (curvatureOperatorImageAt (I := I) g y
            ⟨metricRm04 (I := I) g y,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g y⟩))
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) g x⟩)) :
    (∀ x, curvatureOperatorEndomorphismAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ = 0) ∨
      (And
        (∀ x, Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩) = 1)
        (∀ x, ∃ e : TangentSpace I x,
          And (e ∈ curvatureOperatorImageAnnihilatorAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩)
          (And (g.inner x e e = 1)
            (HasLocalRiemannianProductAt (I := I) g x e)))) ∨
      And
        (∀ x, Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩) = 3)
        (∀ x, ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real, a ≠ 0 →
          0 < (twoFormMetricData (I := I) g x).inner
            (curvatureOperatorEndomorphismAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩ a) a) := by
  exact curvatureOperator_time_slice_trichotomy_of_metric_nonnegative_reaction_constant_rank_parallel_kernel
    (I := I) hE g hpositive hnull hrank hkernel

inductive CurvatureTimeSliceGlobalAlternative
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners Real
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    (g : SmoothRiemannianMetric I M) : Prop where
  | flat
      (hzero : ∀ x, curvatureOperatorEndomorphismAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ = 0)
      (hcover : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.HasEuclideanUniversalCover
        (I := I) (M := M) g)
  | rankOne
      (hrank : ∀ x, Module.finrank Real
        (curvatureOperatorImageAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) g x⟩) = 1)
      (hproduct : DifferentialGeometry.Geometry.Curvature.DimensionThree.HasCurvatureSurfaceProductSplitting
        (I := I) (M := M) g)
  | positive
      (hrank : ∀ x, Module.finrank Real
        (curvatureOperatorImageAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) g x⟩) = 3)
      (hpositive : ∀ x,
        ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real, a ≠ 0 →
          0 < (twoFormMetricData (I := I) g x).inner
            (curvatureOperatorEndomorphismAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩ a) a)

theorem curvature_time_slice_global_trichotomy_of_derived_data
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners Real
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    (g : SmoothRiemannianMetric I M)
    (hg : DifferentialGeometry.RiemannianMetricComplete (I := I) g)
    (hpositive : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        0 ≤ (twoFormMetricData (I := I) g x).inner
          (curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩ a) a)
    (hnull : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩ a = 0 →
          curvatureOperatorReactionEndomorphism3
            (curvatureOperatorEndomorphismAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩).toLinearMap a = 0)
    (hrank : ∀ x y,
      Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩) =
        Module.finrank Real
          (curvatureOperatorImageAt (I := I) g y
            ⟨metricRm04 (I := I) g y,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g y⟩))
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) g x⟩)) :
    CurvatureTimeSliceGlobalAlternative (I := I) (M := M) g := by
  rcases curvatureOperator_time_slice_rank_trichotomy_of_complete_metric_nonnegative_reaction_constant_rank_parallel_kernel
      (I := I) g hg hpositive hnull hrank hkernel with hzero | hline | hpositiveRank
  · exact .flat hzero.1 hzero.2
  · exact .rankOne hline.1 hline.2
  · exact .positive hpositiveRank.1 hpositiveRank.2

theorem flow_time_slice_global_trichotomy_of_derived_data
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners Real
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (hg : ∀ t ∈ D.carrier,
      DifferentialGeometry.RiemannianMetricComplete (I := I) (S.base.metric t))
    {t : Real} (ht : t ∈ D.carrier)
    (hpositive : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        0 ≤ (twoFormMetricData (I := I) (S.base.metric t) x).inner
          (curvatureOperatorEndomorphismAt (I := I) (S.base.metric t) x
            ⟨S.base.rm04 t x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩ a) a)
    (hnull : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        curvatureOperatorEndomorphismAt (I := I) (S.base.metric t) x
            ⟨S.base.rm04 t x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩ a = 0 →
          curvatureOperatorReactionEndomorphism3
            (curvatureOperatorEndomorphismAt (I := I) (S.base.metric t) x
              ⟨S.base.rm04 t x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) (S.base.metric t) x⟩).toLinearMap a = 0)
    (hrank : ∀ x y,
      Module.finrank Real
          (curvatureOperatorImageAt (I := I) (S.base.metric t) x
            ⟨S.base.rm04 t x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩) =
        Module.finrank Real
          (curvatureOperatorImageAt (I := I) (S.base.metric t) y
            ⟨S.base.rm04 t y,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) y⟩))
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily
      (S.base.metric t)
      (fun x => curvatureOperatorKernelAt (I := I) (S.base.metric t) x
        ⟨S.base.rm04 t x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩)) :
    CurvatureTimeSliceGlobalAlternative (I := I) (M := M) (S.base.metric t) := by
  exact curvature_time_slice_global_trichotomy_of_derived_data
    (I := I) (M := M) (S.base.metric t) (hg t ht)
    hpositive hnull hrank hkernel

def curvatureOperatorImageRank
    {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M) : Nat :=
  Module.finrank Real
    (curvatureOperatorImageAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) g x⟩)

structure CurvatureTimeSliceDerivedData
    {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [Nonempty M]
    (g : SmoothRiemannianMetric I M) where
  dimension : Module.finrank Real E = 3
  nonnegative : ∀ x,
    ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
      0 ≤ (twoFormMetricData (I := I) g x).inner
        (curvatureOperatorEndomorphismAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) g x⟩ a) a
  nullReaction : ∀ x,
    ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
      curvatureOperatorEndomorphismAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) g x⟩ a = 0 →
        curvatureOperatorReactionEndomorphism3
          (curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩).toLinearMap a = 0
  spatialRank : ∀ x y, curvatureOperatorImageRank g x = curvatureOperatorImageRank g y
  parallelKernel : IsParallelContinuousAlternatingSubmoduleFamily g
    (fun x => curvatureOperatorKernelAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) g x⟩)

structure CurvatureFlowDerivedData
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners Real
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D) where
  complete : ∀ t ∈ D.carrier,
    DifferentialGeometry.RiemannianMetricComplete (I := I) (S.base.metric t)
  slice : ∀ t ∈ D.carrier,
    CurvatureTimeSliceDerivedData (I := I) (M := M) (S.base.metric t)

inductive WholeFlowCurvatureAlternative
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners Real
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D) : Prop where
  | flat
      (hzero : ∀ t ∈ D.carrier, ∀ x,
        curvatureOperatorEndomorphismAt (I := I) (S.base.metric t) x
          ⟨metricRm04 (I := I) (S.base.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ = 0)
      (hcover : ∀ t ∈ D.carrier,
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.HasEuclideanUniversalCover
          (I := I) (M := M) (S.base.metric t))
  | rankOne
      (hrank : ∀ t ∈ D.carrier, ∀ x, curvatureOperatorImageRank (S.base.metric t) x = 1)
      (hproduct : ∀ t ∈ D.carrier,
        DifferentialGeometry.Geometry.Curvature.DimensionThree.HasCurvatureSurfaceProductSplitting
          (I := I) (M := M) (S.base.metric t))
  | positive
      (hrank : ∀ t ∈ D.carrier, ∀ x, curvatureOperatorImageRank (S.base.metric t) x = 3)
      (hpositive : ∀ t ∈ D.carrier, ∀ x,
        ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real, a ≠ 0 →
          0 < (twoFormMetricData (I := I) (S.base.metric t) x).inner
            (curvatureOperatorEndomorphismAt (I := I) (S.base.metric t) x
              ⟨metricRm04 (I := I) (S.base.metric t) x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) (S.base.metric t) x⟩ a) a)

theorem whole_flow_trichotomy_of_constant_rank_mode
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners Real
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (data : CurvatureFlowDerivedData (I := I) (M := M) S)
    (hmode : ∃ q : Nat, ∀ t ∈ D.carrier, ∀ x,
      curvatureOperatorImageRank (S.base.metric t) x = q)
    (hcarrier : ∃ t, t ∈ D.carrier) :
    WholeFlowCurvatureAlternative S := by
  let global := fun (t : Real) (ht : t ∈ D.carrier) =>
    curvatureOperator_time_slice_rank_trichotomy_of_complete_metric_nonnegative_reaction_constant_rank_parallel_kernel
      (I := I) (M := M) (S.base.metric t) (data.complete t ht)
      (data.slice t ht).nonnegative (data.slice t ht).nullReaction
      (fun x y => by
        simpa [curvatureOperatorImageRank] using (data.slice t ht).spatialRank x y)
      (data.slice t ht).parallelKernel
  obtain ⟨q, hq⟩ := hmode
  obtain ⟨t₀, ht₀⟩ := hcarrier
  have rank_zero_of_zero : ∀ {t : Real}, t ∈ D.carrier →
      (∀ x, curvatureOperatorEndomorphismAt (I := I) (S.base.metric t) x
        ⟨metricRm04 (I := I) (S.base.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ = 0) →
    ∀ x, curvatureOperatorImageRank (S.base.metric t) x = 0 := by
    intro t ht hzero x
    have hrange : curvatureOperatorImageAt (I := I) (S.base.metric t) x
        ⟨metricRm04 (I := I) (S.base.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ = ⊥ := by
      apply le_antisymm
      · rintro v ⟨a, rfl⟩
        change (curvatureOperatorEndomorphismAt (I := I) (S.base.metric t) x
          ⟨metricRm04 (I := I) (S.base.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩) a = 0
        rw [hzero x]
        simp
      · exact bot_le
    change Module.finrank Real
      (curvatureOperatorImageAt (I := I) (S.base.metric t) x
        ⟨metricRm04 (I := I) (S.base.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩) = 0
    rw [hrange]
    simp
  have hq_cases : q = 0 ∨ q = 1 ∨ q = 3 := by
    rcases global t₀ ht₀ with hzero | hline | hpositive
    · exact Or.inl ((hq t₀ ht₀ (Classical.choice (inferInstance : Nonempty M))).symm.trans
        (rank_zero_of_zero ht₀ hzero.1
          (Classical.choice (inferInstance : Nonempty M))))
    · exact Or.inr (Or.inl ((hq t₀ ht₀ (Classical.choice (inferInstance : Nonempty M))).symm.trans
        (by simpa [curvatureOperatorImageRank] using
          hline.1 (Classical.choice (inferInstance : Nonempty M)))))
    · exact Or.inr (Or.inr ((hq t₀ ht₀ (Classical.choice (inferInstance : Nonempty M))).symm.trans
        (by simpa [curvatureOperatorImageRank] using
          hpositive.1 (Classical.choice (inferInstance : Nonempty M)))))
  rcases hq_cases with rfl | rfl | rfl
  · refine .flat ?_ ?_
    · intro t ht x
      rcases global t ht with hzero | hline | hpositive
      · exact hzero.1 x
      · exfalso
        have h := hq t ht x
        have h' : curvatureOperatorImageRank (S.base.metric t) x = 1 := by
          simpa [curvatureOperatorImageRank] using hline.1 x
        omega
      · exfalso
        have h := hq t ht x
        have h' : curvatureOperatorImageRank (S.base.metric t) x = 3 := by
          simpa [curvatureOperatorImageRank] using hpositive.1 x
        omega
    · intro t ht
      rcases global t ht with hzero | hline | hpositive
      · exact hzero.2
      · exfalso
        have h := hq t ht (Classical.choice (inferInstance : Nonempty M))
        have h' : curvatureOperatorImageRank (S.base.metric t)
            (Classical.choice (inferInstance : Nonempty M)) = 1 := by
          simpa [curvatureOperatorImageRank] using
            hline.1 (Classical.choice (inferInstance : Nonempty M))
        omega
      · exfalso
        have h := hq t ht (Classical.choice (inferInstance : Nonempty M))
        have h' : curvatureOperatorImageRank (S.base.metric t)
            (Classical.choice (inferInstance : Nonempty M)) = 3 := by
          simpa [curvatureOperatorImageRank] using
            hpositive.1 (Classical.choice (inferInstance : Nonempty M))
        omega
  · refine .rankOne ?_ ?_
    · intro t ht x
      rcases global t ht with hzero | hline | hpositive
      · have h := hq t ht x
        have h' := rank_zero_of_zero ht hzero.1 x
        omega
      · simpa [curvatureOperatorImageRank] using hline.1 x
      · have h := hq t ht x
        have h' : curvatureOperatorImageRank (S.base.metric t) x = 3 := by
          simpa [curvatureOperatorImageRank] using hpositive.1 x
        omega
    · intro t ht
      rcases global t ht with hzero | hline | hpositive
      · exfalso
        have h := hq t ht (Classical.choice (inferInstance : Nonempty M))
        have h' := rank_zero_of_zero ht hzero.1
          (Classical.choice (inferInstance : Nonempty M))
        omega
      · exact hline.2
      · exfalso
        have h := hq t ht (Classical.choice (inferInstance : Nonempty M))
        have h' : curvatureOperatorImageRank (S.base.metric t)
            (Classical.choice (inferInstance : Nonempty M)) = 3 := by
          simpa [curvatureOperatorImageRank] using
            hpositive.1 (Classical.choice (inferInstance : Nonempty M))
        omega
  · refine .positive ?_ ?_
    · intro t ht x
      rcases global t ht with hzero | hline | hpositive
      · have h := hq t ht x
        have h' := rank_zero_of_zero ht hzero.1 x
        omega
      · have h := hq t ht x
        have h' : curvatureOperatorImageRank (S.base.metric t) x = 1 := by
          simpa [curvatureOperatorImageRank] using hline.1 x
        omega
      · simpa [curvatureOperatorImageRank] using hpositive.1 x
    · intro t ht x a ha
      rcases global t ht with hzero | hline | hpositive
      · have h := hq t ht x
        have h' := rank_zero_of_zero ht hzero.1 x
        omega
      · have h := hq t ht x
        have h' : curvatureOperatorImageRank (S.base.metric t) x = 1 := by
          simpa [curvatureOperatorImageRank] using hline.1 x
        omega
      · exact hpositive.2 x a ha

theorem ancient_curvature_trichotomy_of_constant_rank_mode
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners Real
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]
    {T : Real}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T))
    (data : CurvatureFlowDerivedData (I := I) (M := M) S)
    (hmode : ∃ q : Nat, ∀ t ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T).carrier,
      ∀ x, curvatureOperatorImageRank (S.base.metric t) x = q) :
    WholeFlowCurvatureAlternative S := by
  apply whole_flow_trichotomy_of_constant_rank_mode S data hmode
  exact ⟨T - 1,
    (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient T).initial_mem⟩

theorem flow_time_slice_global_trichotomy_at_later_time
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {s t : ℝ} (hst : s < t) (hreg : Icc s t ⊆ D.regular)
    (hR : ∀ r ∈ Icc s t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : RiemannianMetricComplete (S.family.metric t)) :
    CurvatureTimeSliceGlobalAlternative (S.family.metric t) := by
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hnonneg := fun x => curvatureOperatorEndomorphismAt_inner_nonneg_of_mem_nonnegativeCone
    hdim (S.family.metric t) x _
    (hR t ⟨hst.le, le_rfl⟩ x)
  have hnull : ∀ x, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
      curvatureOperatorEndomorphismAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ a = 0 →
      curvatureOperatorReactionEndomorphism3
        (curvatureOperatorEndomorphismAt (S.family.metric t) x
          ⟨metricRm04At (S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩).toLinearMap a = 0 := by
    intro x a ha
    let _ : FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
      (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
        (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite
    have htwoform : Module.finrank ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) = 3 := by
      rw [ContinuousAlternatingMap.finrank_continuousAlternatingMap]
      change (Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3)).choose 2 = 3
      rw [hdim]
      norm_num
    apply curvatureOperatorReactionEndomorphism3_eq_zero_of_mem_ker_of_finrank_range_ne_two
      htwoform _ _ ha
    have htri := curvatureOperatorImageAt_finrank_trichotomy_at_later_time S hS hdim hst hreg hR x
    change Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ≠ 2
    rcases htri with hzero | hone | hthree <;> omega
  exact curvature_time_slice_global_trichotomy_of_derived_data (S.family.metric t) hcomplete
    hnonneg hnull (curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hst hreg hR)
    (curvatureOperatorKernelAt_parallel_at_later_time S hS hdim hst hreg hR)

theorem flow_time_slice_global_trichotomy_exclusive_at_later_time
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {s t : ℝ} (hst : s < t) (hreg : Icc s t ⊆ D.regular)
    (hR : ∀ r ∈ Icc s t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : RiemannianMetricComplete (S.family.metric t)) :
    let g := S.family.metric t
    let flat := (∀ x, curvatureOperatorEndomorphismAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ = 0) ∧
      Geometry.Riemannian.Topology.UniversalCover.HasEuclideanUniversalCover g
    let rankOne := (∀ x, curvatureOperatorImageRank g x = 1) ∧
      Geometry.Curvature.DimensionThree.HasCurvatureSurfaceProductSplitting g
    let positive := (∀ x, curvatureOperatorImageRank g x = 3) ∧
      ∀ x, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ, a ≠ 0 →
        0 < (twoFormMetricData g x).inner (curvatureOperatorEndomorphismAt g x
          ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩ a) a
    (flat ∨ rankOne ∨ positive) ∧
      ¬(flat ∧ rankOne) ∧ ¬(flat ∧ positive) ∧ ¬(rankOne ∧ positive) := by
  intro g flat rankOne positive
  have halts : flat ∨ rankOne ∨ positive := by
    rcases flow_time_slice_global_trichotomy_at_later_time S hS hst hreg hR hcomplete with
      ⟨hzero, hcover⟩ | ⟨hrank, hsplit⟩ | ⟨hrank, hpos⟩
    · exact Or.inl ⟨hzero, hcover⟩
    · exact Or.inr (Or.inl ⟨hrank, hsplit⟩)
    · exact Or.inr (Or.inr ⟨hrank, hpos⟩)
  let x₀ : M := Classical.choice (inferInstance : Nonempty M)
  have hzero (hf : flat) : curvatureOperatorImageRank g x₀ = 0 := by
    have hrange : curvatureOperatorImageAt g x₀
        ⟨metricRm04At g x₀, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x₀⟩ = ⊥ := by
      change (curvatureOperatorEndomorphismAt g x₀
        ⟨metricRm04At g x₀, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x₀⟩).range = ⊥
      rw [hf.1 x₀]
      exact LinearMap.range_zero
    have hz : Module.finrank ℝ (curvatureOperatorImageAt g x₀
        ⟨metricRm04At g x₀, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x₀⟩) = 0 := by
      rw [hrange]
      exact finrank_bot ℝ _
    exact hz
  refine ⟨halts, ?_, ?_, ?_⟩
  · rintro ⟨hf, h1⟩
    have h0 := hzero hf
    have h1' := h1.1 x₀
    omega
  · rintro ⟨hf, h3⟩
    have h0 := hzero hf
    have h3' := h3.1 x₀
    omega
  · rintro ⟨h1, h3⟩
    have h1' := h1.1 x₀
    have h3' := h3.1 x₀
    omega

end DifferentialGeometry.PDE.RicciFlow.DimensionThree
