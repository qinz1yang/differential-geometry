import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SmoothSolution
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.Mixed
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.LocallyLipschitzTruncation
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.StrictParabolicity
import DifferentialGeometry.Topology.Manifold.AddCircle

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

abbrev CircleSobolevSection
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (r s : ℕ) (σ : ℝ) : Type _ :=
  TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g r s σ

abbrev CircleMaximalRegularitySolutionSpace
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (r s : ℕ) (a T : ℝ) : Type _ :=
  timeH1 (CircleSobolevSection g r s a) T

theorem circleSobolevSection_nonempty
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (r s : ℕ) (σ : ℝ) :
    Nonempty (CircleSobolevSection g r s σ) :=
  ⟨0⟩

theorem circleMaximalRegularitySolutionSpace_nonempty
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (r s : ℕ) (a T : ℝ) :
    Nonempty (CircleMaximalRegularitySolutionSpace g r s a T) :=
  ⟨0⟩

theorem circleLaplacianSymbol_isStrictlyParabolic
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    DifferentialGeometry.PDE.DeTurck.IsStrictlyParabolic (E := ℝ)
      (fun _ : AddCircle (1 : ℝ) => ℝ) g
      (DifferentialGeometry.PDE.DeTurck.laplacianSymbol
        (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g) :=
  DifferentialGeometry.PDE.DeTurck.laplacianSymbol_isStrictlyParabolic
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g

theorem circle_deTurckRicciRHS_isStrictlyParabolic
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    DifferentialGeometry.PDE.IsStrictlyParabolicMetricRHS (I := 𝓘(ℝ, ℝ))
      (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := 𝓘(ℝ, ℝ)) g) g :=
  DifferentialGeometry.Analysis.Parabolic.deTurckRicciRHS_isStrictlyParabolic_at_self g g

def IsMixedSmall (L2 L1 : ℝ≥0) (T : ℝ) : Prop :=
  (L2 : ℝ) * (1 + T) + (L1 : ℝ) * (2 * Real.sqrt T) < 1

theorem isMixedSmall_of_le_mixedHorizon {L2 L1 : ℝ≥0} {T : ℝ}
    (hL2 : 2 * (L2 : ℝ) < 1) (hT : T ≤ mixedHorizon L2 L1) :
    IsMixedSmall L2 L1 T :=
  mixedHorizon_small hL2 hT

theorem not_isMixedSmall_one_zero_zero : ¬ IsMixedSmall 1 0 0 := by
  norm_num [IsMixedSmall]

structure TensorNemytskiiSplit
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ) where
  L2 : ℝ≥0
  L1 : ℝ≥0
  N2 : TensorHs (I := I) (M := M) g r s (a + 2) →
    TensorHs (I := I) (M := M) g r s a
  N1 : TensorHs (I := I) (M := M) g r s (a + 1) →
    TensorHs (I := I) (M := M) g r s a
  lipschitz_N2 : LipschitzWith L2 N2
  lipschitz_N1 : LipschitzWith L1 N1

namespace TensorNemytskiiSplit

def IsSmall (S : TensorNemytskiiSplit g r s a) (T : ℝ) : Prop :=
  IsMixedSmall S.L2 S.L1 T

def zero (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ) :
    TensorNemytskiiSplit g r s a where
  L2 := 0
  L1 := 0
  N2 := fun _ => 0
  N1 := fun _ => 0
  lipschitz_N2 := LipschitzWith.const 0
  lipschitz_N1 := LipschitzWith.const 0

omit [NeZero (Module.finrank ℝ E)] in
theorem zero_isSmall (g : SmoothRiemannianMetric I M) (r s : ℕ) (a T : ℝ) :
    (zero g r s a).IsSmall T := by
  norm_num [IsSmall, IsMixedSmall, zero]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_strong_solution
    (S : TensorNemytskiiSplit g r s a)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : TensorHs (I := I) (M := M) g r s (a + 2))
    (hsmall : S.IsSmall T) :
    ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M)
        (g := g) (r := r) (s := s) a T)
      (force : timeL2 (TensorHs (I := I) (M := M) g r s a) T),
      u = maximalRegularityDuhamelMap (I := I) (M := M) a hT u0 force ∧
        force =
          nemytskii (I := I) (M := M) S.lipschitz_N2
              (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u0 force) +
            nemytskiiHa1 (I := I) (M := M) S.lipschitz_N1
              (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u0 force) ∧
        DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0 _ T u =
          tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a ≤ a + 2 by linarith) u0 ∧
        DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv _ T u =
          timeScaleLaplacian (I := I) (M := M) a
              (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u0 force) +
            (nemytskii (I := I) (M := M) S.lipschitz_N2
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u0 force) +
              nemytskiiHa1 (I := I) (M := M) S.lipschitz_N1
                (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u0
                  force)) :=
  exists_mixed_strong_solution (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u0 S.N2 S.lipschitz_N2
    S.N1 S.lipschitz_N1 hsmall

end TensorNemytskiiSplit

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorNemytskiiSplit_nonempty
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ) :
    Nonempty (TensorNemytskiiSplit g r s a) :=
  ⟨TensorNemytskiiSplit.zero g r s a⟩

theorem circleTensorNemytskiiSplit_exists_strong_solution
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (r s : ℕ) (a T : ℝ)
    (S : TensorNemytskiiSplit (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g r s a)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g r s))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u0 : CircleSobolevSection g r s (a + 2))
    (hsmall : S.IsSmall T) :
    ∃ (u : CircleMaximalRegularitySolutionSpace g r s a T)
      (force : timeL2 (CircleSobolevSection g r s a) T),
      u = maximalRegularityDuhamelMap (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
        a hT u0 force ∧
        force =
          nemytskii (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) S.lipschitz_N2
              (maximalRegularityDuhamelSolutionField (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                a hT u0 force) +
            nemytskiiHa1 (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) S.lipschitz_N1
              (maximalRegularityDuhamelSolutionFieldHa1
                (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) a hT u0 force) ∧
        DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trace0 _ T u =
          tensorHsInclusion (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
            (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith) u0 ∧
        DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.timeDeriv _ T u =
          timeScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) a
              (maximalRegularityDuhamelSolutionField (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                a hT u0 force) +
            (nemytskii (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) S.lipschitz_N2
                (maximalRegularityDuhamelSolutionField
                  (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) a hT u0 force) +
              nemytskiiHa1 (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) S.lipschitz_N1
                (maximalRegularityDuhamelSolutionFieldHa1
                  (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) a hT u0 force)) :=
  S.exists_strong_solution h_compact hT hT1 u0 hsmall

noncomputable abbrev circleDeSimonShortTimeExistence
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (r s : ℕ) (a : ℝ)
    {N : CircleSobolevSection g r s (a + 1) → CircleSobolevSection g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g r s))
    (u0 : CircleSobolevSection g r s (a + 2))
    (hN : LipschitzOnWith L_R N (Metric.closedBall
      (tensorHsInclusion (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
        (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith) u0) R)) :=
  de_simon_quasilinear_tensor_heat_short_time_existence_locally_lipschitz_of_compact_resolvent
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := r) (s := s)
    (a := a) hR h_compact u0 hN

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
