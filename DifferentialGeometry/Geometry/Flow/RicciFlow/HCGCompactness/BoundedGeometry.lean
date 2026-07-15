import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Comparison.Volume.BallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.InjectivityRadius

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Bounded Geometry Inputs

The records in this file state the curvature and curvature-derivative
assumptions used by MSM135 compactness theorems.  The pointwise bounds are
defined from the canonical metric Riemann tensor and its iterated covariant
derivatives, not as opaque placeholders.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedMetric

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- One covariant-derivative step for the metric Riemann tensor.  The input has
valence `a + 4`, and the derivative has valence `a + 5`, with derivative slots
placed first. -/
noncomputable def curvCovDerivStep
    (g : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 4)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 5) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov := DifferentialGeometry.Integral.Connection.metricCov (I := I) (M := M) g
  let hcov := DifferentialGeometry.Integral.Connection.metricCov_smooth (I := I) (M := M) g
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) (a + 4) cov hcov A
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cov, hcov, hreg]
    using
      Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (a + 4) cov A hreg

/-- The `k`-fold covariant derivative of the canonical lowered Riemann tensor
of `g`.  The result has covariant valence `k + 4`. -/
noncomputable def curvCovDeriv
    (g : SmoothRiemannianMetric I M) :
    (k : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (k + 4) :=
  Nat.rec
    (motive := fun k : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (k + 4))
    (by
      haveI : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
        change IsManifold I ∞ M
        infer_instance
      exact DifferentialGeometry.Integral.Connection.metricRm04 (I := I) (M := M) g)
    (fun k A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          curvCovDerivStep (I := I) g k A)

/-- Squared norm `|nabla^k Rm(g)|_g^2` at a point. -/
noncomputable def curvDerivNormSq
    (k : Nat) (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Tensor0SBundle.normSq0S (I := I) g x (k + 4)
    (curvCovDeriv (I := I) (M := M) g k x)

/-- Norm `|nabla^k Rm(g)|_g` at a point. -/
noncomputable def curvDerivNorm
    (k : Nat) (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt (curvDerivNormSq (I := I) (M := M) k g x)

end FixedMetric

/-- Global bound `|nabla^k Rm| <= C` for one pointed metric object. -/
def HasCurvDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (k : Nat)
    (C : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  forall x : X.M, curvDerivNorm (I := I) k X.metric x <= C

/-- A zeroth-order curvature-derivative bound supplies the global Rm04 bound
used by the local volume-comparison endpoint. -/
theorem rm04Bound_of_curv0
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) {C : Real}
    (hX : HasCurvDerivBound (I := I) X 0 C) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := X.M) X.metric C := by
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  intro x
  simpa [Geometry.Riemannian.VolumeComparison.Rm04GlobalBound,
    HasCurvDerivBound, curvDerivNorm, curvDerivNormSq, curvCovDeriv,
    DifferentialGeometry.Integral.Connection.metricRm04_apply] using hX x

/-- Bounded geometry for one pointed metric: all covariant derivatives of
curvature have global bounds. -/
structure BoundedGeometry
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall k : Nat, HasCurvDerivBound (I := I) X k (C k)

/-- Bounded geometry supplies the zeroth-order Rm04 bound consumed by the
volume-comparison endpoint. -/
theorem rm04Bound_of_geom
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (hX : BoundedGeometry (I := I) X) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := X.M) X.metric (hX.C 0) :=
  rm04Bound_of_curv0 (I := I) X (hX.bound 0)

/-- Uniform bounded geometry for a pointed metric sequence, matching MSM135
Definition 3.8. -/
structure SeqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall i k : Nat, HasCurvDerivBound (I := I) (X.obj i) k (C k)

namespace SeqBoundedGeometry

/-- Reindex uniform bounded geometry along a subsequence. -/
def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqBoundedGeometry (I := I) X) (f : Nat -> Nat) :
    SeqBoundedGeometry (I := I) (X.subseq f) where
  C := hX.C
  nonneg := hX.nonneg
  bound := by
    intro i k
    simpa [PointedRiemannianSeq.subseq] using hX.bound (f i) k

end SeqBoundedGeometry

/-- Uniform bounded geometry supplies the time-slice Rm04 bound for each
sequence member. -/
theorem rm04Bound_of_seq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqBoundedGeometry (I := I) X) (i : Nat) :
    letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
    letI : ChartedSpace H (X.obj i).M := (X.obj i).charted
    letI : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
    letI : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
    letI : T2Space (X.obj i).M := (X.obj i).t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := (X.obj i).M) (X.obj i).metric (hX.C 0) :=
  rm04Bound_of_curv0 (I := I) (X.obj i) (hX.bound i 0)

/-- Global spacetime zeroth-order curvature bound for one pointed flow. -/
def HasSpacetimeCurvBound
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (C : Real) : Prop :=
  forall t : Real, t ∈ D.carrier ->
    forall x : F.M, F.rmNormSq (I := I) t x <= C

/-- Global spacetime family of spatial curvature-derivative bounds for one
pointed flow.  At each time, this uses the Levi-Civita connection of the time
slice metric. -/
def HasSpacetimeCurvDerivBound
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (k : Nat) (C : Real) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  forall t : Real, t ∈ D.carrier ->
    forall x : F.M, curvDerivNorm (I := I) k (F.S.family.metric t) x <= C

/-- Uniform zeroth-order curvature bound for a pointed flow sequence. -/
structure SpacetimeCurvBound
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  C : Real
  nonneg : 0 <= C
  bound : forall i : Nat, HasSpacetimeCurvBound (I := I) (X.term i) C

/-- Uniform spacetime curvature-derivative bounds for a pointed flow sequence.

This is stronger than the zeroth-order curvature bound and is the explicit
input used until Shi-type derivative estimates are formalized. -/
structure FlowDerivBounds
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall i k : Nat, HasSpacetimeCurvDerivBound (I := I) (X.term i) k (C k)

/-- Honest derivative input for solution compactness.

The time-zero bounded-geometry field is explicit because the primitive
spacetime derivative predicates are not yet connected to the metric
curvature-derivative predicates by a proved restriction theorem. -/
structure FlowDerivativeInput
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  spacetime : FlowDerivBounds (I := I) X
  at_zero_geom : SeqBoundedGeometry (I := I) (X.atZero (I := I))

end HCGCompactness
end DifferentialGeometry
