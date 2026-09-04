import DifferentialGeometry.Geometry.Comparison.InjectivityRadius.Intrinsic
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Instances

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

open Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def PointedRiemannianManifold.intrInjRadius
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) X)
    (x : X.M) : ENNReal := by
  let _ : TopologicalSpace X.M := X.topology
  let _ : ChartedSpace H X.M := X.charted
  let _ : IsManifold I ∞ X.M := X.smooth
  let _ : IsManifold I 1 X.M :=
    IsManifold.of_le (I := I) (M := X.M) (n := ∞) (by decide)
  let _ : T2Space X.M := X.t2
  let _ : SigmaCompactSpace X.M := X.sigmaCompact
  let _ : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  let _ : RiemannianBundle (fun y : X.M => TangentSpace I y) :=
    X.riemBundle (I := I)
  let _ : (y : X.M) → InnerProductSpace Real (TangentSpace I y) :=
    X.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun y : X.M => TangentSpace I y) := X.riemBundle_cont (I := I)
  let _ : EMetricSpace X.M := X.emetricSpace (I := I)
  let _ : CompleteSpace X.M := MetricComplete.complete (I := I) X hcomplete
  let hEnorm : ∀ (y : X.M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (X.metric.inner y w w)) := by
    intro y w
    with_unfolding_all
      exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) X.metric y w
  exact Geometry.Riemannian.NormalCoordinates.intrInjRadius
    (I := I) X.metric hEnorm x

def HasInjRadiusAt
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M)
    (rho : Real) : Prop :=
  0 < rho ∧ ∀ hcomplete : MetricComplete (I := I) X,
    ENNReal.ofReal rho ≤ X.intrInjRadius (I := I) hcomplete x

omit [CompleteSpace E] in
theorem hasInjRadiusAt_iff
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M)
    (rho : Real) :
    HasInjRadiusAt (I := I) X x rho ↔
      (0 < rho ∧ ∀ hcomplete : MetricComplete (I := I) X,
        ENNReal.ofReal rho ≤ X.intrInjRadius (I := I) hcomplete x) :=
  Iff.rfl

omit [CompleteSpace E] in
theorem hasInjRadiusAt_of_le
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho : Real} (hpos : 0 < rho)
    (h : ∀ hcomplete : MetricComplete (I := I) X,
      ENNReal.ofReal rho ≤ X.intrInjRadius (I := I) hcomplete x) :
    HasInjRadiusAt (I := I) X x rho :=
  ⟨hpos, h⟩

omit [CompleteSpace E] in
theorem HasInjRadiusAt.le_intr
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho : Real} (h : HasInjRadiusAt (I := I) X x rho)
    (hcomplete : MetricComplete (I := I) X) :
    ENNReal.ofReal rho ≤ X.intrInjRadius (I := I) hcomplete x :=
  h.2 hcomplete

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem HasInjRadiusAt.injOn_ball
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho r : Real} (h : HasInjRadiusAt (I := I) X x rho)
    (hcomplete : MetricComplete (I := I) X) (hr : r < rho) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : IsManifold I 1 X.M :=
      IsManifold.of_le (I := I) (M := X.M) (n := ∞) (by decide)
    letI : T2Space X.M := X.t2
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
    letI : RiemannianBundle (fun y : X.M => TangentSpace I y) :=
      X.riemBundle (I := I)
    letI : (y : X.M) → InnerProductSpace Real (TangentSpace I y) :=
      X.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : X.M => TangentSpace I y) := X.riemBundle_cont (I := I)
    letI : EMetricSpace X.M := X.emetricSpace (I := I)
    letI : CompleteSpace X.M := MetricComplete.complete (I := I) X hcomplete
    let hEnorm : ∀ (y : X.M) (w : TangentSpace I y),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (X.metric.inner y w w)) := by
      intro y w
      with_unfolding_all
        exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) X.metric y w
    Set.InjOn (intrinsicFramedExp (I := I) X.metric hEnorm x)
      (Metric.ball (0 : E) r) := by
  let _ : TopologicalSpace X.M := X.topology
  let _ : ChartedSpace H X.M := X.charted
  let _ : IsManifold I ∞ X.M := X.smooth
  let _ : IsManifold I 1 X.M :=
    IsManifold.of_le (I := I) (M := X.M) (n := ∞) (by decide)
  let _ : T2Space X.M := X.t2
  let _ : SigmaCompactSpace X.M := X.sigmaCompact
  let _ : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  let _ : RiemannianBundle (fun y : X.M => TangentSpace I y) :=
    X.riemBundle (I := I)
  let _ : (y : X.M) → InnerProductSpace Real (TangentSpace I y) :=
    X.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun y : X.M => TangentSpace I y) := X.riemBundle_cont (I := I)
  let _ : EMetricSpace X.M := X.emetricSpace (I := I)
  let _ : CompleteSpace X.M := MetricComplete.complete (I := I) X hcomplete
  let hEnorm : ∀ (y : X.M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (X.metric.inner y w w)) := by
    intro y w
    with_unfolding_all
      exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) X.metric y w
  apply intrInjOn_ball (I := I) X.metric hEnorm x
  exact ((ENNReal.ofReal_lt_ofReal_iff h.1).2 hr).trans_le <| by
    simpa only [PointedRiemannianManifold.intrInjRadius] using
      h.le_intr hcomplete

omit [CompleteSpace E] in
theorem HasInjRadiusAt.mono
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho rho' : Real} (h : HasInjRadiusAt (I := I) X x rho)
    (hpos : 0 < rho') (hle : rho' <= rho) :
    HasInjRadiusAt (I := I) X x rho' := by
  rw [hasInjRadiusAt_iff] at h ⊢
  refine ⟨hpos, ?_⟩
  intro hcomplete
  exact (ENNReal.ofReal_le_ofReal hle).trans (h.2 hcomplete)

structure BaseInjBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  ρ : Real
  pos : 0 < ρ
  bound : forall i : Nat, HasInjRadiusAt (I := I) (X.obj i) (X.obj i).basepoint ρ

namespace BaseInjBound

def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : BaseInjBound (I := I) X) (f : Nat -> Nat) :
    BaseInjBound (I := I) (X.subseq f) where
  ρ := h.ρ
  pos := h.pos
  bound := by
    intro i
    simpa [PointedRiemannianSeq.subseq] using h.bound (f i)

end BaseInjBound

end HCGCompactness
end DifferentialGeometry
