import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapWitnessReparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CappingReparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {t₀ t₁ : ℝ}
  (E : MetricCutCapEvent P Q t₀ t₁)
  {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {η δ : ℝ} {order : ℕ}
  {neck : NormalizedNeck E.terminal.metric δ order}
  (b : E.RetainedBoundaryIndex)
  (S : StaticCapWitness neck fixed D m η)
  (K : Capping E.transition.trace.tubes E.capped.Carrier)
  (B : E.transition.trace.tubes.Boundary → ThreeBall ≃ₜ ThreeBall)
  (a : E.transition.trace.tubes.Boundary → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
  (hboundary : ∀ c y, B c (sphereToThreeBall y) = sphereToThreeBall (a c y))
  (hK : E.transition.trace.capping =
    K.reparametrizeCaps B (fun c => (a c).toHomeomorph) hboundary)
  (A : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
  (hB : ∀ x : ThreeBall, (B b.1 x : ThreeSpace) = A x)
  (inclusion : C(S.Output, Q.Carrier))
  (hinc : IsSmoothEmbedding ThreeModel ThreeModel ∞ inclusion)
  (hmetric : ∀ x V W, S.metric.inner x V W =
    E.outputMetric.inner (inclusion x)
      (mfderiv ThreeModel ThreeModel inclusion x V)
      (mfderiv ThreeModel ThreeModel inclusion x W))
  (hattach : (S.attaching : Sphere 2 → Sphere 2) = K.attaching b.1)
  (hcap : ∀ x : ThreeBall, E.transition.trace.presentation (K.cap b.1 x) =
    Sum.inl (inclusion (S.cap x)))
  (point : neckRetainedCollar δ → E.transition.trace.tubes.core)
  (hpoint : ∀ x (hx : x.1 ∈ neckBuffer δ), (point x).1 = (neck.chart ⟨x.1, hx⟩).1)
  (hretained : ∀ x, E.transition.trace.presentation (K.coreInclusion (point x)) =
    Sum.inl (inclusion (S.retained x)))

include hB hboundary in
private theorem sphere_reparametrization_coe (y : Sphere 2) : (a b.1 y : ThreeSpace) = A y := by
  have h := congrArg (fun x : ThreeBall => (x : ThreeSpace)) (hboundary b.1 y)
  rw [hB] at h
  exact h.symm

def PresentedStaticCap.ofReparametrizedCapping : PresentedStaticCap E fixed D m η b := by
  let ha := sphere_reparametrization_coe E b B a hboundary A hB
  let S' := S.reparametrizeCapOfLinearIsometry A (a b.1) ha
  refine
    { delta := δ
      order := order
      neck := neck
      witness := S'
      inclusion := inclusion
      inclusion_smooth := hinc
      inclusion_metric := hmetric
      cap_eq := ?_
      attaching_eq := ?_
      retainedPoint := fun x => ⟨point x, ?_⟩
      retained_point_eq := hpoint
      retained_eq := ?_ }
  · intro x
    rw [hK]
    change E.transition.trace.presentation (K.cap b.1 (B b.1 x)) =
      Sum.inl (inclusion (S'.cap x))
    rw [S.reparametrizeCapOfLinearIsometry_cap_eq_of_coe_eq A (a b.1) ha (B b.1) hB]
    exact hcap (B b.1 x)
  · funext y
    rw [hK]
    change S.attaching (a b.1 y) = K.attaching b.1 (a b.1 y)
    exact congrFun hattach (a b.1 y)
  · change ∃ q, E.transition.trace.presentation
      (E.transition.trace.capping.coreInclusion (point x)) = Sum.inl q
    refine ⟨inclusion (S.retained x), ?_⟩
    rw [hK]
    exact hretained x
  · intro x
    change E.transition.trace.presentation
        (E.transition.trace.capping.coreInclusion (point x)) =
      Sum.inl (inclusion (S.retained x))
    rw [hK]
    exact hretained x

@[simp] theorem PresentedStaticCap.ofReparametrizedCapping_cap (x : ThreeBall) :
    (PresentedStaticCap.ofReparametrizedCapping E b S K B a hboundary hK A hB inclusion hinc hmetric hattach hcap point hpoint hretained).witness.cap x = S.cap (B b.1 x) := by
  exact S.reparametrizeCapOfLinearIsometry_cap_eq_of_coe_eq A (a b.1)
    (sphere_reparametrization_coe E b B a hboundary A hB) (B b.1) hB x

@[simp] theorem PresentedStaticCap.ofReparametrizedCapping_metric :
    (PresentedStaticCap.ofReparametrizedCapping E b S K B a hboundary hK A hB inclusion hinc hmetric hattach hcap point hpoint hretained).witness.metric = S.metric := rfl

@[simp] theorem PresentedStaticCap.ofReparametrizedCapping_inclusion :
    (PresentedStaticCap.ofReparametrizedCapping E b S K B a hboundary hK A hB inclusion hinc hmetric hattach hcap point hpoint hretained).inclusion = inclusion := rfl

@[simp] theorem PresentedStaticCap.ofReparametrizedCapping_retained_point (x : neckRetainedCollar δ) :
    ((PresentedStaticCap.ofReparametrizedCapping E b S K B a hboundary hK A hB inclusion hinc hmetric hattach hcap point hpoint hretained).retainedPoint x).val = point x := rfl

end MetricCutCapEvent

variable (H : ObservedHistory.{u}) (i : Fin H.eventCount)
  {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {η δ : ℝ} {order : ℕ}
  {neck : NormalizedNeck (H.event i).terminal.metric δ order}
  (b : (H.event i).RetainedBoundaryIndex)
  (S : StaticCapWitness neck fixed D m η)
  (K : Capping (H.event i).transition.trace.tubes (H.event i).capped.Carrier)
  (B : (H.event i).transition.trace.tubes.Boundary → ThreeBall ≃ₜ ThreeBall)
  (a : (H.event i).transition.trace.tubes.Boundary → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
  (hboundary : ∀ c y, B c (sphereToThreeBall y) = sphereToThreeBall (a c y))
  (hK : (H.event i).transition.trace.capping =
    K.reparametrizeCaps B (fun c => (a c).toHomeomorph) hboundary)
  (A : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
  (hB : ∀ x : ThreeBall, (B b.1 x : ThreeSpace) = A x)
  (inclusion : C(S.Output, (H.stage i.succ).Carrier))
  (hinc : IsSmoothEmbedding ThreeModel ThreeModel ∞ inclusion)
  (hmetric : ∀ x V W, S.metric.inner x V W =
    (H.event i).outputMetric.inner (inclusion x)
      (mfderiv ThreeModel ThreeModel inclusion x V)
      (mfderiv ThreeModel ThreeModel inclusion x W))
  (hattach : (S.attaching : Sphere 2 → Sphere 2) = K.attaching b.1)
  (hcap : ∀ x : ThreeBall, (H.event i).transition.trace.presentation (K.cap b.1 x) =
    Sum.inl (inclusion (S.cap x)))
  (point : neckRetainedCollar δ → (H.event i).transition.trace.tubes.core)
  (hpoint : ∀ x (hx : x.1 ∈ neckBuffer δ), (point x).1 = (neck.chart ⟨x.1, hx⟩).1)
  (hretained : ∀ x, (H.event i).transition.trace.presentation (K.coreInclusion (point x)) =
    Sum.inl (inclusion (S.retained x)))


def PresentedStaticCap.ofReparametrizedCapping : PresentedStaticCap H i fixed D m η b :=
  MetricCutCapEvent.PresentedStaticCap.ofReparametrizedCapping (H.event i) b S K B a hboundary hK A hB inclusion hinc hmetric hattach hcap point hpoint hretained

@[simp] theorem PresentedStaticCap.ofReparametrizedCapping_cap (x : ThreeBall) :
    (PresentedStaticCap.ofReparametrizedCapping H i b S K B a hboundary hK A hB inclusion hinc hmetric hattach hcap point hpoint hretained).witness.cap x = S.cap (B b.1 x) := by
  exact MetricCutCapEvent.PresentedStaticCap.ofReparametrizedCapping_cap (H.event i) b S K B a hboundary hK A hB inclusion hinc hmetric hattach hcap point hpoint hretained x

@[simp] theorem PresentedStaticCap.ofReparametrizedCapping_metric :
    (PresentedStaticCap.ofReparametrizedCapping H i b S K B a hboundary hK A hB inclusion hinc hmetric hattach hcap point hpoint hretained).witness.metric = S.metric := rfl

@[simp] theorem PresentedStaticCap.ofReparametrizedCapping_inclusion :
    (PresentedStaticCap.ofReparametrizedCapping H i b S K B a hboundary hK A hB inclusion hinc hmetric hattach hcap point hpoint hretained).inclusion = inclusion := rfl

@[simp] theorem PresentedStaticCap.ofReparametrizedCapping_retained_point (x : neckRetainedCollar δ) :
    ((PresentedStaticCap.ofReparametrizedCapping H i b S K B a hboundary hK A hB inclusion hinc hmetric hattach hcap point hpoint hretained).retainedPoint x).val = point x := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
