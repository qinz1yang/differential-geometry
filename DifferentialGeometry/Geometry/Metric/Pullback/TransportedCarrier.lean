import DifferentialGeometry.Topology.Manifold.TransportedCarrier
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteRegularityProof
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric

/-!
# The unchanged finite metric in the transported carrier (kernel of LFR47)

Frozen blueprint master207A, lemma `lem:collapse-soul-flow-smooth-carrier` (LFR47, lines
28975–29034). After the smooth structure of `X` is transported to the points of `N` along a `C^r`
diffeomorphism `F : X ≃ₘ^r⟮IX, I⟯ N` (`DifferentialGeometry.Topology.TransportedCarrier`), the
UNCHANGED `C^n` metric `g` of `N` is a metric of class `C^m` on the new carrier for every `m ≤ n`
with `m + 1 ≤ r` ("the tensor pullback formula ... This is the derivative loss: metric components
contain first derivatives of `F`"). It is the pullback by the identity of the points, so its inner
products are those of `g` read through the differential of the identity transition, and its
sectional curvature is the sectional curvature of `g` on the corresponding planes; in particular
`sec ≥ 0` survives. Distances and completeness are unchanged (`TransportedCarrier.dist_eq`,
`TransportedCarrier.instCompleteSpace`).

The metric is `finitePullbackMetric g (TransportedCarrier.identity F) hmn hmr`
(`Geometry/Metric/Pullback/FiniteRegularityProof.lean`); the curvature identity is
`sectionalCurvature_eq_of_pullback` (`Geometry/Curvature/Riemann/FiniteMetric.lean`), which needs
the same model vector space on both sides and boundaryless models.
-/

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Topology

section Metric

variable {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- **LFR47, metric.** The unchanged `C^n` metric `g` of `N`, read in the carrier transported
along the `C^r` diffeomorphism `F`: a `C^m` metric for `m ≤ n`, `m + 1 ≤ r`. -/
def TransportedCarrier.metric {r : ℕ∞} (F : X ≃ₘ^r⟮IX, I⟯ N) {m n : WithTop ℕ∞}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _)) (hmn : m ≤ n)
    (hmr : m + 1 ≤ r) :
    ContMDiffRiemannianMetric IX m EX
      (TangentSpace IX : TransportedCarrier F.toHomeomorph → Type _) :=
  finitePullbackMetric g (TransportedCarrier.identity F) hmn hmr

omit [FiniteDimensional ℝ E] in
/-- The inner products of the transported metric are those of `g`, through the differential of
the identity transition. -/
@[simp] theorem TransportedCarrier.metric_inner {r : ℕ∞} (F : X ≃ₘ^r⟮IX, I⟯ N)
    {m n : WithTop ℕ∞} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _))
    (hmn : m ≤ n) (hmr : m + 1 ≤ r) (y : TransportedCarrier F.toHomeomorph)
    (v w : TangentSpace IX y) :
    (TransportedCarrier.metric F g hmn hmr).inner y v w =
      g.inner y.point (mfderiv IX I (TransportedCarrier.identity F) y v)
        (mfderiv IX I (TransportedCarrier.identity F) y w) :=
  rfl

end Metric

section Sectional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ E HX} [IX.Boundaryless]
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- The identity transition, regarded as a `C³` diffeomorphism (`3 ≤ r`). -/
def TransportedCarrier.identityThree {r : ℕ∞} (F : X ≃ₘ^r⟮IX, I⟯ N) (hr : 3 ≤ r) :
    TransportedCarrier F.toHomeomorph ≃ₘ^3⟮IX, I⟯ N where
  toEquiv := (TransportedCarrier.identity F).toEquiv
  contMDiff_toFun := (TransportedCarrier.identity F).contMDiff.of_le (WithTop.coe_le_coe.mpr hr)
  contMDiff_invFun :=
    (TransportedCarrier.identity F).symm.contMDiff.of_le (WithTop.coe_le_coe.mpr hr)

/-- **LFR47, curvature.** The sectional curvature of the transported metric is the sectional
curvature of `g` on the corresponding plane (`3 ≤ r`, both metrics of order at least two). -/
theorem TransportedCarrier.metric_sectionalCurvature {r : ℕ∞} (F : X ≃ₘ^r⟮IX, I⟯ N)
    {m n : WithTop ℕ∞} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _))
    (hmn : m ≤ n) (hmr : m + 1 ≤ r) (hr : 3 ≤ r) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (y : TransportedCarrier F.toHomeomorph) (v w : TangentSpace IX y) :
    (TransportedCarrier.metric F g hmn hmr).sectionalCurvature y v w =
      g.sectionalCurvature y.point (mfderiv IX I (TransportedCarrier.identity F) y v)
        (mfderiv IX I (TransportedCarrier.identity F) y w) :=
  ContMDiffRiemannianMetric.sectionalCurvature_eq_of_pullback
    (TransportedCarrier.metric F g hmn hmr) g hm hn
    (TransportedCarrier.identityThree F hr) (fun _ _ _ => rfl) y v w

/-- **LFR47, `sec ≥ 0` survives** the carrier change. -/
theorem TransportedCarrier.metric_sectionalCurvature_nonneg {r : ℕ∞} (F : X ≃ₘ^r⟮IX, I⟯ N)
    {m n : WithTop ℕ∞} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _))
    (hmn : m ≤ n) (hmr : m + 1 ≤ r) (hr : 3 ≤ r) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hsec : ∀ (x : N) (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w)
    (y : TransportedCarrier F.toHomeomorph) (v w : TangentSpace IX y) :
    0 ≤ (TransportedCarrier.metric F g hmn hmr).sectionalCurvature y v w := by
  rw [TransportedCarrier.metric_sectionalCurvature F g hmn hmr hr hm hn]
  exact hsec _ _ _

end Sectional

end DifferentialGeometry.Geometry
