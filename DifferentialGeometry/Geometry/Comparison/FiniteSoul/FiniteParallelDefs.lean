import DifferentialGeometry.Geometry.Geodesic.Flow.FiniteMetric

/-!
# Finite-order parallel fields along curves: the chart ODE (lane CMS3-PT, S3-PT, definitions)

The frozen definitions `chartCoeffFinite` and `IsParallelAlongFinite` of
`build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean` (§1), verbatim bodies; section variables are
minimal. Design: `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §0.2.

Conventions (shared with lane CMS3-SHIFT). In the extended chart at `q`, the fibre coordinate of `V τ` is
`(extChartAt I.tangent ⟨q, 0⟩ ⟨c τ, V τ⟩).2`, the coefficients are `b = chartCoeffFinite g q`, the
Christoffel operator is `Γ y = raisedKoszulOp (b y) (fderiv ℝ b y)` with
`b (Γ u v) w = ½ (D u v w + D v u w − D w u v)` (`D a u v = (∂_a b) u v`), and a field is parallel iff
`V' = −Γ (c', V)` (first slot = velocity of the curve).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Coefficients of `g` in the extended chart at `q` (the `b` of `hasDerivAt_geodesicFlow_chart`). -/
def chartCoeffFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (q : M) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (g.inner ((extChartAt I q).symm x) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (E := E) (F := E) (E' := E)
    (F' := E) (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm x : E →L[ℝ] E)
    (mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm x : E →L[ℝ] E)

local instance continuousDualEquivPTd : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroupD3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpaceD3 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **S3-PT, parallel fields (chart form).** In every chart containing `c t`, the chart representative
of `V` solves `V' = −Γ(c', V)`, `Γ = raisedKoszulOp` of the chart coefficients (the bilinear map whose
diagonal is the geodesic spray of `hasDerivAt_geodesicFlow_chart`). -/
def IsParallelAlongFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (c : ℝ → M) (V : ℝ → E)
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ q : M, c t ∈ (chartAt H q).source →
    HasDerivWithinAt
      (fun τ => (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (⟨c τ, V τ⟩ : TangentBundle I M)).2)
      (-(DifferentialGeometry.MetricKoszul.raisedKoszulOp (chartCoeffFinite g q (extChartAt I q (c t)))
          (fderiv ℝ (chartCoeffFinite g q) (extChartAt I q (c t)))
          (derivWithin (fun τ => extChartAt I q (c τ)) s t)
          (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M) (⟨c t, V t⟩ : TangentBundle I M)).2))
      s t

end DifferentialGeometry.Geometry.FiniteSoul
