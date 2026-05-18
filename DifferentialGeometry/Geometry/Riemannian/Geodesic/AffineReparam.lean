import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.ConstantSpeed
import DifferentialGeometry.Geometry.Riemannian.Geodesic.VelocityChart
import DifferentialGeometry.Geometry.Riemannian.Curve.CovDerivAlong
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

set_option linter.unusedSectionVars false

/-!
# Affine reparametrisation of geodesics

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, the geodesic property
is invariant under affine time reparametrisation: if `γ : ℝ → M` is a
geodesic, so is `s ↦ γ (a · s + b)` for every `a b : ℝ`.

## Main result

* `IsGeodesic.comp_affine`: affine reparametrisation preserves the
  global geodesic property.

## Proof strategy

The geodesic predicate `IsGeodesic` packages a chart basepoint `α : M`
together with a lift `f : ℝ → TangentBundle I M` projecting to `γ` and
integrating the chart-fixed geodesic vector field on `TM`
`V := geodesicVectorFieldChart g α`. For affine reparametrisation, two
ingredients enter:

1. **Time reparametrisation.** Mathlib's `IsMIntegralCurve.comp_add`
   and `IsMIntegralCurve.comp_mul` show that `f₁ := f ∘ (·*a + b)` is
   an integral curve of `a • V`.

2. **Fibre scaling.** The new lift is built by also scaling the fibre of
   `f₁` by `a`: `f̃ s := ⟨(f₁ s).proj, a • (f₁ s).snd⟩`. The bilinearity
   of the Christoffel contraction
   (`chartChristoffelContraction_smul_smul`) ensures that
   `a • V (f₁ s)` and `V (f̃ s)` are related by the bundle scaling
   endomorphism's manifold derivative — exactly the chain-rule
   relation needed to turn `f₁` (an integral curve of `a • V`) into
   `f̃` (an integral curve of `V`).

The degenerate case `a = 0` reduces to the constant curve, handled by
`isGeodesic_const`.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Curve

/-! ## The scaled lift

For `a : ℝ` and a path `f : ℝ → TangentBundle I M`, the "fibre-scaled
lift" keeps the base point of `f` and multiplies the fibre vector by
`a`. -/

/-- Fibre-scaling of a tangent-bundle path by a scalar `a : ℝ`. -/
def scaleFiberPath (a : ℝ) (f : ℝ → TangentBundle I M) :
    ℝ → TangentBundle I M :=
  fun s => ⟨(f s).proj, a • (f s).snd⟩

@[simp] lemma scaleFiberPath_proj (a : ℝ) (f : ℝ → TangentBundle I M) (s : ℝ) :
    (scaleFiberPath (I := I) a f s).proj = (f s).proj := rfl

@[simp] lemma scaleFiberPath_snd (a : ℝ) (f : ℝ → TangentBundle I M) (s : ℝ) :
    (scaleFiberPath (I := I) a f s).snd = a • (f s).snd := rfl

/-- Affine reparametrisation lift: shift the time argument to `a·s + b`,
then scale the fibre by `a`. -/
def affineReparamLift (a b : ℝ) (f : ℝ → TangentBundle I M) :
    ℝ → TangentBundle I M :=
  fun s => scaleFiberPath (I := I) a f (a * s + b)

@[simp] lemma affineReparamLift_proj (a b : ℝ) (f : ℝ → TangentBundle I M)
    (s : ℝ) :
    (affineReparamLift (I := I) a b f s).proj = (f (a * s + b)).proj := rfl

@[simp] lemma affineReparamLift_snd (a b : ℝ) (f : ℝ → TangentBundle I M)
    (s : ℝ) :
    (affineReparamLift (I := I) a b f s).snd = a • (f (a * s + b)).snd := rfl

/-! ## Bundle scaling endomorphism

For `a : ℝ`, the map `fibreScale a : TangentBundle I M → TangentBundle I M`
sends `⟨b, v⟩` to `⟨b, a • v⟩`. -/

/-- The fibre-scaling bundle endomorphism. -/
def fibreScale (a : ℝ) : TangentBundle I M → TangentBundle I M :=
  fun p => ⟨p.proj, a • p.snd⟩

@[simp] lemma fibreScale_proj (a : ℝ) (p : TangentBundle I M) :
    (fibreScale (I := I) a p).proj = p.proj := rfl

@[simp] lemma fibreScale_snd (a : ℝ) (p : TangentBundle I M) :
    (fibreScale (I := I) a p).snd = a • p.snd := rfl

/-- The scaled lift equals `fibreScale a` applied to the time-reparametrised
original lift. -/
lemma affineReparamLift_eq_fibreScale_comp
    (a b : ℝ) (f : ℝ → TangentBundle I M) :
    affineReparamLift (I := I) a b f =
      (fibreScale (I := I) a) ∘ (fun s : ℝ => f (a * s + b)) := by
  funext s
  rfl

/-! ## Time-reparametrisation of the lift

Mathlib's `IsMIntegralCurve.comp_add` and `IsMIntegralCurve.comp_mul`
suffice to handle the time argument. The vector field is on
`TangentBundle I M`, viewed as a manifold modelled on `I.tangent`.
Combining the two transforms yields an integral curve of the *scaled*
vector field `a • V`. -/

/-- Time reparametrisation of the lift: if `f` is a global integral
curve of `V`, then `s ↦ f (a · s + b)` is a global integral curve of
`a • V`. -/
lemma isMIntegralCurve_comp_affine_time
    {V : (p : TangentBundle I M) → TangentSpace I.tangent p}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurve f V) (a b : ℝ) :
    IsMIntegralCurve (fun s : ℝ => f (a * s + b)) (a • V) := by
  have h1 : IsMIntegralCurve (f ∘ (· + b)) V := hf.comp_add b
  have h2 : IsMIntegralCurve ((f ∘ (· + b)) ∘ (· * a)) (a • V) :=
    h1.comp_mul a
  have hfun : ((f ∘ (· + b)) ∘ (· * a)) = (fun s : ℝ => f (a * s + b)) := by
    funext s
    change f (s * a + b) = f (a * s + b)
    rw [mul_comm]
  rw [hfun] at h2
  exact h2

/-! ## Chart-fibre coordinate under fibre scaling

On the chart source at `α`, scaling the fibre of a bundle point by `a`
scales its `chartFiberCoord α` by `a`. -/

/-- The chart-fibre coordinate of `fibreScale a p`, on the chart source. -/
lemma chartFiberCoord_fibreScale_of_mem
    (α : M) (a : ℝ) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α (fibreScale (I := I) a p) =
      a • chartFiberCoord (I := I) α p := by
  classical
  have hsmul := chartFiberCoord_smul_of_mem (I := I) α a (p.snd) hp
  -- `hsmul : chartFiberCoord α ⟨p.proj, a • p.snd⟩ = a • chartFiberCoord α ⟨p.proj, p.snd⟩`
  -- The bundle elements `⟨p.proj, a • p.snd⟩ = fibreScale a p` and `⟨p.proj, p.snd⟩ = p`
  -- are definitional equalities.
  exact hsmul

/-! ## Smoothness of `fibreScale`

`fibreScale a` is smooth: the projection is the identity (smooth) on the
base, and the fibre coordinate scales linearly (smooth) in the
trivialisation. -/

section FibreScaleSmoothness

/-- `fibreScale a` is `C^∞` everywhere on `TangentBundle I M`. -/
lemma fibreScale_contMDiff (a : ℝ) :
    ContMDiff I.tangent I.tangent ∞ (fibreScale (I := I) (M := M) a) := by
  classical
  intro p₀
  -- The trivialisation at `p₀.proj` has `p₀` in its source.
  set e := trivializationAt E (TangentSpace I) p₀.proj with he_def
  have hp₀_base : p₀.proj ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p₀.proj
  -- Use `Bundle.contMDiffAt_totalSpace` to reduce.
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · -- Projection: `(fibreScale a p).proj = p.proj`, so the projection of
    -- `fibreScale a ∘ id` is just `proj`.
    have hproj : ContMDiffAt I.tangent I ∞
        (Bundle.TotalSpace.proj : TangentBundle I M → M) p₀ :=
      (Bundle.contMDiff_proj (TangentSpace I) (n := (∞ : WithTop ℕ∞))).contMDiffAt
    exact hproj
  · -- Fibre coord part: `(trivAt p₀.proj (fibreScale a p)).snd =
    -- a • (trivAt p₀.proj p).snd` on `e.source`. Since the identity is smooth
    -- in `p`, the fibre coord part of `id p = p` is smooth — and multiplying
    -- by `a` is also smooth.
    have h_id_smooth : ContMDiffAt I.tangent I.tangent ∞
        (id : TangentBundle I M → TangentBundle I M) p₀ := contMDiffAt_id
    rw [Bundle.contMDiffAt_totalSpace] at h_id_smooth
    -- `h_id_smooth.2 : ContMDiffAt I.tangent 𝓘(ℝ, E) ∞ (fun p => (e p).snd) p₀`.
    have h_snd_smooth : ContMDiffAt I.tangent 𝓘(ℝ, E) ∞
        (fun p : TangentBundle I M => (e p).snd) p₀ := h_id_smooth.2
    -- Multiplication by `a` is a smooth CLM.
    have h_smul_clm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        ((a • ContinuousLinearMap.id ℝ E : E →L[ℝ] E)) :=
      (a • ContinuousLinearMap.id ℝ E : E →L[ℝ] E).contMDiff
    have h_smul_smooth : ContMDiffAt I.tangent 𝓘(ℝ, E) ∞
        (fun p : TangentBundle I M => a • (e p).snd) p₀ := by
      have : (fun p : TangentBundle I M => a • (e p).snd) =
          (fun v : E => (a • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) v) ∘
            (fun p : TangentBundle I M => (e p).snd) := by
        funext p
        simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      rw [this]
      exact h_smul_clm.contMDiffAt.comp p₀ h_snd_smooth
    -- We want: `ContMDiffAt _ _ _ (fun p => (e (fibreScale a p)).snd) p₀`.
    -- On `e.source`, `(e (fibreScale a p)).snd = a • (e p).snd`.
    have h_source_nhds : e.source ∈ nhds p₀ :=
      (e.open_source.mem_nhds (by
        rw [Trivialization.source_eq]; exact hp₀_base))
    have h_eq : ∀ᶠ p in nhds p₀,
        (e (fibreScale (I := I) a p)).snd = a • (e p).snd := by
      filter_upwards [h_source_nhds] with p hp
      have hp_base : p.proj ∈ e.baseSet := by
        rw [Trivialization.source_eq] at hp; exact hp
      -- `e ⟨b, v⟩ = (b, e.linearMapAt ℝ b v)` for `b ∈ e.baseSet`.
      have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) hp_base
      have h1 : (e (⟨p.proj, p.snd⟩ : TangentBundle I M)).snd =
          (e.linearMapAt ℝ p.proj) p.snd := by
        rw [hcoe]
      have h2 : (e (fibreScale (I := I) a p)).snd =
          (e.linearMapAt ℝ p.proj) (a • p.snd) := by
        change (e (⟨p.proj, a • p.snd⟩ : TangentBundle I M)).snd = _
        rw [hcoe]
      rw [h2, LinearMap.map_smul]
      have h3 : (e p).snd = (e.linearMapAt ℝ p.proj) p.snd := h1
      rw [h3]
    -- Now use `congr_of_eventuallyEq` to conclude.
    exact h_smul_smooth.congr_of_eventuallyEq h_eq

/-- `fibreScale a` is `MDifferentiable` everywhere. -/
lemma fibreScale_mdifferentiable (a : ℝ) :
    MDifferentiable I.tangent I.tangent (fibreScale (I := I) (M := M) a) :=
  (fibreScale_contMDiff (I := I) (M := M) a).mdifferentiable (by decide)

lemma fibreScale_mdifferentiableAt (a : ℝ) (p : TangentBundle I M) :
    MDifferentiableAt I.tangent I.tangent (fibreScale (I := I) a) p :=
  fibreScale_mdifferentiable (I := I) (M := M) a p

end FibreScaleSmoothness

/-! ## Off-chart vanishing of `mfderiv (fibreScale a)` on `V`

When `p.proj ∉ chart source α`, both `V p` and `V (fibreScale a p)`
vanish, so the chain-rule identity is trivial. -/

section MfDerivFibreScaleOff

variable [I.Boundaryless] [CompleteSpace E]

/-- **Off-chart manifold-derivative identity.** When `p.proj ∉ chart
source α`, both sides of the chain-rule relation are zero. -/
lemma mfderiv_fibreScale_geodesicVectorFieldChart_off_chart
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p.proj ∉ (chartAt H α).source) :
    (mfderiv I.tangent I.tangent (fibreScale (I := I) a) p)
        (a • geodesicVectorFieldChart (I := I) g α p) =
      geodesicVectorFieldChart (I := I) g α (fibreScale (I := I) a p) := by
  have hVp : geodesicVectorFieldChart (I := I) g α p = 0 :=
    geodesicVectorFieldChart_eq_zero_of_proj_notMem (I := I) g α hp
  have hp' : (fibreScale (I := I) a p).proj ∉ (chartAt H α).source := hp
  have hVfp : geodesicVectorFieldChart (I := I) g α
      (fibreScale (I := I) a p) = 0 :=
    geodesicVectorFieldChart_eq_zero_of_proj_notMem (I := I) g α hp'
  rw [hVp, smul_zero, hVfp]
  exact map_zero _

end MfDerivFibreScaleOff

/-! ## On-chart manifold-derivative identity

On the chart source at `α`, we need
`mfderiv (fibreScale a) p (a • V p) = V (fibreScale a p)`.

The key Mathlib identity behind this is the chart-pushed form of the
manifold derivative through the trivialisation of `T(TM)` at `⟨α, 0⟩`.
We extract the relevant piece via a HasMFDerivAt witness for `fibreScale a`
at `p` that simultaneously gives both the mfderiv equality and the
chain-rule identity. -/

section MfDerivFibreScaleOn

variable [I.Boundaryless] [CompleteSpace E]

/-- **Chart-pushed form of `fibreScale a` on the chart source.** In the
trivialisation of `TM` at `α`, `fibreScale a` is exactly the linear map
`(b, v) ↦ (b, a • v)`. We record the identity at the level of the
extended chart at `⟨α, 0⟩` of `T(TM)`. -/
lemma extChartAt_tangent_fibreScale_apply
    (α : M) (a : ℝ) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        (fibreScale (I := I) a p) =
      (extChartAt I α p.proj, a • chartFiberCoord (I := I) α p) := by
  classical
  -- By `FiberBundle.extChartAt`, the extended chart factors as
  -- `(extChartAt I α).prod (PartialEquiv.refl E) ∘ trivializationAt`.
  -- Apply to `fibreScale a p = ⟨p.proj, a • p.snd⟩`.
  have hfb : extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
      (fibreScale (I := I) a p) =
      ((extChartAt I α).prod (PartialEquiv.refl E))
        ((trivializationAt E (TangentSpace I) α).toPartialEquiv
          (fibreScale (I := I) a p)) := by
    have := FiberBundle.extChartAt (IB := I) (F := E) (E := TangentSpace I)
      (x := (⟨α, (0 : E)⟩ : TangentBundle I M))
    change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        (fibreScale (I := I) a p) = _
    rw [this]
    rfl
  rw [hfb]
  -- The prod-chart applied to `(triv (fibreScale a p))`:
  -- first coord: `extChartAt I α (triv (fibreScale a p)).1 = extChartAt I α p.proj`
  -- second coord: `(PartialEquiv.refl E) (triv (fibreScale a p)).2 = chartFiberCoord α (fibreScale a p) = a • chartFiberCoord α p`.
  refine Prod.ext ?_ ?_
  · change extChartAt I α ((trivializationAt E (TangentSpace I) α)
        (fibreScale (I := I) a p)).1 = _
    rw [TangentBundle.trivializationAt_fst (I := I) α]
    rfl
  · change ((trivializationAt E (TangentSpace I) α)
        (fibreScale (I := I) a p)).2 = _
    have hcoord : chartFiberCoord (I := I) α (fibreScale (I := I) a p) =
        a • chartFiberCoord (I := I) α p :=
      chartFiberCoord_fibreScale_of_mem (I := I) α a hp
    -- `chartFiberCoord α q = (triv α q).2` by definition.
    change chartFiberCoord (I := I) α (fibreScale (I := I) a p) = _
    rw [hcoord]

/-- **Chart-pushed form of `fibreScale a`.** Composed with the extended
chart at `⟨α, 0⟩`, the bundle scaling agrees with the chart map
`(y, c) ↦ (y, a • c)` (on `E × E`). -/
lemma extChartAt_tangent_fibreScale_apply_eq
    (α : M) (a : ℝ) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        (fibreScale (I := I) a p) =
      (((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p).1,
        a • (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p).2)) := by
  classical
  -- LHS: by `extChartAt_tangent_fibreScale_apply` =
  -- `(extChartAt I α p.proj, a • chartFiberCoord α p)`.
  rw [extChartAt_tangent_fibreScale_apply (I := I) α a hp]
  -- The first coord of `extChartAt I.tangent ⟨α,0⟩ p` is `extChartAt I α p.proj` by
  -- `fst_extChartAt_tangent_zeroSection_apply`.
  have hfst := fst_extChartAt_tangent_zeroSection_apply (I := I) α p
  -- The second coord of `extChartAt I.tangent ⟨α,0⟩ p` is `chartFiberCoord α p`.
  have hsnd : (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p).2 =
      chartFiberCoord (I := I) α p := by
    -- Same decomposition as above for `p`.
    have hfb : extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p =
        ((extChartAt I α).prod (PartialEquiv.refl E))
          ((trivializationAt E (TangentSpace I) α).toPartialEquiv p) := by
      have := FiberBundle.extChartAt (IB := I) (F := E) (E := TangentSpace I)
        (x := (⟨α, (0 : E)⟩ : TangentBundle I M))
      change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p = _
      rw [this]
      rfl
    rw [hfb]; rfl
  rw [hfst, hsnd]

/-- **Chart-fibre bilinearity identity.** Applying the chart-conjugated
linear map `(y, v) ↦ (y, a • v)` to `a • gvfChartFiber g α p` gives
`gvfChartFiber g α (fibreScale a p)`. This is the algebraic heart of
the affine reparametrisation identity, packaging
`chartChristoffelContraction_smul_smul`. -/
lemma chi_apply_smul_gvfChartFiber
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    ((a • (geodesicVectorFieldChartFiber (I := I) g α p)).1,
        a • (a • (geodesicVectorFieldChartFiber (I := I) g α p)).2) =
      geodesicVectorFieldChartFiber (I := I) g α (fibreScale (I := I) a p) := by
  classical
  -- LHS: `(a • c, a • (-a Γ(c,c)(y))) = (a c, -a² Γ(c,c)(y))`.
  -- RHS: `(chartFiberCoord α (fibreScale a p), -Γ(...) (...))`
  --    = `(a c, -Γ(a c, a c)(y))` = `(a c, -a² Γ(c, c)(y))` by bilinearity.
  refine Prod.ext ?_ ?_
  · -- First coord: `(a • (c, -Γ(c,c)(y))).1 = a • c = chartFiberCoord α (fibreScale a p)`.
    change a • (geodesicVectorFieldChartFiber (I := I) g α p).1 =
      (geodesicVectorFieldChartFiber (I := I) g α (fibreScale (I := I) a p)).1
    -- `(gvfChartFiber g α p).1 = chartFiberCoord α p` by def.
    -- `(gvfChartFiber g α q).1 = chartFiberCoord α q` by def, and equals `a • chartFiberCoord α p`.
    change a • chartFiberCoord (I := I) α p =
      chartFiberCoord (I := I) α (fibreScale (I := I) a p)
    rw [chartFiberCoord_fibreScale_of_mem (I := I) α a hp]
  · -- Second coord: `a • (a • (-Γ(c,c)(y))) = -Γ(a c, a c)(y)`.
    change a • (a • (geodesicVectorFieldChartFiber (I := I) g α p).2) =
      (geodesicVectorFieldChartFiber (I := I) g α (fibreScale (I := I) a p)).2
    -- `(gvfChartFiber g α p).2 = -Γ(c, c)(y)`. So LHS = `a • (a • (-Γ(c,c)(y))) = -(a*a) • Γ(c,c)(y)`.
    -- `(gvfChartFiber g α q).2 = -Γ(c_q, c_q)(y_q) = -Γ(a c, a c)(y) = -(a*a) • Γ(c,c)(y)` by bilinearity.
    have hcq : chartFiberCoord (I := I) α (fibreScale (I := I) a p) =
        a • chartFiberCoord (I := I) α p :=
      chartFiberCoord_fibreScale_of_mem (I := I) α a hp
    have hyq : extChartAt I α (fibreScale (I := I) a p).proj =
        extChartAt I α p.proj := rfl
    change a • (a • (- chartChristoffelContraction (I := I) g α
        (chartFiberCoord (I := I) α p)
        (chartFiberCoord (I := I) α p)
        (extChartAt I α p.proj))) =
      - chartChristoffelContraction (I := I) g α
        (chartFiberCoord (I := I) α (fibreScale (I := I) a p))
        (chartFiberCoord (I := I) α (fibreScale (I := I) a p))
        (extChartAt I α (fibreScale (I := I) a p).proj)
    rw [hcq, hyq]
    rw [chartChristoffelContraction_smul_smul (I := I) g α a
      (chartFiberCoord (I := I) α p) (extChartAt I α p.proj)]
    -- After rewrite, both sides are `-((a*a) • Γ(c, c)(y))` (modulo smul_neg/smul_smul).
    simp [smul_neg, smul_smul]

/-- The chart-pushed CLM `χ : E × E →L[ℝ] E × E` defined by `(y, v) ↦ (y, a • v)`. -/
def chartScaleCLM (a : ℝ) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ E)

@[simp] lemma chartScaleCLM_apply (a : ℝ) (q : E × E) :
    chartScaleCLM (E := E) a q = (q.1, a • q.2) := by
  rcases q with ⟨y, v⟩
  simp [chartScaleCLM]

/-- **The on-chart manifold-derivative identity for `fibreScale a` on `V`.**
This is the chain-rule identity needed to verify the integral curve
property for the scaled lift.

The proof uses chart conjugation. We show: applying the chart-pushed
derivative `mfderiv Φ q` to both sides (where `Φ := extChartAt I.tangent ⟨α, 0⟩`)
yields the same chart-fibre data on both sides, namely
`gvfChartFiber g α q`. Since `mfderiv Φ q` is invertible at chart-source
points (Mathlib `isInvertible_mfderiv_extChartAt`), the identity follows. -/
lemma mfderiv_fibreScale_geodesicVectorFieldChart_on_chart
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    (mfderiv I.tangent I.tangent (fibreScale (I := I) a) p)
        (a • geodesicVectorFieldChart (I := I) g α p) =
      geodesicVectorFieldChart (I := I) g α (fibreScale (I := I) a p) := by
  classical
  set V : (p : TangentBundle I M) → TangentSpace I.tangent p :=
    geodesicVectorFieldChart (I := I) g α with hV_def
  set q := fibreScale (I := I) a p with hq_def
  -- The chart at `⟨α, 0⟩` for `T(TM)`.
  set Φ : TangentBundle I M → E × E :=
    fun p => extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p with hΦ_def
  -- (1) Both `p` and `q` have proj in chart source α.
  have hq_proj : q.proj ∈ (chartAt H α).source := hp
  -- (2) Both `p` and `q` are in the source of the tangent-bundle chart at `⟨α, 0⟩`.
  have hp_src : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) p
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hp
  have hq_src : q ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) q
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hq_proj
  have hp_ext_src : p ∈ (extChartAt I.tangent
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I.tangent)]
    exact hp_src
  -- (3) `mfderiv Φ p` is invertible (chart at p in chart source).
  have hΦp_inv : (mfderiv I.tangent 𝓘(ℝ, E × E) Φ p).IsInvertible :=
    isInvertible_mfderiv_extChartAt (I := I.tangent) (x := (⟨α, (0 : E)⟩ : TangentBundle I M))
      (y := p) hp_ext_src
  -- (4) `Φ ∘ fibreScale a` agrees with `chartScaleCLM a ∘ Φ` on the chart source.
  have hΦ_chartSrc_mem : ∀ p' : TangentBundle I M,
      p'.proj ∈ (chartAt H α).source →
      Φ (fibreScale (I := I) a p') = chartScaleCLM (E := E) a (Φ p') := by
    intro p' hp'
    change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        (fibreScale (I := I) a p') =
      chartScaleCLM (E := E) a (extChartAt I.tangent
        (⟨α, (0 : E)⟩ : TangentBundle I M) p')
    rw [extChartAt_tangent_fibreScale_apply_eq (I := I) α a hp']
    simp [chartScaleCLM_apply]
  have h_eventuallyEq :
      (fun p' : TangentBundle I M => Φ (fibreScale (I := I) a p')) =ᶠ[𝓝 p]
        (fun p' : TangentBundle I M => chartScaleCLM (E := E) a (Φ p')) := by
    -- chart source at α is open, and `p.proj ∈ chart source α`. So `geodesicChartDomain α`
    -- is a nbhd of `p`.
    have hopen : IsOpen (geodesicChartDomain (I := I) (M := M) α) :=
      geodesicChartDomain_isOpen (I := I) (M := M) α
    have hp_mem : p ∈ geodesicChartDomain (I := I) (M := M) α := hp
    have hnhd : geodesicChartDomain (I := I) (M := M) α ∈ 𝓝 p :=
      hopen.mem_nhds hp_mem
    filter_upwards [hnhd] with p' hp'
    exact hΦ_chartSrc_mem p' hp'
  -- (5) mfderiv of `chartScaleCLM a ∘ Φ` at `p` is `chartScaleCLM a ∘L mfderiv Φ p`.
  -- Chain rule + CLM mfderiv.
  have h_chi_mdiff : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E × E)
      (chartScaleCLM (E := E) a) (Φ p) := (chartScaleCLM (E := E) a).mdifferentiableAt
  have hΦ_mdiff : MDifferentiableAt I.tangent 𝓘(ℝ, E × E) Φ p :=
    mdifferentiableAt_extChartAt (I := I.tangent) hp_src
  have hmfd_chi_Phi :
      mfderiv I.tangent 𝓘(ℝ, E × E)
        (fun p' : TangentBundle I M => chartScaleCLM (E := E) a (Φ p')) p =
      (chartScaleCLM (E := E) a).comp
        (mfderiv I.tangent 𝓘(ℝ, E × E) Φ p) := by
    have h_chi_mfderiv :
        mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) (chartScaleCLM (E := E) a) (Φ p) =
        chartScaleCLM (E := E) a := by
      have h : HasFDerivAt (chartScaleCLM (E := E) a)
          (chartScaleCLM (E := E) a) (Φ p) :=
        (chartScaleCLM (E := E) a).hasFDerivAt
      exact h.hasMFDerivAt.mfderiv
    have h_comp := mfderiv_comp (I := I.tangent) (I' := 𝓘(ℝ, E × E)) (I'' := 𝓘(ℝ, E × E))
      (f := Φ) (g := chartScaleCLM (E := E) a) (x := p) h_chi_mdiff hΦ_mdiff
    -- `h_comp : mfderiv I.tangent 𝓘(ℝ, E × E) (chartScaleCLM a ∘ Φ) p =
    --   (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) (chartScaleCLM a) (Φ p)).comp (mfderiv I.tangent 𝓘(ℝ, E × E) Φ p)`
    -- The target `(fun p' => chartScaleCLM a (Φ p'))` is definitionally `chartScaleCLM a ∘ Φ`.
    change mfderiv I.tangent 𝓘(ℝ, E × E)
      ((chartScaleCLM (E := E) a : E × E → E × E) ∘ Φ) p = _
    rw [h_comp, h_chi_mfderiv]
    rfl
  -- (6) mfderiv of `Φ ∘ fibreScale a` at `p` equals mfderiv of `chartScaleCLM a ∘ Φ` at `p`.
  have hmfd_Phi_fibreScale :
      mfderiv I.tangent 𝓘(ℝ, E × E)
        (fun p' : TangentBundle I M => Φ (fibreScale (I := I) a p')) p =
      mfderiv I.tangent 𝓘(ℝ, E × E)
        (fun p' : TangentBundle I M => chartScaleCLM (E := E) a (Φ p')) p :=
    Filter.EventuallyEq.mfderiv_eq h_eventuallyEq
  -- (7) mfderiv of `Φ ∘ fibreScale a` at `p` via chain rule on `fibreScale a` then `Φ`.
  have hΦ_q_mdiff : MDifferentiableAt I.tangent 𝓘(ℝ, E × E) Φ q :=
    mdifferentiableAt_extChartAt (I := I.tangent) hq_src
  have h_fibreScale_mdiff : MDifferentiableAt I.tangent I.tangent
      (fibreScale (I := I) a) p :=
    fibreScale_mdifferentiableAt (I := I) (M := M) a p
  have hmfd_comp_chain :
      mfderiv I.tangent 𝓘(ℝ, E × E)
        (fun p' : TangentBundle I M => Φ (fibreScale (I := I) a p')) p =
      (mfderiv I.tangent 𝓘(ℝ, E × E) Φ q).comp
        (mfderiv I.tangent I.tangent (fibreScale (I := I) a) p) := by
    -- `Φ ∘ fibreScale a` written as composition: Φ then fibreScale a.
    -- The chain rule: `mfderiv (g ∘ f) x = mfderiv g (f x) ∘L mfderiv f x`.
    -- Here, `f = fibreScale a`, `g = Φ`, `x = p`, `f x = q`.
    have h_comp := mfderiv_comp (I := I.tangent) (I' := I.tangent) (I'' := 𝓘(ℝ, E × E))
      (f := fibreScale (I := I) a) (g := Φ) (x := p) hΦ_q_mdiff h_fibreScale_mdiff
    -- `h_comp : mfderiv (Φ ∘ fibreScale a) p = (mfderiv Φ (fibreScale a p)).comp (mfderiv (fibreScale a) p)`.
    -- We have `fibreScale a p = q` definitionally.
    change mfderiv I.tangent 𝓘(ℝ, E × E) (Φ ∘ fibreScale (I := I) a) p = _
    rw [h_comp]
  -- (8) Combine (6) and (7) to get:
  -- `mfderiv Φ q ∘L mfderiv (fibreScale a) p = chartScaleCLM a ∘L mfderiv Φ p`.
  have hkey :
      (mfderiv I.tangent 𝓘(ℝ, E × E) Φ q).comp
        (mfderiv I.tangent I.tangent (fibreScale (I := I) a) p) =
      (chartScaleCLM (E := E) a).comp
        (mfderiv I.tangent 𝓘(ℝ, E × E) Φ p) := by
    rw [← hmfd_comp_chain, hmfd_Phi_fibreScale, hmfd_chi_Phi]
  -- (9) Apply both sides to `a • V p`. The RHS becomes `chartScaleCLM a (a • gvfChartFiber g α p)`,
  -- which equals `gvfChartFiber g α q` (= LHS via `mfderiv Φ q (V q) = gvfChartFiber g α q`).
  have happ := congrArg (fun L : TangentSpace I.tangent p →L[ℝ] (E × E) => L (a • V p)) hkey
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at happ
  -- happ : mfderiv Φ q (mfderiv (fibreScale a) p (a • V p)) = chartScaleCLM a (mfderiv Φ p (a • V p))
  -- We compute each side.
  -- LHS: We want `mfderiv (fibreScale a) p (a • V p) = V q`.
  -- RHS: `chartScaleCLM a (a • mfderiv Φ p (V p)) = chartScaleCLM a (a • gvfChartFiber g α p)`.
  --      By `chi_apply_smul_gvfChartFiber` (paired with `chartScaleCLM_apply`),
  --      this equals `gvfChartFiber g α q`.
  -- Meanwhile, by `mfderiv_extChartAt_tangent_geodesicVectorFieldChart` applied at `q`:
  --      `mfderiv Φ q (V q) = gvfChartFiber g α q`.
  -- So `mfderiv Φ q (mfderiv (fibreScale a) p (a • V p)) = mfderiv Φ q (V q)`.
  -- By invertibility of `mfderiv Φ q`, we get the conclusion.
  have hΦq_inv : (mfderiv I.tangent 𝓘(ℝ, E × E) Φ q).IsInvertible := by
    have hq_ext_src : q ∈ (extChartAt I.tangent
        (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I.tangent)]
      exact hq_src
    exact isInvertible_mfderiv_extChartAt (I := I.tangent)
      (x := (⟨α, (0 : E)⟩ : TangentBundle I M)) (y := q) hq_ext_src
  -- Compute RHS of happ.
  have hRHS_eq : chartScaleCLM (E := E) a
      (mfderiv I.tangent 𝓘(ℝ, E × E) Φ p (a • V p)) =
      geodesicVectorFieldChartFiber (I := I) g α q := by
    have hlin := (mfderiv I.tangent 𝓘(ℝ, E × E) Φ p).map_smul a (V p)
    rw [hlin, mfderiv_extChartAt_tangent_geodesicVectorFieldChart (I := I) g α hp]
    -- Goal: `chartScaleCLM a (a • gvfChartFiber g α p) = gvfChartFiber g α q`.
    rw [chartScaleCLM_apply]
    -- Need: `(a • (gvfChartFiber p).1, a • (a • (gvfChartFiber p).2)) = gvfChartFiber q`.
    -- This is exactly `chi_apply_smul_gvfChartFiber`, BUT we need to handle:
    -- `(a • X).1 = a • X.1` and `(a • X).2 = a • X.2` for products.
    change ((a • geodesicVectorFieldChartFiber (I := I) g α p).1,
          a • (a • geodesicVectorFieldChartFiber (I := I) g α p).2) =
        geodesicVectorFieldChartFiber (I := I) g α q
    exact chi_apply_smul_gvfChartFiber (I := I) g α a hp
  -- Compute LHS of happ.
  have hLHS_eq : mfderiv I.tangent 𝓘(ℝ, E × E) Φ q (V q) =
      geodesicVectorFieldChartFiber (I := I) g α q :=
    mfderiv_extChartAt_tangent_geodesicVectorFieldChart (I := I) g α hq_proj
  -- happ : ((mfderiv Φ q).comp (mfderiv (fibreScale a) p)) (a • V p) = chartScaleCLM a (mfderiv Φ p (a • V p))
  -- Rewrite both sides into the form mfderiv Φ q (X) = mfderiv Φ q (V q).
  have happ' : mfderiv I.tangent 𝓘(ℝ, E × E) Φ q
      (mfderiv I.tangent I.tangent (fibreScale (I := I) a) p (a • V p)) =
      geodesicVectorFieldChartFiber (I := I) g α q := by
    rw [← hRHS_eq]
    exact happ
  rw [← hLHS_eq] at happ'
  -- happ' : mfderiv Φ q (mfderiv (fibreScale a) p (a • V p)) = mfderiv Φ q (V q).
  -- Use invertibility: `mfderiv Φ q` is injective.
  exact (ContinuousLinearMap.IsInvertible.injective hΦq_inv) happ'

end MfDerivFibreScaleOn

/-! ## Integral-curve property — pointwise verification

We assemble the integral-curve identity for the scaled lift by chain-rule
through `fibreScale a`. -/

section IntegralCurve

variable [I.Boundaryless] [CompleteSpace E]

/-- **Off-chart integral-curve identity.** When `γ (a · s + b) ∉ chart
source α`, both sides of the integral-curve identity vanish. -/
lemma hasMFDerivAt_affineReparamLift_off_chart
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    (a b : ℝ) {s : ℝ}
    (hoff : γ (a * s + b) ∉ (chartAt H α).source) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent (affineReparamLift (I := I) a b f) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorFieldChart (I := I) g α
          (affineReparamLift (I := I) a b f s))) := by
  classical
  set V : (p : TangentBundle I M) → TangentSpace I.tangent p :=
    geodesicVectorFieldChart (I := I) g α with hV
  have hf₁ : IsMIntegralCurve (fun s : ℝ => f (a * s + b)) (a • V) :=
    isMIntegralCurve_comp_affine_time (I := I) hf a b
  have hf₁_s := hf₁ s
  -- Off chart: `V (f₁ s) = 0`, so `(a • V) (f₁ s) = 0`.
  have hf_proj : (f (a * s + b)).proj = γ (a * s + b) := hproj (a * s + b)
  have hf_off : (f (a * s + b)).proj ∉ (chartAt H α).source := hf_proj ▸ hoff
  have hV_f₁ : V (f (a * s + b)) = 0 :=
    geodesicVectorFieldChart_eq_zero_of_proj_notMem (I := I) g α hf_off
  have hsmul_zero : (a • V) (f (a * s + b)) = 0 := by
    change a • V (f (a * s + b)) = 0
    rw [hV_f₁, smul_zero]
  have hf₁_mfd : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent
      (fun s : ℝ => f (a * s + b)) s 0 := by
    have := hf₁_s
    rw [hsmul_zero, ContinuousLinearMap.smulRight_zero] at this
    exact this
  have hFS_mfd := (fibreScale_mdifferentiableAt (I := I) (M := M) a
    (f (a * s + b))).hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent
      ((fibreScale (I := I) a) ∘ (fun s : ℝ => f (a * s + b))) s
      ((mfderiv I.tangent I.tangent (fibreScale (I := I) a)
          (f (a * s + b))).comp 0) :=
    hFS_mfd.comp s hf₁_mfd
  rw [ContinuousLinearMap.comp_zero] at hcomp
  have hfun : (fibreScale (I := I) a) ∘ (fun s : ℝ => f (a * s + b)) =
      affineReparamLift (I := I) a b f :=
    (affineReparamLift_eq_fibreScale_comp (I := I) a b f).symm
  rw [hfun] at hcomp
  have hftilde_proj : (affineReparamLift (I := I) a b f s).proj ∉
      (chartAt H α).source := by
    simp only [affineReparamLift_proj]
    exact hf_off
  have hV_ftilde : geodesicVectorFieldChart (I := I) g α
      (affineReparamLift (I := I) a b f s) = 0 :=
    geodesicVectorFieldChart_eq_zero_of_proj_notMem (I := I) g α hftilde_proj
  have htarget_zero : ((1 : ℝ →L[ℝ] ℝ).smulRight
          (geodesicVectorFieldChart (I := I) g α
            (affineReparamLift (I := I) a b f s))) = 0 := by
    rw [hV_ftilde, ContinuousLinearMap.smulRight_zero]
  rw [htarget_zero]
  exact hcomp

/-- **On-chart integral-curve identity.** When `γ (a · s + b) ∈ chart
source α`, the scaled lift has the correct manifold derivative. -/
lemma hasMFDerivAt_affineReparamLift_on_chart
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    (a b : ℝ) {s : ℝ}
    (hon : γ (a * s + b) ∈ (chartAt H α).source) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent (affineReparamLift (I := I) a b f) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorFieldChart (I := I) g α
          (affineReparamLift (I := I) a b f s))) := by
  classical
  set V : (p : TangentBundle I M) → TangentSpace I.tangent p :=
    geodesicVectorFieldChart (I := I) g α with hV
  have hf₁ : IsMIntegralCurve (fun s : ℝ => f (a * s + b)) (a • V) :=
    isMIntegralCurve_comp_affine_time (I := I) hf a b
  have hf₁_s := hf₁ s
  have hFS_mfd := (fibreScale_mdifferentiableAt (I := I) (M := M) a
    (f (a * s + b))).hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent
      ((fibreScale (I := I) a) ∘ (fun s : ℝ => f (a * s + b))) s
      ((mfderiv I.tangent I.tangent (fibreScale (I := I) a)
          (f (a * s + b))).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight ((a • V) (f (a * s + b))))) :=
    hFS_mfd.comp s hf₁_s
  have hfun : (fibreScale (I := I) a) ∘ (fun s : ℝ => f (a * s + b)) =
      affineReparamLift (I := I) a b f :=
    (affineReparamLift_eq_fibreScale_comp (I := I) a b f).symm
  rw [hfun] at hcomp
  -- Use the on-chart manifold-derivative identity.
  have hf_proj : (f (a * s + b)).proj = γ (a * s + b) := hproj (a * s + b)
  have hf_on : (f (a * s + b)).proj ∈ (chartAt H α).source := hf_proj ▸ hon
  have hid := mfderiv_fibreScale_geodesicVectorFieldChart_on_chart
    (I := I) g α a (p := f (a * s + b)) hf_on
  have hsmul_def : (a • V) (f (a * s + b)) = a • V (f (a * s + b)) := rfl
  have hftilde_eq : affineReparamLift (I := I) a b f s =
      fibreScale (I := I) a (f (a * s + b)) := rfl
  rw [hftilde_eq]
  -- Rewrite the right-hand side of `hcomp` to match the goal.
  -- The key identity: applied to `r : ℝ`, both sides agree by
  -- `mfderiv_fibreScale_geodesicVectorFieldChart_on_chart`.
  have hclm_eq : ((mfderiv I.tangent I.tangent (fibreScale (I := I) a)
              (f (a * s + b))).comp
            ((1 : ℝ →L[ℝ] ℝ).smulRight ((a • V) (f (a * s + b))))) =
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (geodesicVectorFieldChart (I := I) g α
            (fibreScale (I := I) a (f (a * s + b))))) := by
    apply ContinuousLinearMap.ext
    intro r
    -- LHS r: `(mfderiv ...) ((.smulRight ((a • V)(...))) r) = (mfderiv ...) (r • ((a • V)(...)))`.
    -- RHS r: `(.smulRight (V (fibreScale a ...))) r = r • V (fibreScale a ...)`.
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, map_smul]
    -- After simp, goal: `r • (mfderiv ...) ((a • V) (f (a*s+b))) = r • geodesicVectorFieldChart g α (fibreScale a (f (a*s+b)))`.
    -- Use `hid : mfderiv (fibreScale a) (f (a*s+b)) (a • geodesicVectorFieldChart g α (f (a*s+b))) = geodesicVectorFieldChart g α (fibreScale a (f (a*s+b)))`.
    -- And `(a • V) (f (a*s+b)) = a • V (f (a*s+b)) = a • geodesicVectorFieldChart g α (f (a*s+b))`
    -- by `rfl`.
    change r • (mfderiv I.tangent I.tangent (fibreScale (I := I) a)
        (f (a * s + b))) (a • geodesicVectorFieldChart (I := I) g α
          (f (a * s + b))) = _
    rw [hid]
  exact hcomp.congr_mfderiv hclm_eq

/-- **Integral-curve identity for the scaled lift.** At every time `s`,
the manifold derivative of `affineReparamLift a b f` at `s` agrees with
the value of the geodesic vector field at the lift. -/
lemma hasMFDerivAt_affineReparamLift
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    (a b : ℝ) (s : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent (affineReparamLift (I := I) a b f) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorFieldChart (I := I) g α
          (affineReparamLift (I := I) a b f s))) := by
  by_cases hon : γ (a * s + b) ∈ (chartAt H α).source
  · exact hasMFDerivAt_affineReparamLift_on_chart (I := I) hproj hf a b hon
  · exact hasMFDerivAt_affineReparamLift_off_chart (I := I) hproj hf a b hon

/-- The scaled lift is a global integral curve of `geodesicVectorFieldChart g α`. -/
lemma isMIntegralCurve_affineReparamLift
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    (a b : ℝ) :
    IsMIntegralCurve (affineReparamLift (I := I) a b f)
      (geodesicVectorFieldChart (I := I) g α) := by
  intro s
  exact hasMFDerivAt_affineReparamLift (I := I) hproj hf a b s

end IntegralCurve

/-! ## Headline -/

section MainTheorem

variable [I.Boundaryless] [CompleteSpace E]

/-- **Affine reparametrisation of geodesics.** If `γ : ℝ → M` is a
geodesic, so is `s ↦ γ (a · s + b)` for every `a b : ℝ`. -/
theorem IsGeodesic.comp_affine
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (a b : ℝ) :
    IsGeodesic (I := I) g (fun t : ℝ => γ (a * t + b)) := by
  obtain ⟨α, f, hproj, hf⟩ := hγ
  refine ⟨α, affineReparamLift (I := I) a b f, ?_, ?_⟩
  · intro t
    simp only [affineReparamLift_proj]
    exact hproj (a * t + b)
  · exact isMIntegralCurve_affineReparamLift (I := I) hproj hf a b

/-- **Translation of a geodesic.** If `γ` is a geodesic, so is `t ↦ γ (t + b)`.
Thin wrapper around `IsGeodesic.comp_affine`. -/
theorem IsGeodesic.translate
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (b : ℝ) :
    IsGeodesic (I := I) g (fun t : ℝ => γ (t + b)) := by
  simpa [one_mul] using hγ.comp_affine 1 b

/-- **Linear rescaling of a geodesic.** If `γ` is a geodesic, so is `t ↦ γ (a * t)`.
Thin wrapper around `IsGeodesic.comp_affine`. -/
theorem IsGeodesic.smul_param
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (a : ℝ) :
    IsGeodesic (I := I) g (fun t : ℝ => γ (a * t)) := by
  simpa [add_zero] using hγ.comp_affine a 0

/-- **Time reversal of a geodesic.** If `γ` is a geodesic, so is `t ↦ γ (-t)`.
Thin wrapper around `IsGeodesic.comp_affine`. -/
theorem IsGeodesic.neg_param
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) :
    IsGeodesic (I := I) g (fun t : ℝ => γ (-t)) := by
  simpa [neg_one_mul, add_zero] using hγ.comp_affine (-1 : ℝ) 0

end MainTheorem

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
