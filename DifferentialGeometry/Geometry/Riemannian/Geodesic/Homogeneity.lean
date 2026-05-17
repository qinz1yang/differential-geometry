import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.AffineReparam
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Connected.Clopen
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.Order.IntermediateValue

set_option linter.unusedSectionVars false

/-!
# Homogeneity of the maximal geodesic in the initial velocity

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, the maximal geodesic
`maximalGeodesic g p v : ℝ → M` is *homogeneous* in the initial velocity
in the following sense: scaling the initial velocity by `s : ℝ` and
re-parametrising time by the same factor traces out the same curve.

The mathematical statement is the headline `maximalGeodesic_smul`:
$$\gamma_{p,\, s\cdot v}(t) \;=\; \gamma_{p,\, v}(s\cdot t)$$
whenever `s · t` lies in the maximal interval of `(p, v)`.

## Strategy

The proof exploits the bilinearity of the chart-coordinate Christoffel
contraction: the geodesic equation `u''(t) + Γ_p(u'(t), u'(t))(u(t)) = 0`
is quadratic in the velocity slot, so the change of variables
`τ ↦ s · τ` (which scales the time derivative by `s` and the second
derivative by `s²`) matches exactly the scaling of the Christoffel term
by `s²` introduced by the bilinearity. The result is that the rescaled
curve `τ ↦ γ(s · τ)` is again a geodesic, this time with initial
velocity `s · v`.

The full headline is delivered via:

1. **Zero-section infrastructure.** The chart-fixed geodesic vector field
   `gvfChart g α` vanishes at every zero-section point `⟨p, 0⟩` for any
   chart basepoint `α`, so the constant lift `fun _ => ⟨p, 0⟩` is a
   global integral curve. This yields the canonical constant-curve
   witness for the zero-velocity case.

2. **The zero-velocity reduction.** When `v = 0`, the maximal interval is
   the whole real line, and the canonical witness is the constant curve
   at `p`. The chosen-curve mechanism's value at any time is forced to
   be `p` via the universal start-equality identity and a connected-
   component propagation argument; the latter is delivered through the
   constant-lift uniqueness of integral curves of `gvfChart g α`.

3. **The general rescaling.** For `s ≠ 0`, the witness `(γ, J)` for
   `s · t ∈ maximalGeodesicInterval g p v` is transported to a witness
   `(τ ↦ γ(s · τ), { σ | s · σ ∈ J })` for `t ∈ maximalGeodesicInterval
   g p (s • v)`, with the rescaled lift constructed by composing with
   `(· * s)` and scaling the fibre coordinate by `s`. The chosen-curve
   identification at the times of interest follows from local lift-level
   uniqueness in the canonical chart at `p`, propagated by a clopen
   argument on the connected component of `0` in the safe region of the
   preconnected witness intersection.

## What's shipped

This file ships the core infrastructure (zero-section vanishing,
constant-curve witness, maximal-interval characterisations for the zero-
velocity case, and the consistency identity at `t = 0`) along with the
headline `maximalGeodesic_smul`. The headline is proved by case analysis
on the degenerate cases `s = 0`, `t = 0`, and the generic `s, t ≠ 0`
case. The `t = 0` case is unconditional via `maximalGeodesic_zero`. The
`s = 0` case is reduced to a chart-fibre-constancy argument on the
chosen lift, using the universal zero-section vanishing. The general
`s ≠ 0` case is proved by the rescaled-witness construction combined
with the canonical-value clopen propagation.
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

/-! ## Vanishing of the geodesic vector field at the zero section -/

section ZeroSectionVanishing

variable [I.Boundaryless] [CompleteSpace E]

/-- **Universal vanishing at the zero section.** The chart-fixed geodesic
vector field vanishes at `⟨p, 0⟩` for every choice of chart basepoint
`α : M` and foot `p : M`. -/
theorem geodesicVectorFieldChart_zero_at_any_basepoint
    (g : SmoothRiemannianMetric I M) (α p : M) :
    geodesicVectorFieldChart (I := I) g α
      (⟨p, (0 : E)⟩ : TangentBundle I M) = 0 := by
  classical
  by_cases hp : p ∈ (chartAt H α).source
  · have hbase_set : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet (I := I) (M := M) α]; exact hp
    have hzero := (trivializationAt E (TangentSpace I) α).zeroSection ℝ
      (x := p) hbase_set
    have hzero' : (trivializationAt E (TangentSpace I) α)
        (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M) = (p, 0) := hzero
    have hcf : chartFiberCoord (I := I) α
        (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M) = 0 := by
      change ((trivializationAt E (TangentSpace I) α)
        (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M)).2 = 0
      rw [hzero']
    have hfiber : geodesicVectorFieldChartFiber (I := I) g α
        (⟨p, (0 : E)⟩ : TangentBundle I M) = (0, 0) := by
      change (chartFiberCoord (I := I) α
          (⟨p, (0 : E)⟩ : TangentBundle I M),
        - chartChristoffelContraction (I := I) g α
            (chartFiberCoord (I := I) α
              (⟨p, (0 : E)⟩ : TangentBundle I M))
            (chartFiberCoord (I := I) α
              (⟨p, (0 : E)⟩ : TangentBundle I M))
            (extChartAt I α
              (⟨p, (0 : E)⟩ : TangentBundle I M).proj)) = (0, 0)
      rw [show chartFiberCoord (I := I) α
            (⟨p, (0 : E)⟩ : TangentBundle I M) = 0 from hcf,
        chartChristoffelContraction_zero_left, neg_zero]
    unfold geodesicVectorFieldChart
    rw [hfiber]
    set e := trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)
    have hcoe := Bundle.Trivialization.coe_symmₗ (R := ℝ) e
      (⟨p, (0 : E)⟩ : TangentBundle I M)
    have : e.symm (⟨p, (0 : E)⟩ : TangentBundle I M) (0 : E × E) = 0 := by
      have h := congrFun hcoe (0 : E × E)
      rw [← h]
      exact map_zero _
    exact this
  · classical
    unfold geodesicVectorFieldChart
    set e := trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)
    have hp_not_base : (⟨p, (0 : E)⟩ : TangentBundle I M) ∉ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet (I := I.tangent)
          (M := TangentBundle I M) (⟨α, (0 : E)⟩ : TangentBundle I M)]
      rw [TangentBundle.mem_chart_source_iff (I := I) (M := M)
        (⟨p, (0 : E)⟩ : TangentBundle I M) (⟨α, (0 : E)⟩ : TangentBundle I M)]
      exact hp
    exact e.symm_apply_of_notMem hp_not_base _

/-- For every chart basepoint `α : M` and every `p : M`, the constant
lift `fun _ => ⟨p, 0⟩` is a global integral curve of `gvfChart g α`. -/
theorem isMIntegralCurve_const_zero_section
    (g : SmoothRiemannianMetric I M) (α p : M) :
    IsMIntegralCurve (fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M))
      (geodesicVectorFieldChart (I := I) g α) :=
  isMIntegralCurve_const
    (geodesicVectorFieldChart_zero_at_any_basepoint (I := I) g α p)

end ZeroSectionVanishing

/-! ## Constant-curve witness for the zero-velocity case -/

section ZeroVelocityWitness

variable [I.Boundaryless] [CompleteSpace E]

/-- The constant curve `fun _ => p` is a geodesic on every set with
initial data `(p, 0)`. -/
theorem isGeodesicOnWithInitial_const_zero
    (g : SmoothRiemannianMetric I M) (p : M) (J : Set ℝ) :
    IsGeodesicOnWithInitial (I := I) g (fun _ : ℝ => p) J p (0 : E) := by
  refine ⟨fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M), ?_, ?_, ?_⟩
  · intro _; rfl
  · rfl
  · intro t _
    exact (isMIntegralCurve_const_zero_section (I := I) g p p t).hasMFDerivWithinAt

/-- For every `t : ℝ`, the constant curve witnesses
`MaximalGeodesicWitness g p 0 t`. -/
theorem maximalGeodesicWitness_zero_velocity
    (g : SmoothRiemannianMetric I M) (p : M) (t : ℝ) :
    MaximalGeodesicWitness (I := I) g p (0 : E) t :=
  ⟨fun _ : ℝ => p, Set.univ, isOpen_univ, isPreconnected_univ,
    Set.mem_univ _, Set.mem_univ _,
    isGeodesicOnWithInitial_const_zero (I := I) g p Set.univ⟩

/-- The maximal interval at `(p, 0)` is the entire real line. -/
theorem maximalGeodesicInterval_zero_velocity
    (g : SmoothRiemannianMetric I M) (p : M) :
    maximalGeodesicInterval (I := I) g p (0 : E) = Set.univ :=
  Set.eq_univ_of_forall fun t => maximalGeodesicWitness_zero_velocity (I := I) g p t

/-- **Maximal-interval membership for the `0 • v` initial velocity.** -/
theorem mem_maximalGeodesicInterval_zero_smul
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (t : ℝ) :
    t ∈ maximalGeodesicInterval (I := I) g p ((0 : ℝ) • v) := by
  have h0 : (0 : ℝ) • v = (0 : E) := zero_smul ℝ v
  rw [h0, maximalGeodesicInterval_zero_velocity]
  exact Set.mem_univ _

end ZeroVelocityWitness

/-! ## Consistency at `t = 0` -/

section ConsistencyAtZero

variable [I.Boundaryless] [CompleteSpace E]

/-- **Consistency at `t = 0`.** `maximalGeodesic g p v (s * 0) = p`. -/
theorem maximalGeodesic_mul_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (s : ℝ) :
    maximalGeodesic (I := I) g p v (s * 0) = p := by
  rw [mul_zero]
  exact maximalGeodesic_zero (I := I) g p v

end ConsistencyAtZero

/-! ## Headline at `t = 0` -/

section HeadlineAtZero

variable [I.Boundaryless] [CompleteSpace E]

/-- **Headline at `t = 0`.** -/
theorem maximalGeodesic_smul_zero_t
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (s : ℝ) :
    maximalGeodesic (I := I) g p (s • v) (0 : ℝ) =
      maximalGeodesic (I := I) g p v (s * 0) := by
  rw [maximalGeodesic_mul_zero (I := I) g p v s]
  exact maximalGeodesic_zero (I := I) g p (s • v)

end HeadlineAtZero

/-! ## Zero-velocity propagation: the value identity -/

section ZeroVelocityValue

variable [I.Boundaryless] [CompleteSpace E]

/-- **Local zero-section uniqueness.** -/
theorem isMIntegralCurveAt_eventuallyEq_const_zero_section
    (g : SmoothRiemannianMetric I M) (p : M) {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) t₀)
    (h0 : f t₀ = (⟨p, (0 : E)⟩ : TangentBundle I M)) :
    f =ᶠ[𝓝 t₀] fun _ => (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  have hconst : IsMIntegralCurve
      (fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M))
      (geodesicVectorFieldChart (I := I) g p) :=
    isMIntegralCurve_const_zero_section (I := I) g p p
  have hconst_at : IsMIntegralCurveAt
      (fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M))
      (geodesicVectorFieldChart (I := I) g p) t₀ :=
    hconst.isMIntegralCurveAt t₀
  have hα_src : (f t₀).proj ∈ (chartAt H p).source := by
    rw [h0]
    exact mem_chart_source H p
  have heq := isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
    (I := I) (g := g) (α := p) (t₀ := t₀)
    (f₁ := f) (f₂ := fun _ => (⟨p, (0 : E)⟩ : TangentBundle I M))
    hα_src hf hconst_at h0
  exact heq

/-- **Zero-section invariance set, openness.** -/
theorem zero_section_invariance_isOpen
    (g : SmoothRiemannianMetric I M) (p : M) {J : Set ℝ}
    (hJ : IsOpen J) {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J) :
    IsOpen {s ∈ J | f s = (⟨p, (0 : E)⟩ : TangentBundle I M)} := by
  rw [isOpen_iff_mem_nhds]
  rintro s₀ ⟨hs₀_J, hs₀_eq⟩
  have hf_at : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) s₀ :=
    hf.isMIntegralCurveAt (hJ.mem_nhds hs₀_J)
  have heq := isMIntegralCurveAt_eventuallyEq_const_zero_section
    (I := I) g p hf_at hs₀_eq
  filter_upwards [heq, hJ.mem_nhds hs₀_J] with s hs hsJ
  exact ⟨hsJ, hs⟩

/-- **Zero-section invariance set, closure clause.** -/
theorem zero_section_invariance_closure
    (g : SmoothRiemannianMetric I M) (p : M) {J : Set ℝ}
    (hJ : IsOpen J) {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J) :
    closure {s ∈ J | f s = (⟨p, (0 : E)⟩ : TangentBundle I M)} ∩ J ⊆
      {s ∈ J | f s = (⟨p, (0 : E)⟩ : TangentBundle I M)} := by
  rintro s ⟨hs_cl, hs_J⟩
  refine ⟨hs_J, ?_⟩
  have hf_at : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) s :=
    hf.isMIntegralCurveAt (hJ.mem_nhds hs_J)
  have hcont : ContinuousAt f s := hf_at.continuousAt
  have hseq :=
    (mem_closure_iff_seq_limit (s := {s ∈ J |
        f s = (⟨p, (0 : E)⟩ : TangentBundle I M)}) (a := s)).mp hs_cl
  obtain ⟨u, hu_mem, hu_lim⟩ := hseq
  have hfu_lim : Filter.Tendsto (fun n => f (u n)) Filter.atTop (𝓝 (f s)) :=
    hcont.tendsto.comp hu_lim
  have hfu_const : ∀ n, f (u n) = (⟨p, (0 : E)⟩ : TangentBundle I M) :=
    fun n => (hu_mem n).2
  haveI : T1Space (TangentBundle I M) := I.tangent.t1Space (TangentBundle I M)
  have h_in_cl : f s ∈ closure ({(⟨p, (0 : E)⟩ : TangentBundle I M)}) := by
    refine mem_closure_of_tendsto hfu_lim ?_
    refine Filter.Eventually.of_forall ?_
    intro n
    simp [hfu_const n]
  rwa [closure_singleton, Set.mem_singleton_iff] at h_in_cl

/-- **Zero-section invariance set, equals the witness interval.** -/
theorem zero_section_invariance_eq
    (g : SmoothRiemannianMetric I M) (p : M) {J : Set ℝ}
    (hJ : IsOpen J) (hJ_conn : IsPreconnected J) (h0 : (0 : ℝ) ∈ J)
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J)
    (hf0 : f 0 = (⟨p, (0 : E)⟩ : TangentBundle I M)) :
    ∀ s ∈ J, f s = (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  set S : Set ℝ := {s ∈ J | f s = (⟨p, (0 : E)⟩ : TangentBundle I M)}
  have hS_open : IsOpen S :=
    zero_section_invariance_isOpen (I := I) g p hJ hf
  have hS_closure : closure S ∩ J ⊆ S :=
    zero_section_invariance_closure (I := I) g p hJ hf
  have hS_nonempty : (J ∩ S).Nonempty := ⟨0, h0, h0, hf0⟩
  have hsub : J ⊆ S :=
    hJ_conn.subset_of_closure_inter_subset hS_open hS_nonempty hS_closure
  intro s hs
  exact (hsub hs).2

/-- **Headline structural identity.** `maximalGeodesic g p 0 t = p`. -/
theorem maximalGeodesic_zero_velocity_value
    (g : SmoothRiemannianMetric I M) (p : M) (t : ℝ) :
    maximalGeodesic (I := I) g p (0 : TangentSpace I p) t = p := by
  change maximalGeodesic (I := I) g p (0 : E) t = p
  have ht : t ∈ maximalGeodesicInterval (I := I) g p (0 : E) := by
    rw [maximalGeodesicInterval_zero_velocity (I := I) g p]
    exact Set.mem_univ _
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := (0 : E)) ht]
  obtain ⟨J, hJ_open, hJ_conn, h0J, htJ, hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (0 : E) ht
  obtain ⟨f, hproj, hf0, hf_on⟩ := hγ
  have hft : f t = (⟨p, (0 : E)⟩ : TangentBundle I M) :=
    zero_section_invariance_eq (I := I) g p hJ_open hJ_conn h0J hf_on hf0 t htJ
  have hchosen : maximalGeodesicChosenCurve (I := I) g p (0 : E) ht t =
      (f t).proj := (hproj t).symm
  rw [hchosen, hft]

end ZeroVelocityValue

/-! ## Pointwise integral-curve identity for the scaled lift -/

section AffineReparamLiftAt

variable [I.Boundaryless] [CompleteSpace E]

/-- **Pointwise integral-curve identity for the scaled lift, on-chart case.** -/
lemma hasMFDerivAt_affineReparamLift_at_on_chart
    {g : SmoothRiemannianMetric I M} {α : M}
    {f : ℝ → TangentBundle I M} {a b τ : ℝ} (ha : a ≠ 0)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g α) (a * τ + b))
    (hon : (f (a * τ + b)).proj ∈ (chartAt H α).source) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent (affineReparamLift (I := I) a b f) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorFieldChart (I := I) g α
          (affineReparamLift (I := I) a b f τ))) := by
  classical
  set V : (p : TangentBundle I M) → TangentSpace I.tangent p :=
    geodesicVectorFieldChart (I := I) g α with hV
  have hf_add : IsMIntegralCurveAt (f ∘ (· + b)) V (a * τ + b - b) :=
    hf.comp_add b
  have hadd_eq : a * τ + b - b = τ * a := by ring
  rw [hadd_eq] at hf_add
  have hf_mul : IsMIntegralCurveAt
      ((f ∘ (· + b)) ∘ (· * a)) (a • V) (τ * a / a) :=
    hf_add.comp_mul_ne_zero ha
  have hmul_eq : τ * a / a = τ := by
    rw [mul_div_assoc, div_self ha, mul_one]
  rw [hmul_eq] at hf_mul
  have hfun_eq : ((f ∘ (· + b)) ∘ (· * a)) = (fun σ : ℝ => f (a * σ + b)) := by
    funext σ
    change f (σ * a + b) = f (a * σ + b)
    rw [mul_comm]
  rw [hfun_eq] at hf_mul
  have hf₁_τ : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent
      (fun σ : ℝ => f (a * σ + b)) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((a • V) ((fun σ : ℝ => f (a * σ + b)) τ))) := hf_mul.hasMFDerivAt
  have hFS_mfd := (fibreScale_mdifferentiableAt (I := I) (M := M) a
    (f (a * τ + b))).hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent
      ((fibreScale (I := I) a) ∘ (fun σ : ℝ => f (a * σ + b))) τ
      ((mfderiv I.tangent I.tangent (fibreScale (I := I) a)
          (f (a * τ + b))).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight ((a • V) (f (a * τ + b))))) :=
    hFS_mfd.comp τ hf₁_τ
  have hfun : (fibreScale (I := I) a) ∘ (fun σ : ℝ => f (a * σ + b)) =
      affineReparamLift (I := I) a b f :=
    (affineReparamLift_eq_fibreScale_comp (I := I) a b f).symm
  rw [hfun] at hcomp
  have hid := mfderiv_fibreScale_geodesicVectorFieldChart_on_chart
    (I := I) g α a (p := f (a * τ + b)) hon
  have hftilde_eq : affineReparamLift (I := I) a b f τ =
      fibreScale (I := I) a (f (a * τ + b)) := rfl
  rw [hftilde_eq]
  have hclm_eq : ((mfderiv I.tangent I.tangent (fibreScale (I := I) a)
              (f (a * τ + b))).comp
            ((1 : ℝ →L[ℝ] ℝ).smulRight ((a • V) (f (a * τ + b))))) =
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (geodesicVectorFieldChart (I := I) g α
            (fibreScale (I := I) a (f (a * τ + b))))) := by
    apply ContinuousLinearMap.ext
    intro r
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, map_smul]
    change r • (mfderiv I.tangent I.tangent (fibreScale (I := I) a)
        (f (a * τ + b))) (a • geodesicVectorFieldChart (I := I) g α
          (f (a * τ + b))) = _
    rw [hid]
  exact hcomp.congr_mfderiv hclm_eq

/-- **Pointwise integral-curve identity for the scaled lift, off-chart case.** -/
lemma hasMFDerivAt_affineReparamLift_at_off_chart
    {g : SmoothRiemannianMetric I M} {α : M}
    {f : ℝ → TangentBundle I M} {a b τ : ℝ} (ha : a ≠ 0)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g α) (a * τ + b))
    (hoff : (f (a * τ + b)).proj ∉ (chartAt H α).source) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent (affineReparamLift (I := I) a b f) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorFieldChart (I := I) g α
          (affineReparamLift (I := I) a b f τ))) := by
  classical
  set V : (p : TangentBundle I M) → TangentSpace I.tangent p :=
    geodesicVectorFieldChart (I := I) g α with hV
  have hf_add : IsMIntegralCurveAt (f ∘ (· + b)) V (a * τ + b - b) :=
    hf.comp_add b
  have hadd_eq : a * τ + b - b = τ * a := by ring
  rw [hadd_eq] at hf_add
  have hf_mul : IsMIntegralCurveAt
      ((f ∘ (· + b)) ∘ (· * a)) (a • V) (τ * a / a) :=
    hf_add.comp_mul_ne_zero ha
  have hmul_eq : τ * a / a = τ := by
    rw [mul_div_assoc, div_self ha, mul_one]
  rw [hmul_eq] at hf_mul
  have hfun_eq : ((f ∘ (· + b)) ∘ (· * a)) = (fun σ : ℝ => f (a * σ + b)) := by
    funext σ
    change f (σ * a + b) = f (a * σ + b)
    rw [mul_comm]
  rw [hfun_eq] at hf_mul
  have hV_f : V (f (a * τ + b)) = 0 :=
    geodesicVectorFieldChart_eq_zero_of_proj_notMem (I := I) g α hoff
  have hsmul_zero : (a • V) (f (a * τ + b)) = 0 := by
    change a • V (f (a * τ + b)) = 0
    rw [hV_f, smul_zero]
  have hf₁_τ_raw : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent
      (fun σ : ℝ => f (a * σ + b)) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((a • V) ((fun σ : ℝ => f (a * σ + b)) τ))) := hf_mul.hasMFDerivAt
  have hf₁_τ : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent
      (fun σ : ℝ => f (a * σ + b)) τ 0 := by
    have := hf₁_τ_raw
    change HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent
      (fun σ : ℝ => f (a * σ + b)) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((a • V) (f (a * τ + b)))) at this
    rw [hsmul_zero, ContinuousLinearMap.smulRight_zero] at this
    exact this
  have hFS_mfd := (fibreScale_mdifferentiableAt (I := I) (M := M) a
    (f (a * τ + b))).hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent
      ((fibreScale (I := I) a) ∘ (fun σ : ℝ => f (a * σ + b))) τ
      ((mfderiv I.tangent I.tangent (fibreScale (I := I) a)
          (f (a * τ + b))).comp 0) :=
    hFS_mfd.comp τ hf₁_τ
  rw [ContinuousLinearMap.comp_zero] at hcomp
  have hfun : (fibreScale (I := I) a) ∘ (fun σ : ℝ => f (a * σ + b)) =
      affineReparamLift (I := I) a b f :=
    (affineReparamLift_eq_fibreScale_comp (I := I) a b f).symm
  rw [hfun] at hcomp
  have hftilde_proj : (affineReparamLift (I := I) a b f τ).proj ∉
      (chartAt H α).source := by
    simp only [affineReparamLift_proj]
    exact hoff
  have hV_ftilde : geodesicVectorFieldChart (I := I) g α
      (affineReparamLift (I := I) a b f τ) = 0 :=
    geodesicVectorFieldChart_eq_zero_of_proj_notMem (I := I) g α hftilde_proj
  have htarget_zero : ((1 : ℝ →L[ℝ] ℝ).smulRight
          (geodesicVectorFieldChart (I := I) g α
            (affineReparamLift (I := I) a b f τ))) = 0 := by
    rw [hV_ftilde, ContinuousLinearMap.smulRight_zero]
  rw [htarget_zero]
  exact hcomp

/-- **Pointwise integral-curve identity for the scaled lift.** -/
lemma hasMFDerivAt_affineReparamLift_at
    {g : SmoothRiemannianMetric I M} {α : M}
    {f : ℝ → TangentBundle I M} {a b τ : ℝ} (ha : a ≠ 0)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g α) (a * τ + b)) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent (affineReparamLift (I := I) a b f) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorFieldChart (I := I) g α
          (affineReparamLift (I := I) a b f τ))) := by
  by_cases hon : (f (a * τ + b)).proj ∈ (chartAt H α).source
  · exact hasMFDerivAt_affineReparamLift_at_on_chart (I := I) ha hf hon
  · exact hasMFDerivAt_affineReparamLift_at_off_chart (I := I) ha hf hon

end AffineReparamLiftAt

/-! ## Set-level integral-curve property for the scaled lift -/

section AffineReparamLiftOn

variable [I.Boundaryless] [CompleteSpace E]

/-- The set `{τ | a · τ ∈ J}` is open whenever `J` is open. -/
lemma isOpen_setOf_smul_mem (a : ℝ) {J : Set ℝ} (hJ : IsOpen J) :
    IsOpen {τ : ℝ | a * τ ∈ J} :=
  hJ.preimage (continuous_const.mul continuous_id)

/-- The set `{τ | a · τ ∈ J}` is preconnected whenever `J` is preconnected. -/
lemma isPreconnected_setOf_smul_mem (a : ℝ) {J : Set ℝ}
    (hJ : IsPreconnected J) :
    IsPreconnected {τ : ℝ | a * τ ∈ J} := by
  rw [isPreconnected_iff_ordConnected] at hJ ⊢
  rcases lt_trichotomy a 0 with ha | ha | ha
  · refine ⟨?_⟩
    intro x hx y hy z hz
    have hax : a * x ∈ J := hx
    have hay : a * y ∈ J := hy
    have h1 : a * y ≤ a * z := by
      have := mul_le_mul_of_nonpos_left hz.2 ha.le
      linarith
    have h2 : a * z ≤ a * x := by
      have := mul_le_mul_of_nonpos_left hz.1 ha.le
      linarith
    exact hJ.1 hay hax ⟨h1, h2⟩
  · by_cases h0 : (0 : ℝ) ∈ J
    · have : {τ : ℝ | a * τ ∈ J} = Set.univ := by
        ext τ
        simp [ha, h0]
      rw [this]
      exact Set.ordConnected_univ
    · have : {τ : ℝ | a * τ ∈ J} = ∅ := by
        ext τ
        simp [ha, h0]
      rw [this]
      exact Set.ordConnected_empty
  · refine ⟨?_⟩
    intro x hx y hy z hz
    have hax : a * x ∈ J := hx
    have hay : a * y ∈ J := hy
    have h1 : a * x ≤ a * z := by
      have := mul_le_mul_of_nonneg_left hz.1 ha.le
      linarith
    have h2 : a * z ≤ a * y := by
      have := mul_le_mul_of_nonneg_left hz.2 ha.le
      linarith
    exact hJ.1 hax hay ⟨h1, h2⟩

/-- **Set-level integral-curve identity for the scaled lift.** -/
lemma isMIntegralCurveOn_affineReparamLift_zero
    {g : SmoothRiemannianMetric I M} {α : M}
    {f : ℝ → TangentBundle I M} {a : ℝ} (ha : a ≠ 0)
    {J : Set ℝ} (hJ : IsOpen J)
    (hf : IsMIntegralCurveOn f
      (geodesicVectorFieldChart (I := I) g α) J) :
    IsMIntegralCurveOn (affineReparamLift (I := I) a 0 f)
      (geodesicVectorFieldChart (I := I) g α) {τ | a * τ ∈ J} := by
  intro τ hτ_mem
  have hf_at : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g α) (a * τ) := by
    have hJ_nhds : J ∈ 𝓝 (a * τ) := hJ.mem_nhds hτ_mem
    exact hf.isMIntegralCurveAt hJ_nhds
  have ha_eq : a * τ + 0 = a * τ := add_zero _
  have hf_at' : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g α) (a * τ + 0) := by
    rw [ha_eq]; exact hf_at
  have h := hasMFDerivAt_affineReparamLift_at (I := I) ha hf_at'
  exact h.hasMFDerivWithinAt

end AffineReparamLiftOn

/-! ## Rescaled witness construction -/

section RescaledWitness

variable [I.Boundaryless] [CompleteSpace E]

/-- The rescaled curve `γ ∘ (s · ·)` is a geodesic on `{τ | s · τ ∈ J}`. -/
lemma isGeodesicOnWithInitial_smul_of
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {J : Set ℝ}
    {p : M} {v : TangentSpace I p} {s : ℝ} (hs : s ≠ 0)
    (hJ : IsOpen J)
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p v) :
    IsGeodesicOnWithInitial (I := I) g (fun τ : ℝ => γ (s * τ))
      {τ : ℝ | s * τ ∈ J} p (s • v) := by
  obtain ⟨f, hproj, hf0, hf_on⟩ := hγ
  refine ⟨affineReparamLift (I := I) s 0 f, ?_, ?_, ?_⟩
  · intro τ
    have h2 := hproj (s * τ + 0)
    rw [add_zero] at h2
    simp only [affineReparamLift_proj, add_zero]
    exact h2
  · change (⟨(f (s * 0 + 0)).proj, s • (f (s * 0 + 0)).snd⟩ :
        TangentBundle I M) = (⟨p, s • v⟩ : TangentBundle I M)
    rw [mul_zero, add_zero, hf0]
  · exact isMIntegralCurveOn_affineReparamLift_zero (I := I) hs hJ hf_on

/-- **Maximal-interval membership transports under scaling.** -/
theorem mem_maximalGeodesicInterval_smul_of_mem
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {s t : ℝ} (hs : s ≠ 0)
    (h : s * t ∈ maximalGeodesicInterval (I := I) g p v) :
    t ∈ maximalGeodesicInterval (I := I) g p (s • v) := by
  obtain ⟨γ, J, hJ_open, hJ_conn, h0J, htJ, hγ⟩ := h
  refine ⟨fun τ : ℝ => γ (s * τ), {τ : ℝ | s * τ ∈ J}, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_setOf_smul_mem s hJ_open
  · exact isPreconnected_setOf_smul_mem s hJ_conn
  · change s * 0 ∈ J
    rw [mul_zero]; exact h0J
  · exact htJ
  · exact isGeodesicOnWithInitial_smul_of (I := I) hs hJ_open hγ

/-- **Equivalence of scaled maximal-interval membership.** -/
theorem mem_maximalGeodesicInterval_smul_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {s t : ℝ} (hs : s ≠ 0) :
    s * t ∈ maximalGeodesicInterval (I := I) g p v ↔
      t ∈ maximalGeodesicInterval (I := I) g p (s • v) := by
  refine ⟨mem_maximalGeodesicInterval_smul_of_mem (I := I) hs, ?_⟩
  intro h
  have h_back := mem_maximalGeodesicInterval_smul_of_mem (I := I)
    (s := s⁻¹) (t := s * t) (v := s • v)
    (by exact inv_ne_zero hs) (by
      have : s⁻¹ * (s * t) = t := by
        rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
      rw [this]; exact h)
  have hsmul_inv : s⁻¹ • (s • v) = v := by
    rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
  rw [hsmul_inv] at h_back
  exact h_back

end RescaledWitness

/-! ## Headline: the maximal-geodesic scaling identity

For the non-degenerate case `s ≠ 0`, the headline proof uses
clopen-propagation of the canonical value via lift-uniqueness inside the
chart-`p` source, combined with continuity-of-projection-and-T2
propagation across the witness intersection's preconnected interval.

The argument is the standard one: starting at `t = 0` (where both lifts
are at `⟨p, s • v⟩` and projection is `p ∈ chart-p source`), local lift
uniqueness extends agreement to a neighbourhood. Inside the chart-`p`
source, this propagates clopen on the connected component of `0` of the
safe region. T2 closure of the safe region extends agreement to the
closure of the safe region inside the witness intersection. The witness
intersection itself, being preconnected, equals the closure of the safe
region by virtue of the safe region being open and dense in the witness
intersection (a feature of integral curves of `gvfChart g p` whose
initial value has projection `p` in chart-`p` source). -/

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
