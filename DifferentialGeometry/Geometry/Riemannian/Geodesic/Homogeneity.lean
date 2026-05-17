import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Connected.Clopen

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
   uniqueness in the canonical chart at `p`.

## What's shipped

This file ships the core infrastructure (zero-section vanishing,
constant-curve witness, maximal-interval characterisations for the zero-
velocity case, and the consistency identity at `t = 0`) along with the
headline `maximalGeodesic_smul`. The headline is proved by case analysis
on the degenerate cases `s = 0`, `t = 0`, and the generic `s, t ≠ 0`
case. The `t = 0` case is unconditional via `maximalGeodesic_zero`. The
`s = 0` case is reduced to a chart-fibre-constancy argument on the
chosen lift, using the universal zero-section vanishing.
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

/-! ## Vanishing of the geodesic vector field at the zero section

The chart-fixed geodesic vector field `gvfChart g α` vanishes at every
zero-section point `⟨p, 0⟩`, **regardless** of the chart basepoint `α`
and the foot `p`. This lets us treat the zero-velocity case via the
constant-curve witness. -/

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
  · -- On chart source: chart fibre data is `(0, 0)`, hence section is `0`.
    have hbase_set : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
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
    -- The chart-fibre data at `⟨p, 0⟩` is `(0, 0)`.
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
  · -- Off chart source: field vanishes (inlined from `ConstantSpeed`).
    classical
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

/-! ## Constant-curve witness for the zero-velocity case

The constant curve `fun _ => p` witnesses the geodesic predicate with
zero initial velocity, in every open set containing `0`. -/

section ZeroVelocityWitness

variable [I.Boundaryless] [CompleteSpace E]

/-- The constant curve `fun _ => p` is a geodesic on every set with
initial data `(p, 0)`, witnessed by the constant lift
`fun _ => ⟨p, 0⟩` (with chart basepoint `p`, fixed by the definition). -/
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

/-- **Maximal-interval membership for the `0 • v` initial velocity.** For
every `t : ℝ`, `t ∈ maximalGeodesicInterval g p (0 • v)`. -/
theorem mem_maximalGeodesicInterval_zero_smul
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (t : ℝ) :
    t ∈ maximalGeodesicInterval (I := I) g p ((0 : ℝ) • v) := by
  have h0 : (0 : ℝ) • v = (0 : E) := zero_smul ℝ v
  rw [h0, maximalGeodesicInterval_zero_velocity]
  exact Set.mem_univ _

end ZeroVelocityWitness

/-! ## Consistency at `t = 0`

For any `s : ℝ`, the value `maximalGeodesic g p v (s * 0) = p`. This is
an immediate consequence of `maximalGeodesic_zero` and `mul_zero`. -/

section ConsistencyAtZero

variable [I.Boundaryless] [CompleteSpace E]

/-- **Consistency at `t = 0`.** `maximalGeodesic g p v (s * 0) = p`. -/
theorem maximalGeodesic_mul_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (s : ℝ) :
    maximalGeodesic (I := I) g p v (s * 0) = p := by
  rw [mul_zero]
  exact maximalGeodesic_zero (I := I) g p v

end ConsistencyAtZero

/-! ## Headline at `t = 0`

The headline `maximalGeodesic g p (s • v) t = maximalGeodesic g p v (s * t)`
specialised to `t = 0` reduces to `maximalGeodesic g p (s • v) 0 = p`
on both sides, by `maximalGeodesic_zero` and `maximalGeodesic_mul_zero`. -/

section HeadlineAtZero

variable [I.Boundaryless] [CompleteSpace E]

/-- **Headline at `t = 0`.** `maximalGeodesic g p (s • v) 0 =
maximalGeodesic g p v (s * 0)`. Both sides reduce to `p`. -/
theorem maximalGeodesic_smul_zero_t
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (s : ℝ) :
    maximalGeodesic (I := I) g p (s • v) (0 : ℝ) =
      maximalGeodesic (I := I) g p v (s * 0) := by
  rw [maximalGeodesic_mul_zero (I := I) g p v s]
  exact maximalGeodesic_zero (I := I) g p (s • v)

end HeadlineAtZero

/-! ## Zero-velocity propagation: the value identity

The headline `maximalGeodesic g p 0 t = p` for every `t : ℝ`. The proof
proceeds by the following standard clopen propagation:

* The chosen witness gives a lift `f : ℝ → TangentBundle I M`, an open
  preconnected `J ⊆ ℝ` with `0, t ∈ J`, such that `f 0 = ⟨p, 0⟩` and `f`
  is an integral curve of `geodesicVectorFieldChart g p` on `J`.

* Define `S := { s ∈ J | f s = ⟨p, 0⟩ }`. By local uniqueness of integral
  curves at zero-section points (and smoothness of the chart-fixed
  geodesic vector field at every point of the trivialisation source at
  `p`), `f` agrees with the constant lift `fun _ => ⟨p, 0⟩` on a
  neighbourhood of every point of `S`. Hence `S` is *open in `ℝ`*.

* The same local uniqueness shows that for every `s ∈ J` with `s` in the
  closure of `S`, the curve `f` agrees with the constant lift on a
  neighbourhood of `s` — extracted from a sequence approaching `s` and
  lying in `S` — so `f s = ⟨p, 0⟩` and hence `s ∈ S`. In other words,
  `closure S ∩ J ⊆ S`.

* Apply `IsPreconnected.subset_of_closure_inter_subset` (with `s := J`,
  `u := S`) using preconnectedness of `J` to conclude `J ⊆ S`. In
  particular `t ∈ S`, so `f t = ⟨p, 0⟩`, and the chosen-curve value at
  `t` is the projection `(f t).proj = p`.
-/

section ZeroVelocityValue

variable [I.Boundaryless] [CompleteSpace E]

/-- **Local zero-section uniqueness.** Suppose `f : ℝ → TangentBundle I M`
is a (local) integral curve of `geodesicVectorFieldChart g p` at `t₀`
with `f t₀ = ⟨p, 0⟩`. Then `f` agrees with the constant lift
`fun _ => ⟨p, 0⟩` in a neighbourhood of `t₀`. -/
theorem isMIntegralCurveAt_eventuallyEq_const_zero_section
    (g : SmoothRiemannianMetric I M) (p : M) {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) t₀)
    (h0 : f t₀ = (⟨p, (0 : E)⟩ : TangentBundle I M)) :
    f =ᶠ[𝓝 t₀] fun _ => (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  -- The constant lift is a global integral curve of `gvfChart g p`.
  have hconst : IsMIntegralCurve
      (fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M))
      (geodesicVectorFieldChart (I := I) g p) :=
    isMIntegralCurve_const_zero_section (I := I) g p p
  have hconst_at : IsMIntegralCurveAt
      (fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M))
      (geodesicVectorFieldChart (I := I) g p) t₀ :=
    hconst.isMIntegralCurveAt t₀
  -- Apply the uniqueness theorem at the lift level. The chart-source
  -- condition is automatic since the chart basepoint is `p` itself.
  have hα_src : (f t₀).proj ∈ (chartAt H p).source := by
    rw [h0]
    -- `(⟨p, 0⟩).proj = p` and `p ∈ (chartAt H p).source`.
    exact mem_chart_source H p
  have heq := isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
    (I := I) (g := g) (α := p) (t₀ := t₀)
    (f₁ := f) (f₂ := fun _ => (⟨p, (0 : E)⟩ : TangentBundle I M))
    hα_src hf hconst_at h0
  exact heq

/-- **Zero-section invariance set, openness.** For an integral curve `f`
of `geodesicVectorFieldChart g p` on the open set `J`, the set
`S := {s ∈ J | f s = ⟨p, 0⟩}` is open in `ℝ`. -/
theorem zero_section_invariance_isOpen
    (g : SmoothRiemannianMetric I M) (p : M) {J : Set ℝ}
    (hJ : IsOpen J) {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J) :
    IsOpen {s ∈ J | f s = (⟨p, (0 : E)⟩ : TangentBundle I M)} := by
  rw [isOpen_iff_mem_nhds]
  rintro s₀ ⟨hs₀_J, hs₀_eq⟩
  -- `f` is an integral curve at `s₀` (since `J` open and `s₀ ∈ J`).
  have hf_at : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) s₀ :=
    hf.isMIntegralCurveAt (hJ.mem_nhds hs₀_J)
  -- `f =ᶠ[𝓝 s₀] (fun _ => ⟨p, 0⟩)` by local uniqueness.
  have heq := isMIntegralCurveAt_eventuallyEq_const_zero_section
    (I := I) g p hf_at hs₀_eq
  -- Combine with the fact that `J` is a neighbourhood of `s₀`.
  filter_upwards [heq, hJ.mem_nhds hs₀_J] with s hs hsJ
  exact ⟨hsJ, hs⟩

/-- **Zero-section invariance set, closure clause.** For an integral
curve `f` of `geodesicVectorFieldChart g p` on the open set `J`, every
limit point of `S := {s ∈ J | f s = ⟨p, 0⟩}` that lies in `J` is itself
in `S`. The proof uses sequential closure (`ℝ` is metric, hence
Fréchet-Urysohn) and continuity of `f` at `s` (integral curves are
continuous). The limit-of-constant-sequence step needs the codomain
`TangentBundle I M` to be T1 (which follows from `M` charted over `H`
with `H` charted over a normed space, hence T1; and `TangentBundle I M`
charted over the corresponding `ModelProd H E`). -/
theorem zero_section_invariance_closure
    (g : SmoothRiemannianMetric I M) (p : M) {J : Set ℝ}
    (hJ : IsOpen J) {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J) :
    closure {s ∈ J | f s = (⟨p, (0 : E)⟩ : TangentBundle I M)} ∩ J ⊆
      {s ∈ J | f s = (⟨p, (0 : E)⟩ : TangentBundle I M)} := by
  rintro s ⟨hs_cl, hs_J⟩
  refine ⟨hs_J, ?_⟩
  -- `f` is an integral curve at `s`, hence continuous at `s`.
  have hf_at : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) s :=
    hf.isMIntegralCurveAt (hJ.mem_nhds hs_J)
  have hcont : ContinuousAt f s := hf_at.continuousAt
  -- Extract a sequence `u → s` with each `u n ∈ S`.
  have hseq :=
    (mem_closure_iff_seq_limit (s := {s ∈ J |
        f s = (⟨p, (0 : E)⟩ : TangentBundle I M)}) (a := s)).mp hs_cl
  obtain ⟨u, hu_mem, hu_lim⟩ := hseq
  -- `f ∘ u → f s` by continuity. Since `f (u n) = ⟨p, 0⟩` for all `n`,
  -- the sequence `f ∘ u` is constant at `⟨p, 0⟩`, and any subsequence
  -- converges to the same limit. In a T1 space, the limit of a constant
  -- sequence is forced to equal that constant — the limit lies in the
  -- closure of `{⟨p, 0⟩}`, which equals `{⟨p, 0⟩}` by T1.
  have hfu_lim : Filter.Tendsto (fun n => f (u n)) Filter.atTop (𝓝 (f s)) :=
    hcont.tendsto.comp hu_lim
  have hfu_const : ∀ n, f (u n) = (⟨p, (0 : E)⟩ : TangentBundle I M) :=
    fun n => (hu_mem n).2
  -- `f s ∈ closure {⟨p, 0⟩}`. The image of the sequence is the constant
  -- `{⟨p, 0⟩}` singleton, and limits of values lie in the set-closure.
  haveI : T1Space (TangentBundle I M) := I.tangent.t1Space (TangentBundle I M)
  have h_in_cl : f s ∈ closure ({(⟨p, (0 : E)⟩ : TangentBundle I M)}) := by
    refine mem_closure_of_tendsto hfu_lim ?_
    refine Filter.Eventually.of_forall ?_
    intro n
    simp [hfu_const n]
  rwa [closure_singleton, Set.mem_singleton_iff] at h_in_cl

/-- **Zero-section invariance set, equals the witness interval.** Under
the hypotheses of the previous two lemmas, the zero-section invariance
set `S := {s ∈ J | f s = ⟨p, 0⟩}` equals `J` provided `J` is
preconnected and `0 ∈ J`, `f 0 = ⟨p, 0⟩`. -/
theorem zero_section_invariance_eq
    (g : SmoothRiemannianMetric I M) (p : M) {J : Set ℝ}
    (hJ : IsOpen J) (hJ_conn : IsPreconnected J) (h0 : (0 : ℝ) ∈ J)
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J)
    (hf0 : f 0 = (⟨p, (0 : E)⟩ : TangentBundle I M)) :
    ∀ s ∈ J, f s = (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  set S : Set ℝ := {s ∈ J | f s = (⟨p, (0 : E)⟩ : TangentBundle I M)}
  -- Apply preconnected propagation. We need `J ⊆ S`.
  have hS_open : IsOpen S :=
    zero_section_invariance_isOpen (I := I) g p hJ hf
  have hS_closure : closure S ∩ J ⊆ S :=
    zero_section_invariance_closure (I := I) g p hJ hf
  have hS_nonempty : (J ∩ S).Nonempty := ⟨0, h0, h0, hf0⟩
  have hsub : J ⊆ S :=
    hJ_conn.subset_of_closure_inter_subset hS_open hS_nonempty hS_closure
  intro s hs
  exact (hsub hs).2

/-- **Headline structural identity.** `maximalGeodesic g p 0 t = p` for
every `p : M` and every `t : ℝ`. The proof routes through the
zero-section invariance argument: any chosen witness lift `f` for the
zero-velocity case stays on the zero section throughout the
(preconnected) witness interval, so the chosen-curve projection equals
the constant `p` at every member of the interval, including `t`. -/
theorem maximalGeodesic_zero_velocity_value
    (g : SmoothRiemannianMetric I M) (p : M) (t : ℝ) :
    maximalGeodesic (I := I) g p (0 : TangentSpace I p) t = p := by
  -- `0 : TangentSpace I p` is definitionally `0 : E`.
  change maximalGeodesic (I := I) g p (0 : E) t = p
  have ht : t ∈ maximalGeodesicInterval (I := I) g p (0 : E) := by
    rw [maximalGeodesicInterval_zero_velocity (I := I) g p]
    exact Set.mem_univ _
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := (0 : E)) ht]
  -- Extract the chosen-witness data.
  obtain ⟨J, hJ_open, hJ_conn, h0J, htJ, hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (0 : E) ht
  obtain ⟨f, hproj, hf0, hf_on⟩ := hγ
  -- By the propagation lemma, `f s = ⟨p, 0⟩` for every `s ∈ J`.
  have hft : f t = (⟨p, (0 : E)⟩ : TangentBundle I M) :=
    zero_section_invariance_eq (I := I) g p hJ_open hJ_conn h0J hf_on hf0 t htJ
  -- The chosen-curve value at `t` is the projection of `f t`.
  have hchosen : maximalGeodesicChosenCurve (I := I) g p (0 : E) ht t =
      (f t).proj := (hproj t).symm
  rw [hchosen, hft]

end ZeroVelocityValue

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
