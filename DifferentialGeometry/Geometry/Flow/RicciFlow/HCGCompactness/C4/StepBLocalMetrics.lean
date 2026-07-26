import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBLocalizedAA
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs

set_option autoImplicit false

/-!
# Local metric limits on an open Euclidean domain (MSM135 Ch4 Step B, `lbl394` metric part)

The metric half of `lbl394`: the pulled-back normal-coordinate metrics `ḡ_k^β` on the
Euclidean ball `vec E^β` have uniformly bounded Euclidean derivatives (Hamilton
`lbl395`, the `NormalCoordMetricBoundInput` honest input) and are uniformly equivalent
to the Euclidean metric, so by Arzelà–Ascoli (here the localized engine
`exists_cInf_subseq_on`) a subsequence converges in `C^∞` on compact sets to a limit
Riemannian metric `g_∞^β` that retains the uniform equivalence (hence positivity).

This file gives the **generic** model-coordinate statement for a sequence of
bilinear-form-valued maps `gLoc : ℕ → E → (E →L[ℝ] E →L[ℝ] ℝ)` on an open `U`.  The
target `E →L[ℝ] E →L[ℝ] ℝ` is the project's pullback-bilinear-form type
(`Geometry.Metric.Pullback`, `StepBInputs.normalCoordMetric`), finite-dimensional when
`E` is.  Equivalence/positivity is preserved by passing the pointwise inequalities to
the (pointwise) limit (`ge_of_tendsto`/`le_of_tendsto`).

The HCG-facing `β`-indexed wrapper (a sequence of centers `c k : (X.obj k).M`, the fixed
domain `vec E^β`, and `NormalCoordMetricBoundInput`) additionally needs (i) a uniform
lower bound on the per-center `radius` so the fixed ball sits inside every chart domain,
and (ii) `C^∞` smoothness of `normalCoordMetric` on that ball — neither is supplied by
the current `NormalCoordMetricBoundInput` (a B-input follow-up: add a smoothness field
and a uniform-radius field).  That Step-A wiring is recorded in `StepBLocalMetrics.md`,
not fabricated here.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local metric limit** (`lbl394`, generic model-coordinate form).  A sequence of
bilinear-form-valued maps `gLoc k : E → (E →L[ℝ] E →L[ℝ] ℝ)` that are `C^∞` on an open
`U`, with Euclidean derivatives uniformly bounded on compact subsets of `U`, and each
uniformly equivalent to the Euclidean metric (`½‖v‖² ≤ gₖ(z)(v,v) ≤ 2‖v‖²`), has a
subsequence converging in `C^∞` on compacts of `U` to a limit `gInf` that is `C^∞` on
`U` and retains the same uniform Euclidean equivalence (so `gInf` is positive
definite on `U`). -/
theorem exists_metricLimit_on
    {U : Set E} (hU : IsOpen U)
    (gLoc : ℕ → E → (E →L[ℝ] E →L[ℝ] ℝ))
    (hg : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (gLoc k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (gLoc k) x‖ ≤ M)
    (hequiv : ∀ k : ℕ, ∀ z ∈ U, ∀ v : E,
        (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gLoc k z v v ∧ gLoc k z v v ≤ 2 * ‖v‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (gInf : E → (E →L[ℝ] E →L[ℝ] ℝ)),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) gInf U ∧
        MapCInfConvOnCompacts U (fun k => gLoc (φ k)) gInf ∧
        ∀ z ∈ U, ∀ v : E,
          (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gInf z v v ∧ gInf z v v ≤ 2 * ‖v‖ ^ 2 := by
  obtain ⟨φ, gInf, hφ, hsmooth, hconv⟩ := exists_cInf_subseq_on hU gLoc hg hbdd
  refine ⟨φ, gInf, hφ, hsmooth, hconv, fun z hz v => ?_⟩
  have htend : Tendsto (fun k => gLoc (φ k) z) atTop (𝓝 (gInf z)) := tendsto_of_cInf hconv hz
  have hcont : Continuous (fun c : E →L[ℝ] E →L[ℝ] ℝ => c v v) := by fun_prop
  have htendv : Tendsto (fun k => gLoc (φ k) z v v) atTop (𝓝 (gInf z v v)) :=
    (hcont.tendsto (gInf z)).comp htend
  exact ⟨ge_of_tendsto htendv (Filter.Eventually.of_forall fun k => (hequiv (φ k) z hz v).1),
    le_of_tendsto htendv (Filter.Eventually.of_forall fun k => (hequiv (φ k) z hz v).2)⟩

/-! ## HCG-facing wrapper: `normalCoordMetric` limit from the `lbl395` honest input

Wires `NormalCoordMetricBoundInput` (B-input) into `exists_metricLimit_on`, for a fixed
sequence of chart centers `c k : (X.obj k).M` (one `β`) on a fixed open domain `U`.  The
two remaining hypotheses are now both **honest geometric containments** of `U` in a
per-term ball: `hdom` (`U ⊆ ball 0 (input.radius k (c k))`, where the `lbl395`
derivative/equivalence bounds apply) and `hsub` (`U ⊆ ball 0 (expRadiusGp … (c k))`,
where the pulled-back metric is `C^∞`).  The previous `hsmooth` hypothesis — the
`C^∞` smoothness of `normalCoordMetric` on `U` — is **no longer a frontier**: it is
discharged internally from `hsub` via `contDiffOn_normalCoordMetric_of_subset_expBall`
(`StepBInputs`), which rests on the now-available single-radius
`expMap_contMDiffAt_infty_of_norm_lt_radius`.  The only remaining Step-A wiring is a
uniform positive lower bound on the two radii across the sequence so a single `U` works
(recorded in `StepBLocalMetrics.md`). -/

section HCGNormalCoord

open Bundle
open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Geometry.Riemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

set_option synthInstance.maxHeartbeats 800000 in
/-- **`normalCoordMetric` local metric limit** (`lbl394` metric part, fixed-`β` HCG
form).  For a fixed sequence of chart centers `c k : (X.obj k).M` on a fixed open `U`
contained in every `lbl395` bound ball (`hdom`) and in every `expRadiusGp` smoothness
ball (`hsub`), with the `lbl395` derivative/equivalence input (`input`), a subsequence of
`normalCoordMetric (X.obj k) (c k)` converges in `C^∞` on compacts of `U` to a limit
metric that is `C^∞` on `U` and retains the `½δ ≤ g ≤ 2δ` equivalence (hence positive
definite on `U`).  `C^∞` smoothness on `U` is discharged from `hsub` internally (no
`hsmooth` frontier).  Fixed-`β` only — NOT the finite diagonal over all `β`. -/
theorem exists_metricLimit_normalCoord
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBoundInput (I := I) X)
    (c : ∀ k : ℕ, (X.obj k).M)
    {U : Set E} (hU : IsOpen U)
    (hdom : ∀ k, U ⊆ Metric.ball (0 : E) (input.radius k (c k)))
    (hsub : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E) (expRadiusGp (I := I) (X.obj k).metric (c k))) :
    ∃ (φ : ℕ → ℕ) (gInf : E → (E →L[ℝ] E →L[ℝ] ℝ)),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) gInf U ∧
        MapCInfConvOnCompacts U
          (fun k => normalCoordMetric (I := I) (X.obj (φ k)) (c (φ k))) gInf ∧
        ∀ z ∈ U, ∀ v : E,
          (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gInf z v v ∧ gInf z v v ≤ 2 * ‖v‖ ^ 2 :=
  exists_metricLimit_on hU (fun k => normalCoordMetric (I := I) (X.obj k) (c k))
    (contDiffOn_normalCoordMetric_of_subset_expBall (I := I) c hsub)
    (fun r _K _hKcpt hKU =>
      ⟨input.metricC r, fun k z hz => input.metric_deriv k r (c k) z (hdom k (hKU hz))⟩)
    (fun k z hz v => input.metric_equiv k (c k) z (hdom k hz) v)

set_option synthInstance.maxHeartbeats 800000 in
/-- Finitely many moving normal-coordinate metrics admit one common
`C^∞`-convergent subsequence on a fixed open model domain. -/
theorem exists_metric_lim_pi
    {ι : Type*} [Fintype ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBoundInput (I := I) X)
    (c : ι → ∀ k : Nat, (X.obj k).M)
    {U : Set E} (hU : IsOpen U)
    (hdom : ∀ k i, U ⊆ Metric.ball (0 : E) (input.radius k (c i k)))
    (hsub : ∀ k i,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expRadiusGp (I := I) (X.obj k).metric (c i k))) :
    ∃ (phi : Nat → Nat)
        (gInf : E → (ι → (E →L[Real] E →L[Real] Real))),
      StrictMono phi ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) gInf U ∧
      MapCInfConvOnCompacts U
        (fun k z i ↦ normalCoordMetric (I := I) (X.obj (phi k))
          (c i (phi k)) z) gInf ∧
      ∀ z ∈ U, ∀ i v,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z i v v ∧
          gInf z i v v ≤ 2 * ‖v‖ ^ 2 := by
  classical
  let gLoc : Nat → E → (ι → (E →L[Real] E →L[Real] Real)) :=
    fun k z i ↦ normalCoordMetric (I := I) (X.obj k) (c i k) z
  have hsmooth_comp : ∀ k i, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ gLoc k z i) U := by
    intro k i
    exact contDiffOn_normalCoordMetric_of_subset_expBall
      (I := I) (fun n ↦ c i n) (fun n ↦ hsub n i) k
  have hsmooth : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (gLoc k) U :=
    fun k ↦ contDiffOn_pi.mpr (hsmooth_comp k)
  have hbdd_comp : ∀ i,
      IsometryDerivBoundsOn U (fun k z ↦ gLoc k z i) := by
    intro i r K hK hKU
    exact ⟨input.metricC r, fun k z hz ↦
      input.metric_deriv k r (c i k) z (hdom k i (hKU hz))⟩
  have hbdd : IsometryDerivBoundsOn U gLoc :=
    IsometryDerivBoundsOn.pi hU hsmooth_comp hbdd_comp
  obtain ⟨phi, gInf, hphi, hginf, hconv⟩ :=
    exists_cInf_subseq_on hU gLoc hsmooth hbdd
  refine ⟨phi, gInf, hphi, hginf, hconv, ?_⟩
  intro z hz i v
  have htendAll : Tendsto (fun k ↦ gLoc (phi k) z) atTop (nhds (gInf z)) :=
    tendsto_of_cInf hconv hz
  have htend : Tendsto (fun k ↦ gLoc (phi k) z i) atTop
      (nhds (gInf z i)) := (tendsto_pi_nhds.mp htendAll) i
  have heval : Continuous
      (fun A : E →L[Real] E →L[Real] Real ↦ A v v) := by
    fun_prop
  have htendv : Tendsto (fun k ↦ gLoc (phi k) z i v v) atTop
      (nhds (gInf z i v v)) := (heval.tendsto _).comp htend
  exact ⟨
    ge_of_tendsto htendv (Filter.Eventually.of_forall fun k ↦
      (input.metric_equiv (phi k) (c i (phi k)) z
        (hdom (phi k) i hz) v).1),
    le_of_tendsto htendv (Filter.Eventually.of_forall fun k ↦
      (input.metric_equiv (phi k) (c i (phi k)) z
        (hdom (phi k) i hz) v).2)⟩

end HCGNormalCoord

end HCGCompactness
end DifferentialGeometry
