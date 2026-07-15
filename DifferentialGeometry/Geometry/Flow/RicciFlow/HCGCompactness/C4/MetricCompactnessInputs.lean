import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCovering
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringItem3
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.VolumeComparisonBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Theorem 3.9 — the conditional endpoint (`MetricCompactnessInputs`)

**Endpoint ruling (2026-07-05, user).**  The unconditional `metricCompactness`
(`HCGCompactness/MetricCompactness.lean`) cannot be discharged by the Chapter 4
construction alone: the construction consumes book-external theorems (the honest
inputs below) that are *not* among its three hypotheses, and the project has no
volume-form/comparison infrastructure to prove them natively.  The Chapter 4
working target is therefore this **conditional** endpoint: the same conclusion,
with the externally cited theorems bundled as an explicit input structure.  The
unconditional `metricCompactness` keeps its single `sorry`, now documented as
`= MetricCompactnessInputs.metricCompactness + the cited external theorems`.

## The bundle, field by field (mathematical audit 2026-07-05)

Sequence-level external inputs, each TRUE under the Theorem 3.9 hypotheses
(complete + `|∇^ℓ Rm| ≤ C_ℓ` + `inj(O_k) ≥ ρ`) by the book's citations:

* `decay` — Cheeger–Gromov–Taylor injectivity-radius decay (`lbl384`):
  `inj(x) ≥ a·min{ρ,1}^n·e^{−C·d(x,O)}`, constants `a(n,C₀), C(n,C₀)`.  The Lean
  field matches the book form exactly.
* `pack` — Bishop–Gromov total packing count `A(r)` (`lbl387`): per-radius, no
  uniformity trap.  `MetricCompactBase` supplies this after each positive `D`;
  `MetricCompactnessInputs` stores only the family selected at the final `D`.
* `volume` — Bishop-Gromov intersection multiplicity, capped at containing
  scale `m * r ≤ r0` (the joint cap is mathematically necessary; see the
  structure docstring), with `stepA_cap_le` recording the producer's choice
  that `r0` dominates the largest Step A ratio times `λ[0]`.
* `realizes` — the supplied distance realizes the Riemannian emetric
  (plumbing; discharged at instantiation from the Hopf–Rinow realization).
* `normalBounds` — normal-coordinate metric `C^p` bounds (`lbl395`, [H6]
  Cor 4.12): per-center radius, `k`- and center-uniform constants (uniformity is
  genuine: the Jacobi-field ODE analysis depends only on the curvature bounds).
* `normalRadius` — compatibility of the preceding radius with the CGT profile:
  one fixed positive fraction of `mu (dist x O)` lies in every controlled
  normal-coordinate ball.  Its derived `gpRatio` also lies below the intrinsic
  `expRadiusGp`, using H6 metric equivalence at the chart origin.  This is the
  noncompact uniformity actually used by the construction; an absolute radius
  floor over all base points would be false.
## Deliberately NOT in the bundle (derived at assembly, or bundle-v2)

* **Construction-stage scale data** (`SigmaScaleField` and the
  per-configuration `CmHessianInput` / `StrictDistInput`): these are
  parameterized by Step A's constructed nets and Step C's configurations, so
  they cannot appear at sequence level.  The packing-local intrinsic and
  Euclidean-radius members are derived below as `gpScaleTail` and
  `radiusScaleTail` after `D`, `pb`, and `r` are fixed.  The legacy all-index
  `Item3RadiusInput` is compatibility-only.  Sigma-domain, full convexity,
  Hessian, and strict-distance geometry stays separate assembly work.
* **`IsometryDerivBounds`** (`lbl375`, [H6] §5): the isometry-derivative
  polynomial recursion is per-map-sequence; its bundle-v2 field shape is pinned
  by the B-loc bridge brick (see `CHAPTER4_PLAN.md`), not yet stated here.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- Compatibility between the CGT injectivity profile and the source radius of
the normal-coordinate metric estimates.

The fixed positive ratio is global, while the actual lower bound is allowed to
decay with basepoint distance.  The same floor lies both in the ball carrying
the metric estimates and in the named smooth exponential-chart ball.  This is
the H6-compatible noncompact substitute for an unjustified absolute radius
floor. -/
structure NormalRadiusProfile
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X)
    (hb : NormalCoordMetricBoundInput (I := I) X) where
  ratio : Real
  ratio_pos : 0 < ratio
  le_radius : ∀ k x,
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) ≤ hb.radius k x
  le_exp_radius : ∀ k x,
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) ≤
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x

namespace NormalRadiusProfile

/-- Reindex a normal-coordinate radius profile along a subsequence. -/
def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (f : Nat → Nat) :
    NormalRadiusProfile (hd.subseq f) (hb.subseq f) where
  ratio := h.ratio
  ratio_pos := h.ratio_pos
  le_radius := by
    intro k x
    change h.ratio * hd.mu (hd.dist (f k) x (X.obj (f k)).basepoint) ≤
      hb.radius (f k) x
    exact h.le_radius (f k) x
  le_exp_radius := by
    intro k x
    letI : TopologicalSpace (X.obj (f k)).M := (X.obj (f k)).topology
    letI : ChartedSpace H (X.obj (f k)).M := (X.obj (f k)).charted
    letI : IsManifold I ∞ (X.obj (f k)).M := (X.obj (f k)).smooth
    letI : T2Space (TangentBundle I (X.obj (f k)).M) :=
      (X.obj (f k)).t2TangentBundle
    change h.ratio * hd.mu (hd.dist (f k) x (X.obj (f k)).basepoint) ≤
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj (f k)).metric x
    exact h.le_exp_radius (f k) x

/-- The relative radius coefficient that also fits inside the intrinsic
`g_p`-radius. -/
def gpRatio
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) : Real :=
  Real.sqrt (1 / 2 : Real) * h.ratio

/-- The intrinsic-radius profile coefficient is strictly positive. -/
theorem gpRatio_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) : 0 < h.gpRatio := by
  rw [gpRatio]
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) h.ratio_pos

/-- The intrinsic-radius coefficient is no larger than the original normal
coordinate profile coefficient. -/
theorem gpRatio_le_ratio
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) : h.gpRatio ≤ h.ratio := by
  rw [gpRatio]
  have hsqrt : Real.sqrt (1 / 2 : Real) ≤ 1 :=
    Real.sqrt_le_one.mpr (by norm_num)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hsqrt h.ratio_pos.le

/-- The profile gives a positive source-radius floor on each fixed
basepoint-distance sublevel. -/
theorem floor_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real) :
    0 < h.ratio * hd.mu R :=
  mul_pos h.ratio_pos (hd.mu_pos R)

/-- On a fixed basepoint-distance sublevel, the profile floor lies inside the
normal-coordinate control radius. -/
theorem floor_le_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    h.ratio * hd.mu R ≤ hb.radius k x := by
  calc
    h.ratio * hd.mu R ≤
        h.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ ≤ hb.radius k x := h.le_radius k x

/-- On a fixed basepoint-distance sublevel, the profile floor also lies in the
named smooth exponential-chart ball. -/
theorem floor_le_exp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    h.ratio * hd.mu R ≤
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  calc
    h.ratio * hd.mu R ≤
        h.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ ≤ Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x :=
      h.le_exp_radius k x

/-- On a fixed basepoint-distance sublevel, the strengthened H6 profile also
lies inside the intrinsic `g_p` exponential radius. -/
theorem floor_le_expGp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    h.gpRatio * hd.mu R ≤
      Geometry.Riemannian.expRadiusGp (I := I) (X.obj k).metric x := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  rw [gpRatio, Geometry.Riemannian.expRadiusGp]
  calc
    Real.sqrt (1 / 2 : Real) * h.ratio * hd.mu R =
        Real.sqrt (1 / 2 : Real) * (h.ratio * hd.mu R) := by ring
    _ ≤ Real.sqrt (Geometry.Riemannian.gpCoerciveConst
          (I := I) (X.obj k).metric x) * (h.ratio * hd.mu R) :=
      mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (hb.half_le_gpConst k x)) (h.floor_pos R).le
    _ ≤ Real.sqrt (Geometry.Riemannian.gpCoerciveConst
          (I := I) (X.obj k).metric x) *
          Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x :=
      mul_le_mul_of_nonneg_left (h.floor_le_exp hx) (Real.sqrt_nonneg _)

/-- Choosing the covering divisor larger than `c / ratio` places the scaled
covering radius strictly below the profile floor. -/
theorem mul_lambda_lt_floor
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.ratio * D) :
    c * hd.lambda D R < h.ratio * hd.mu R := by
  rw [InjRadiusDecayInput.lambda]
  calc
    c * (hd.mu R / D) = (c / D) * hd.mu R := by ring
    _ < h.ratio * hd.mu R :=
      mul_lt_mul_of_pos_right ((div_lt_iff₀ hD).2 hc) (hd.mu_pos R)

/-- On a fixed basepoint-distance sublevel, the same divisor choice places the
scaled covering radius inside every controlled normal-coordinate ball. -/
theorem mul_lambda_lt_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.ratio * D)
    {k : Nat} {x : (X.obj k).M}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    c * hd.lambda D R < hb.radius k x :=
  (h.mul_lambda_lt_floor hD hc).trans_le (h.floor_le_radius hx)

/-- On a fixed basepoint-distance sublevel, the same divisor choice places the
scaled covering radius inside the named smooth exponential-chart ball. -/
theorem mul_lambda_lt_exp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.ratio * D)
    {k : Nat} {x : (X.obj k).M}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    c * hd.lambda D R <
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  exact (h.mul_lambda_lt_floor hD hc).trans_le (h.floor_le_exp hx)

/-- Choosing the covering divisor larger than `c / gpRatio` places the scaled
covering radius inside every controlled intrinsic `g_p` exponential ball. -/
theorem mul_lambda_lt_expGp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.gpRatio * D)
    {k : Nat} {x : (X.obj k).M}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    c * hd.lambda D R <
      Geometry.Riemannian.expRadiusGp (I := I) (X.obj k).metric x := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  have hfloor : c * hd.lambda D R < h.gpRatio * hd.mu R := by
    rw [InjRadiusDecayInput.lambda]
    calc
      c * (hd.mu R / D) = (c / D) * hd.mu R := by ring
      _ < h.gpRatio * hd.mu R :=
        mul_lt_mul_of_pos_right ((div_lt_iff₀ hD).2 hc) (hd.mu_pos R)
  exact hfloor.trans_le (h.floor_le_expGp hx)

/-- On the finite family of slots selected after packing, the item-3 intrinsic
radius inequality holds eventually along the net-limit subsequence.  The factor
`8` is the exact budget produced by the lower half of `lambda_window`. -/
theorem gpScaleTail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D : Real} (hD : 0 < D)
    (h8 : (8 : Real) < h.gpRatio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    Item3GpScaleTail (I := I) hd D P L pb r := by
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  calc
    4 * L.lamInf (γ : Nat) = 8 * (L.lamInf (γ : Nat) / 2) := by ring
    _ ≤ 8 * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      mul_le_mul_of_nonneg_left
        (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by norm_num)
    _ < Geometry.Riemannian.expRadiusGp
          (I := I) (X.obj (L.φ n)).metric c :=
      h.mul_lambda_lt_expGp (D := D) (c := 8)
        (R := seqRadius hd D P (L.φ n) (γ : Nat)) hD h8 hx

/-- The same lower half of `lambda_window` places half of any item-3 radius
inside the intrinsic `g_p` exponential ball.  The hypothesis is expressed in
the original normal-radius ratio: the numerical inequality
`sqrt (1 / 2) > 1 / 2` converts it to the strengthened `gpRatio` budget. -/
theorem halfGpScaleTail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D a : Real} (hD : 0 < D)
    (ha : 0 < a) (haRatio : 2 * a < h.ratio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ n in atTop, ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
      seqCenter hd D P (L.φ n) (γ : Nat) = some c →
        letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
        letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
        letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
        letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
        letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
          (X.obj (L.φ n)).t2TangentBundle
        (a / 2) * L.lamInf (γ : Nat) <
          Geometry.Riemannian.expRadiusGp
            (I := I) (X.obj (L.φ n)).metric c := by
  have hsqrt : (1 / 2 : Real) < Real.sqrt (1 / 2 : Real) := by
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
    have hsqrtNonneg := Real.sqrt_nonneg (1 / 2 : Real)
    nlinarith
  have hratioD : 0 < h.ratio * D := mul_pos h.ratio_pos hD
  have haGp : a < h.gpRatio * D := by
    calc
      a < (1 / 2 : Real) * (h.ratio * D) := by nlinarith
      _ < Real.sqrt (1 / 2 : Real) * (h.ratio * D) :=
        mul_lt_mul_of_pos_right hsqrt hratioD
      _ = h.gpRatio * D := by rw [gpRatio]; ring
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  calc
    (a / 2) * L.lamInf (γ : Nat) =
        a * (L.lamInf (γ : Nat) / 2) := by ring
    _ ≤ a * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      mul_le_mul_of_nonneg_left
        (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) ha.le
    _ < Geometry.Riemannian.expRadiusGp
          (I := I) (X.obj (L.φ n)).metric c :=
      h.mul_lambda_lt_expGp (D := D) (c := a)
        (R := seqRadius hd D P (L.φ n) (γ : Nat)) hD haGp hx

/-- On the finite packing family, the H6 metric-control radius eventually
contains every ball of radius `a * lamInf`. -/
theorem metricScaleTail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D a : Real} (hD : 0 < D)
    (ha : 0 < a) (haRatio : 2 * a < h.ratio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ n in atTop, ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
      seqCenter hd D P (L.φ n) (γ : Nat) = some c →
        a * L.lamInf (γ : Nat) ≤ hb.radius (L.φ n) c := by
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  calc
    a * L.lamInf (γ : Nat) =
        (2 * a) * (L.lamInf (γ : Nat) / 2) := by ring
    _ ≤ (2 * a) * hd.lambda D
        (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      mul_le_mul_of_nonneg_left
        (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by positivity)
    _ ≤ h.ratio * hd.mu
        (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      (h.mul_lambda_lt_floor hD haRatio).le
    _ ≤ h.ratio * hd.mu
        (hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ ≤ hb.radius (L.φ n) c := h.le_radius (L.φ n) c

/-- On the finite packing family, a radius `a * lamInf` eventually lies below
both the pointwise injectivity radius and the smooth exponential-chart radius.
The two factor-`2` budgets are exactly the loss in `lambda_window`. -/
theorem radiusScaleTail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D a : Real} (hD : 0 < D) (ha : 0 < a)
    (haD : 2 * a < D) (haRatio : 2 * a < h.ratio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    Item3RadiusTail (I := I) hd D P L pb r a := by
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  have hrad_pos : 0 < a * L.lamInf (γ : Nat) :=
    mul_pos ha (hd.lambda_pos hD (L.rInf (γ : Nat)))
  have hrad_mu : a * L.lamInf (γ : Nat) <
      hd.mu (seqRadius hd D P (L.φ n) (γ : Nat)) := by
    calc
      a * L.lamInf (γ : Nat) =
          (2 * a) * (L.lamInf (γ : Nat) / 2) := by ring
      _ ≤ (2 * a) * hd.lambda D
          (seqRadius hd D P (L.φ n) (γ : Nat)) :=
        mul_le_mul_of_nonneg_left
          (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by positivity)
      _ < D * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) :=
        mul_lt_mul_of_pos_right haD
          (hd.lambda_pos hD (seqRadius hd D P (L.φ n) (γ : Nat)))
      _ = hd.mu (seqRadius hd D P (L.φ n) (γ : Nat)) := by
        rw [InjRadiusDecayInput.lambda]
        exact mul_div_cancel₀ _ hD.ne'
  have hmu := hd.mu_hasInj_of_le hx
  rw [hasInjRadiusAt_iff] at hmu
  have hinj : ENNReal.ofReal (a * L.lamInf (γ : Nat)) <
      Geometry.Riemannian.injRadius (I := I) (X.obj (L.φ n)).metric c :=
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrad_pos.le).2 hrad_mu).trans_le hmu.2
  have hrad_lambda : a * L.lamInf (γ : Nat) ≤
      (2 * a) * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) := by
    calc
      a * L.lamInf (γ : Nat) =
          (2 * a) * (L.lamInf (γ : Nat) / 2) := by ring
      _ ≤ (2 * a) * hd.lambda D
          (seqRadius hd D P (L.φ n) (γ : Nat)) :=
        mul_le_mul_of_nonneg_left
          (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by positivity)
  have hexp := h.mul_lambda_lt_exp (D := D) (c := 2 * a)
    (R := seqRadius hd D P (L.φ n) (γ : Nat)) hD haRatio hx
  exact ⟨hinj, hrad_lambda.trans hexp.le⟩

end NormalRadiusProfile

/-- The `D`-independent producer data for Chapter 4 metric compactness.

The total packing bound is supplied as a family because its counting function
may depend on the covering divisor.  The divisor is chosen only after all
scalar scale constraints are known; `MetricCompactnessInputs.ofBase` then
instantiates this family at that single value. -/
structure MetricCompactBase
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  /-- A0 (`lbl384`): Cheeger–Gromov–Taylor injectivity-radius decay. -/
  decay : InjRadiusDecayInput (I := I) X
  /-- `lbl387`, uniformly available after each positive divisor is chosen. -/
  pack : ∀ D : Real, 0 < D → decay.PackingBound D
  /-- A0': Bishop–Gromov intersection multiplicity at small scales. -/
  volume : VolumeComparisonInput (I := I) X
  /-- The two Bishop–Gromov inputs quantify over the same supplied distance. -/
  dist_eq : volume.dist = decay.dist
  /-- The supplied distance realizes the Riemannian emetric. -/
  realizes : decay.RealizesEdist
  /-- `lbl395` ([H6] Cor 4.12): normal-coordinate metric `C^p` bounds. -/
  normalBounds : NormalCoordMetricBoundInput (I := I) X
  /-- H6/CGT compatibility at a fixed positive fraction of the decay profile. -/
  normalRadius : NormalRadiusProfile decay normalBounds

namespace MetricCompactBase

/-- A single sufficiently large divisor simultaneously fits one supplied
`gpRatio` scale budget (which may aggregate finitely many constants) and the
existing Step A multiplicity cap. -/
theorem exists_largeD
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c : Real) :
    ∃ D : Real, 1 < D ∧
      b.decay.mu 0 ≤ D ∧
      c < b.normalRadius.gpRatio * D ∧
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) *
        b.decay.lambda D 0 ≤ b.volume.r0 := by
  let q : Real :=
    b.decay.a * (min b.decay.baseInj.ρ 1) ^ (Module.finrank Real E)
  let K : Real := max 4 (50 * Real.exp (b.decay.C * 20))
  let B : Real := max 1
    (max q (max (K * q / b.volume.r0) (c / b.normalRadius.gpRatio)))
  let D : Real := B + 1
  have hB_lt : B < D := by
    dsimp only [D]
    linarith
  have honeB : (1 : Real) ≤ B := by
    dsimp only [B]
    exact le_max_left _ _
  have hqB : q ≤ B := by
    dsimp only [B]
    exact (le_max_left q _).trans (le_max_right 1 _)
  have hcapB : K * q / b.volume.r0 ≤ B := by
    dsimp only [B]
    exact ((le_max_left (K * q / b.volume.r0) _).trans
      (le_max_right q _)).trans (le_max_right 1 _)
  have hcB : c / b.normalRadius.gpRatio ≤ B := by
    dsimp only [B]
    exact ((le_max_right (K * q / b.volume.r0) _).trans
      (le_max_right q _)).trans (le_max_right 1 _)
  have hD_one : (1 : Real) < D := honeB.trans_lt hB_lt
  have hD : 0 < D := zero_lt_one.trans hD_one
  have hqD : q ≤ D := hqB.trans hB_lt.le
  have hmuD : b.decay.mu 0 ≤ D := by
    simpa only [InjRadiusDecayInput.mu, q, mul_zero, Real.exp_zero, mul_one]
      using hqD
  have hlam_le : b.decay.lambda D 0 ≤ 1 :=
    b.decay.lambda_le_one_at_zero (by simpa only [q] using hqD)
  have hlam_nonneg : 0 ≤ b.decay.lambda D 0 :=
    (b.decay.lambda_pos hD 0).le
  have harg :
      b.decay.C * (20 * b.decay.lambda D 0) ≤ b.decay.C * 20 := by
    have h20 : 20 * b.decay.lambda D 0 ≤ (20 : Real) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlam_le (by norm_num : (0 : Real) ≤ 20)
    exact mul_le_mul_of_nonneg_left h20 b.decay.C_nonneg
  have hfac :
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) ≤ K := by
    dsimp only [K]
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr harg) (by norm_num))
  have hKq : K * q < D * b.volume.r0 :=
    (div_lt_iff₀ b.volume.r0_pos).1 (hcapB.trans_lt hB_lt)
  have hKlam : K * b.decay.lambda D 0 < b.volume.r0 := by
    calc
      K * b.decay.lambda D 0 = K * q / D := by
        dsimp only [InjRadiusDecayInput.lambda, InjRadiusDecayInput.mu, q]
        simp only [mul_zero, Real.exp_zero, mul_one]
        ring
      _ < b.volume.r0 := (div_lt_iff₀ hD).2 (by
        simpa only [mul_comm] using hKq)
  have hc : c < b.normalRadius.gpRatio * D := by
    simpa only [mul_comm] using
      (div_lt_iff₀ b.normalRadius.gpRatio_pos).1 (hcB.trans_lt hB_lt)
  refine ⟨D, hD_one, hmuD, hc, ?_⟩
  exact (mul_le_mul_of_nonneg_right hfac hlam_nonneg).trans hKlam.le

/-- Choose one divisor before packing so that the intrinsic `g_p` and item-3
exponential-ball scales fit the available normal,
comparison, and injectivity radii, while retaining the Step A cap. -/
theorem exists_item3D
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c₀ : Real) :
    ∃ D : Real, 1 < D ∧
      b.decay.mu 0 ≤ D ∧
      c₀ < b.normalRadius.gpRatio * D ∧
      (8 : Real) < b.normalRadius.gpRatio * D ∧
      (16 : Real) < b.normalRadius.ratio * D ∧
      2 * item3RadiusFactor b.decay D < D ∧
      2 * item3RadiusFactor b.decay D < b.normalRadius.ratio * D ∧
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) *
        b.decay.lambda D 0 ≤ b.volume.r0 := by
  let Q : Real := 410 * Real.exp (b.decay.C * 20)
  let c : Real := max c₀ (max 8
    (max Q (Q * b.normalRadius.gpRatio)))
  obtain ⟨D, hD_one, hmuD, hc, hcap⟩ := b.exists_largeD c
  have hD : 0 < D := zero_lt_one.trans hD_one
  have hc₀c : c₀ ≤ c := by
    dsimp only [c]
    exact le_max_left _ _
  have h8c : (8 : Real) ≤ c := by
    dsimp only [c]
    exact (le_max_left (8 : Real) _).trans (le_max_right c₀ _)
  have hQc : Q ≤ c := by
    dsimp only [c]
    exact ((le_max_left Q _).trans (le_max_right 8 _)).trans
      (le_max_right c₀ _)
  have hQgc : Q * b.normalRadius.gpRatio ≤ c := by
    dsimp only [c]
    exact ((le_max_right Q _).trans (le_max_right 8 _)).trans
      (le_max_right c₀ _)
  have hc₀ : c₀ < b.normalRadius.gpRatio * D := hc₀c.trans_lt hc
  have h8 : (8 : Real) < b.normalRadius.gpRatio * D := h8c.trans_lt hc
  have hQgp : Q < b.normalRadius.gpRatio * D := hQc.trans_lt hc
  have hQg : Q * b.normalRadius.gpRatio <
      b.normalRadius.gpRatio * D := hQgc.trans_lt hc
  have hQD : Q < D := by
    exact lt_of_mul_lt_mul_right (by simpa only [mul_comm] using hQg)
      b.normalRadius.gpRatio_pos.le
  have hQratio : Q < b.normalRadius.ratio * D := by
    exact hQgp.trans_le (mul_le_mul_of_nonneg_right
      b.normalRadius.gpRatio_le_ratio hD.le)
  have h16Q : (16 : Real) ≤ Q := by
    dsimp only [Q]
    have hexp : (1 : Real) ≤ Real.exp (b.decay.C * 20) :=
      Real.one_le_exp (mul_nonneg b.decay.C_nonneg (by norm_num))
    calc
      (16 : Real) ≤ 410 * 1 := by norm_num
      _ ≤ 410 * Real.exp (b.decay.C * 20) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
  have h16 : (16 : Real) < b.normalRadius.ratio * D :=
    h16Q.trans_lt hQratio
  have hqD :
      b.decay.a * (min b.decay.baseInj.ρ 1) ^ (Module.finrank Real E) ≤ D := by
    simpa only [InjRadiusDecayInput.mu, mul_zero, Real.exp_zero, mul_one]
      using hmuD
  have hlam_le : b.decay.lambda D 0 ≤ 1 :=
    b.decay.lambda_le_one_at_zero hqD
  have harg :
      b.decay.C * (20 * b.decay.lambda D 0) ≤ b.decay.C * 20 := by
    have h20 : 20 * b.decay.lambda D 0 ≤ (20 : Real) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlam_le (by norm_num : (0 : Real) ≤ 20)
    exact mul_le_mul_of_nonneg_left h20 b.decay.C_nonneg
  have hfac : 2 * item3RadiusFactor b.decay D ≤ Q := by
    dsimp only [item3RadiusFactor, Q]
    calc
      2 * (205 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) =
          410 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0)) := by ring
      _ ≤ 410 * Real.exp (b.decay.C * 20) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
  exact ⟨D, hD_one, hmuD, hc₀, h8, h16, hfac.trans_lt hQD,
    hfac.trans_lt hQratio, hcap⟩

end MetricCompactBase

/-- The bundled Chapter 4 book-external inputs for MSM135 Theorem 3.9.

The geometric fields are the theorems cited externally by the book
(Cheeger–Gromov–Taylor, Bishop–Gromov, and [H6] Cor 4.12).  The
fixed-divisor scale compatibility is now produced in-tree from
`MetricCompactBase.exists_largeD`; it is not an additional book input.  See the
module docstring for the per-field mathematical audit. -/
structure MetricCompactnessInputs
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  /-- A0 (`lbl384`): Cheeger–Gromov–Taylor injectivity-radius decay. -/
  decay : InjRadiusDecayInput (I := I) X
  /-- The good-covering scale divisor (`λ = μ/D`); the assembly chooses it
  large against the relative normal-coordinate radius profile. -/
  D : Real
  hD : 0 < D
  /-- `lbl387`: Bishop–Gromov total packing count `A(r)`. -/
  pack : decay.PackingBound D
  /-- A0': Bishop-Gromov intersection multiplicity, capped at `m * r ≤ r0`. -/
  volume : VolumeComparisonInput (I := I) X
  /-- The two Bishop–Gromov inputs quantify over the same supplied distance. -/
  dist_eq : volume.dist = decay.dist
  /-- Producer compatibility: the multiplicity cap dominates the largest Step A
  ratio times the largest packing scale `λ[0]`. -/
  stepA_cap_le :
    max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
      decay.lambda D 0 <= volume.r0
  /-- The supplied distance realizes the Riemannian emetric. -/
  realizes : decay.RealizesEdist
  /-- `lbl395` ([H6] Cor 4.12): normal-coordinate metric `C^p` bounds. -/
  normalBounds : NormalCoordMetricBoundInput (I := I) X
  /-- H6/CGT compatibility: the controlled normal-coordinate radius contains a
  fixed positive fraction of the injectivity profile. -/
  normalRadius : NormalRadiusProfile decay normalBounds

namespace MetricCompactnessInputs

/-- Instantiate the fixed-divisor consumer bundle from the `D`-independent
producer data once the scalar cap has been verified. -/
def ofBase
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (D : Real) (hD : 0 < D)
    (hcap :
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) *
        b.decay.lambda D 0 ≤ b.volume.r0) :
    MetricCompactnessInputs (I := I) X where
  decay := b.decay
  D := D
  hD := hD
  pack := b.pack D hD
  volume := b.volume
  dist_eq := b.dist_eq
  stepA_cap_le := hcap
  realizes := b.realizes
  normalBounds := b.normalBounds
  normalRadius := b.normalRadius

/-- Choose the divisor once, instantiate its packing bound, and return the
existing fixed-divisor consumer bundle with the requested scalar budget. -/
theorem exists_ofBase
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c : Real) :
    ∃ inp : MetricCompactnessInputs (I := I) X,
      1 < inp.D ∧ inp.decay.mu 0 ≤ inp.D ∧
        c < inp.normalRadius.gpRatio * inp.D := by
  obtain ⟨D, hD_one, hmuD, hc, hcap⟩ := b.exists_largeD c
  have hD : 0 < D := zero_lt_one.trans hD_one
  refine ⟨ofBase b D hD hcap, ?_, ?_, ?_⟩
  · exact hD_one
  · exact hmuD
  · exact hc

/-- Choose the divisor with all current item-3 scale budgets and instantiate
the original fixed-divisor consumer bundle at that same value. -/
theorem exists_item3OfBase
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c₀ : Real) :
    ∃ inp : MetricCompactnessInputs (I := I) X,
      1 < inp.D ∧ inp.decay.mu 0 ≤ inp.D ∧
      c₀ < inp.normalRadius.gpRatio * inp.D ∧
      (8 : Real) < inp.normalRadius.gpRatio * inp.D ∧
      (16 : Real) < inp.normalRadius.ratio * inp.D ∧
      2 * item3RadiusFactor inp.decay inp.D < inp.D ∧
      2 * item3RadiusFactor inp.decay inp.D <
        inp.normalRadius.ratio * inp.D := by
  obtain ⟨D, hD_one, hmuD, hc₀, h8, h16, hradD, hradRatio, hcap⟩ :=
    b.exists_item3D c₀
  have hD : 0 < D := zero_lt_one.trans hD_one
  refine ⟨ofBase b D hD hcap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hD_one
  · exact hmuD
  · exact hc₀
  · exact h8
  · exact h16
  · exact hradD
  · exact hradRatio

/-- Convert the arbitrary aggregate budget returned by the one-shot divisor
selector into the slotwise physical-cage scale inequality. -/
theorem physScale_of_extra
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) {aMin : Real}
    (haMin : 0 < aMin)
    (hextra :
      (8 * Real.exp inp.decay.C / aMin) * inp.normalRadius.gpRatio <
        inp.normalRadius.gpRatio * inp.D) :
    8 * Real.exp inp.decay.C < aMin * inp.D := by
  have hD : 8 * Real.exp inp.decay.C / aMin < inp.D := by
    exact lt_of_mul_lt_mul_right
      (by simpa only [mul_comm] using hextra) inp.normalRadius.gpRatio_pos.le
  simpa only [mul_comm] using (div_lt_iff₀ haMin).1 hD

/-- The fixed-divisor bundle and its scalar budgets produce both finite-slot
item-3 scale tails after the net limit and packing range are fixed. -/
theorem item3ScaleTails
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) inp.decay inp.D P) (r : Real) :
    Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r ∧
      Item3RadiusTail (I := I) inp.decay inp.D P L inp.pack r
        (item3RadiusFactor inp.decay inp.D) := by
  exact ⟨inp.normalRadius.gpScaleTail inp.hD h8 P inp.realizes L inp.pack r,
    inp.normalRadius.radiusScaleTail inp.hD
      (item3Factor_pos inp.decay inp.D) hradD hradRatio
      P inp.realizes L inp.pack r⟩

/-- Build the conditional compactness input bundle from an explicit uniform
local-volume packing producer.

This keeps the public `MetricCompactnessInputs.volume` field as the Step A
consumer shape `VolumeComparisonInput`, while allowing callers to supply the
more precise uniform local-volume data checked by `UniformBallPack.toVCInput`. -/
def ofUniformVolume
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (decay : InjRadiusDecayInput (I := I) X)
    (D : Real) (hD : 0 < D)
    (pack : decay.PackingBound D)
    (vol : UniformBallPack (I := I) X)
    (dist_eq : vol.dist = decay.dist)
    (stepA_cap_le :
      max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
        decay.lambda D 0 ≤ vol.r0)
    (realizes : decay.RealizesEdist)
    (normalBounds : NormalCoordMetricBoundInput (I := I) X)
    (normalRadius : NormalRadiusProfile decay normalBounds) :
    MetricCompactnessInputs (I := I) X where
  decay := decay
  D := D
  hD := hD
  pack := pack
  volume := vol.toVCInput
  dist_eq := by
    change vol.dist = decay.dist
    exact dist_eq
  stepA_cap_le := by
    change max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
      decay.lambda D 0 ≤ vol.r0
    exact stepA_cap_le
  realizes := realizes
  normalBounds := normalBounds
  normalRadius := normalRadius

/-- Reindex the conditional compactness input bundle along a subsequence. -/
def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) (f : Nat -> Nat) :
    MetricCompactnessInputs (I := I) (X.subseq f) where
  decay := inp.decay.subseq f
  D := inp.D
  hD := inp.hD
  pack := inp.pack.subseq f
  volume := inp.volume.subseq f
  dist_eq := by
    funext k x y
    change inp.volume.dist (f k) x y = inp.decay.dist (f k) x y
    rw [inp.dist_eq]
  stepA_cap_le := by
    simpa [InjRadiusDecayInput.subseq, InjRadiusDecayInput.lambda, InjRadiusDecayInput.mu]
      using inp.stepA_cap_le
  realizes := inp.realizes.subseq f
  normalBounds := inp.normalBounds.subseq f
  normalRadius := inp.normalRadius.subseq f

/-- The Step A `m = 4` multiplicity cap extracted from the bundled maximum cap.

This is the exact cap needed by `net_multiplicity` at scale `lambda[0]`. -/
theorem cap_four
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) :
    (4 : Real) * inp.decay.lambda inp.D 0 <= inp.volume.r0 := by
  have hlam : 0 <= inp.decay.lambda inp.D 0 :=
    (inp.decay.lambda_pos inp.hD 0).le
  have hle :
      (4 : Real) <=
        max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) :=
    le_max_left _ _
  exact (mul_le_mul_of_nonneg_right hle hlam).trans inp.stepA_cap_le

/-- The Step A `m = 4` multiplicity cap at any nonnegative radius argument.

This combines `cap_four` with monotonicity of `lambda`; it is the form used
when a net radius is known to be bounded by the base scale `lambda[0]`. -/
theorem cap_four_of_nonneg
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) {R : Real} (hR : 0 <= R) :
    (4 : Real) * inp.decay.lambda inp.D R <= inp.volume.r0 := by
  have hlam : inp.decay.lambda inp.D R <= inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_antitone inp.hD hR
  have hmul :
      (4 : Real) * inp.decay.lambda inp.D R <=
        (4 : Real) * inp.decay.lambda inp.D 0 :=
    mul_le_mul_of_nonneg_left hlam (by norm_num)
  exact hmul.trans inp.cap_four

/-- The Step A item-5 ratio cap extracted from the bundled maximum cap.

This is the exact cap hypothesis required by `NetLimitData.inter_count`. -/
theorem cap_inter
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) :
    (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) *
        inp.decay.lambda inp.D 0 <= inp.volume.r0 := by
  have hlam : 0 <= inp.decay.lambda inp.D 0 :=
    (inp.decay.lambda_pos inp.hD 0).le
  have hle :
      50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) <=
        max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) :=
    le_max_right _ _
  exact (mul_le_mul_of_nonneg_right hle hlam).trans inp.stepA_cap_le

/-- Bundle-level wrapper for Step A's net multiplicity estimate. -/
theorem net_mult
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) (k : Nat) {R : Real}
    (hR : 0 <= R) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (inp.decay.lambdaBall inp.D k))
    (hSR : ∀ x ∈ S, inp.decay.dist k x (X.obj k).basepoint <= R)
    (z : (X.obj k).M) (J : Finset ((X.obj k).M)) (hJS : ↑J ⊆ S)
    (hJz : ∀ x ∈ J, inp.decay.dist k x z <= 4 * inp.decay.lambda inp.D R) :
    J.card <= inp.volume.Imult 4 := by
  exact InjRadiusDecayInput.net_multiplicity
    inp.decay inp.D k inp.hD inp.realizes inp.volume inp.dist_eq R
    (inp.cap_four_of_nonneg hR) hS hSR z J hJS hJz

/-- Bundle-level wrapper for the Step A item-5 intersection count. -/
theorem inter_count
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (α : Nat) :
    ∀ᶠ k in atTop,
      ∀ xα : (X.obj (L.φ k)).M,
        seqCenter inp.decay inp.D P (L.φ k) α = some xα →
      ∀ J : Finset Nat,
        (∀ β ∈ J, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) →
        J.card <=
          inp.volume.Imult
            (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) := by
  exact NetLimitData.inter_count inp.decay inp.hD P L inp.realizes inp.pack
    inp.volume inp.dist_eq inp.cap_inter α

/-- Bundle-level wrapper for the Step A diagonal net datum. -/
theorem exists_net_data
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    Nonempty (NetLimitData inp.decay inp.D P) :=
  exists_netLimitData inp.decay inp.hD P

/-- Bundle-level wrapper for the stabilized Step A net datum. -/
theorem exists_stable_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      ∀ α β : Nat,
        (∀ᶠ k in atTop, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k)) :=
  exists_stableNetData inp.decay inp.hD P

/-- Bundle-level Step A net package: a stable diagonal net datum together with
the item-5 intersection bound supplied by the bundled volume input. -/
theorem exists_stepA_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      (∀ α β : Nat,
        (∀ᶠ k in atTop, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : (X.obj (L.φ k)).M,
            seqCenter inp.decay inp.D P (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) →
            J.card <=
              inp.volume.Imult
                (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)))) := by
  obtain ⟨L, hstable⟩ := inp.exists_stable_net P
  exact ⟨L, hstable, fun α => inp.inter_count P L α⟩

/-- The per-member proper metric realization supplied by the endpoint's
completeness and connectedness hypotheses. -/
noncomputable def properMetrics
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (_inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∀ k : Nat, ProperMetricOn (I := I) (X.obj k) :=
  fun k => properMetricOn (I := I) (X.obj k) (hcomplete.complete k) (hconn k)

/-- Endpoint-hypothesis wrapper for the Step A net package. -/
theorem stepA_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ L : NetLimitData inp.decay inp.D (inp.properMetrics hcomplete hconn),
      (∀ α β : Nat,
        (∀ᶠ k in atTop,
          BInter inp.decay inp.D (inp.properMetrics hcomplete hconn)
            L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop,
          ¬ BInter inp.decay inp.D (inp.properMetrics hcomplete hconn)
            L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : (X.obj (L.φ k)).M,
            seqCenter inp.decay inp.D (inp.properMetrics hcomplete hconn)
              (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J,
              BInter inp.decay inp.D (inp.properMetrics hcomplete hconn)
                L.lamInf α β (L.φ k)) →
            J.card <=
              inp.volume.Imult
                (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)))) :=
  inp.exists_stepA_net (inp.properMetrics hcomplete hconn)

/-- Endpoint-hypothesis wrapper for the Step A net package after reindexing by
a subsequence. -/
theorem stepA_net_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (f : Nat -> Nat) :
    ∃ L : NetLimitData (inp.subseq f).decay (inp.subseq f).D
        ((inp.subseq f).properMetrics (hcomplete.subseq f)
          (fun k => by
            simpa [PointedRiemannianSeq.subseq] using hconn (f k))),
      (∀ α β : Nat,
        (∀ᶠ k in atTop,
          BInter (inp.subseq f).decay (inp.subseq f).D
            ((inp.subseq f).properMetrics (hcomplete.subseq f)
              (fun k => by
                simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
            L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop,
          ¬ BInter (inp.subseq f).decay (inp.subseq f).D
            ((inp.subseq f).properMetrics (hcomplete.subseq f)
              (fun k => by
                simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
            L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : ((X.subseq f).obj (L.φ k)).M,
            seqCenter (inp.subseq f).decay (inp.subseq f).D
              ((inp.subseq f).properMetrics (hcomplete.subseq f)
                (fun k => by
                  simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
              (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J,
              BInter (inp.subseq f).decay (inp.subseq f).D
                ((inp.subseq f).properMetrics (hcomplete.subseq f)
                  (fun k => by
                    simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
                L.lamInf α β (L.φ k)) →
            J.card <=
              (inp.subseq f).volume.Imult
                (50 * Real.exp
                  ((inp.subseq f).decay.C *
                    (20 * (inp.subseq f).decay.lambda (inp.subseq f).D 0)))) := by
  exact (inp.subseq f).stepA_net (hcomplete.subseq f)
    (fun k => by
      simpa [PointedRiemannianSeq.subseq] using hconn (f k))

/-- **MSM135 Theorem 3.9, conditional form — the Chapter 4 working target.**
Compactness for complete pointed Riemannian manifolds with uniformly bounded
geometry and a basepoint injectivity-radius lower bound, given the bundled
book-external inputs.  The `sorry` is the Steps A→D assembly (good coverings →
local metrics/transition maps → center-of-mass averaging → direct limit); no
external mathematics hides in it beyond the bundle.

Connectedness is required by the Hopf–Rinow proper-realization step
(`properMetricOn`): on a disconnected member the Riemannian emetric is `⊤`
across components and no realizing proper distance exists.  (The book's
manifolds are connected by convention.) -/
def metricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (_inp : MetricCompactnessInputs (I := I) X)
    (_hcomplete : SeqMetricComplete (I := I) X)
    (_hgeom : SeqBoundedGeometry (I := I) X)
    (_hinj : BaseInjBound (I := I) X)
    (_hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactnessConclusion (I := I) X := by
  sorry

end MetricCompactnessInputs

end HCGCompactness
end DifferentialGeometry
