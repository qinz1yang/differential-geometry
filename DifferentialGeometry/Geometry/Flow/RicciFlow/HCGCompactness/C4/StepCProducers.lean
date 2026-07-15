import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveragePOU
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringItem3
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCTransitionRefine
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomDiagonal
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCPairTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSourceCover

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step C: the C3 producer join

This file wires the concrete Step-A/Step-B data into the abstract finite-hat
center-average convergence capstone `NetLimitData.unifHatCageSelfComp`
(`StepCAveragePOU.lean`).

## Step (1): the cage↔chart-image bridge

`properBallImgOfRad` — general Gauss-lemma bridge (sibling of
`properBallSrcOfRad`): a realized proper-metric closed ball of radius `R <
expRadiusGp` is carried by the normal chart into the Euclidean ball of radius
`expMapC2Radius`.  `hatCageImg` composes it with `hatCageInClosed` to give the
finite-hat cage image inclusion consumed by the capstone's domain inputs
(`hKU`/`hKV`) and by `existsTransUniv`'s `hUx`/`hVy`/`hmaps` obligations.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [Module.Finite Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- **Image form of `properBallSrcOfRad`.**  A realized proper-metric closed ball
`closedBall c R` with `R` strictly below the `g_p` radial normal radius
`expRadiusGp g c` is carried by the normal chart `normalChartAt g c` into the
Euclidean ball `ball 0 (expMapC2Radius g c)`.  Together with `properBallSrcOfRad`
(source membership) this pins both the chart domain and the chart-image radius
from the single scale input `R < expRadiusGp`.

Proof: for `q ∈ closedBall c R`, `dist c q ≤ R < expRadiusGp`, so
`metricBall_subset_normalBall` gives the chart vector `v` with `normalChartAt g c
q = v`, `√(g_c(v,v)) = dist c q < expRadiusGp`, and `‖v‖ < expMapC2Radius` via
`norm_lt_expMapC2Radius_of_sqrt_inner_lt` (the `g_p`-coercivity comparison). -/
theorem properBallImgOfRad
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    (NormalCoordinates.normalChartAt (I := I) Y.metric c) '' Metric.closedBall c R ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric c) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x v)
  rintro a ⟨q, hq, rfl⟩
  have hdist_le : dist c q ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hed : riemannianEDist I c q = ENNReal.ofReal (dist c q) := by
    have h := P.realizes c q
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c q ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]; exact ENNReal.ofReal_ne_top
  have hsmall : (riemannianEDist I c q).toReal < expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact lt_of_le_of_lt hdist_le hR
  obtain ⟨v, hv_tgt, _hv_dom, hv_len, hy_eq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  have hchart : NormalCoordinates.normalChartAt (I := I) Y.metric c q = v := by
    have hsymm : (NormalCoordinates.normalChartAt (I := I) Y.metric c).symm v = q := by
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Y.metric c hv_tgt]
      exact hy_eq.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt (I := I) Y.metric c).right_inv hv_tgt
  rw [Metric.mem_ball, dist_zero_right, hchart]
  have hsq : Real.sqrt (Y.metric.inner c v v) < expRadiusGp (I := I) Y.metric c := by
    rw [hv_len]; exact hsmall
  exact norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric c hsq

/-- **Coercive-tightened image form of `properBallImgOfRad`** (Ruling #4, no boundary analysis).
Same as `properBallImgOfRad` but into the *tighter* Euclidean ball `ball 0 σ` for any `σ` strictly
above `R / √(gpCoerciveConst g c)`.  The proof needs no strictness of the cage: from `dist c q ≤ R`
(closed ball) and the `g_p`-coercivity `gpCoerciveConst g c · ‖v‖² ≤ g_c(v,v)` we get
`√coercive · ‖v‖ ≤ √(g_c(v,v)) = dist c q ≤ R`, hence `‖v‖ ≤ R/√coercive < σ` by the strict
hypothesis.  This is the σ-refined cage-image bound `stepCJoin` consumes for `U γ := ball 0 (σ γ)`. -/
theorem properBallImgOfRad'
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R σ : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c)
    (hσ :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R / Real.sqrt (gpCoerciveConst (I := I) Y.metric c) < σ) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    (NormalCoordinates.normalChartAt (I := I) Y.metric c) '' Metric.closedBall c R ⊆
      Metric.ball (0 : E) σ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x v)
  rintro a ⟨q, hq, rfl⟩
  have hdist_le : dist c q ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hed : riemannianEDist I c q = ENNReal.ofReal (dist c q) := by
    have h := P.realizes c q
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c q ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]; exact ENNReal.ofReal_ne_top
  have hsmall : (riemannianEDist I c q).toReal < expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact lt_of_le_of_lt hdist_le hR
  obtain ⟨v, hv_tgt, _hv_dom, hv_len, hy_eq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  have hchart : NormalCoordinates.normalChartAt (I := I) Y.metric c q = v := by
    have hsymm : (NormalCoordinates.normalChartAt (I := I) Y.metric c).symm v = q := by
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Y.metric c hv_tgt]
      exact hy_eq.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt (I := I) Y.metric c).right_inv hv_tgt
  rw [Metric.mem_ball, dist_zero_right, hchart]
  have hcoerc : 0 < gpCoerciveConst (I := I) Y.metric c := gpCoerciveConst_pos (I := I) Y.metric c
  have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I) Y.metric c) := Real.sqrt_pos.mpr hcoerc
  have hcle : gpCoerciveConst (I := I) Y.metric c * ‖v‖ ^ 2 ≤ Y.metric.inner c v v :=
    gpCoerciveConst_le (I := I) Y.metric c v
  have hsqrt_le :
      Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖ ≤
        Real.sqrt (Y.metric.inner c v v) := by
    have hrw : Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖
        = Real.sqrt (gpCoerciveConst (I := I) Y.metric c * ‖v‖ ^ 2) := by
      rw [Real.sqrt_mul (le_of_lt hcoerc), Real.sqrt_sq (norm_nonneg v)]
    rw [hrw]
    exact Real.sqrt_le_sqrt hcle
  have hgc_le : Real.sqrt (Y.metric.inner c v v) ≤ R := by
    rw [hv_len, hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact hdist_le
  have hbound : ‖v‖ ≤ R / Real.sqrt (gpCoerciveConst (I := I) Y.metric c) := by
    rw [le_div_iff₀ hsc]
    calc ‖v‖ * Real.sqrt (gpCoerciveConst (I := I) Y.metric c)
        = Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖ := by ring
      _ ≤ Real.sqrt (Y.metric.inner c v v) := hsqrt_le
      _ ≤ R := hgc_le
  exact lt_of_le_of_lt hbound hσ

/-- **Finite-hat cage image inclusion.**  Under the packing-local `g_p` scale
fact `hR` (`4 λ^γ < expRadiusGp` at the live center), the
normal chart at `center γ` carries the canonical source cage into the Euclidean
`expMapC2Radius` ball.  Composes `hatCageInClosed` with `properBallImgOfRad`. -/
theorem hatCageImg (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) <
        expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma)) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ n)).metric (center gamma)) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  refine Set.Subset.trans
    (Set.image_mono
      (NetLimitData.hatCageInClosed (I := I) (X := X) hd P L pb r n gamma hcenter)) ?_
  exact properBallImgOfRad (I := I) (X.obj (L.φ n)) (P (L.φ n))
    (c := center gamma) (R := 4 * L.lamInf (gamma : Nat)) hR

/-- **Coercive-tightened cage image inclusion** (Ruling #4, GREEN — no boundary analysis).
The normal chart at `center γ` carries the canonical source cage into the open Euclidean ball
`ball 0 (σ γ)`, for any `σ γ` strictly above the coercive radius `4 λ^γ / √(gpCoerciveConst (center γ))`
(`hσ`).  This is the σ-refined `hcage` that `stepCJoin` consumes for `U γ := Metric.ball 0 (σ γ)`;
the strict scale hypothesis dissolves the open/closed-ball gap (`hatCageInClosed` gives the *closed*
`4 λ^γ` ball, and `properBallImgOfRad'`'s coercivity turns that into `‖v‖ ≤ 4 λ^γ/√coercive < σ γ`).
`hR : 4 λ^γ < expRadiusGp` is the chart-domain scale (`= √coercive · expMapC2Radius`); both `hR` and
`hσ` are packaged in the sibling `SigmaScaleField` (below). -/
theorem hatCageImg' (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (sigma : Fin (pb.A r) -> Real)
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) <
        expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma))
    (hσ :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) /
          Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ n)).metric (center gamma)) <
        sigma gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      Metric.ball (0 : E) (sigma gamma) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  refine Set.Subset.trans
    (Set.image_mono
      (NetLimitData.hatCageInClosed (I := I) (X := X) hd P L pb r n gamma hcenter)) ?_
  exact properBallImgOfRad' (I := I) (X.obj (L.φ n)) (P (L.φ n))
    (c := center gamma) (R := 4 * L.lamInf (gamma : Nat)) (σ := sigma gamma) hR hσ

/-- **σ-discharge of `stepCJoin`'s `hUx`/`hVy` domain-radius hypotheses** (Ruling #2 tail, green).
Given a per-hat radius family `σ` below the `expMapC2Radius` at every live center of every subsequence
index `k` (`hσ` — the `SigmaScaleField` upper bound, with `k`-independent `σ γ`), the domain
`U γ := Metric.ball 0 (σ γ)` sits inside the `expMapC2Radius`-ball that `stepCJoin`'s `hUx`/`hVy`
demand.  This is `Metric.ball_subset_ball` — the σ-parametric domain inputs are discharged from the
single scale field, no per-`k` threading.  (Instantiate with `x`/`y` for `hUx`/`hVy` respectively.) -/
theorem hUx_of_sigma (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M) (σ : Fin (pb.A r) -> Real)
    (hσ : forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)) :
    forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      Metric.ball (0 : E) (σ gamma) ⊆
        Metric.ball (0 : E) (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)) := by
  intro gamma k
  exact Metric.ball_subset_ball (hσ gamma k)

/-- The sigma-scale inequalities at one index of the net-limit subsequence. -/
def SigmaScaleAt (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (σ : Fin (pb.A r) -> Real) (n : Nat) : Prop :=
  forall gamma : Fin (pb.A r),
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) /
        Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ n)).metric (x gamma n)) < σ gamma ∧
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ n)).metric (x gamma n)

/-- The finite family of sigma-scale inequalities eventually holds along the
net-limit subsequence. -/
def SigmaScaleTail (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (σ : Fin (pb.A r) -> Real) : Prop :=
  ∀ᶠ n in Filter.atTop, SigmaScaleAt (I := I) hd P L pb r x σ n

/-- **The sibling `g_p`-scale field for the σ-domain discharge** (Ruling #4,
`lbl383` family).  A `k`-independent per-hat radius `σ γ` sandwiched, at every live center of
every subsequence index `k`, between the coercive cage radius and the chart `C²`-radius:
`4 λ^γ / √(gpCoerciveConst (x γ k)) < σ γ ≤ expMapC2Radius (x γ k)`.  The upper bound feeds
`hUx_of_sigma` (`hUx`/`hVy`), the strict lower bound feeds `hatCageImg'`'s `hσ`, and its
`expRadiusGp` consequence (`.expRadiusGp`) feeds `hatCageImg'`'s `hR` — so both cage-image and
domain hypotheses of `stepCJoin` come from this single honest field. -/
def SigmaScaleField (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M) (σ : Fin (pb.A r) -> Real) : Prop :=
  forall gamma : Fin (pb.A r), forall k : Nat,
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) /
        Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) < σ gamma ∧
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)

/-- Restrict an all-index sigma field to one sequence index. -/
theorem SigmaScaleField.at {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ) (n : Nat) :
    SigmaScaleAt (I := I) hd P L pb r x σ n := fun gamma => hfield gamma n

/-- An all-index sigma field gives the corresponding eventual tail. -/
theorem SigmaScaleField.to_tail {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ) :
    SigmaScaleTail (I := I) hd P L pb r x σ :=
  Filter.Eventually.of_forall hfield.at

/-- Reindex a sigma-scale tail along a further strict subsequence. -/
theorem SigmaScaleTail.subseq {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (htail : SigmaScaleTail (I := I) hd P L pb r x σ)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    SigmaScaleTail (I := I) hd P (L.subseq hψ) pb r
      (fun gamma k => x gamma (ψ k)) σ := by
  filter_upwards [hψ.tendsto_atTop.eventually htail] with n hn
  intro gamma
  exact hn gamma

/-- Shift past an eventual sigma tail to obtain an all-index field on one
strictly refined subsequence. -/
theorem SigmaScaleTail.exists_field
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (htail : SigmaScaleTail (I := I) hd P L pb r x σ) :
    ∃ ψ : Nat → Nat, ∃ hψ : StrictMono ψ,
      SigmaScaleField (I := I) hd P (L.subseq hψ) pb r
        (fun gamma k => x gamma (ψ k)) σ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htail
  let ψ : Nat → Nat := fun k => k + N
  have hψ : StrictMono ψ := by
    simpa only [ψ] using strictMono_id.add_const N
  refine ⟨ψ, hψ, ?_⟩
  intro gamma k
  exact hN (ψ k) (by simp only [ψ]; omega) gamma

/-- The `expRadiusGp` scale (`4 λ^γ < expRadiusGp`, `hatCageImg'`'s `hR`) is a consequence of the
sibling field: `4 λ^γ/√c < σ γ ≤ expMapC2Radius` gives `4 λ^γ < √c · expMapC2Radius = expRadiusGp`. -/
theorem SigmaScaleField.expRadiusGp {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M} {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ)
    (gamma : Fin (pb.A r)) (k : Nat) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) <
      expRadiusGp (I := I) (X.obj (L.φ k)).metric (x gamma k) := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
  obtain ⟨hlo, hhi⟩ := hfield gamma k
  have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) :=
    Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) (X.obj (L.φ k)).metric (x gamma k))
  have h1 : 4 * L.lamInf (gamma : Nat) /
      Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) <
      expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k) := lt_of_lt_of_le hlo hhi
  rw [div_lt_iff₀ hsc] at h1
  exact h1.trans_eq (mul_comm _ _)

/-- The H6 radius profile produces a uniform sigma tail at the canonical
totalized net centres, with `σ γ = 8 * λ^γ`. -/
theorem NormalRadiusProfile.sigmaCenterTail
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D : Real} (hD : 0 < D)
    (h16 : (16 : Real) < h.ratio * D)
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist)
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    SigmaScaleTail (I := I) hd P L pb r
      (fun gamma k => seqCenterD hd P L k (gamma : Nat))
      (fun gamma => 8 * L.lamInf (gamma : Nat)) := by
  have hwin : ∀ᶠ n in Filter.atTop, ∀ gamma ∈ Finset.range (pb.A r),
      L.lamInf gamma / 2 ≤
        hd.lambda D (seqRadius hd D P (L.φ n) gamma) :=
    (Filter.eventually_all_finset _).mpr fun gamma _ =>
      (L.lambda_window hd hD P gamma).mono fun _ hgamma => by
        simpa only [NetLimitData.lamInf] using hgamma.1
  filter_upwards [hwin] with n hn
  intro gamma
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hx : hd.dist (L.φ n) (seqCenterD hd P L n (gamma : Nat))
      (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (gamma : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n),
      ← seqCenterD_dist_eq hd P L n (gamma : Nat)]
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  constructor
  · have hhalf : (1 / 2 : Real) ≤ gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat)) :=
      hb.half_le_gpConst (L.φ n) (seqCenterD hd P L n (gamma : Nat))
    have hsqrt_half : (1 / 2 : Real) < Real.sqrt (1 / 2 : Real) := by
      have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
      have hn := Real.sqrt_nonneg (1 / 2 : Real)
      nlinarith
    have hsqrt : (1 / 2 : Real) < Real.sqrt (gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) :=
      hsqrt_half.trans_le (Real.sqrt_le_sqrt hhalf)
    have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) :=
      Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat)))
    have hlam : 0 < L.lamInf (gamma : Nat) :=
      hd.lambda_pos hD (L.rInf (gamma : Nat))
    apply (div_lt_iff₀ hsc).2
    have hfour : (4 : Real) < 8 * Real.sqrt (gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) := by
      nlinarith
    calc
      4 * L.lamInf (gamma : Nat) <
          (8 * Real.sqrt (gpCoerciveConst (I := I)
            (X.obj (L.φ n)).metric
              (seqCenterD hd P L n (gamma : Nat)))) *
            L.lamInf (gamma : Nat) :=
        mul_lt_mul_of_pos_right hfour hlam
      _ = (8 * L.lamInf (gamma : Nat)) *
          Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ n)).metric
            (seqCenterD hd P L n (gamma : Nat))) := by ring
  · calc
      8 * L.lamInf (gamma : Nat) =
          16 * (L.lamInf (gamma : Nat) / 2) := by ring
      _ ≤ 16 * hd.lambda D
          (seqRadius hd D P (L.φ n) (gamma : Nat)) :=
        mul_le_mul_of_nonneg_left
          (hn (gamma : Nat) (Finset.mem_range.mpr gamma.isLt)) (by norm_num)
      _ ≤ expMapC2Radius (I := I) (X.obj (L.φ n)).metric
          (seqCenterD hd P L n (gamma : Nat)) :=
        (h.mul_lambda_lt_exp (D := D) (c := 16)
          (R := seqRadius hd D P (L.φ n) (gamma : Nat)) hD h16 hx).le

/-- **Limit-membership bridge for the capstone's `hKV`.**  If the two-index Step-B
maps `B a` eventually carry `v` into a closed set `V'` and `B → Binf` in `C∞` on
compacts of `U ∋ v`, then the limit map lands in `V'` as well. -/
theorem binfMemClosed {U V' : Set E} {B : Nat -> E -> E} {Binf : E -> E}
    (hB : MapCInfConvOnCompacts U B Binf) {v : E} (hv : v ∈ U)
    (hV'closed : IsClosed V') (hmem : ∀ᶠ a in Filter.atTop, B a v ∈ V') :
    Binf v ∈ V' :=
  hV'closed.mem_of_tendsto (tendsto_of_cInf hB hv) hmem

/-- A nonzero normalized limit weight at a live target forces any convergent
source-to-target transition limit into the target six-lambda ball.  The proof
uses only target liveness; eventual interaction is supplied separately by the
sparse source-support producer. -/
theorem HasAtomWeightLim.binf_of_live
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (gamma : LiveSlot L inp.pack r)
    (Binf : E -> E)
    (hB : MapCInfConvOnCompacts U
      (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)))
      Binf)
    {z : E} (hz : z ∈ U)
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
        (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma.1 ≠ 0) :
    Binf z ∈ Metric.closedBall 0 (6 * L.lamInf (gamma.1 : Nat)) := by
  have hweightTail := hphi.tendsto_atTop.eventually
    (hlim.weight_ne_tail hz hweight)
  have hrad : Item3RadiusTail (I := I) inp.decay inp.D P L inp.pack r
      (item3RadiusFactor inp.decay inp.D) :=
    inp.normalRadius.radiusScaleTail inp.hD
      (item3Factor_pos inp.decay inp.D) hradD hradRatio
      P inp.realizes L inp.pack r
  have hradTail := hphi.tendsto_atTop.eventually hrad
  have hgpTail := hphi.tendsto_atTop.eventually hgp
  have hcenterTail := hphi.tendsto_atTop.eventually
    (seqCenterD_live inp.decay P L (gamma.1 : Nat) gamma.2)
  have hmem : ∀ᶠ k in Filter.atTop,
      normalTransition (I := I) (X.obj (L.φ (phi k)))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)) z ∈
        Metric.closedBall 0 (6 * L.lamInf (gamma.1 : Nat)) := by
    filter_upwards [hweightTail, hradTail, hgpTail, hcenterTail]
      with k hweightK hradK hgpK hcenterK
    letI : TopologicalSpace (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).topology
    letI : ChartedSpace H (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).charted
    letI : IsManifold I ∞ (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ (phi k))).M) :=
      (X.obj (L.φ (phi k))).t2TangentBundle
    have hExp : (1 : Real) ≤
        Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) := by
      rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr
        (mul_nonneg inp.decay.C_nonneg
          (by nlinarith [(inp.decay.lambda_pos inp.hD 0).le]))
    have hfactor : (8 : Real) ≤ item3RadiusFactor inp.decay inp.D := by
      rw [item3RadiusFactor]
      nlinarith
    have hC2 : 8 * L.lamInf (gamma.1 : Nat) ≤
        expMapC2Radius (I := I) (X.obj (L.φ (phi k))).metric
          (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)) :=
      (mul_le_mul_of_nonneg_right hfactor
        (inp.decay.lambda_pos inp.hD (L.rInf (gamma.1 : Nat))).le).trans
          (hradK gamma.1
            (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)) hcenterK).2
    exact Metric.ball_subset_closedBall
      (inp.weight_trans_small P L r (phi k) hgpK
        (fun j => seqCenterD inp.decay P L j (alpha.1 : Nat))
        (baseIndex inp.decay inp.realizes inp.pack hr) gamma.1 hC2 z hweightK)
  exact binfMemClosed hB hz Metric.isClosed_closedBall hmem

/-- Interacting-slot specialization of `binf_of_live`. -/
theorem HasAtomWeightLim.binf_of_slot
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (target : InterSlot L inp.pack r alpha)
    (Binf : InterSlot L inp.pack r alpha -> E -> E)
    (hB : MapCInfConvOnCompacts U
      (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
      (Binf target))
    {z : E} (hz : z ∈ U)
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
        (baseIndex inp.decay inp.realizes inp.pack hr)) z target.1.1 ≠ 0) :
    Binf target z ∈
      Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat)) := by
  exact hlim.binf_of_live inp hradD hradRatio P L r hr hgp alpha U aInf
    phi hphi target.1 (Binf target) hB hz hweight

/-- A nonzero normalized limit weight selects an interacting live target, and
the corresponding H6 transition limit lands in the closed six-lambda ball. -/
theorem HasAtomWeightLim.binf_of_weight
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        U (L.hatBall inp.decay inp.D P inp.pack r k alpha.1))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (Binf : InterSlot L inp.pack r alpha -> E -> E)
    (hB : forall target : InterSlot L inp.pack r alpha,
      MapCInfConvOnCompacts U
        (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
        (Binf target))
    {z : E} (hz : z ∈ U) (gamma : Fin (inp.pack.A r))
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
        (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma ≠ 0) :
    ∃ target : InterSlot L inp.pack r alpha,
      target.1.1 = gamma ∧
        Binf target z ∈ Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  have hdata := hlim
  dsimp only [HasAtomWeightLim] at hdata
  have hgammaLive : L.alive (gamma : Nat) = true := by
    cases hgamma : L.alive (gamma : Nat) with
    | false =>
        have haZero : aInf gamma = 0 := hdata.1 gamma hgamma
        have hnum : aInf gamma z ≠ 0 :=
          num_ne_of_cut_ne (num_ne_of_raw_ne hweight)
        exact False.elim (hnum (by rw [haZero]; rfl))
    | true => rfl
  have hinter : ∀ᶠ k in Filter.atTop,
      BInter inp.decay inp.D P L.lamInf
        (alpha.1 : Nat) (gamma : Nat) (L.φ k) :=
    hlim.binter_of_weight hgp alpha.1 gamma hz hsource hweight
  let target : InterSlot L inp.pack r alpha :=
    ⟨⟨gamma, hgammaLive⟩, hinter⟩
  refine ⟨target, rfl, ?_⟩
  simpa only [target] using
    (hlim.binf_of_slot inp hradD hradRatio P L r hr hgp alpha U aInf
      phi hphi target Binf (hB target) hz (by simpa only [target] using hweight))

/-- Extract one common H6 transition subsequence for every target interacting
with a fixed live source, while retaining the support-to-closed-ball readout for
the normalized atom limits on any smaller source domain. -/
theorem MetricCompactnessInputs.exists_supp_trans
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (hUsub : U ⊆ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        U (L.hatBall inp.decay inp.D P inp.pack r k alpha.1)) :
    ∃ phi : Nat -> Nat, StrictMono phi ∧
      ∃ Jinf : InterSlot L inp.pack r alpha -> E -> E,
      ∃ Jbarinf : InterSlot L inp.pack r alpha -> E -> E,
        (forall target : InterSlot L inp.pack r alpha,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          ContinuousOn (Jinf target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContinuousOn (Jbarinf target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
            (Jinf target) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
            (Jbarinf target) ∧
          (forall z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) ->
            Jinf target z ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) ->
              Jbarinf target (Jinf target z) = z) ∧
          (forall w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) ->
            Jbarinf target w ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) ->
              Jinf target (Jbarinf target w) = w)) ∧
        forall z : E, z ∈ U -> forall gamma : Fin (inp.pack.A r),
          rawWeights
            (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
              (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma ≠ 0 ->
            ∃ target : InterSlot L inp.pack r alpha,
              target.1.1 = gamma ∧
                Jinf target z ∈
                  Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  letI : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  obtain ⟨phi, hphi, Jinf, Jbarinf, hspec⟩ :=
    inp.exists_pair_trans hradD hradRatio P L r
      (fun _ : InterSlot L inp.pack r alpha => alpha)
      (fun target : InterSlot L inp.pack r alpha => target.1)
      (fun target : InterSlot L inp.pack r alpha => target.2)
  refine ⟨phi, hphi, Jinf, Jbarinf, hspec, ?_⟩
  intro z hz gamma hweight
  exact hlim.binf_of_weight inp hradD hradRatio P L r hr hgp alpha U aInf
    hsource phi hphi Jinf (fun target K hK hKU p =>
      (hspec target).2.2.2.2.1 K hK (hKU.trans hUsub) p)
    hz gamma hweight

/-- Extract one common H6 transition subsequence for the interacting targets of
every live source.  The dependent pair index avoids a second source-by-source
diagonal and retains each target in the original stabilized pair family. -/
theorem MetricCompactnessInputs.exists_supp_fin
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (U : LiveSlot L inp.pack r → Set E)
    (hUsub : ∀ alpha, U alpha ⊆
      Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (hlim : ∀ alpha,
      HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
        inp.pack r hr
        (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat))
        (U alpha) (aInf alpha))
    (hsource : ∀ alpha, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        (U alpha) (L.hatBall inp.decay inp.D P inp.pack r k alpha.1)) :
    ∃ phi : Nat → Nat, StrictMono phi ∧
      ∃ Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E,
      ∃ Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E,
        (∀ alpha target,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          ContinuousOn (Jinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContinuousOn (Jbarinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
            (Jinf alpha target) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
            (Jbarinf alpha target) ∧
          (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
            Jinf alpha target z ∈
                Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
              Jbarinf alpha target (Jinf alpha target z) = z) ∧
          (∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
            Jbarinf alpha target w ∈
                Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
              Jinf alpha target (Jbarinf alpha target w) = w)) ∧
        ∀ alpha z, z ∈ U alpha → ∀ gamma : Fin (inp.pack.A r),
          rawWeights
            (cutRaw
              (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
              (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
            z gamma ≠ 0 →
          ∃ target : InterSlot L inp.pack r alpha,
            target.1.1 = gamma ∧
              Jinf alpha target z ∈
                Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  let PairSlot := Σ alpha : LiveSlot L inp.pack r, InterSlot L inp.pack r alpha
  letI (alpha : LiveSlot L inp.pack r) : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  letI : Finite PairSlot := inferInstance
  obtain ⟨phi, hphi, J, Jbar, hspec⟩ :=
    inp.exists_pair_trans hradD hradRatio P L r
      (fun pair : PairSlot => pair.1)
      (fun pair : PairSlot => pair.2.1)
      (fun pair : PairSlot => pair.2.2)
  let Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => J ⟨alpha, target⟩
  let Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => Jbar ⟨alpha, target⟩
  refine ⟨phi, hphi, Jinf, Jbarinf, ?_, ?_⟩
  · intro alpha target
    exact hspec ⟨alpha, target⟩
  · intro alpha z hz gamma hweight
    exact (hlim alpha).binf_of_weight inp hradD hradRatio P L r hr hgp
      alpha (U alpha) (aInf alpha) (hsource alpha) phi hphi (Jinf alpha)
      (fun target K hK hKU p =>
        (hspec ⟨alpha, target⟩).2.2.2.2.1 K hK
          (hKU.trans (hUsub alpha)) p)
      hz gamma hweight

/-- Look up the unique interacting target carried by a fixed finite target
slot, when that slot belongs to the stabilized interaction family. -/
noncomputable def interSlot?
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r) (gamma : Fin (pb.A r)) :
    Option (InterSlot L pb r alpha) := by
  classical
  exact
    if h : ∃ target : InterSlot L pb r alpha, target.1.1 = gamma then
      some (Classical.choose h)
    else
      none

/-- Totalize a point family indexed by interacting targets to the original
finite target slots.  Missing targets are filled by the source point itself;
`centerAverage.activeFill` makes that branch invisible at zero weight. -/
noncomputable def totalPts
    {M : Type u}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (pairPts : (alpha : LiveSlot L pb r) →
      InterSlot L pb r alpha → Nat → Nat → M → M)
    (alpha : LiveSlot L pb r) (a b : Nat) (x : M)
    (gamma : Fin (pb.A r)) : M :=
  match interSlot? alpha gamma with
  | some target => pairPts alpha target a b x
  | none => x

/-- A zero-weight slot is filled by the source point, independently of whether
that slot has an interacting-target representative. -/
@[simp] theorem activeFill_totalPts_zero
    {M : Type u}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (mu : M → Fin (pb.A r) → Real)
    (pairPts : (alpha : LiveSlot L pb r) →
      InterSlot L pb r alpha → Nat → Nat → M → M)
    (alpha : LiveSlot L pb r) (a b : Nat) (x : M)
    (gamma : Fin (pb.A r)) (hzero : mu x gamma = 0) :
    centerAverage.activeFill mu (totalPts pairPts alpha a b)
        (fun y => y) x gamma = x := by
  simp [centerAverage.activeFill, hzero]

/-- A nonzero-weight slot represented in the interaction family reads out the
corresponding pair-indexed point through the totalized family.  The premise
`hslot` is the exact support witness supplied by `exists_supp_fin`. -/
theorem activeFill_totalPts_of_ne
    {M : Type u}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (mu : M → Fin (pb.A r) → Real)
    (pairPts : (alpha : LiveSlot L pb r) →
      InterSlot L pb r alpha → Nat → Nat → M → M)
    (alpha : LiveSlot L pb r) (a b : Nat) (x : M)
    (gamma : Fin (pb.A r))
    (hslot : mu x gamma ≠ 0 →
      ∃ target : InterSlot L pb r alpha, target.1.1 = gamma)
    (hne : mu x gamma ≠ 0) :
    ∃ target : InterSlot L pb r alpha,
      target.1.1 = gamma ∧
        centerAverage.activeFill mu (totalPts pairPts alpha a b)
            (fun y => y) x gamma = pairPts alpha target a b x := by
  classical
  obtain ⟨target, htarget⟩ := hslot hne
  have hexists :
      ∃ target' : InterSlot L pb r alpha, target'.1.1 = gamma :=
    ⟨target, htarget⟩
  have hlookup : interSlot? alpha gamma = some target := by
    unfold interSlot?
    split
    next h =>
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact (Classical.choose_spec h).trans htarget.symm
    next h =>
      exact (h hexists).elim
  refine ⟨target, htarget, ?_⟩
  simp [centerAverage.activeFill, hne, totalPts, hlookup]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Extract one master subsequence carrying the finite source cover, sparse
old-`InterSlot` transition limits, chartwise atom/weight limits, and the
nonzero-support closed-ball readout.  No chartwise limit weights are glued. -/
theorem MetricCompactnessInputs.exists_atom_supp_fin
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (r : Real) (hr : 0 ≤ r) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E),
      let Lphi := L.subseq hphi
      (∀ alpha, IsOpen (U alpha)) ∧
      (∀ alpha, U alpha ⊆
        Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
      (∀ alpha, IsCompact (C0 alpha)) ∧
      (∀ alpha, IsCompact (C1 alpha)) ∧
      (∀ alpha, C0 alpha ⊆ interior (C1 alpha)) ∧
      (∀ alpha, C1 alpha ⊆ U alpha) ∧
      (∀ k,
        let Y := X.obj (Lphi.φ k)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
        Lphi.hatSourceBall inp.decay P r k ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) ''
                interior (C0 alpha)) ∧
      (∀ k,
        let Y := X.obj (Lphi.φ k)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
        (∀ alpha : LiveSlot L inp.pack r,
          U alpha ⊆ Metric.ball 0
              (inp.normalBounds.radius (Lphi.φ k)
                (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
          U alpha ⊆ Metric.ball 0
              (expMapC2Radius (I := I) Y.metric
                (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
          Set.MapsTo
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z)
            (U alpha)
            (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
              ⋃ gamma : Fin (inp.pack.A r),
                Lphi.innerBall inp.decay inp.D P inp.pack r k gamma)) ∧
        Lphi.hatSourceBall inp.decay P r k ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) '' U alpha) ∧
      (∀ alpha,
        HasAtomWeightLim (I := I) inp.decay inp.hD P Lphi inp.realizes
          inp.pack r hr
          (fun k => seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
          (U alpha) (aInf alpha)) ∧
      (∀ alpha target,
        ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
        ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
        ContinuousOn (Jinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
        ContinuousOn (Jbarinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
        MapCInfConvOnCompacts
          (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
          (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (Jinf alpha target) ∧
        MapCInfConvOnCompacts
          (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
          (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
          (Jbarinf alpha target) ∧
        (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
          Jinf alpha target z ∈
              Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
            Jbarinf alpha target (Jinf alpha target z) = z) ∧
        (∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
          Jbarinf alpha target w ∈
              Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
            Jinf alpha target (Jbarinf alpha target w) = w)) ∧
      ∀ alpha z, z ∈ U alpha → ∀ gamma : Fin (inp.pack.A r),
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma ≠ 0 →
        ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma ∧
            Jinf alpha target z ∈
              Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  let PairSlot := Σ alpha : LiveSlot L inp.pack r,
    InterSlot L inp.pack r alpha
  letI (alpha : LiveSlot L inp.pack r) : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  letI : Finite PairSlot := inferInstance
  obtain ⟨psi, hpsi, gInf, U, C0, C1, hginf, hg, hUopen, hU8,
      hC0, hC1, hC01, hC1U, hcore⟩ :=
    inp.exists_live_cores h8 hradD hradRatio P L r
  have hcover : ∀ᶠ k in Filter.atTop,
      let Y := X.obj (L.φ (psi k))
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (L.φ (psi k))).ms
      (∀ alpha : LiveSlot L inp.pack r,
        U alpha ⊆ Metric.ball 0
            (inp.normalBounds.radius (L.φ (psi k))
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))) ∧
        U alpha ⊆ Metric.ball 0
            (expMapC2Radius (I := I) Y.metric
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))) ∧
        Set.MapsTo
          (fun z => expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z)
          (U alpha)
          (L.hatBall inp.decay inp.D P inp.pack r (psi k) alpha.1 ∩
            ⋃ gamma : Fin (inp.pack.A r),
              L.innerBall inp.decay inp.D P inp.pack r (psi k) gamma)) ∧
      L.hatSourceBall inp.decay P r (psi k) ⊆
        ⋃ alpha : LiveSlot L inp.pack r,
          (fun z => expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z) '' U alpha := by
    filter_upwards [hcore] with k hk
    refine ⟨hk.1, ?_⟩
    intro y hy
    obtain ⟨alpha, v, hv, rfl⟩ := mem_iUnion.mp (hk.2 hy)
    refine mem_iUnion.mpr ⟨alpha, v, ?_, rfl⟩
    exact hC1U alpha (interior_subset (hC01 alpha (interior_subset hv)))
  let L0 := L.subseq hpsi
  let live0 : LiveSlot L inp.pack r → LiveSlot L0 inp.pack r := fun alpha =>
    ⟨alpha.1, by simpa only [L0, NetLimitData.subseq] using alpha.2⟩
  have hinter0 (pair : PairSlot) : ∀ᶠ k in Filter.atTop,
      BInter inp.decay inp.D P L0.lamInf
        ((live0 pair.1).1 : Nat) ((live0 pair.2.1).1 : Nat) (L0.φ k) := by
    simpa only [L0, live0, NetLimitData.subseq, NetLimitData.subseq_lamInf,
      Function.comp_apply] using
        hpsi.tendsto_atTop.eventually pair.2.2
  obtain ⟨tau, htau, J, Jbar, hspec⟩ :=
    inp.exists_pair_trans hradD hradRatio P L0 r
      (fun pair : PairSlot => live0 pair.1)
      (fun pair : PairSlot => live0 pair.2.1)
      hinter0
  have hpair : ∀ᶠ k in Filter.atTop, ∀ pair : PairSlot,
      let x := seqCenterD inp.decay P L0 k ((live0 pair.1).1 : Nat)
      let y := seqCenterD inp.decay P L0 k ((live0 pair.2.1).1 : Nat)
      let Y := X.obj (L0.φ k)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (L0.φ k)).ms
      ContDiffOn Real (⊤ : ℕ∞)
          (normalTransition (I := I) Y x y)
          (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat))) ∧
        NormalOverlapOn (I := I) Y x y
          (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat))) :=
    Filter.eventually_all.mpr fun pair =>
      (inp.pair_overlap_tail hradD hradRatio P L0 r
        (live0 pair.1) (live0 pair.2.1) (hinter0 pair)).mono fun _ hk =>
          ⟨hk.2.2.2.2.1, hk.2.2.2.2.2.1⟩
  obtain ⟨hgp, _hrad⟩ := inp.item3ScaleTails h8 hradD hradRatio P L r
  have hgp0 : Item3GpScaleTail (I := I)
      inp.decay inp.D P L0 inp.pack r :=
    hgp.subseq inp.decay inp.D P L inp.pack r hpsi
  have hall : ∀ᶠ k in Filter.atTop,
      (let Y := X.obj (L.φ (psi (tau k)))
       letI : TopologicalSpace Y.M := Y.topology
       letI : ChartedSpace H Y.M := Y.charted
       letI : IsManifold I ∞ Y.M := Y.smooth
       letI : T2Space Y.M := Y.t2
       letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
       letI : MetricSpace Y.M := (P (L.φ (psi (tau k)))).ms
       (∀ alpha : LiveSlot L inp.pack r,
          U alpha ⊆ Metric.ball 0
              (inp.normalBounds.radius (L.φ (psi (tau k)))
                (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat))) ∧
          U alpha ⊆ Metric.ball 0
              (expMapC2Radius (I := I) Y.metric
                (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat))) ∧
          Set.MapsTo
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z)
            (U alpha)
            (L.hatBall inp.decay inp.D P inp.pack r (psi (tau k)) alpha.1 ∩
              ⋃ gamma : Fin (inp.pack.A r),
                L.innerBall inp.decay inp.D P inp.pack r (psi (tau k)) gamma)) ∧
        L.hatSourceBall inp.decay P r (psi (tau k)) ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z) '' U alpha) ∧
      Item3GpScaleAt (I := I) inp.decay inp.D P L0 inp.pack r (tau k) ∧
      (∀ pair : PairSlot,
        let x := seqCenterD inp.decay P L0 (tau k) ((live0 pair.1).1 : Nat)
        let y := seqCenterD inp.decay P L0 (tau k) ((live0 pair.2.1).1 : Nat)
        let Y := X.obj (L0.φ (tau k))
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (L0.φ (tau k))).ms
        ContDiffOn Real (⊤ : ℕ∞)
            (normalTransition (I := I) Y x y)
            (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat))) ∧
          NormalOverlapOn (I := I) Y x y
            (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat)))) ∧
      (let Y := X.obj (L.φ (psi (tau k)))
       letI : TopologicalSpace Y.M := Y.topology
       letI : ChartedSpace H Y.M := Y.charted
       letI : IsManifold I ∞ Y.M := Y.smooth
       letI : T2Space Y.M := Y.t2
       letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
       letI : MetricSpace Y.M := (P (L.φ (psi (tau k)))).ms
       L.hatSourceBall inp.decay P r (psi (tau k)) ⊆
        ⋃ alpha : LiveSlot L inp.pack r,
          (fun z => expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z) ''
              interior (C0 alpha)) := by
    filter_upwards [htau.tendsto_atTop.eventually hcover,
      htau.tendsto_atTop.eventually hcore,
      htau.tendsto_atTop.eventually hgp0,
      htau.tendsto_atTop.eventually hpair]
      with k hcoverK hcoreK hgpK hpairK
    exact ⟨hcoverK, hgpK, hpairK, hcoreK.2⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  let shift : Nat → Nat := fun k => k + N
  have hshift : StrictMono shift := by
    simpa only [shift] using strictMono_id.add_const N
  let phi : Nat → Nat := psi ∘ tau ∘ shift
  have hphi : StrictMono phi := hpsi.comp (htau.comp hshift)
  let Lphi := L.subseq hphi
  let Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => J ⟨alpha, target⟩
  let Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => Jbar ⟨alpha, target⟩
  let aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real := fun alpha gamma =>
    if htarget : ∃ target : InterSlot L inp.pack r alpha,
        target.1.1 = gamma then
      let target := Classical.choose htarget
      fun z => stepCBump (L.lamInf (gamma : Nat))
        (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))
        (gInf z target.1 (Jinf alpha target z) (Jinf alpha target z))
    else fun _ => 0
  have hlimAll : ∀ alpha,
      HasAtomWeightLim (I := I) inp.decay inp.hD P Lphi inp.realizes
        inp.pack r hr
        (fun k => seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (U alpha) (aInf alpha) := by
    intro alpha
    let beta : ∀ k : Nat, (X.obj (Lphi.φ k)).M := fun k =>
      seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
    have hgpPhi (k : Nat) : Item3GpScaleAt (I := I)
        inp.decay inp.D P Lphi inp.pack r k := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      simpa only [Item3GpScaleAt, Lphi, phi, L0, Function.comp_apply,
        NetLimitData.subseq, NetLimitData.subseq_lamInf] using hk.2.1
    have hUexpPhi (k : Nat) :
        letI : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
          (X.obj (Lphi.φ k)).t2TangentBundle
        U alpha ⊆ Metric.ball 0
          (expMapC2Radius (I := I) (X.obj (Lphi.φ k)).metric (beta k)) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      simpa only [beta, Lphi, phi, Function.comp_apply, seqCenterD_subseq] using
        (hk.1.1 alpha).2.1
    have hsourcePhi (k : Nat) :
        letI : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
          (X.obj (Lphi.φ k)).t2TangentBundle
        Set.MapsTo
          (fun z => expMapDiffeo (I := I) (X.obj (Lphi.φ k)).metric (beta k) z)
          (U alpha) (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      intro z hz
      have hmem := (hk.1.1 alpha).2.2 hz
      simpa only [beta, Lphi, phi, Function.comp_apply, seqCenterD_subseq,
        NetLimitData.hatBall_subseq] using hmem.1
    have hcoverPhi (k : Nat) :
        letI : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
          (X.obj (Lphi.φ k)).t2TangentBundle
        Set.MapsTo
          (fun z => expMapDiffeo (I := I) (X.obj (Lphi.φ k)).metric (beta k) z)
          (U alpha)
          (⋃ gamma : Fin (inp.pack.A r),
            Lphi.innerBall inp.decay inp.D P inp.pack r k gamma) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      intro z hz
      have hmem := (hk.1.1 alpha).2.2 hz
      simpa only [beta, Lphi, phi, Function.comp_apply, seqCenterD_subseq,
        NetLimitData.innerBall_subseq] using hmem.2
    have hgPhi : MapCInfConvOnCompacts Set.univ
        (fun k _ gamma => normalCoordMetric (I := I) (X.obj (Lphi.φ k))
          (seqCenterD inp.decay P Lphi k (gamma.1 : Nat)) 0) gInf := by
      simpa only [Lphi, phi, Function.comp_apply, seqCenterD_subseq] using
        hg.comp_subseq (htau.comp hshift)
    have hgU : MapCInfConvOnCompacts (U alpha)
        (fun k _ gamma => normalCoordMetric (I := I) (X.obj (Lphi.φ k))
          (seqCenterD inp.decay P Lphi k (gamma.1 : Nat)) 0) gInf := by
      intro K hK hKU p
      exact hgPhi K hK (hKU.trans (Set.subset_univ (U alpha))) p
    have hginfU : ContDiffOn Real (∞ : WithTop ℕ∞) gInf (U alpha) :=
      hginf.mono (Set.subset_univ (U alpha))
    have hJInf (target : InterSlot L inp.pack r alpha) :
        ContDiffOn Real (∞ : WithTop ℕ∞) (Jinf alpha target) (U alpha) :=
      (hspec (⟨alpha, target⟩ : PairSlot)).1.mono (hU8 alpha)
    have hJConv (target : InterSlot L inp.pack r alpha) :
        MapCInfConvOnCompacts (U alpha)
          (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
            (beta k) (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (Jinf alpha target) := by
      intro K hK hKU p
      have hconv :=
        (hspec (⟨alpha, target⟩ : PairSlot)).2.2.2.2.1.comp_subseq hshift
          K hK (hKU.trans (hU8 alpha)) p
      simpa only [Jinf, beta, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using hconv
    have hJStage (target : InterSlot L inp.pack r alpha) (k : Nat) :
        ContDiffOn Real (∞ : WithTop ℕ∞)
          (normalTransition (I := I) (X.obj (Lphi.φ k))
            (beta k) (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (U alpha) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      have hsmooth := (hk.2.2.1 (⟨alpha, target⟩ : PairSlot)).1.mono (hU8 alpha)
      simpa only [beta, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using hsmooth
    have hOverlap (target : InterSlot L inp.pack r alpha) (k : Nat) :
        NormalOverlapOn (I := I) (X.obj (Lphi.φ k))
          (beta k) (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
          (U alpha) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      have hover := (hk.2.2.1 (⟨alpha, target⟩ : PairSlot)).2
      intro z hz
      have hz' := hover z (hU8 alpha hz)
      simpa only [beta, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using hz'
    have hatom (gamma : Fin (inp.pack.A r)) :
        MapCInfConvOnCompacts (U alpha)
          (fun k => seqAtomChart (I := I) inp.decay inp.hD P Lphi inp.pack r
            beta gamma k) (aInf alpha gamma) := by
      by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma
      · let target := Classical.choose htarget
        have hslot : target.1.1 = gamma := Classical.choose_spec htarget
        have hgamma : Lphi.alive (gamma : Nat) = true := by
          simpa only [Lphi, NetLimitData.subseq, hslot] using target.1.2
        have hraw := quadPiBump_conv (hUopen alpha) hgU (hJConv target)
          (fun _ => contDiffOn_const) hginfU (hJStage target) (hJInf target)
          target.1 (stepCBump (L.lamInf (gamma : Nat))
            (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat))))
          (stepCBump (L.lamInf (gamma : Nat))
            (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))).contDiff
        have hstep : MapCInfConvOnCompacts (U alpha)
            (fun k => stepCAtomChart (I := I) (X.obj (Lphi.φ k)) (beta k)
              (seqCenterD inp.decay P Lphi k (gamma : Nat))
              (L.lamInf (gamma : Nat))
              (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat))))
            (aInf alpha gamma) := by
          refine hraw.congr (hUopen alpha) (fun k z hz => ?_) (fun z _hz => ?_)
          · simpa only [stepCAtomChart, hslot] using
              (stepCAtom_readout (I := I) (X.obj (Lphi.φ k)) (beta k)
                (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
                (L.lamInf (gamma : Nat))
                (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))
                ((hOverlap target k) z hz).2)
          · simp only [aInf, dif_pos htarget, target]
        exact seqAtom_live_conv (I := I) inp.decay inp.hD P Lphi inp.pack r
          beta gamma (hUopen alpha) hgamma (by
            simpa only [Lphi, NetLimitData.subseq_lamInf] using hstep)
      · cases hgamma : L.alive (gamma : Nat) with
        | false =>
            have hgammaPhi : Lphi.alive (gamma : Nat) = false := by
              simpa only [Lphi, NetLimitData.subseq] using hgamma
            simpa only [aInf, dif_neg htarget] using
              (seqAtom_dead_conv (I := I) inp.decay inp.hD P Lphi inp.pack r
                beta gamma (hUopen alpha) hgammaPhi)
        | true =>
            rcases hstable (alpha.1 : Nat) (gamma : Nat) with hinter | hdisjoint
            · exact (htarget
                ⟨⟨⟨gamma, hgamma⟩, hinter⟩, rfl⟩).elim
            · have hdisjointPhi : ∀ᶠ k in Filter.atTop,
                  ¬ BInter inp.decay inp.D P Lphi.lamInf
                    (alpha.1 : Nat) (gamma : Nat) (Lphi.φ k) := by
                simpa only [Lphi, NetLimitData.subseq, Function.comp_apply,
                  NetLimitData.subseq_lamInf] using
                    hphi.tendsto_atTop.eventually hdisjoint
              have hgpTail : Item3GpScaleTail (I := I)
                  inp.decay inp.D P Lphi inp.pack r :=
                Filter.Eventually.of_forall hgpPhi
              have hsourceTail : ∀ᶠ k in Filter.atTop,
                  letI : TopologicalSpace (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).topology
                  letI : ChartedSpace H (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).charted
                  letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).smooth
                  letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
                    (X.obj (Lphi.φ k)).t2TangentBundle
                  Set.MapsTo
                    (fun z => expMapDiffeo (I := I) (X.obj (Lphi.φ k)).metric
                      (beta k) z)
                    (U alpha)
                    (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1) :=
                Filter.Eventually.of_forall hsourcePhi
              simpa only [aInf, dif_neg htarget] using
                (atom_disjoint_conv (I := I) inp.decay inp.hD P Lphi inp.pack r
                  hgpTail beta alpha.1 gamma (hUopen alpha) hsourceTail
                  hdisjointPhi)
    have hdead (gamma : Fin (inp.pack.A r))
        (hgamma : Lphi.alive (gamma : Nat) = false) :
        aInf alpha gamma = 0 := by
      have hnone : ¬ ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma := by
        rintro ⟨target, hslot⟩
        have htrue : Lphi.alive (gamma : Nat) = true := by
          simpa only [Lphi, NetLimitData.subseq, hslot] using target.1.2
        rw [hgamma] at htrue
        contradiction
      simp only [aInf, dif_neg hnone]
      rfl
    have hatomSmooth (k : Nat) (gamma : Fin (inp.pack.A r)) :
        ContDiffOn Real (∞ : WithTop ℕ∞)
          (seqAtomChart (I := I) inp.decay inp.hD P Lphi inp.pack r
            beta gamma k) (U alpha) :=
      seqAtomChart_smooth (I := I) inp.decay inp.hD P Lphi inp.pack r k
        (hgpPhi k) beta gamma (hUexpPhi k)
    have hatomInfSmooth (gamma : Fin (inp.pack.A r)) :
        ContDiffOn Real (∞ : WithTop ℕ∞) (aInf alpha gamma) (U alpha) := by
      by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma
      · let target := Classical.choose htarget
        have hquad : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun z => gInf z target.1 (Jinf alpha target z)
              (Jinf alpha target z)) (U alpha) :=
          ((contDiffOn_pi.mp hginfU target.1).clm_apply (hJInf target)).clm_apply
            (hJInf target)
        simpa only [aInf, dif_pos htarget, target] using
          (stepCBump (L.lamInf (gamma : Nat))
            (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))).contDiff.comp_contDiffOn
              hquad
      · simpa only [aInf, dif_neg htarget] using
          (contDiffOn_const : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun _ : E => (0 : Real)) (U alpha))
    exact HasAtomWeightLim.of_atoms (I := I) inp.hD P Lphi inp.realizes inp.pack
      r hr hgpPhi beta (U alpha) (hUopen alpha) hcoverPhi (aInf alpha)
      hdead hatom hatomSmooth hatomInfSmooth
  refine ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, ?_⟩
  dsimp only
  refine ⟨hUopen, hU8, hC0, hC1, hC01, hC1U, ?_, ?_, hlimAll, ?_, ?_⟩
  · intro k
    have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
    simpa only [Lphi, phi, Function.comp_apply,
      seqCenterD_subseq, NetLimitData.hatSourceBall_subseq] using hk.2.2.2
  · intro k
    have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
    simpa only [Lphi, phi, Function.comp_apply,
      seqCenterD_subseq, NetLimitData.hatBall_subseq,
      NetLimitData.innerBall_subseq, NetLimitData.hatSourceBall_subseq] using hk.1
  · intro alpha target
    have hs := hspec (⟨alpha, target⟩ : PairSlot)
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_,
      hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩
    · simpa only [Jinf, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using
        hs.2.2.2.2.1.comp_subseq hshift
    · simpa only [Jbarinf, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using
        hs.2.2.2.2.2.1.comp_subseq hshift
  · intro alpha z hz gamma hweight
    have hnum : aInf alpha gamma z ≠ 0 :=
      num_ne_of_cut_ne (num_ne_of_raw_ne hweight)
    have htarget : ∃ target : InterSlot L inp.pack r alpha,
        target.1.1 = gamma := by
      by_contra hnone
      apply hnum
      simp only [aInf, dif_neg hnone]
    let target := Classical.choose htarget
    have hslot : target.1.1 = gamma := Classical.choose_spec htarget
    let alphaPhi : LiveSlot Lphi inp.pack r :=
      ⟨alpha.1, by simpa only [Lphi, NetLimitData.subseq] using alpha.2⟩
    let gammaPhi : LiveSlot Lphi inp.pack r :=
      ⟨target.1.1, by simpa only [Lphi, NetLimitData.subseq] using target.1.2⟩
    have hgpPhi : Item3GpScaleTail (I := I)
        inp.decay inp.D P Lphi inp.pack r :=
      Filter.Eventually.of_forall fun k => by
        have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
        simpa only [Item3GpScaleAt, Lphi, phi, L0, Function.comp_apply,
          NetLimitData.subseq, NetLimitData.subseq_lamInf] using hk.2.1
    have hlimPhi : HasAtomWeightLim (I := I) inp.decay inp.hD P Lphi
        inp.realizes inp.pack r hr
        (fun k => seqCenterD inp.decay P Lphi k (alphaPhi.1 : Nat))
        (U alpha) (aInf alpha) := by
      simpa only [alphaPhi] using hlimAll alpha
    have hB : MapCInfConvOnCompacts (U alpha)
        (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
          (seqCenterD inp.decay P Lphi k (alphaPhi.1 : Nat))
          (seqCenterD inp.decay P Lphi k (gammaPhi.1 : Nat)))
        (Jinf alpha target) := by
      intro K hK hKU p
      have hconv :=
        (hspec (⟨alpha, target⟩ : PairSlot)).2.2.2.2.1.comp_subseq hshift
          K hK (hKU.trans (hU8 alpha)) p
      simpa only [Jinf, alphaPhi, gammaPhi, Lphi, phi, L0, live0,
        NetLimitData.subseq, Function.comp_apply, seqCenterD_subseq,
        NetLimitData.subseq_lamInf] using hconv
    refine ⟨target, hslot, ?_⟩
    have hmem := hlimPhi.binf_of_live inp hradD hradRatio P Lphi r hr
      hgpPhi alphaPhi (U alpha) (aInf alpha) (fun k : Nat => k)
      strictMono_id gammaPhi (Jinf alpha target) (by
        simpa only [Function.id_def] using hB) hz (by
          simpa only [gammaPhi, hslot] using hweight)
    simpa only [Jinf, gammaPhi, hslot, Lphi, NetLimitData.subseq_lamInf] using hmem

/-- A finite source-patch family admits compact cores which still cover the
whole source set. -/
def HasCompactCover {Y J : Type*} [TopologicalSpace Y]
    (sourceBall : Set Y) (sourcePatch : J → Set Y) : Prop :=
  ∃ K : J → Set Y, (∀ j, IsCompact (K j)) ∧
    (∀ j, K j ⊆ sourcePatch j) ∧ sourceBall = ⋃ j, K j

/-- Data retained from the finite source-cover extraction on one master
subsequence: the chart domains, all-stage cover geometry, chartwise normalized
weight limits, and the two-sided transition limits.  This predicate records
existing producer output; it adds no compatibility between different source
charts. -/
def HasSuppConvData
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E) : Prop :=
  let Lphi := L.subseq hphi
  (∀ alpha, IsOpen (U alpha)) ∧
  (∀ alpha, U alpha ⊆
    Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
  (∀ alpha, IsCompact (C0 alpha)) ∧
  (∀ alpha, IsCompact (C1 alpha)) ∧
  (∀ alpha, C0 alpha ⊆ interior (C1 alpha)) ∧
  (∀ alpha, C1 alpha ⊆ U alpha) ∧
  (∀ k,
    let Y := X.obj (Lphi.φ k)
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
    Lphi.hatSourceBall inp.decay P r k ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (fun z => expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) ''
            interior (C0 alpha)) ∧
  (∀ k,
    let Y := X.obj (Lphi.φ k)
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
    (∀ alpha : LiveSlot L inp.pack r,
      U alpha ⊆ Metric.ball 0
          (inp.normalBounds.radius (Lphi.φ k)
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
      U alpha ⊆ Metric.ball 0
          (expMapC2Radius (I := I) Y.metric
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z)
        (U alpha)
        (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
          ⋃ gamma : Fin (inp.pack.A r),
            Lphi.innerBall inp.decay inp.D P inp.pack r k gamma)) ∧
    Lphi.hatSourceBall inp.decay P r k ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (fun z => expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) '' U alpha) ∧
  (∀ alpha,
    HasAtomWeightLim (I := I) inp.decay inp.hD P Lphi inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      (U alpha) (aInf alpha)) ∧
  ∀ alpha target,
    ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
    ContinuousOn (Jinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContinuousOn (Jbarinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
      (Jinf alpha target) ∧
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
      (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
      (Jbarinf alpha target) ∧
    (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
      Jinf alpha target z ∈
          Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
        Jbarinf alpha target (Jinf alpha target z) = z) ∧
    ∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
      Jbarinf alpha target w ∈
          Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
        Jinf alpha target (Jbarinf alpha target w) = w

set_option maxHeartbeats 800000 in
/-- Produce one master subsequence with source-local normalized weights and
old-`InterSlot` two-index points.  Each weight family is pulled back only to its
own source patch; no chartwise weights are identified or glued. -/
theorem MetricCompactnessInputs.exists_supp_pts_fin
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (r : Real) (hr : 0 ≤ r)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E),
      let Lphi := L.subseq hphi
      let beta := fun (n : Nat) (alpha : LiveSlot L inp.pack r) =>
        seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      let weightInf := fun (alpha : LiveSlot L inp.pack r) (z : E)
          (gamma : Fin (inp.pack.A r)) =>
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma
      HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
        aInf Jinf Jbarinf ∧
      ∀ᶠ n in Filter.atTop,
        let Y := X.obj (Lphi.φ n)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : SigmaCompactSpace Y.M := Y.sigmaCompact
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : ConnectedSpace Y.M := hconn (Lphi.φ n)
        letI : TopologicalSpace.MetrizableSpace Y.M :=
          Manifold.metrizableSpace I Y.M
        letI : T3Space Y.M := inferInstance
        letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
          ⟨Y.metric.toRiemannianMetric⟩
        letI : IsContinuousRiemannianBundle E
            (fun x : Y.M => TangentSpace I x) :=
          ⟨Y.metric.inner, Y.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
        letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
        let chi := fun (alpha : LiveSlot L inp.pack r) =>
          NormalCoordinates.normalChartAt (I := I) Y.metric (beta n alpha)
        let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
          Lphi.hatSourceBall inp.decay P r n ∩
            (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
        let localWeight := fun (alpha : LiveSlot L inp.pack r)
            (x : Y.M) (gamma : Fin (inp.pack.A r)) =>
          weightInf alpha (chi alpha x) gamma
        let pairPts : (alpha : LiveSlot L inp.pack r) →
            InterSlot L inp.pack r alpha → Nat → Nat → Y.M → Y.M :=
          fun alpha target a b x =>
            (chi alpha).symm
              (normalTransition (I := I) (X.obj (Lphi.φ b))
                (beta b target.1) (beta b alpha)
                (normalTransition (I := I) (X.obj (Lphi.φ a))
                  (beta a alpha) (beta a target.1) (chi alpha x)))
        let pts := fun (alpha : LiveSlot L inp.pack r) =>
          totalPts (X := X) pairPts alpha
        HasCompactCover (Lphi.hatSourceBall inp.decay P r n) sourcePatch ∧
          Lphi.hatSourceBall inp.decay P r n ⊆
            ⋃ alpha : LiveSlot L inp.pack r, sourcePatch alpha ∧
          (∀ alpha,
            sourcePatch alpha ⊆
              Lphi.hatBall inp.decay inp.D P inp.pack r n alpha.1) ∧
          (∀ alpha,
            centerAverage.WeightDataOn (sourcePatch alpha)
              (fun _ : Fin (inp.pack.A r) => Set.univ)
              (localWeight alpha)) ∧
          ∀ alpha gamma epsilon, 0 < epsilon →
            ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
              ∀ x ∈ sourcePatch alpha,
                localWeight alpha x gamma ≠ 0 →
                  dist x (pts alpha a b x gamma) < epsilon := by
  classical
  obtain ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, hUopen, hU8,
      hC0, hC1, hC01, hC1U, hcore, hgeom, hlim, htrans, hsupp⟩ :=
    inp.exists_atom_supp_fin h8 hradD hradRatio P L hstable r hr
  refine ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, ?_⟩
  dsimp only
  refine ⟨⟨hUopen, hU8, hC0, hC1, hC01, hC1U, hcore,
    hgeom, hlim, htrans⟩, ?_⟩
  obtain ⟨hgp0, _hrad⟩ := inp.item3ScaleTails h8 hradD hradRatio P L r
  have hgpPhi : Item3GpScaleTail (I := I) inp.decay inp.D P
      (L.subseq hphi) inp.pack r :=
    hgp0.subseq inp.decay inp.D P L inp.pack r hphi
  have hcenters : ∀ᶠ n in Filter.atTop, ∀ alpha : LiveSlot L inp.pack r,
      seqCenter inp.decay inp.D P ((L.subseq hphi).φ n) (alpha.1 : Nat) =
        some (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) :=
    Filter.eventually_all.mpr fun alpha =>
      seqCenterD_live inp.decay P (L.subseq hphi) (alpha.1 : Nat) (by
        simpa only [NetLimitData.subseq] using alpha.2)
  filter_upwards [hgpPhi, hcenters] with n hgpN hcenterN
  let Y := X.obj ((L.subseq hphi).φ n)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : ConnectedSpace Y.M := hconn ((L.subseq hphi).φ n)
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.inner, Y.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  have hcover : (L.subseq hphi).hatSourceBall inp.decay P r n ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (L.subseq hphi).hatSourceBall inp.decay P r n ∩
          (NormalCoordinates.normalChartAt (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))).source ∩
          (NormalCoordinates.normalChartAt (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))) ⁻¹' U alpha := by
    intro x hx
    rcases Set.mem_iUnion.mp ((hgeom n).2 hx) with ⟨alpha, z, hzU, rfl⟩
    refine Set.mem_iUnion.mpr ⟨alpha, ⟨hx, ?_⟩, ?_⟩
    · have hzball := ((hgeom n).1 alpha).2.1 hzU
      have hznorm : ‖z‖ < expMapC2Radius (I := I)
          (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) := by
        simpa only [Metric.mem_ball, dist_zero_right] using hzball
      have hzsrc := mem_expMapDiffeo_source_of_norm_lt_radius (I := I)
        (X.obj ((L.subseq hphi).φ n)).metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) hznorm
      have hxtarget :=
        (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))).map_source hzsrc
      simpa only [normalChartAt_source_eq] using hxtarget
    · have hzball := ((hgeom n).1 alpha).2.1 hzU
      have hznorm : ‖z‖ < expMapC2Radius (I := I)
          (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) := by
        simpa only [Metric.mem_ball, dist_zero_right] using hzball
      have hzsrc := mem_expMapDiffeo_source_of_norm_lt_radius (I := I)
        (X.obj ((L.subseq hphi).φ n)).metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) hznorm
      have hchart :
          NormalCoordinates.normalChartAt (I := I)
              (X.obj ((L.subseq hphi).φ n)).metric
              (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
              (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
                (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) z) = z := by
        simpa only [normalChartAt] using
          (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))).left_inv hzsrc
      change NormalCoordinates.normalChartAt (I := I)
          (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
          (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) z) ∈ U alpha
      rw [hchart]
      exact hzU
  refine ⟨?_, hcover, ?_, ?_, ?_⟩
  · let chi := fun (alpha : LiveSlot L inp.pack r) =>
      NormalCoordinates.normalChartAt (I := I) Y.metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
    let sourceBall := (L.subseq hphi).hatSourceBall inp.decay P r n
    let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      sourceBall ∩ (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    let patchOpen : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    change HasCompactCover sourceBall sourcePatch
    have hopen : ∀ alpha, IsOpen (patchOpen alpha) := fun alpha =>
      (chi alpha).toOpenPartialHomeomorph.isOpen_inter_preimage (hUopen alpha)
    have hcoverOpen : sourceBall ⊆ ⋃ alpha, patchOpen alpha := by
      intro x hx
      rcases Set.mem_iUnion.mp (hcover hx) with ⟨alpha, hxalpha⟩
      exact Set.mem_iUnion.mpr ⟨alpha, ⟨hxalpha.1.2, hxalpha.2⟩⟩
    obtain ⟨K, hKcompact, hKsub, hKeq⟩ :=
      ((L.subseq hphi).hatSourceCompact inp.decay P r n).finite_compact_cover
        Finset.univ patchOpen (fun alpha _ => hopen alpha)
          (by simpa using hcoverOpen)
    refine ⟨K, hKcompact, ?_, ?_⟩
    · intro alpha x hxK
      have hxSource : x ∈ sourceBall := by
        change x ∈ (L.subseq hphi).hatSourceBall inp.decay P r n
        rw [hKeq]
        exact Set.mem_iUnion.mpr ⟨alpha,
          Set.mem_iUnion.mpr ⟨Finset.mem_univ alpha, hxK⟩⟩
      have hxOpen : x ∈ patchOpen alpha := hKsub alpha hxK
      exact ⟨⟨hxSource, hxOpen.1⟩, hxOpen.2⟩
    · simpa using hKeq
  · intro alpha x hx
    have hmap := ((hgeom n).1 alpha).2.2 hx.2
    have hexp : expMapDiffeo (I := I) Y.metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        (NormalCoordinates.normalChartAt (I := I) Y.metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) x) = x := by
      simpa only [normalChartAt] using
        NormalCoordinates.normalChartAt_left_inv (I := I) Y.metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
          hx.1.2
    change expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
          (NormalCoordinates.normalChartAt (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) x) ∈
        (L.subseq hphi).hatBall inp.decay inp.D P inp.pack r n alpha.1 ∩
          ⋃ gamma : Fin (inp.pack.A r),
            (L.subseq hphi).innerBall inp.decay inp.D P inp.pack r n gamma
      at hmap
    rw [hexp] at hmap
    exact hmap.1
  · intro alpha
    have hcoverU : ∀ᶠ k in Filter.atTop,
        letI : TopologicalSpace (X.obj ((L.subseq hphi).φ k)).M :=
          (X.obj ((L.subseq hphi).φ k)).topology
        letI : ChartedSpace H (X.obj ((L.subseq hphi).φ k)).M :=
          (X.obj ((L.subseq hphi).φ k)).charted
        letI : IsManifold I ∞ (X.obj ((L.subseq hphi).φ k)).M :=
          (X.obj ((L.subseq hphi).φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj ((L.subseq hphi).φ k)).M) :=
          (X.obj ((L.subseq hphi).φ k)).t2TangentBundle
        Set.MapsTo
          (fun z => expMapDiffeo (I := I)
            (X.obj ((L.subseq hphi).φ k)).metric
            (seqCenterD inp.decay P (L.subseq hphi) k (alpha.1 : Nat)) z)
          (U alpha)
          (⋃ gamma : Fin (inp.pack.A r),
            (L.subseq hphi).innerBall inp.decay inp.D P inp.pack r k gamma) :=
      Filter.Eventually.of_forall fun k z hz => ((hgeom k).1 alpha).2.2 hz |>.2
    have hdata := (hlim alpha).weight_data_of_innerCover hgpPhi hcoverU
    simpa only [Set.preimage_univ] using hdata.comp (fun _ hx => hx.2)
  · let chi := fun (alpha : LiveSlot L inp.pack r) =>
      NormalCoordinates.normalChartAt (I := I) Y.metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
    let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      (L.subseq hphi).hatSourceBall inp.decay P r n ∩
        (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    let localWeight := fun (alpha : LiveSlot L inp.pack r) (x : Y.M)
        (gamma : Fin (inp.pack.A r)) =>
      rawWeights
        (cutRaw
          (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
          (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
        (chi alpha x) gamma
    let pairPts : (alpha : LiveSlot L inp.pack r) →
        InterSlot L inp.pack r alpha → Nat → Nat → Y.M → Y.M :=
      fun alpha target a b x =>
        (chi alpha).symm
          (normalTransition (I := I) (X.obj ((L.subseq hphi).φ b))
            (seqCenterD inp.decay P (L.subseq hphi) b
              (target.1.1 : Nat))
            (seqCenterD inp.decay P (L.subseq hphi) b (alpha.1 : Nat))
            (normalTransition (I := I) (X.obj ((L.subseq hphi).φ a))
              (seqCenterD inp.decay P (L.subseq hphi) a (alpha.1 : Nat))
              (seqCenterD inp.decay P (L.subseq hphi) a
                (target.1.1 : Nat))
              (chi alpha x)))
    let pts := fun (alpha : LiveSlot L inp.pack r) =>
      totalPts (X := X) pairPts alpha
    change ∀ alpha gamma epsilon, 0 < epsilon →
      ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ sourcePatch alpha,
        localWeight alpha x gamma ≠ 0 →
          dist x (pts alpha a b x gamma) < epsilon
    have hpair (alpha : LiveSlot L inp.pack r) :
        ∀ target : InterSlot L inp.pack r alpha, ∀ epsilon : Real,
          0 < epsilon → ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
            ∀ x ∈ sourcePatch alpha,
              localWeight alpha x target.1.1 ≠ 0 →
                dist x (pairPts alpha target a b x) < epsilon := by
      let centerAll : Fin (inp.pack.A r) → Y.M := fun gamma =>
        seqCenterD inp.decay P (L.subseq hphi) n (gamma : Nat)
      let pairWeight : Y.M → InterSlot L inp.pack r alpha → Real :=
        fun x target => localWeight alpha x target.1.1
      let centerPair : InterSlot L inp.pack r alpha → Y.M := fun _ =>
        seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)
      let sourceCage : InterSlot L inp.pack r alpha → Set Y.M := fun _ =>
        (L.subseq hphi).hatSourceCage inp.decay P inp.pack r n alpha.1
      let U8 : InterSlot L inp.pack r alpha → Set E := fun _ =>
        Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))
      let V6 : InterSlot L inp.pack r alpha → Set E := fun target =>
        Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat))
      let V8 : InterSlot L inp.pack r alpha → Set E := fun target =>
        Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))
      let B : InterSlot L inp.pack r alpha → Nat → E → E :=
        fun target k => normalTransition (I := I)
          (X.obj ((L.subseq hphi).φ k))
          (seqCenterD inp.decay P (L.subseq hphi) k (alpha.1 : Nat))
          (seqCenterD inp.decay P (L.subseq hphi) k
            (target.1.1 : Nat))
      let A : InterSlot L inp.pack r alpha → Nat → E → E :=
        fun target k => normalTransition (I := I)
          (X.obj ((L.subseq hphi).φ k))
          (seqCenterD inp.decay P (L.subseq hphi) k
            (target.1.1 : Nat))
          (seqCenterD inp.decay P (L.subseq hphi) k (alpha.1 : Nat))
      have hCageCompact : ∀ target : InterSlot L inp.pack r alpha,
          IsCompact (sourceCage target) := by
        intro target
        simpa only [sourceCage] using
          NetLimitData.hatCageCompact (I := I) (X := X) inp.decay P
            (L.subseq hphi) inp.pack r n alpha.1
      have hSuppCage : ∀ target : InterSlot L inp.pack r alpha,
          ∀ x : Y.M, x ∈ sourcePatch alpha → pairWeight x target ≠ 0 →
            x ∈ sourceCage target := by
        intro target x hx _hne
        have hmap := ((hgeom n).1 alpha).2.2 hx.2
        have hexp : expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
            (chi alpha x) = x := by
          simpa only [chi, normalChartAt] using
            NormalCoordinates.normalChartAt_left_inv (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
              hx.1.2
        change expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
            (chi alpha x) ∈
          (L.subseq hphi).hatBall inp.decay inp.D P inp.pack r n alpha.1 ∩
            ⋃ gamma : Fin (inp.pack.A r),
              (L.subseq hphi).innerBall inp.decay inp.D P inp.pack r n gamma
          at hmap
        rw [hexp] at hmap
        exact NetLimitData.hatCageSub (I := I) (X := X) inp.decay P
          (L.subseq hphi) inp.pack r n alpha.1 ⟨hx.1.1, hmap.1⟩
      have hR : 4 * L.lamInf (alpha.1 : Nat) <
          expRadiusGp (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) :=
        hgpN alpha.1 _ (hcenterN alpha)
      have hsrc : ∀ target : InterSlot L inp.pack r alpha,
          sourceCage target ⊆ (chi alpha).source := by
        intro target
        simpa only [sourceCage, chi, centerAll] using
          NetLimitData.hatCageSrcOfRad (I := I) (X := X) inp.decay P
            (L.subseq hphi) inp.pack r n centerAll alpha.1
            (hcenterN alpha) hR
      have hBcont : ∀ target : InterSlot L inp.pack r alpha,
          ContinuousOn (Jinf alpha target) (U8 target) := by
        intro target
        simpa only [U8] using (htrans alpha target).2.2.1
      have hsigma : 4 * L.lamInf (alpha.1 : Nat) /
            Real.sqrt (gpCoerciveConst (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n
                (alpha.1 : Nat))) <
          8 * L.lamInf (alpha.1 : Nat) := by
        have hhalf : (1 / 2 : Real) ≤ gpCoerciveConst (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) :=
          inp.normalBounds.half_le_gpConst ((L.subseq hphi).φ n)
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        have hsqrtHalf : (1 / 2 : Real) < Real.sqrt (1 / 2 : Real) := by
          have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
          have hn := Real.sqrt_nonneg (1 / 2 : Real)
          nlinarith
        have hsqrt : (1 / 2 : Real) < Real.sqrt
            (gpCoerciveConst (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n
                (alpha.1 : Nat))) :=
          hsqrtHalf.trans_le (Real.sqrt_le_sqrt hhalf)
        have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))) :=
          Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)))
        have hlam : 0 < L.lamInf (alpha.1 : Nat) :=
          inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
        apply (div_lt_iff₀ hsc).2
        have hfour : (4 : Real) < 8 * Real.sqrt
            (gpCoerciveConst (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n
                (alpha.1 : Nat))) := by
          nlinarith
        calc
          4 * L.lamInf (alpha.1 : Nat) <
              (8 * Real.sqrt (gpCoerciveConst (I := I) Y.metric
                (seqCenterD inp.decay P (L.subseq hphi) n
                  (alpha.1 : Nat)))) * L.lamInf (alpha.1 : Nat) :=
            mul_lt_mul_of_pos_right hfour hlam
          _ = (8 * L.lamInf (alpha.1 : Nat)) *
              Real.sqrt (gpCoerciveConst (I := I) Y.metric
                (seqCenterD inp.decay P (L.subseq hphi) n
                  (alpha.1 : Nat))) := by ring
      have hKU : ∀ target : InterSlot L inp.pack r alpha,
          (chi alpha) '' sourceCage target ⊆ U8 target := by
        intro target
        simpa only [chi, sourceCage, U8, centerAll] using
          hatCageImg' (I := I) (X := X) inp.decay P (L.subseq hphi)
            inp.pack r n centerAll alpha.1
            (fun gamma => 8 * L.lamInf (gamma : Nat))
            (hcenterN alpha) hR hsigma
      have hSuppV : ∀ target : InterSlot L inp.pack r alpha,
          ∀ x : Y.M, x ∈ sourcePatch alpha → pairWeight x target ≠ 0 →
            Jinf alpha target (chi alpha x) ∈ V6 target := by
        intro target x hx hne
        obtain ⟨target', hslot, hmem⟩ :=
          hsupp alpha (chi alpha x) hx.2 target.1.1 (by
            simpa only [pairWeight] using hne)
        have htarget : target' = target := by
          apply Subtype.ext
          apply Subtype.ext
          exact hslot
        simpa only [V6, htarget] using hmem
      obtain ⟨sourceK, hK, hSuppK, hsrcK, hKU_K, hKV6⟩ :=
        NetLimitData.hatSuppCageData (I := I) (X := X) inp.decay P
          (L.subseq hphi) inp.pack r n (s := sourcePatch alpha)
          pairWeight centerPair sourceCage U8 V6 (Jinf alpha)
          hCageCompact hSuppCage (by
            intro target
            simpa only [centerPair] using hsrc target)
          hBcont (by
            intro target
            simpa only [centerPair] using hKU target)
          (fun _ => Metric.isClosed_closedBall) (by
            intro target x hx hne
            simpa only [centerPair] using hSuppV target x hx hne)
      have hKV8 : ∀ target : InterSlot L inp.pack r alpha, ∀ v : E,
          v ∈ (chi alpha) '' sourceK target →
            Jinf alpha target v ∈ V8 target := by
        intro target v hv
        have hv6 := hKV6 target v (by
          simpa only [centerPair] using hv)
        change Jinf alpha target v ∈ Metric.closedBall 0
          (6 * L.lamInf (target.1.1 : Nat)) at hv6
        rw [Metric.mem_closedBall, dist_zero_right] at hv6
        change Jinf alpha target v ∈
          Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))
        rw [Metric.mem_ball, dist_zero_right]
        have hlam : 0 < L.lamInf (target.1.1 : Nat) :=
          inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat))
        nlinarith
      have hpoints := NetLimitData.hatSuppPtsOfComp (I := I) (X := X)
        inp.decay P (L.subseq hphi) inp.pack r n (s := sourcePatch alpha)
        pairWeight centerPair sourceK U8 V8 B (Jinf alpha) A (Jbarinf alpha)
        (hconn ((L.subseq hphi).φ n)) hK hSuppK hsrcK
        (fun _ => Metric.isOpen_ball)
        (fun target => by simpa only [B, U8] using
          (htrans alpha target).2.2.2.2.1)
        (fun target => by simpa only [A, V8] using
          (htrans alpha target).2.2.2.2.2.1)
        hBcont
        (fun target => by simpa only [V8] using
          (htrans alpha target).2.2.2.1)
        (fun target => by simpa only [U8, V8] using
          (htrans alpha target).2.2.2.2.2.2.1)
        hKU_K (by
          intro target v hv
          simpa only [centerPair] using hKV8 target v (by
            simpa only [centerPair] using hv))
      intro target epsilon hepsilon
      simpa only [pairWeight, centerPair, B, A, pairPts, chi] using
        hpoints target epsilon hepsilon
    intro alpha gamma epsilon hepsilon
    by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
        target.1.1 = gamma
    · let target := Classical.choose htarget
      have hslot : target.1.1 = gamma := Classical.choose_spec htarget
      obtain ⟨N, hN⟩ := hpair alpha target epsilon hepsilon
      refine ⟨N, ?_⟩
      intro a ha b hb x hx hne
      have hp := hN a ha b hb x hx (by simpa only [hslot] using hne)
      have hlookup : interSlot? alpha gamma = some target := by
        unfold interSlot?
        split
        next h =>
          congr 1
        next h =>
          exact (h htarget).elim
      simpa only [pts, totalPts, hlookup] using hp
    · refine ⟨0, ?_⟩
      intro a _ha b _hb x hx hne
      exfalso
      obtain ⟨target, hslot, _hmem⟩ := hsupp alpha (chi alpha x) hx.2 gamma hne
      exact htarget ⟨target, hslot⟩

set_option maxHeartbeats 800000 in
/-- **C3 join, fixed-subsequence form (shape A).**  `unifHatCageSelfComp` with the two
limit obligations discharged from the producer bridges: `hR` from the fixed-index
`Item3GpScaleAt` fact (`hgp`), and `hKV` from `binfMemClosed` (the two-index
maps land in a closed `V' γ ⊆ V γ`, so their `C∞`-limit `Binf γ` does too).  `B`/`A` stay
abstract; the concrete Step-B transition maps are plugged by the outer wrapper. -/
theorem stepCJoinFixed (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, B gamma a v ∈ V' gamma) :
    let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  exact NetLimitData.unifHatCageSelfComp hd P L pb r n rho hrho join radSeq center U V
    B Binf A Ainf hconn hX hcenter
    (fun gamma => hgp gamma (center gamma) (hcenter gamma))
    hrad hactive_mem hstrict hVopen hB hA hBcont hAcont hid hKU
    (fun gamma v hv =>
      hV'sub gamma (binfMemClosed (hB gamma) (hKU gamma hv) (hV'closed gamma)
        (Filter.Eventually.of_forall (hKV0 gamma v hv))))

set_option maxHeartbeats 800000 in
/-- **C3 join, fixed-subsequence explicit-weight form.**  This is the `4 * lamInf`
finite-hat endpoint matching `unifHatCageData`: it consumes an explicit normalized
`WeightDataOn` package instead of a bundled smooth partition of unity.  It is not yet the
book's `5 * lamInf` support-ball instantiation, which still needs a support-set adapter. -/
theorem stepCJoinDataFixed (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (mu : (X.obj (L.φ n)).M -> Fin (pb.A r) -> Real)
    (hmu :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      centerAverage.WeightDataOn
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
        (fun gamma : Fin (pb.A r) =>
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) mu)
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), mu x gamma ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill mu (ptsSeq a b)
              (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, B gamma a v ∈ V' gamma) :
    let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                mu
                (centerAverage.activeFill mu (ptsSeq a b)
                  (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric) (μ := mu)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hactive_mem a b y hy)
                  ((hmu.data hy).1.1) ((hmu.data hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  exact NetLimitData.unifHatCageData hd P L pb r n mu hmu join radSeq center U V
    B Binf A Ainf hconn hX hcenter
    (fun gamma => hgp gamma (center gamma) (hcenter gamma))
    hrad hactive_mem hstrict hVopen hB hA hBcont hAcont hid hKU
    (fun gamma v hv =>
      hV'sub gamma (binfMemClosed (hB gamma) (hKU gamma hv) (hV'closed gamma)
        (Filter.Eventually.of_forall (hKV0 gamma v hv))))

/-- **C3 producer join (shape B).**  Feeds the concrete Step-B same-manifold transition maps
`normalTransition` (indexed by the two sequence indices, over the reindexed sequence
`X ∘ L.φ`) into `stepCJoinFixed`: the H6-backed `existsTransUniv` produces the
subsequence `phi` and the `C∞` limit maps `Jinf`/`Jbarinf` with the two-sided cocycle,
then `stepCJoinFixed` averages them to the identity on the frozen source ball.  The
fixed convergence domains and independent H6 target-anchor domains, their
metric/exp-radius data, smoothness, overlap, maps-to, and cocycle data for
`existsTransUniv` are honest parametric inputs; the map-dependent
`hactive0`/`hstrict0`/`hKV0` are stated over ALL sequence indices and specialised at
`phi` (the `decodedCompPts` reindexing is a definitional identity). -/
theorem stepCJoin (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (x y : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (U V Ua Va : Fin (pb.A r) -> Set E)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (x gamma n))
    (hrad : forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
      xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b xx)
    (hU : forall gamma : Fin (pb.A r), IsOpen (U gamma))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hUa : forall gamma : Fin (pb.A r), IsOpen (Ua gamma))
    (hVa : forall gamma : Fin (pb.A r), IsOpen (Va gamma))
    (hUanorm : forall gamma : Fin (pb.A r),
      ∃ Z : Real, ∀ z ∈ Ua gamma, ‖z‖ ≤ Z)
    (hVanorm : forall gamma : Fin (pb.A r),
      ∃ Z : Real, ∀ z ∈ Va gamma, ‖z‖ ≤ Z)
    (hUmetric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      U gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (x gamma k)))
    (hVmetric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      V gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (y gamma k)))
    (hUametric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Ua gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (x gamma k)))
    (hVametric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Va gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (y gamma k)))
    (hUexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)))
    (hVexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      V gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (y gamma k)))
    (hUaexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Ua gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)))
    (hVaexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Va gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (y gamma k)))
    (hJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      ContDiffOn Real (⊤ : ℕ∞)
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k))
        (U gamma))
    (hJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      ContDiffOn Real (⊤ : ℕ∞)
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k))
        (V gamma))
    (hovlJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k) (U gamma))
    (hovlJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k) (V gamma))
    (hmapJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Set.MapsTo
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k))
        (U gamma) (Va gamma))
    (hmapJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Set.MapsTo
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k))
        (V gamma) (Ua gamma))
    (hLeft : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop, forall z, z ∈ U gamma ->
      normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k)
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k) z) = z)
    (hRight : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop, forall w, w ∈ V gamma ->
      normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k)
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k) w) = w)
    (hactive0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
        xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma xx ≠ 0 ->
            dist xx (NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
              (fun gamma => x gamma n)
              (fun gamma a => normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a))
              (fun gamma b => normalTransition (I := I) (X.obj (L.φ b)) (y gamma b) (x gamma b))
              a b xx gamma) < radSeq a b xx)
    (hstrict0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
        xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
              (NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
                (fun gamma => x gamma n)
                (fun gamma a => normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a))
                (fun gamma b => normalTransition (I := I) (X.obj (L.φ b)) (y gamma b) (x gamma b))
                a b)
              (fun yy : (X.obj (L.φ n)).M => yy) xx)
            join xx (radSeq a b xx))
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (x gamma n)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (x gamma n)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a) v ∈ V' gamma) :
    exists phi : Nat -> Nat, StrictMono phi /\
      (let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
       letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
       letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
       letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
       letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
       letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
       letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
       letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
       letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
         Manifold.metrizableSpace I (X.obj (L.φ n)).M
       letI : T3Space (X.obj (L.φ n)).M := inferInstance
       letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
         ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
       letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
         ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
       letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
       let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
         (fun gamma => x gamma n)
         (fun gamma a => normalTransition (I := I) (X.obj (L.φ (phi a))) (x gamma (phi a)) (y gamma (phi a)))
         (fun gamma b => normalTransition (I := I) (X.obj (L.φ (phi b))) (y gamma (phi b)) (x gamma (phi b)))
       forall eps : Real, eps > 0 -> exists N : Nat,
         forall a : Nat, a >= N -> forall b : Nat, b >= N ->
           forall xx : (X.obj (L.φ n)).M,
             xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
               dist xx
                 (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                   (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                   (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                   (centerAverage.activeFill
                     (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                     (ptsSeq a b) (fun yy : (X.obj (L.φ n)).M => yy))
                   join (fun yy : (X.obj (L.φ n)).M => yy)
                   (fun xx => radSeq (phi a) (phi b) xx)
                   (fun yy : (X.obj (L.φ n)).M => yy)
                   (fun yy hy => centerAverage.inputOfFillSelf (I := I)
                     (g := (X.obj (L.φ n)).metric)
                     (μ := fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                     (pts := ptsSeq a b) (join := join)
                     (r := fun xx => radSeq (phi a) (phi b) xx) (qstar := fun yy : (X.obj (L.φ n)).M => yy)
                     yy hcomplete (hrad (phi a) (phi b) yy hy) (hactive0 (phi a) (phi b) yy hy)
                     ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                       (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                       (rho := rho) (hrho := hrho) a b hy).1.1)
                     ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                       (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                       (rho := rho) (hrho := hrho) a b hy).1.2.1)
                     (hstrict0 (phi a) (phi b) yy hy)) xx) < eps) := by
  classical
  have htail (gamma : Fin (pb.A r)) : ∀ᶠ k in atTop,
      NormalTransAt (I := I)
        (NormalCoordMetricBoundInput.subseq (I := I) metricInput L.φ)
        x y U V Ua Va gamma k := by
    filter_upwards
      [hUmetric gamma, hVmetric gamma, hUametric gamma, hVametric gamma,
        hUexp gamma, hVexp gamma, hUaexp gamma, hVaexp gamma,
        hJ gamma, hJbar gamma, hovlJ gamma, hovlJbar gamma,
        hmapJ gamma, hmapJbar gamma, hLeft gamma, hRight gamma]
      with k hkUM hkVM hkUaM hkVaM hkUE hkVE hkUaE hkVaE
        hkJ hkJbar hkOvl hkOvlbar hkMap hkMapbar hkLeft hkRight
    exact
      { Umetric := hkUM
        Vmetric := hkVM
        Uametric := hkUaM
        Vametric := hkVaM
        Uexp := hkUE
        Vexp := hkVE
        Uaexp := hkUaE
        Vaexp := hkVaE
        J := hkJ
        Jbar := hkJbar
        ovlJ := hkOvl
        ovlJbar := hkOvlbar
        mapJ := hkMap
        mapJbar := hkMapbar
        left := hkLeft
        right := hkRight }
  obtain ⟨phi, hphi, Jinf, Jbarinf, hspec⟩ :=
    existsTransTail (I := I) (X := X.subseq L.φ)
      (NormalCoordMetricBoundInput.subseq (I := I) metricInput L.φ)
      x y U V Ua Va hU hVopen hUa hVa hUanorm hVanorm htail
  refine ⟨phi, hphi, ?_⟩
  exact stepCJoinFixed hd P L pb r n rho hrho join
    (fun a b => radSeq (phi a) (phi b))
    (fun gamma => x gamma n) U V
    (fun gamma a => normalTransition (I := I) (X.obj (L.φ (phi a))) (x gamma (phi a)) (y gamma (phi a)))
    Jinf
    (fun gamma b => normalTransition (I := I) (X.obj (L.φ (phi b))) (y gamma (phi b)) (x gamma (phi b)))
    Jbarinf
    hconn hX hcenter hgp
    (fun a b => hrad (phi a) (phi b))
    (fun a b => hactive0 (phi a) (phi b))
    (fun a b => hstrict0 (phi a) (phi b))
    hVopen
    (fun gamma => by
      simpa only [PointedRiemannianSeq.subseq] using (hspec gamma).2.2.2.2.1)
    (fun gamma => by
      simpa only [PointedRiemannianSeq.subseq] using (hspec gamma).2.2.2.2.2.1)
    (fun gamma => (hspec gamma).2.2.1)
    (fun gamma => (hspec gamma).2.2.2.1)
    (fun gamma => (hspec gamma).2.2.2.2.2.2.1)
    hKU V' hV'closed hV'sub
    (fun gamma v hv a => hKV0 gamma v hv (phi a))

end HCGCompactness
end DifferentialGeometry


