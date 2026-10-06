import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNbhdP6Seed_S23
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalNorm

/-!
# CH12-O12: traced families (G2d, generic history part)

Notation of [FROZEN] CH12-O9/O12: a traced family `TF(a, X, ρ, τ, K)` is a backward
trace `X` of `x0` from `activeStage a` to `activeStage top` such that every time-`u` ball
`B_{g_u}(X(u), ρ)` (`a ≤ u ≤ top`) is a traced region of depth `τ` and bound `K`.

* `sectional_of_traced_O12`: a traced region with bound `K` has `sec ≥ -K` on its ball
  (read off at the top time of each trace, `|Sec| ≤ |Rm|`).
* `kl82_inputs_of_traced_family_O12`: restricting a traced family to a later initial
  time `v` gives exactly the unscathed-family and sectional hypotheses of the frozen
  KL82.1 statement at radius `r1 ≤ ρ` with `K ≤ r1⁻²`.

Source: Kleiner–Lott, G&T 12 (2008), Lemma 82.1 hypotheses and §86 (the local copy of the
book is not available on this machine; statements follow the frozen CH12-O6/O9 records).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- A traced region with curvature bound `K` has sectional curvature `≥ -K` on its ball. -/
theorem sectional_of_traced_O12 {H : ObservedHistory.{u}} {u : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt u).Carrier} {ρ τ K : ℝ} (h : H.isTracedRegion u p ρ τ K) (hK : 0 ≤ K) :
    ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage u) u) p ρ,
      SectionalBoundedBelowAt (H.stageMetric (H.activeStage u) u) q (-K) := by
  obtain ⟨_, _, a, hat, _, htr⟩ := h
  intro q hq
  obtain ⟨A, hA⟩ := htr q hq
  have h1 := hA.1 u hat le_rfl
  have he : A.point (H.activeStage u) (H.activeStage_mono hat) (H.activeStage_mono le_rfl) = q :=
    A.endpoint_eq
  rw [he] at h1
  apply sectionalBoundedBelowAt_neg_of_sqrt_normSq0S_le
  calc Real.sqrt _ ≤ Real.sqrt (K ^ 2) := Real.sqrt_le_sqrt h1
    _ = K := Real.sqrt_sq hK

/-- A traced family, restricted to the initial time `v ≥ top - τ`, supplies the
unscathed-family and sectional hypotheses of the frozen KL82.1 statement at radius
`r1 ≤ ρ`, provided `K ≤ r1⁻²`. -/
theorem kl82_inputs_of_traced_family_O12 {H : ObservedHistory.{u}}
    {top a : Icc (0 : ℝ) H.horizon} {hat : a ≤ top} {x0 : (H.stageAt top).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top) (H.activeStage_mono hat) x0)
    {ρ τ K r1 : ℝ} (hK : 0 ≤ K) (hr1 : r1 ≤ ρ) (hKr : K ≤ (r1 ^ 2)⁻¹)
    (hTF : ∀ (u : Icc (0 : ℝ) H.horizon) (hau : a ≤ u) (hut : u ≤ top),
      H.isTracedRegion u (X.point (H.activeStage u) (H.activeStage_mono hau)
        (H.activeStage_mono hut)) ρ τ K)
    (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top) (hwin : (top : ℝ) - τ ≤ v) :
    ∀ (u : Icc (0 : ℝ) H.horizon) (hvu : v ≤ u) (hut : u ≤ top),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage u) u)
          ((X.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt)).point
            (H.activeStage u) (H.activeStage_mono hvu) (H.activeStage_mono hut)) r1,
        (∃ A : BackwardPointTrace H (H.activeStage v) (H.activeStage u)
            (H.activeStage_mono hvu) q, A.isRmBoundedBy (hat := hvu) K) ∧
          SectionalBoundedBelowAt (H.stageMetric (H.activeStage u) u) q (-(r1 ^ 2)⁻¹) := by
  intro u hvu hut q hq
  have hTFu := hTF u (hav.trans hvu) hut
  have hq' : q ∈ riemannianBallOf (H.stageMetric (H.activeStage u) u)
      (X.point (H.activeStage u) (H.activeStage_mono (hav.trans hvu))
        (H.activeStage_mono hut)) ρ :=
    riemannianBallOf_mono _ _ hr1 hq
  refine ⟨?_, (sectional_of_traced_O12 hTFu hK q hq').mono (neg_le_neg hKr)⟩
  obtain ⟨_, _, b, hbu, hbeq, htr⟩ := hTFu
  obtain ⟨A, hA⟩ := htr q hq'
  have hut' : (u : ℝ) ≤ top := hut
  have hbv : b ≤ v := by
    change (b : ℝ) ≤ v
    rw [hbeq]
    linarith
  exact ⟨A.restrictFirst (H.activeStage_mono hbv) (H.activeStage_mono hvu),
    BackwardPointTrace.isRmBoundedBy.restrictFirst A hA hbv hvu⟩

end GC.LongTime.Ch12
