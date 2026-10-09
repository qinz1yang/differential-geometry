import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Topology.SigmaCompactOpen

/-!
# Fixed terminal open buffers

Restriction to an actual terminal ball turns finite spatial curvature bounds
into global bounds on one fixed open carrier, preserving the original flow.
-/

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- Restrict the SAME flow to its fixed terminal open quarter-ball. Curvature jets
on the actual closed quarter-ball become global bounds on this restricted carrier.
The closure is compact in the original carrier, not a compactness assertion about
the open carrier. The original time interval is unchanged. -/
theorem exists_fixed_open_terminal_buffer
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric 0) p R))
    (J : Set ℝ) (B : ℕ → ℝ)
    (hjets : ∀ k : ℕ, ∀ s ∈ J,
      ∀ y ∈ riemannianClosedBallOf (S.base.metric 0) p (R/4),
        curvDerivNorm k (S.base.metric s) y ≤ B k) :
    ∃ V : Opens M,
      (V : Set M) = riemannianBallOf (S.base.metric 0) p (R/4) ∧
      p ∈ V ∧ IsCompact (closure (V : Set M)) ∧
      closure (V : Set M) ⊆ riemannianClosedBallOf (S.base.metric 0) p (R/4) ∧
      letI : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
      let T := solutionOnRestrictOpen S V
      IsSolutionOn T ∧
      (∀ s : ℝ, T.base.metric s = (S.base.metric s).restrictOpen V) ∧
      ∀ k : ℕ, ∀ s ∈ J, ∀ y : V,
        curvDerivNorm k (T.base.metric s) y ≤ B k := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let V : Opens M := ⟨riemannianBallOf (S.base.metric 0) p (R/4),
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist (S.base.metric 0) p)
      continuous_const⟩
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  have hsub : (V : Set M) ⊆ riemannianClosedBallOf (S.base.metric 0) p (R/4) := by
    intro y hy
    change riemannianEDistOf (S.base.metric 0) p y < ENNReal.ofReal (R/4) at hy
    change riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal (R/4)
    exact hy.le
  have hclosure : closure (V : Set M) ⊆
      riemannianClosedBallOf (S.base.metric 0) p (R/4) :=
    closure_minimal hsub (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
  have hsmall : IsCompact (riemannianClosedBallOf (S.base.metric 0) p (R/4)) :=
    hcompact.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
      (riemannianClosedBallOf_mono _ _ (by linarith : R/4 ≤ R))
  have hp : p ∈ V := by
    change riemannianEDistOf (S.base.metric 0) p p < ENNReal.ofReal (R/4)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  refine ⟨V,rfl,hp,hsmall.of_isClosed_subset isClosed_closure hclosure,hclosure,?_,?_,?_⟩
  · exact isSolutionOn_restrictOpen S hS V
  · intro s
    rfl
  · intro k s hs y
    change curvDerivNorm k ((S.base.metric s).restrictOpen V) y ≤ B k
    rw [curvDerivNorm_restrictOpen]
    exact hjets k s hs y.val (hsub y.property)

end DifferentialGeometry.PDE.RicciFlow
