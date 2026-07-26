import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ConnAddD2Blocks

/-!
# Traced top-order cancellation for the local addition

The full-state local-addition Hessian has one term containing the second
derivative of the section.  This file contracts that identity against an
arbitrary finite coefficient matrix.  On the locus where the vertical
derivative is invertible, its inverse still cancels after the contraction.

This is the exact Banach-calculus principal cancellation used when a local
coordinate expression of harmonic-map tension is converted into an equation
for the local-addition state.  It does not identify the remaining first-jet
term with the geometric tension remainder.
-/

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

/-- The finite coefficient trace of the first-jet remainder in the
local-addition Hessian. -/
noncomputable def connAddTraceRem {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E) : E :=
  ∑ i, ∑ j, c i j • connAddD2Rem (I := I) g p v z (e i) (e j)

/-- The finite coefficient trace of the Hessian of a local-addition section
composition. -/
noncomputable def connAddTraceD2 {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E) : E :=
  ∑ i, ∑ j, c i j •
    fderiv ℝ
      (fderiv ℝ (fun x ↦ localAddTarget (I := I) g p (x, v x))) z
      (e i) (e j)

/-- Tracing the full-state Hessian preserves its exact split into the
vertical derivative of the traced section Hessian and a first-jet
remainder. -/
theorem connAddTrace_split {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E)
    (hF : ContDiffAt ℝ 2 (localAddTarget (I := I) g p) (z, v z))
    (hv : ContDiffAt ℝ 2 v z) :
    connAddTraceD2 (I := I) g p v z c e =
      partialFDeriv₂ (localAddTarget (I := I) g p) z (v z)
          (∑ i, ∑ j, c i j •
            fderiv ℝ (fderiv ℝ v) z (e i) (e j)) +
        connAddTraceRem (I := I) g p v z c e := by
  classical
  simp only [connAddTraceD2, connAddTraceRem]
  simp_rw [connAddD2_split (I := I) g p v z _ _ hF hv]
  simp only [smul_add, Finset.sum_add_distrib, map_sum, map_smul]

/-- The traced first-jet remainder separates into the horizontal-horizontal,
horizontal-vertical, vertical-horizontal, and vertical-vertical blocks.  In
particular, the last block is quadratic in the first derivative of the
section and the middle two blocks are linear in it. -/
theorem connAddTrace_blocks {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E) :
    connAddTraceRem (I := I) g p v z c e =
      (∑ i, ∑ j, c i j •
        fderiv ℝ (fderiv ℝ (localAddTarget (I := I) g p)) (z, v z)
          (e i, 0) (e j, 0)) +
      (∑ i, ∑ j, c i j •
        fderiv ℝ (fderiv ℝ (localAddTarget (I := I) g p)) (z, v z)
          (e i, 0) (0, fderiv ℝ v z (e j))) +
      (∑ i, ∑ j, c i j •
        fderiv ℝ (fderiv ℝ (localAddTarget (I := I) g p)) (z, v z)
          (0, fderiv ℝ v z (e i)) (e j, 0)) +
      (∑ i, ∑ j, c i j •
        fderiv ℝ (fderiv ℝ (localAddTarget (I := I) g p)) (z, v z)
          (0, fderiv ℝ v z (e i)) (0, fderiv ℝ v z (e j))) := by
  classical
  simp only [connAddTraceRem]
  simp_rw [connAddD2_blocks (I := I) g p v z _ _]
  simp only [smul_add, Finset.sum_add_distrib]

/-- On the invertible vertical-derivative locus, subtracting the traced
first-jet remainder and applying the inverse recovers the complete traced
second derivative of the local-addition state. -/
theorem connAddTrace_cancel {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E)
    (hF : ContDiffAt ℝ 2 (localAddTarget (I := I) g p) (z, v z))
    (hv : ContDiffAt ℝ 2 v z)
    (hJ : (partialFDeriv₂
      (localAddTarget (I := I) g p) z (v z)).IsInvertible) :
    (partialFDeriv₂ (localAddTarget (I := I) g p) z (v z)).inverse
        (connAddTraceD2 (I := I) g p v z c e -
          connAddTraceRem (I := I) g p v z c e) =
      ∑ i, ∑ j, c i j •
        fderiv ℝ (fderiv ℝ v) z (e i) (e j) := by
  rw [connAddTrace_split (I := I) g p v z c e hF hv,
    add_sub_cancel_right]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self hJ _

/-- A fixed chart has one compact state tube on which every finite
coefficient trace enjoys the exact top-order cancellation.  The radius is
chosen before the coefficient matrix, frame directions, and section state. -/
theorem exists_connAddTrace
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r > 0,
      IsCompact (Metric.closedBall (localAddZeroCoord (I := I) p) r) ∧
      ContinuousOn
        (fun w : E × E ↦
          (partialFDeriv₂
            (localAddTarget (I := I) g p) w.1 w.2).inverse)
        (Metric.closedBall (localAddZeroCoord (I := I) p) r) ∧
      ∀ (n : ℕ) (v : E → E) (z : E)
          (c : Fin n → Fin n → ℝ) (e : Fin n → E),
        (z, v z) ∈ Metric.closedBall (localAddZeroCoord (I := I) p) r →
        ContDiffAt ℝ 2 (localAddTarget (I := I) g p) (z, v z) →
        ContDiffAt ℝ 2 v z →
        (partialFDeriv₂
            (localAddTarget (I := I) g p) z (v z)).inverse
            (connAddTraceD2 (I := I) g p v z c e -
              connAddTraceRem (I := I) g p v z c e) =
          ∑ i, ∑ j, c i j •
            fderiv ℝ (fderiv ℝ v) z (e i) (e j) := by
  obtain ⟨r, hr, hcompact, hinv, hcont⟩ :=
    exists_connAdd_tube (I := I) g p
  refine ⟨r, hr, hcompact, hcont, ?_⟩
  intro n v z c e hstate hF hv
  exact connAddTrace_cancel (I := I) g p v z c e hF hv
    (hinv (z, v z) hstate)

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
