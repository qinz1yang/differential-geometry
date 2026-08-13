import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ConnAddD2Blocks
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

noncomputable def connAddTraceRem {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E) : E :=
  ∑ i, ∑ j, c i j • connAddD2Rem (I := I) g p v z (e i) (e j)

noncomputable def connAddTraceD2 {n : ℕ}
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z : E) (c : Fin n → Fin n → ℝ)
    (e : Fin n → E) : E :=
  ∑ i, ∑ j, c i j •
    fderiv ℝ
      (fderiv ℝ (fun x ↦ localAddTarget (I := I) g p (x, v x))) z
      (e i) (e j)

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
