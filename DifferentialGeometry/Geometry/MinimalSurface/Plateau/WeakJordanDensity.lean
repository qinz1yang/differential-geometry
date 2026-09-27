import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TraceLiftLipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TracePhaseAnnulus.Lipschitz
import DifferentialGeometry.Geometry.Metric.LoopLipschitz
import DifferentialGeometry.Geometry.Measure.Area.Reparametrization
import DifferentialGeometry.Geometry.Measure.Area.SmoothDensity

section

noncomputable section

open Set Function Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

private theorem exists_spanning_disk_area_eq_of_continuous_lift
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hp : ∀ t, ψ (t + 1) = ψ t + 1)
    {u : C(closedDisk, M)} {L : ℝ≥0}
    (htr : ∀ t : ℝ, u (diskBoundary (t : loopCircle)) = γ (ψ t : loopCircle))
    (hL : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) :
    ∃ v ∈ spanningDiskCompetitors g γ, riemannianDiskArea g v = riemannianDiskArea g u := by
  let B : ℝ≥0 := ⟨2 * Real.pi, by positivity⟩
  have hb : LipschitzWith B
      (diskBoundary : loopCircle → closedDisk) := fun s t => circle_boundary_lipschitz s t
  have hbr : LipschitzWith B
      (fun t : ℝ => diskBoundary (t : loopCircle)) := by
    intro s t
    apply (hb (s : loopCircle) (t : loopCircle)).trans
    apply mul_le_mul' le_rfl
    simpa only [ENNReal.coe_one, one_mul] using loopCircle_projection_lipschitz s t
  have hc : ∀ s t : ℝ, riemannianEDistOf g (γ (ψ s : loopCircle))
      (γ (ψ t : loopCircle)) ≤
        ((L * B : ℝ≥0) : ℝ≥0∞) * edist s t := by
    intro s t
    rw [← htr s, ← htr t]
    apply (hL _ _).trans
    rw [ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' le_rfl (hbr s t)
  obtain ⟨C, hC⟩ := exists_lipschitzWith_affinePeriodic_parameterLift g hγ him hψ hp hc
  obtain ⟨Lγ, hγL⟩ := exists_riemannian_lipschitz_freeLoop_of_contMDiff g (hγ.of_le (by simp))
  exact exists_spanning_disk_area_eq_of_lipschitz_lift g hγ hγL hC hp htr hL

theorem exists_spanning_disk_area_eq_of_weakJordanTrace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {u : C(closedDisk, M)} (hu : DiskWeakJordanTrace γ u) {L : ℝ≥0}
    (hL : ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) :
    ∃ v ∈ spanningDiskCompetitors g γ, riemannianDiskArea g v = riemannianDiskArea g u := by
  obtain ⟨σ, ⟨ψ, hc, hl, hsign⟩, htr⟩ := hu
  have hlift (t : ℝ) : u (diskBoundary (t : loopCircle)) = γ (ψ t : loopCircle) := by
    rw [hl]
    exact congrArg (fun η : freeLoop M => η (t : loopCircle)) htr
  rcases hsign with ⟨_, hp⟩ | ⟨_, hp⟩
  · exact exists_spanning_disk_area_eq_of_continuous_lift g hγ him hc hp hlift hL
  · let v : C(closedDisk, M) := u.comp ⟨diskReflection, diskReflection.continuous⟩
    have hvlip (z w : closedDisk) : riemannianEDistOf g (v z) (v w) ≤
        (L : ℝ≥0∞) * edist z w := by
      apply (hL (diskReflection z) (diskReflection w)).trans
      apply mul_le_mul' le_rfl
      simpa only [ENNReal.coe_one, one_mul] using diskReflection_lipschitz z w
    have hperiod (t : ℝ) : ψ (-(t + 1)) = ψ (-t) + 1 := by
      have hh := hp (-t - 1)
      rw [sub_add_cancel] at hh
      have heq : -(t + 1) = -t - 1 := by ring
      rw [heq]
      linarith
    have hvtr (t : ℝ) : v (diskBoundary (t : loopCircle)) =
        γ (ψ (-t) : loopCircle) := by
      change u (diskReflection (diskBoundary (t : loopCircle))) = _
      rw [diskReflection_diskBoundary, ← QuotientAddGroup.mk_neg]
      exact hlift (-t)
    obtain ⟨w, hw, hwa⟩ := exists_spanning_disk_area_eq_of_continuous_lift g hγ him
      (hc.comp continuous_neg) hperiod hvtr hvlip
    exact ⟨w, hw, hwa.trans (riemannianDiskArea_diskReflection g hL)⟩

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Filter Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_smooth_spanning_disks_tendsto_area_of_weakJordanTrace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {u : C(closedDisk, M)} (hu : DiskWeakJordanTrace γ u) {L : ℝ≥0}
    (hL : ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) :
    ∃ (vj : ℕ → C(closedDisk, M)) (Vj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Vj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g u)) := by
  obtain ⟨v, hv, harea⟩ := exists_spanning_disk_area_eq_of_weakJordanTrace g hγ him hu hL
  obtain ⟨vj, Vj, hj, ht⟩ := exists_smooth_disk_approximation_preserving_trace_area g hγ hv
  exact ⟨vj, Vj, hj, harea ▸ ht⟩

theorem exists_smooth_spanning_disk_area_lt_of_weakJordanTrace_of_immersion
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {u : C(closedDisk, M)} (hu : DiskWeakJordanTrace γ u) {L : ℝ≥0}
    (hL : ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : C(closedDisk, M)) (V : ℂ → M), SmoothDiskExtension (E := E) v V ∧
      diskTrace v = γ ∧ riemannianDiskArea g v < riemannianDiskArea g u + ε := by
  obtain ⟨vj, Vj, hj, ht⟩ :=
    exists_smooth_spanning_disks_tendsto_area_of_weakJordanTrace g hγ him hu hL
  obtain ⟨j, hjnear⟩ :=
    (ht.eventually (gt_mem_nhds (lt_add_of_pos_right (riemannianDiskArea g u) hε))).exists
  exact ⟨vj j, Vj j, (hj j).1, (hj j).2, hjnear⟩

theorem riemannianDiskArea_le_of_minimizingSmoothDisk_of_weakJordanTrace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {u : C(closedDisk, M)}
    (hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      diskTrace v = γ → riemannianDiskArea g u ≤ riemannianDiskArea g v)
    {v : C(closedDisk, M)} (hv : DiskWeakJordanTrace γ v) {L : ℝ≥0}
    (hL : ∀ z w : closedDisk,
      riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) :
    riemannianDiskArea g u ≤ riemannianDiskArea g v := by
  obtain ⟨vj, Vj, hj, ht⟩ :=
    exists_smooth_spanning_disks_tendsto_area_of_weakJordanTrace g hγ him hv hL
  exact ge_of_tendsto' ht fun j => hmin (vj j) (hj j).1.smoothUpToBoundary (hj j).2

end DifferentialGeometry.Geometry

end

end
