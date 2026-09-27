import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDensity

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem exists_smooth_spanning_disks_tendsto_area_of_area_approximation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)}
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ w : C(closedDisk, M),
      DiskSmoothUpToBoundary (E := E) w ∧ diskTrace w = γ ∧
        |riemannianDiskArea g w - riemannianDiskArea g v| ≤ ε) :
    ∃ vj : ℕ → C(closedDisk, M),
      (∀ j, DiskSmoothUpToBoundary (E := E) (vj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) := by
  let w : ℕ → C(closedDisk, M) := fun j =>
    Classical.choose (happrox (1 / ((j : ℝ) + 1)) (by positivity))
  have hw (j : ℕ) : DiskSmoothUpToBoundary (E := E) (w j) ∧ diskTrace (w j) = γ ∧
      |riemannianDiskArea g (w j) - riemannianDiskArea g v| ≤ 1 / ((j : ℝ) + 1) :=
    Classical.choose_spec (happrox (1 / ((j : ℝ) + 1)) (by positivity))
  refine ⟨w, fun j => ⟨(hw j).1, (hw j).2.1⟩, ?_⟩
  have hnorm : Tendsto
      (fun j : ℕ => ‖riemannianDiskArea g (w j) - riemannianDiskArea g v‖) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_norm]
    simpa only [Real.norm_eq_abs] using (hw j).2.2
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr hnorm

omit [FiniteDimensional ℝ E] in
theorem exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_area_approximation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)}
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (w : C(closedDisk, M)) (W : ℂ → M),
      SmoothDiskExtension (E := E) w W ∧ diskTrace w = γ ∧
        |riemannianDiskArea g w - riemannianDiskArea g v| ≤ ε) :
    ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) := by
  let w : ℕ → C(closedDisk, M) := fun j =>
    Classical.choose (happrox (1 / ((j : ℝ) + 1)) (by positivity))
  let W : ℕ → ℂ → M := fun j =>
    Classical.choose (Classical.choose_spec (happrox (1 / ((j : ℝ) + 1)) (by positivity)))
  have hw (j : ℕ) : SmoothDiskExtension (E := E) (w j) (W j) ∧ diskTrace (w j) = γ ∧
      |riemannianDiskArea g (w j) - riemannianDiskArea g v| ≤ 1 / ((j : ℝ) + 1) :=
    Classical.choose_spec (Classical.choose_spec (happrox (1 / ((j : ℝ) + 1)) (by positivity)))
  refine ⟨w, W, fun j => ⟨(hw j).1, (hw j).2.1⟩, ?_⟩
  have hnorm : Tendsto
      (fun j : ℕ => ‖riemannianDiskArea g (w j) - riemannianDiskArea g v‖) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_norm]
    simpa only [Real.norm_eq_abs] using (hw j).2.2
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr hnorm

end DifferentialGeometry.Geometry
