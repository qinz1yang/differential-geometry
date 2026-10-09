import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Reparametrization.Interior
import DifferentialGeometry.Analysis.Complex.RiemannMapping.InverseBoundary
import DifferentialGeometry.Topology.LoopSpace.DiskBoundaryHomeomorphism
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Locality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.WeakJordanHomeomorphism
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.RadialStationarity

section

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped ContDiff Topology Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem SmoothDiskExtension.exists_competitor_energy_lt_area_add
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (htrace : DiskWeakJordanTrace γ q) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : C(closedDisk, M), v ∈ weaklyMonotoneDiskCompetitors g γ ∧
      riemannianDiskEnergy g v < riemannianDiskArea g q + ε := by
  obtain ⟨r, W, e, f, ψ, hr, _, _, _, hes, _, heW, he, hei, hfs, hft, hf, _, _,
    hψs, hψt, _, _, _, _, hψieq, _, hEn⟩ :=
    hQ.exists_interior_reparametrization_energy_lt_area g hε
  have hfsource : f.source = e '' Metric.ball (0 : ℂ) 1 := by rw [heW]; exact hfs
  obtain ⟨C, D, H, _, hHiLip, _, _, hHi⟩ :=
    Complex.exists_bilipschitz_riemann_map_comp_extension_of_buffered_disk
      e f hr hes he hei hfsource hft hf
  have hHiψ (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      (H.symm ⟨z, Metric.ball_subset_closedBall hz⟩ : ℂ) = ψ.symm z := by
    rw [hHi z hz, hψieq]
  obtain ⟨δ, hδ⟩ := exists_circle_homeomorph_of_disk_homeomorph_extension
    H.symm ψ.symm hψt hψs hHiψ
  let φ : C(closedDisk, closedDisk) := ⟨H.symm, H.symm.continuous⟩
  have hq : q ∈ weaklyMonotoneDiskCompetitors g γ := ⟨htrace, hQ.lipschitz g⟩
  have hcomp := (mem_weaklyMonotoneDiskCompetitors_comp_of_boundary_reparametrization
    g hq φ hHiLip ⟨δ, δ.continuous⟩ (isWeaklyMonotoneOnce_homeomorph δ) hδ).1
  refine ⟨q.comp φ, hcomp, ?_⟩
  rw [riemannianDiskEnergy_comp_eq_of_extensions g hQ.1 φ hHiψ]
  exact hEn

theorem SmoothDiskExtension.disk_energy_inf_le_area
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (htrace : DiskWeakJordanTrace γ q) :
    sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) ≤ riemannianDiskArea g q := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v, hv, hEn⟩ := hQ.exists_competitor_energy_lt_area_add g htrace hε
  have hbound : BddBelow ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g w
  exact (csInf_le hbound (mem_image_of_mem _ hv)).trans hEn.le

end DifferentialGeometry.Geometry

end

end
