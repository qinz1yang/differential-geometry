import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Reparametrization.EnergyTransport
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Reparametrization.ConductivityStream
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

section

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped ContDiff Topology Manifold ENNReal

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem SmoothDiskExtension.exists_interior_reparametrization_energy_lt_area
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (W : ℂ → ℂ) (e f ψ : OpenPartialHomeomorph ℂ ℂ),
      1 < r ∧ ContDiffOn ℝ ∞ W (Metric.ball (0 : ℂ) r) ∧
      InjOn W (Metric.ball (0 : ℂ) r) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, 0 < (fderiv ℝ W z).toLinearMap.det) ∧
      e.source = Metric.ball (0 : ℂ) r ∧ e.target = W '' Metric.ball (0 : ℂ) r ∧
      (e : ℂ → ℂ) = W ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      f.source = W '' Metric.ball (0 : ℂ) 1 ∧ f.target = Metric.ball (0 : ℂ) 1 ∧
      DifferentiableOn ℂ f f.source ∧ DifferentiableOn ℂ f.symm f.target ∧
      (∀ z ∈ f.source, deriv f z ≠ 0) ∧
      ψ.source = Metric.ball (0 : ℂ) 1 ∧ ψ.target = Metric.ball (0 : ℂ) 1 ∧
      ψ 0 = 0 ∧ ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      (∀ z, ψ z = f (W z)) ∧ (∀ z, ψ.symm z = e.symm (f.symm z)) ∧
      IntegrableOn (diskMapEnergyDensity g (Q ∘ ψ.symm)) (Metric.closedBall (0 : ℂ) 1) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (Q ∘ ψ.symm) z) <
        riemannianDiskArea g q + ε := by
  obtain ⟨hext, N, hN, hDN, hQs⟩ := hQ
  let Ω : TopologicalSpace.Opens ℂ := ⟨N, hN⟩
  obtain ⟨δ, h, hδ, hinner, _, harea⟩ :=
    exists_regularized_pullback_disk_metric_area_lt g Ω hQs hDN hε
  obtain ⟨η, hη, hsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hN hDN
  have hball : Metric.closedBall (0 : ℂ) (η + 1) ⊆ N := by
    simpa only [cthickening_closedBall hη.le (zero_le_one' ℝ)] using hsub
  let r := η / 2 + 1
  have hr : 1 < r := by dsimp [r]; linarith
  have hrR : r < η + 1 := by dsimp [r]; linarith
  have hp := exists_dirichlet_stream_pullbackConductivity g hN hQs hδ
    (zero_lt_one.trans hr) hrR hball
  have hz : Complex.orthonormalBasisOneI.repr (0 : ℂ) = 0 := map_zero _
  rw [hz] at hp
  obtain ⟨B, A, u, v, s, hAB, _, hA, hu, ht, hv, hs, huv, hds, hBel⟩ := hp
  have hdet (x : V) (hx : x ∈ Metric.ball (0 : V) (η + 1)) : (A.a x).det = 1 := by
    rw [hA x (Metric.ball_subset_closedBall hx)]
    exact det_pullbackConductivity g Q hδ _
  have hsol := DeGiorgi.isHomogeneousWeakSolution_isSolution hu
  have hinj := hsol.injOn_complex_stream_of_coordinate_trace (zero_lt_one.trans hr) hrR.le B
    (fun x _ => congrFun hAB x) hdet ht hv.continuousOn huv hds
  have hJ := hsol.det_fderiv_pos_of_coordinate_trace_stream (zero_lt_one.trans hr) hrR.le B
    (fun x _ => congrFun hAB x) hdet ht hv.continuousOn huv hds
  let W := fun z => (v (Complex.orthonormalBasisOneI.repr z) : ℂ) +
    (s (Complex.orthonormalBasisOneI.repr z) : ℂ) * Complex.I
  have hmap : MapsTo Complex.orthonormalBasisOneI.repr (Metric.ball (0 : ℂ) r)
      (Metric.ball (0 : V) r) := by intro z hz; simpa using hz
  have hW : ContDiffOn ℝ ∞ W (Metric.ball (0 : ℂ) r) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hv.comp Complex.orthonormalBasisOneI.repr.contDiff.contDiffOn hmap)).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hs.comp Complex.orthonormalBasisOneI.repr.contDiff.contDiffOn hmap)).mul contDiffOn_const)
  obtain ⟨e, f, ψ, hes, het, heW, he, hei, hfs, hft, hf, hfi, hfd,
    hψs, hψt, hψ0, hψ, hψi, hψeq, hψieq, hInt, hEn⟩ :=
    exists_normalized_disk_coordinate_energy_le_regularized_area g Q Ω h hδ
      (hQs.of_le (by norm_cast)) hinner hr hDN hW hinj (fun z hz => (hJ z hz).ne') hBel
  have harea' : (∫ z in Metric.closedBall (0 : ℂ) 1, regularizedPullbackAreaDensity g Q δ z) <
      riemannianDiskArea g q + ε := by
    simpa only [riemannianDiskArea_eq_of_extension g q Q hext] using harea
  exact ⟨r, W, e, f, ψ, hr, hW, hinj, hJ, hes, het, heW, he, hei, hfs, hft, hf, hfi, hfd,
    hψs, hψt, hψ0, hψ, hψi, hψeq, hψieq, hInt, hEn.trans_lt harea'⟩

end DifferentialGeometry.Geometry

end

end
