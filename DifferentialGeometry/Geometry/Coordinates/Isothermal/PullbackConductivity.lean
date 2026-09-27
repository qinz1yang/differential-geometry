import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.Coefficients
import DifferentialGeometry.Geometry.Coordinates.Isothermal.PullbackBeltrami
import DifferentialGeometry.Analysis.Elliptic.Coefficients.Extension
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.StreamFunction
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.Noncritical

section

noncomputable section
open Set Filter MeasureTheory Manifold
open scoped ContDiff Topology Manifold ENNReal

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)

def pullbackConductivity (g : SmoothRiemannianMetric I M) (q : ℂ → M) (δ : ℝ) (z : ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  planarConductivity (pullbackMetricCoefficients g q z 1 1 + δ)
    (pullbackMetricCoefficients g q z Complex.I Complex.I + δ)
    (pullbackMetricCoefficients g q z 1 Complex.I)

theorem pullbackConductivity_posDef
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    (pullbackConductivity g q δ z).PosDef :=
  planarConductivity_posDef
    (add_pos_of_nonneg_of_pos (metric_inner_self_nonneg g (q z) _) hδ)
    (regularized_pullback_gram_pos g q hδ z)

theorem contDiffOn_pullbackConductivity
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ q Ω) {δ : ℝ} (hδ : 0 < δ) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun z => pullbackConductivity g q δ z i j) Ω := by
  have hA := contDiffOn_pullback_metric_coefficients g hΩ hq
  exact contDiffOn_planarConductivity
    (((hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add contDiffOn_const)
    (((hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add contDiffOn_const)
    ((hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
    (fun z _ => regularized_pullback_gram_pos g q hδ z) i j

theorem exists_smoothEllipticBilinearForm_pullbackConductivity
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ q Ω) {δ : ℝ} (hδ : 0 < δ)
    {c : ℂ} {R : ℝ} (hball : Metric.closedBall c R ⊆ Ω) :
    ∃ B : SmoothEllipticBilinearForm 2 (univ : Set V),
      (∀ x ∈ Metric.closedBall (Complex.orthonormalBasisOneI.repr c) R,
        B.a x = pullbackConductivity g q δ (Complex.orthonormalBasisOneI.repr.symm x)) ∧
      (∀ x, (B.a x).PosDef) ∧ B.c = 0 := by
  let e := Complex.orthonormalBasisOneI.repr
  let S := e.symm ⁻¹' Ω
  have hS : IsOpen S := hΩ.preimage e.symm.continuous
  have hsub : Metric.closedBall (e c) R ⊆ S := by
    intro x hx
    apply hball
    simpa only [Metric.mem_closedBall, ← e.symm.dist_map,
      LinearIsometryEquiv.symm_apply_apply] using hx
  exact exists_smoothEllipticBilinearForm_extension hS (isCompact_closedBall _ _) hsub
    (fun x => pullbackConductivity g q δ (e.symm x))
    (fun i j => (contDiffOn_pullbackConductivity g hΩ hq hδ i j).comp
      e.symm.toContinuousLinearEquiv.contDiff.contDiffOn (fun x hx => hx))
    (fun x _ => pullbackConductivity_posDef g q hδ (e.symm x))

theorem exists_dirichlet_solution_pullbackConductivity
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ q Ω) {δ : ℝ} (hδ : 0 < δ)
    {c : ℂ} {R : ℝ} (hball : Metric.closedBall c R ⊆ Ω) :
    ∃ (B : SmoothEllipticBilinearForm 2 (univ : Set V))
      (A : DeGiorgi.EllipticCoeff 2 (Metric.ball (Complex.orthonormalBasisOneI.repr c) R))
      (u : V → ℝ), A.a = B.a ∧ B.c = 0 ∧
      (∀ x ∈ Metric.closedBall (Complex.orthonormalBasisOneI.repr c) R,
        A.a x = pullbackConductivity g q δ (Complex.orthonormalBasisOneI.repr.symm x)) ∧
      DeGiorgi.IsHomogeneousWeakSolution A u ∧
      DeGiorgi.MemW01p 2 (fun x => u x - x 0)
        (Metric.ball (Complex.orthonormalBasisOneI.repr c) R) := by
  obtain ⟨B, hB, hBp, hBc⟩ := exists_smoothEllipticBilinearForm_pullbackConductivity
    g hΩ hq hδ hball
  obtain ⟨A, hA⟩ := ellipticCoeff_of_continuous_posDef_on_compact
    Metric.isOpen_ball.measurableSet Metric.ball_subset_closedBall
    (isCompact_closedBall (Complex.orthonormalBasisOneI.repr c) R)
    B.a (fun i j => (B.smooth_a i j).continuous.measurable)
    (fun i j => (B.smooth_a i j).continuous.continuousOn) (fun x _ => hBp x)
  obtain ⟨hw, _⟩ := exists_memW1pWitness_of_contDiffOn_closedBall isOpen_univ
    ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))).contDiffOn)
    (subset_univ (Metric.closedBall (Complex.orthonormalBasisOneI.repr c) R)) 2
  obtain ⟨u, hu, htrace⟩ := DeGiorgi.aHarmonic_replacement_exists (by norm_num)
    Metric.isOpen_ball (Metric.isBounded_ball) A hw.memW1p
  exact ⟨B, A, u, hA, hBc, fun x hx => (congrFun hA x).trans (hB x hx), hu, htrace⟩

end DifferentialGeometry.Geometry

end

end

section

noncomputable section
open Set Filter MeasureTheory Manifold
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem exists_dirichlet_stream_pullbackConductivity
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ q Ω) {δ : ℝ} (hδ : 0 < δ)
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hball : Metric.closedBall c R ⊆ Ω) :
    ∃ (B : SmoothEllipticBilinearForm 2 (univ : Set V))
      (A : DeGiorgi.EllipticCoeff 2 (Metric.ball (Complex.orthonormalBasisOneI.repr c) R))
      (u v s : V → ℝ), A.a = B.a ∧ B.c = 0 ∧
      (∀ x ∈ Metric.closedBall (Complex.orthonormalBasisOneI.repr c) R,
        A.a x = pullbackConductivity g q δ (Complex.orthonormalBasisOneI.repr.symm x)) ∧
      DeGiorgi.IsHomogeneousWeakSolution A u ∧
      DeGiorgi.MemW01p 2 (fun x => u x - x 0)
        (Metric.ball (Complex.orthonormalBasisOneI.repr c) R) ∧
      ContDiffOn ℝ ∞ v (Metric.ball (Complex.orthonormalBasisOneI.repr c) r) ∧
      ContDiffOn ℝ ∞ s (Metric.ball (Complex.orthonormalBasisOneI.repr c) r) ∧
      u =ᵐ[volume.restrict (Metric.ball (Complex.orthonormalBasisOneI.repr c) r)] v ∧
      (∀ x ∈ Metric.ball (Complex.orthonormalBasisOneI.repr c) r,
        HasFDerivAt s
          (planarFluxForm (fun y => DeGiorgi.matMulE (A.a y) (DeGiorgi.smoothGradField v y)) x) x) ∧
      ∀ z ∈ Metric.ball c r,
        complexAntilinearPart (fderiv ℝ (fun w =>
          (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
            (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) =
          pullbackBeltramiCoefficient g q δ z * complexLinearPart (fderiv ℝ (fun w =>
            (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
              (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) := by
  obtain ⟨B, A, u, hAB, hBc, hA, hu, htrace⟩ :=
    exists_dirichlet_solution_pullbackConductivity g hΩ hq hδ hball
  obtain ⟨v, s, hv, hs, huv, _, hds⟩ :=
    (DeGiorgi.isHomogeneousWeakSolution_isSolution hu).exists_smooth_representative_stream_function
      Metric.isOpen_ball B (fun x _ => congrFun hAB x) hr (Metric.closedBall_subset_ball hrR)
  refine ⟨B, A, u, v, s, hAB, hBc, hA, hu, htrace, hv, hs, huv, hds, ?_⟩
  intro z hz
  let e := Complex.orthonormalBasisOneI.repr
  have hzr : e z ∈ Metric.ball (e c) r := by simpa only [Metric.mem_ball, e.dist_map] using hz
  have hzR : e z ∈ Metric.closedBall (e c) R :=
    Metric.ball_subset_closedBall ((Metric.ball_subset_ball hrR.le) hzr)
  have heq := hA (e z) hzR
  rw [LinearIsometryEquiv.symm_apply_apply] at heq
  have hdsz := hds (e z) hzr
  have heqform : planarFluxForm
      (fun y => DeGiorgi.matMulE (A.a y) (DeGiorgi.smoothGradField v y)) (e z) =
      planarFluxForm
        (fun y => DeGiorgi.matMulE (pullbackConductivity g q δ z)
          (DeGiorgi.smoothGradField v y)) (e z) := by
    simp only [planarFluxForm, heq]
  rw [heqform] at hdsz
  exact beltrami_fderiv_of_conductivity_stream
    (add_pos_of_nonneg_of_pos (metric_inner_self_nonneg g (q z) _) hδ)
    (regularized_pullback_gram_pos g q hδ z)
    ((hv.differentiableOn (by simp)).differentiableAt (Metric.isOpen_ball.mem_nhds hzr)) hdsz

end DifferentialGeometry.Geometry

end

end

section

noncomputable section
open Set Filter MeasureTheory Manifold
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem det_pullbackConductivity
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    (pullbackConductivity g q δ z).det = 1 :=
  det_planarConductivity (regularized_pullback_gram_pos g q hδ z)

theorem exists_positive_jacobian_dirichlet_stream_pullbackConductivity
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ q Ω) {δ : ℝ} (hδ : 0 < δ)
    {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall (0 : ℂ) R ⊆ Ω) :
    ∃ (B : SmoothEllipticBilinearForm 2 (univ : Set V))
      (A : DeGiorgi.EllipticCoeff 2 (Metric.ball (0 : V) R)) (u v s : V → ℝ),
      A.a = B.a ∧ B.c = 0 ∧
      (∀ x ∈ Metric.closedBall (0 : V) R,
        A.a x = pullbackConductivity g q δ (Complex.orthonormalBasisOneI.repr.symm x)) ∧
      DeGiorgi.IsHomogeneousWeakSolution A u ∧
      DeGiorgi.MemH01 (fun x => u x - x 0) (Metric.ball (0 : V) R) ∧
      ContDiffOn ℝ ∞ v (Metric.ball (0 : V) R) ∧
      ContDiffOn ℝ ∞ s (Metric.ball (0 : V) R) ∧
      ContinuousOn v (Metric.closedBall (0 : V) R) ∧
      u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v ∧
      (∀ x ∈ Metric.sphere (0 : V) R, v x = x 0) ∧
      (∀ x ∈ Metric.ball (0 : V) R, fderiv ℝ v x ≠ 0) ∧
      (∀ x ∈ Metric.ball (0 : V) R,
        HasFDerivAt s (planarFluxForm (fun y => DeGiorgi.matMulE (A.a y)
          (DeGiorgi.smoothGradField v y)) x) x) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R,
        0 < (fderiv ℝ (fun w => (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
          (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z).toLinearMap.det := by
  have hproducer := exists_dirichlet_solution_pullbackConductivity g hΩ hq hδ hball
  have hz : Complex.orthonormalBasisOneI.repr (0 : ℂ) = 0 := map_zero _
  rw [hz] at hproducer
  obtain ⟨B, A, u, hAB, hBc, hA, hu, ht⟩ := hproducer
  have heq : EqOn A.a B.a (Metric.ball (0 : V) R) := fun x _ => congrFun hAB x
  have hdet (x : V) (hx : x ∈ Metric.ball (0 : V) R) : (A.a x).det = 1 := by
    rw [hA x (Metric.ball_subset_closedBall hx)]
    exact det_pullbackConductivity g q hδ _
  have hsol := DeGiorgi.isHomogeneousWeakSolution_isSolution hu
  obtain ⟨v, hv, hc, huv, hbd, hn⟩ :=
    hsol.exists_continuous_noncritical_coordinate_representative hR B heq hdet ht
  obtain ⟨s, hs, hds⟩ := exists_smooth_stream_of_smooth_representative
    Metric.isOpen_ball (convex_ball (0 : V) R) hsol B heq hv huv
  exact ⟨B, A, u, v, s, hAB, hBc, hA, hu, ht, hv, hs, hc, huv, hbd, hn, hds,
    hsol.det_fderiv_pos_of_coordinate_boundary_stream hR B heq hdet hc huv hbd hds⟩

end DifferentialGeometry.Geometry

end

end
