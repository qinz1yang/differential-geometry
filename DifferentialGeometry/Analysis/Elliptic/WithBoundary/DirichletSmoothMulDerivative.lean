import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartPullback
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMul
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.WeakDerivative

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

omit [T2Space M] [CompactSpace M] in
private theorem exists_smooth_chart_multiplier
    (α : M) {Ω : Set EuStd}
    (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    ∃ ψ : EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ EqOn ψ P Ω := by
  intro P
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) P U := by
    apply (scalarOnE_contDiffOn α φ.contMDiff).comp
      (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
    rintro z ⟨y, hy, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
  obtain ⟨δ, χ, _, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood hΩc hU hΩs
  let ψ := fun z => χ z * P z
  have hψs : tsupport ψ ⊆ U := tsupport_mul_subset_left.trans hχs
  refine ⟨ψ, (hχ.contDiffOn.mul hP).contDiff_of_tsupport_subset hU hψs, hχc.mul_right, ?_⟩
  intro z hz
  dsimp only [ψ]
  rw [hχone z (Metric.self_subset_cthickening _ (subset_closure hz)), one_mul]

omit [NeZero n] in
private theorem hasWeakPartialDeriv_congr_left
    {Ω : Set EuStd} {i : Fin (Module.finrank ℝ EuN)} {g f f' : EuStd → ℝ}
    (h : DeGiorgi.HasWeakPartialDeriv i g f Ω)
    (heq : f' =ᵐ[volume.restrict Ω] f) : DeGiorgi.HasWeakPartialDeriv i g f' Ω := by
  intro ψ hψ hψc hψs
  rw [← h ψ hψ hψc hψs]
  exact integral_congr_ae (heq.mono fun z hz => congrArg (· * fderiv ℝ ψ z (EuclideanSpace.single i 1)) hz)

theorem dirichletLocalWeakPartialLp_smoothMulH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (j : Fin (Module.finrank ℝ EuN)) (u : H1ComplDirichlet q) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let U := fun z => H1ComplDirichletToLp q u
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    (D j (smoothMulH1ComplDirichlet q φ u) : EuStd → ℝ) =ᵐ[volume.restrict Ω]
      fun z => P z * D j u z + fderiv ℝ P z (EuclideanSpace.single j 1) * U z := by
  intro P U D
  obtain ⟨ψ, hψ, hψc, heq⟩ := exists_smooth_chart_multiplier α hΩc hΩs φ
  have hu : MemLp U 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u).memLp
  have hg : MemLp (D j u : EuStd → ℝ) 2 (volume.restrict Ω) := Lp.memLp _
  have hdψ : Continuous (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hG : MemLp (fun z => ψ z * D j u z + fderiv ℝ ψ z (EuclideanSpace.single j 1) * U z)
      2 (volume.restrict Ω) :=
    (hg.mul' ((hψ.continuous.memLp_of_hasCompactSupport hψc : MemLp ψ ∞ volume).restrict Ω)).add
      (hu.mul' ((hdψ.memLp_of_hasCompactSupport (hψc.fderiv_apply (𝕜 := ℝ)
        (EuclideanSpace.single j 1)) : MemLp _ ∞ volume).restrict Ω))
  have hp := (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j u).mul_smooth
    hΩ hψ (hu.locallyIntegrable (by norm_num)) (hg.locallyIntegrable (by norm_num))
  have hval : (fun z => H1ComplDirichletToLp q (smoothMulH1ComplDirichlet q φ u)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) =ᵐ[volume.restrict Ω]
      fun z => ψ z * U z := by
    rw [H1ComplDirichletToLp_smoothMulH1ComplDirichlet]
    filter_upwards [ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) (smoothMulLp_apply_coeFn q φ (H1ComplDirichletToLp q u)),
      ae_restrict_mem hΩ.measurableSet] with z hz hzΩ
    rw [hz, heq hzΩ]
  have hweak := hasWeakPartialDeriv_congr_left hp hval
  have hae := DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
    (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j
      (smoothMulH1ComplDirichlet q φ u)) hweak
    ((Lp.memLp _).locallyIntegrable (by norm_num)) (hG.locallyIntegrable (by norm_num))
  apply hae.trans
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
  have hd : fderiv ℝ ψ z = fderiv ℝ P z := (heq.eventuallyEq_of_mem (hΩ.mem_nhds hz)).fderiv_eq
  rw [heq hz, hd]

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
