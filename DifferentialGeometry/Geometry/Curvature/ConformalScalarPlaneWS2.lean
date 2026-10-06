import DifferentialGeometry.Geometry.Connection.ConformalEuclidean
import DifferentialGeometry.Geometry.Metric.Conformal.Curvature
import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.GreenIdentity
import DifferentialGeometry.Geometry.Curvature.StabilityConformalWS2
import DifferentialGeometry.Geometry.MinimalSurface.Variation.UnitNormalWS2

/-!
# S-W-STAB-2 G4：共形盘标量曲率的平面公式 `scalarCurv gN = −Δ(log λ)/λ`

`N ⊆ ℂ` 开，`gN = g.pullback (U|_N)`、`U` 共形（`gN = λ|dz|²`，`λ = diskMapConformalCoefficient g U > 0`）：

* `laplacian_euclidean_complex_WS2`：`ℂ` 上平坦度量的 Laplace–Beltrami = `Laplacian.laplacian`；
* `scalarCurv_pullback_conformal_WS2`：`scalarCurv gN q = −Δ(log λ)(q)/λ(q)`
  （`gN = conformalMetric ((euclid).restrictOpen N) (½ log λ)`，
  `scalarCurv_conformalMetric_of_finrank_eq_two`，
  平坦度量标量曲率 0，`laplacian_restrictOpen_of_contMDiffAt`）；
* `IsMorreyDisk.stability_inequality_conformal_planar_WS2`：G1/G2 的 `VJ ≤ K_Σ − R/2` 换成平面形式
  `VJ z ≤ −Δ(log λ)(z)/(2λ(z)) − R(U z)/2`。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology MeasureTheory
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry

theorem trace_complex_WS2 (L : ℂ →L[ℝ] ℂ) :
    LinearMap.trace ℝ ℂ L.toLinearMap = (L 1).re + (L Complex.I).im := by
  rw [LinearMap.trace_eq_matrix_trace ℝ Complex.basisOneI]
  simp [Matrix.trace, Fin.sum_univ_two, LinearMap.toMatrix_apply]

/-- flat Laplace–Beltrami on ℂ = standard Laplacian. -/
theorem laplacian_euclidean_complex_WS2 {F : ℂ → ℝ} {z : ℂ} (hF : ContDiffAt ℝ 2 F z) :
    laplacian (LeviCivita (euclideanMetric ℂ)) (euclideanMetric ℂ) F z =
      Laplacian.laplacian F z := by
  have hmet : euclideanMetric ℂ = conformalEuclideanMetric (fun _ : ℂ => (0 : ℝ))
      contDiff_const := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    change inner ℝ (v : ℂ) (w : ℂ) = Real.exp (2 * 0) * inner ℝ (v : ℂ) (w : ℂ)
    simp
  have hgrad : gradientFun (euclideanMetric ℂ) F = fun x => gradient F x := by
    funext x
    apply Curvature.SmoothRiemannianMetric.eq_of_inner_eq_gen (euclideanMetric ℂ)
    intro v
    rw [inner_gradientFun]
    have h := inner_gradient_left (f := F) (x := x) (y := (v : ℂ))
    change mvfderiv 𝓘(ℝ, ℂ) F x (v : ℂ) = inner ℝ (gradient F x) (v : ℂ)
    rw [h, mvfderiv_eq_fderiv]
    rfl
  have hY : DifferentiableAt ℝ (fun x => gradient F x) z := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) z := hF.fderiv_right (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun x => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ F x)) z :=
      (InnerProductSpace.toDual ℝ ℂ).symm.contDiff.contDiffAt.comp z h1
    exact (h2.differentiableAt (by norm_num))
  have hcov : ∀ v : ℂ, LeviCivita (euclideanMetric ℂ) (gradientFun (euclideanMetric ℂ) F) z v =
      fderiv ℝ (fun x => gradient F x) z v := by
    intro v
    rw [hgrad, hmet, leviCivita_conformalEuclidean contDiff_const hY v]
    simp [conformalEuclideanCorrection]
    rfl
  have hre : fderiv ℝ (fun q => fderiv ℝ F q 1) z =
      Complex.reCLM.comp (fderiv ℝ (fun x => gradient F x) z) := by
    have h := (Complex.reCLM.hasFDerivAt.comp z hY.hasFDerivAt).fderiv
    have hfun : (fun q => fderiv ℝ F q 1) = Complex.reCLM ∘ (fun x => gradient F x) := by
      funext q
      exact (DifferentialGeometry.Analysis.gradient_complex_re F q).symm
    rw [hfun]
    exact h
  have him : fderiv ℝ (fun q => fderiv ℝ F q Complex.I) z =
      Complex.imCLM.comp (fderiv ℝ (fun x => gradient F x) z) := by
    have h := (Complex.imCLM.hasFDerivAt.comp z hY.hasFDerivAt).fderiv
    have hfun : (fun q => fderiv ℝ F q Complex.I) = Complex.imCLM ∘ (fun x => gradient F x) := by
      funext q
      exact (DifferentialGeometry.Analysis.gradient_complex_im F q).symm
    rw [hfun]
    exact h
  have hdiv := DifferentialGeometry.Analysis.complexDivergence_gradient hF
  rw [DifferentialGeometry.Analysis.complexDivergence, hre, him] at hdiv
  have htr : (LeviCivita (euclideanMetric ℂ) (gradientFun (euclideanMetric ℂ) F) z).toLinearMap =
      (fderiv ℝ (fun x => gradient F x) z).toLinearMap := LinearMap.ext hcov
  change LinearMap.trace ℝ ℂ
    (LeviCivita (euclideanMetric ℂ) (gradientFun (euclideanMetric ℂ) F) z).toLinearMap = _
  rw [htr, trace_complex_WS2]
  exact hdiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- `ℂ` 上平坦度量的标量曲率为零（`Geometry.euclideanMetric ℂ` 版）。 -/
theorem metricScalarAt_euclideanMetric_complex_WS2 (z : ℂ) :
    metricScalarAt (euclideanMetric ℂ) z = 0 := by
  have h : euclideanMetric ℂ = DifferentialGeometry.euclideanMetric (E := ℂ) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rfl
  rw [h]
  exact euclideanMetric_scalarCurvature z

/-- **G4 核心.**  共形盘 `gN = λ|dz|²` 的标量曲率的平面公式。 -/
theorem scalarCurv_pullback_conformal_WS2 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    (N : TopologicalSpace.Opens ℂ)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hconf : ∀ z ∈ N, DiskMapConformalAt g U z) (q : N) :
    scalarCurv (g.pullback (fun p : N => U p) hUN hiN) q =
      -Laplacian.laplacian (fun p => Real.log (diskMapConformalCoefficient g U p)) q /
        diskMapConformalCoefficient g U q := by
  classical
  obtain ⟨hlamC, hlamP⟩ := conformalFactor_data_WS2 g N hUN hiN hconf
  let lam : ℂ → ℝ := diskMapConformalCoefficient g U
  let F : ℂ → ℝ := fun p => (1 / 2) * Real.log (lam p)
  have hFC : ContDiffOn ℝ ∞ F (N : Set ℂ) :=
    contDiffOn_const.mul (hlamC.log (fun z hz => (hlamP z hz).ne'))
  have hFmd : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun p : N => F p) := fun p =>
    contMDiffAt_subtype_iff.mpr
      ((contMDiffOn_iff_contDiffOn.mpr hFC).contMDiffAt (N.isOpen.mem_nhds p.2))
  let u : C^∞⟮𝓘(ℝ, ℂ), N; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨fun p : N => F p, hFmd⟩
  let g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N := (euclideanMetric ℂ).restrictOpen N
  have hmetric : g.pullback (fun p : N => U p) hUN hiN =
      DifferentialGeometry.conformalMetric g₀ u := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [pullback_inner_conformal_WS2 g N hUN hiN hconf x v w]
    change diskMapConformalCoefficient g U x * @inner ℝ ℂ _ v w =
      Real.exp (2 * ((1 / 2) * Real.log (lam x))) * @inner ℝ ℂ _ v w
    congr 1
    rw [show 2 * ((1 / 2) * Real.log (lam x)) = Real.log (lam x) by ring,
      Real.exp_log (hlamP x x.2)]
  have hn : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have hF2 : ContDiffAt ℝ 2 F q := (hFC.contDiffAt (N.isOpen.mem_nhds q.2)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hlap : laplacian (LeviCivita g₀) g₀ (fun y : N => F y) q = Laplacian.laplacian F q := by
    rw [laplacian_restrictOpen_of_contMDiffAt (euclideanMetric ℂ) N (f := F) (x := q)
      (contMDiffAt_iff_contDiffAt.mpr hF2)]
    exact laplacian_euclidean_complex_WS2 hF2
  have hflat : scalarCurv g₀ q = 0 := by
    rw [← metricScalar_eq_scal]
    rw [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen
      (euclideanMetric ℂ) N q]
    exact metricScalarAt_euclideanMetric_complex_WS2 q
  have hlog : ContDiffAt ℝ 2 (fun p => Real.log (lam p)) q :=
    ((hlamC.log (fun z hz => (hlamP z hz).ne')).contDiffAt (N.isOpen.mem_nhds q.2)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hFlog : Laplacian.laplacian F q = (1 / 2) * Laplacian.laplacian
      (fun p => Real.log (lam p)) q := by
    have h := InnerProductSpace.laplacian_smul (1 / 2 : ℝ) hlog
    exact h
  have hlap' : laplacian (LeviCivita g₀) g₀ (⇑u) q = Laplacian.laplacian F q := hlap
  rw [hmetric, Curvature.scalarCurv_conformalMetric_of_finrank_eq_two g₀ u hn q, hflat, hlap',
    hFlog]
  have huq : u q = (1 / 2) * Real.log (lam q) := rfl
  rw [huq, show -(2 * ((1 / 2) * Real.log (lam q))) = -Real.log (lam q) by ring, Real.exp_neg,
    Real.exp_log (hlamP q q.2)]
  have hne : lam q ≠ 0 := (hlamP q q.2).ne'
  field_simp
  ring

section MorreyPlanarK

variable [FiniteDimensional ℝ E] [T3Space M]

/-- **G4 `IsMorreyDisk` 平面 `K_Σ` 形式.**  G2 的 `ν`-free 共形 stability，`VJ ≤ K_Σ − R/2` 里的
`K_Σ` 换成平面公式：`VJ z ≤ −Δ(log λ)(z)/(2λ(z)) − R(U z)/2`，`z ∈ N`。 -/
theorem IsMorreyDisk.stability_inequality_conformal_planar_WS2
    (hdim : Module.finrank ℝ E = 3) {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U) (W : Set M) (hW : Set.range u ⊆ W)
    (o : DifferentialGeometry.ManifoldOrientation 𝓘(ℝ, E) M 3)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W) :
    ∃ VJ : ℂ → ℝ, ContDiffOn ℝ ∞ VJ (N : Set ℂ) ∧
      (∀ z ∈ N, VJ z ≤ -Laplacian.laplacian
          (fun p => Real.log (diskMapConformalCoefficient g U p)) z /
            (2 * diskMapConformalCoefficient g U z) - scalarCurv g (U z) / 2) ∧
      ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ (N : Set ℂ) →
        Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2 +
          diskMapConformalCoefficient g U x * VJ x * ψ x ^ 2) ∧
        0 ≤ ∫ x, (‖fderiv ℝ ψ x‖ ^ 2 + diskMapConformalCoefficient g U x * VJ x * ψ x ^ 2) := by
  have hconf : ∀ z ∈ N, DiskMapConformalAt g U z :=
    fun z hz => hu.conformal_of_extension hExt z (hNball hz)
  obtain ⟨VJ, hC, hb, hs⟩ :=
    IsMorreyDisk.stability_inequality_conformal_nu_free_WS2 hdim hγ hu hExt W hW o N hNball hUN
      hiN hint
  refine ⟨VJ, hC, fun z hz => ?_, hs⟩
  have h1 := hb ⟨z, hz⟩
  rw [scalarCurv_pullback_conformal_WS2 g N hUN hiN hconf ⟨z, hz⟩] at h1
  rw [mul_comm 2, ← div_div]
  exact h1

end MorreyPlanarK

end DifferentialGeometry.Geometry
