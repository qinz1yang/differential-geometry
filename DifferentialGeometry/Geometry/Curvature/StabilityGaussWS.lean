import DifferentialGeometry.Geometry.MinimalSurface.Variation.ParamStabilityMorreyWS
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskFullJacobiPotential
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.IntegrationByParts
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

/-!
# S-W-STAB G3：Gauss 形式的 stability inequality 与 `R ≥ σ` 弱化

G2（`stability_inequality_regular_WS`）的 Ric 形式 `|∇φ|² − φ²(Ric(ν,ν) + |II|²)` 用 Gauss 方程
`Ric(ν,ν) + |II|² = (R + |II|²)/2 − S_{gN}/2`（`normal_jacobi_coefficient_eq_scalar_gauss…`）改写成

* `stability_inequality_gauss_WS`：存在光滑势 `VJ = K_Σ − q̃`（`K_Σ = S_{gN}/2`，`q̃ = (R∘U + |II|²)/2`，
  任何 `gN`-标准正交标架下的公式），`VJ ≤ S_{gN}/2 − R∘U/2`，且对一切 `φ ∈ C_c^∞(N)`：
  `0 ≤ ∫_N (|∇φ|² + VJ φ²) dμ_{gN}`（与 IMS03 `…_smooth_full_jacobi_potential` 同形，`N` 取任意
  regular part）；
* `stability_inequality_scalar_lower_WS`：`R∘U ≥ σ`（在 `φ ≠ 0` 处）⇒
  `(σ/2) ∫ φ² ≤ ∫ (|∇φ|² + K_Σ φ²)`（IMS05 用的形式，`K_Σ = scalarCurv gN / 2`）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open scoped ContDiff Manifold _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

open Riemannian Riemannian.CovariantDerivativeAlong

private local instance (N : TopologicalSpace.Opens ℂ) : MeasurableSpace N := borel N
private local instance (N : TopologicalSpace.Opens ℂ) : BorelSpace N := ⟨rfl⟩
private local instance (N : TopologicalSpace.Opens ℂ) : LocallyCompactSpace N :=
  N.isOpen.locallyCompactSpace
private local instance (N : TopologicalSpace.Opens ℂ) : SigmaCompactSpace N := by infer_instance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- 每点处存在 `gN`-标准正交基（重标为 `Fin 2`）。 -/
theorem exists_orthonormal_basis_pullback_WS (N : TopologicalSpace.Opens ℂ)
    (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N) (q : N) :
    ∃ b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q),
      ∀ i j, gN.inner q (b i) (b j) = if i = j then 1 else 0 := by
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis gN q
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℂ) q) = 2 := by
    change Module.finrank ℝ ℂ = 2
    rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
  refine ⟨b.reindex (finCongr hdim), ?_⟩
  intro i j
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
  simp only [Equiv.apply_eq_iff_eq]

/-- **G3a `stability_inequality_gauss_WS`.**  G2 的 Gauss 形式：存在光滑势 `VJ`（`= K_Σ − q̃`）。 -/
theorem stability_inequality_gauss_WS (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M) (γ : freeLoop M)
    {u : C(closedDisk, M)} {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U)
    (hW : Set.range u ⊆ W) (htr : DiskWeakJordanTrace γ u)
    (hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W → riemannianDiskArea g u ≤ riemannianDiskArea g v)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (hmean : ∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, (g.pullback (fun p : N => U p) hUN hiN).inner q (b i) (b j) =
        if i = j then 1 else 0) →
      ∑ i : Fin 2, secondFundamentalFormAmbientAt (g.pullback (fun p : N => U p) hUN hiN)
        g (fun p : N => U p) q (b i) (b i) = 0) :
    let gN := g.pullback (fun p : N => U p) hUN hiN
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N) gN
    ∃ VJ : C^∞⟮𝓘(ℝ, ℂ), N; ℝ⟯,
      (∀ q : N, VJ q = scalarCurv gN q - scalarCurv g (U q) +
        ricciTensor g (U q) (ν q) (ν q)) ∧
      (∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
        (∀ i j, gN.inner q (b i) (b j) = if i = j then 1 else 0) →
        let II := secondFundamentalFormAmbientAt gN g (fun p : N => U p) q
        VJ q = metricScalarAt gN q / 2 -
          (metricScalarAt g (U q) +
            ∑ i : Fin 2, ∑ j : Fin 2,
              g.inner (U q) (II (b i) (b j)) (II (b i) (b j))) / 2) ∧
      (∀ q : N, VJ q ≤ scalarCurv gN q / 2 - scalarCurv g (U q) / 2) ∧
      (∀ (φ : N → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
        let QJ : N → ℝ := fun q =>
          gN.inner q (gradFun gN φ q) (gradFun gN φ q) + VJ q * φ q ^ 2
        Integrable QJ μ ∧ 0 ≤ ∫ q : N, QJ q ∂μ) := by
  classical
  intro gN μ
  obtain ⟨VJ, hformula, hcoeff, hbound⟩ :=
    exists_smooth_full_jacobi_potential_of_zero_mean_curvature_complex
      N g hdim U hUN hiN ν hν hunit hnormal hmean
  let b₀ : ∀ q : N, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q) :=
    fun q => (exists_orthonormal_basis_pullback_WS N gN q).choose
  have hb₀ : ∀ (q : N) (i j : Fin 2),
      gN.inner q (b₀ q i) (b₀ q j) = if i = j then 1 else 0 :=
    fun q => (exists_orthonormal_basis_pullback_WS N gN q).choose_spec
  refine ⟨VJ, hformula, hcoeff, hbound, ?_⟩
  intro φ hφ hφc
  have hG2 := stability_inequality_regular_WS hdim g W γ hExt hW htr hmin N hNball hUN hiN hint
    ν hν hunit hnormal hmean φ hφ hφc b₀ hb₀
  have heq : (fun q : N =>
      gN.inner q (gradFun gN φ q) (gradFun gN φ q) + VJ q * φ q ^ 2) =
      fun q : N =>
        let II := secondFundamentalFormAmbientAt gN g (fun p : N => U p) q
        gN.inner q (gradFun gN φ q) (gradFun gN φ q) -
          φ q ^ 2 * ((∑ i : Fin 2, g.inner (U q) ((riemannOp (LeviCivita g) (U q)) (ν q)
              (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b₀ q i)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b₀ q i)))
              (ν q)) +
            ∑ i : Fin 2, ∑ j : Fin 2,
              g.inner (U q) (II (b₀ q i) (b₀ q j)) (II (b₀ q i) (b₀ q j))) := by
    funext q
    have hc := normal_jacobi_coefficient_eq_scalar_gauss_of_zero_mean_curvature_complex
      N g hdim U hUN hiN q (ν q) (hunit q) (hnormal q) (b₀ q) (hb₀ q) (hmean q (b₀ q) (hb₀ q))
    have hv := hcoeff q (b₀ q) (hb₀ q)
    change gN.inner q (gradFun gN φ q) (gradFun gN φ q) + VJ q * φ q ^ 2 =
      gN.inner q (gradFun gN φ q) (gradFun gN φ q) - φ q ^ 2 * _
    rw [hv]
    have hc' := hc
    simp only at hc'
    rw [hc']
    ring
  change Integrable (fun q : N =>
      gN.inner q (gradFun gN φ q) (gradFun gN φ q) + VJ q * φ q ^ 2) μ ∧
    0 ≤ ∫ q : N, (gN.inner q (gradFun gN φ q) (gradFun gN φ q) + VJ q * φ q ^ 2) ∂μ
  rw [heq]
  exact hG2

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem hasCompactSupport_gradSq_add_WS {N : TopologicalSpace.Opens ℂ}
    (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N) {φ : N → ℝ} (hφc : HasCompactSupport φ)
    (c : N → ℝ) :
    HasCompactSupport (fun q : N =>
      gN.inner q (gradFun gN φ q) (gradFun gN φ q) + c q * φ q ^ 2) := by
  apply hφc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal ?_ (isClosed_tsupport φ)
  intro q hq
  by_contra hnot
  have hφq : φ q = 0 := by
    by_contra hne
    exact hnot (subset_tsupport φ hne)
  have hgrad : gradFun gN φ q = 0 := by
    by_contra hne
    exact hnot (support_gradFun_subset gN φ hne)
  apply hq
  change gN.inner q (gradFun gN φ q) (gradFun gN φ q) + c q * φ q ^ 2 = 0
  rw [hgrad, hφq, map_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]

/-- **G3b `stability_inequality_scalar_lower_WS`.**  `R∘U ≥ σ`（在 `φ ≠ 0` 处）⇒
`(σ/2) ∫ φ² ≤ ∫ (|∇φ|² + K_Σ φ²)`，`K_Σ = scalarCurv gN / 2`。 -/
theorem stability_inequality_scalar_lower_WS (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M) (γ : freeLoop M)
    {u : C(closedDisk, M)} {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U)
    (hW : Set.range u ⊆ W) (htr : DiskWeakJordanTrace γ u)
    (hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W → riemannianDiskArea g u ≤ riemannianDiskArea g v)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (hmean : ∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, (g.pullback (fun p : N => U p) hUN hiN).inner q (b i) (b j) =
        if i = j then 1 else 0) →
      ∑ i : Fin 2, secondFundamentalFormAmbientAt (g.pullback (fun p : N => U p) hUN hiN)
        g (fun p : N => U p) q (b i) (b i) = 0)
    (σ : ℝ) :
    let gN := g.pullback (fun p : N => U p) hUN hiN
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N) gN
    ∀ (φ : N → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      (∀ q : N, φ q ≠ 0 → σ ≤ metricScalarAt g (U q)) →
      Integrable (fun q : N =>
        gN.inner q (gradFun gN φ q) (gradFun gN φ q) + (scalarCurv gN q / 2) * φ q ^ 2) μ ∧
      Integrable (fun q : N => φ q ^ 2) μ ∧
      (σ / 2) * ∫ q : N, φ q ^ 2 ∂μ ≤ ∫ q : N,
        (gN.inner q (gradFun gN φ q) (gradFun gN φ q) + (scalarCurv gN q / 2) * φ q ^ 2) ∂μ := by
  classical
  intro gN μ φ hφ hφc hσ
  obtain ⟨VJ, -, -, hbound, hstab⟩ :=
    stability_inequality_gauss_WS hdim g W γ hExt hW htr hmin N hNball hUN hiN hint
      ν hν hunit hnormal hmean
  obtain ⟨hQJint, hQJnn⟩ := hstab φ hφ hφc
  have hFc : Continuous (fun q : N =>
      gN.inner q (gradFun gN φ q) (gradFun gN φ q) + (scalarCurv gN q / 2) * φ q ^ 2) :=
    (normGradSqFun_continuous gN hφ).add
      ((((scalarCurv_contMDiff gN).div_const 2).continuous).mul (hφ.continuous.pow 2))
  have hFint : Integrable (fun q : N =>
      gN.inner q (gradFun gN φ q) (gradFun gN φ q) + (scalarCurv gN q / 2) * φ q ^ 2) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      gN hFc (hasCompactSupport_gradSq_add_WS gN hφc _)
  have hφ2c : HasCompactSupport (fun q : N => φ q ^ 2) :=
    hφc.of_isClosed_subset (isClosed_tsupport _) (by
      apply closure_minimal ?_ (isClosed_tsupport φ)
      intro q hq
      by_contra hnot
      have hφq : φ q = 0 := by
        by_contra hne
        exact hnot (subset_tsupport φ hne)
      exact hq (by simp [hφq]))
  have hφ2int : Integrable (fun q : N => φ q ^ 2) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      gN (hφ.continuous.pow 2) hφ2c
  have hle : ∀ q : N,
      gN.inner q (gradFun gN φ q) (gradFun gN φ q) + VJ q * φ q ^ 2 ≤
        (gN.inner q (gradFun gN φ q) (gradFun gN φ q) + (scalarCurv gN q / 2) * φ q ^ 2) -
          (σ / 2) * φ q ^ 2 := by
    intro q
    by_cases hz : φ q = 0
    · simp [hz]
    · have h1 := hbound q
      have h2 := hσ q hz
      rw [metricScalar_eq_scal] at h2
      have hcoef : VJ q ≤ scalarCurv gN q / 2 - σ / 2 := by linarith
      have := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (φ q))
      nlinarith [this]
  have hint2 : Integrable (fun q : N =>
      (gN.inner q (gradFun gN φ q) (gradFun gN φ q) + (scalarCurv gN q / 2) * φ q ^ 2) -
        (σ / 2) * φ q ^ 2) μ := hFint.sub (hφ2int.const_mul (σ / 2))
  have hmono := integral_mono hQJint hint2 hle
  rw [integral_sub hFint (hφ2int.const_mul (σ / 2)), integral_const_mul] at hmono
  refine ⟨hFint, hφ2int, ?_⟩
  linarith

/-- **G3 `IsMorreyDisk` 版（consumer）.**  `hmin`、`hmean` 自动（`IsMorreyDisk.area_eq_morreyLeastAreaS`、
harmonic + conformal）。`R∘U ≥ σ`（`φ ≠ 0` 处）⇒ `(σ/2) ∫ φ² ≤ ∫ (|∇φ|² + K_Σ φ²)`。 -/
theorem IsMorreyDisk.stability_inequality_scalar_lower_WS [T3Space M]
    (hdim : Module.finrank ℝ E = 3)
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U) (W : Set M) (hW : Set.range u ⊆ W)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (σ : ℝ) :
    let gN := g.pullback (fun p : N => U p) hUN hiN
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N) gN
    ∀ (φ : N → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      (∀ q : N, φ q ≠ 0 → σ ≤ metricScalarAt g (U q)) →
      Integrable (fun q : N =>
        gN.inner q (gradFun gN φ q) (gradFun gN φ q) + (scalarCurv gN q / 2) * φ q ^ 2) μ ∧
      Integrable (fun q : N => φ q ^ 2) μ ∧
      (σ / 2) * ∫ q : N, φ q ^ 2 ∂μ ≤ ∫ q : N,
        (gN.inner q (gradFun gN φ q) (gradFun gN φ q) + (scalarCurv gN q / 2) * φ q ^ 2) ∂μ := by
  intro gN μ
  have hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W →
        riemannianDiskArea g u ≤ riemannianDiskArea g v := by
    intro v hv hw hWv
    rw [hu.area_eq_morreyLeastAreaS hdim hγ hW]
    exact morreyLeastAreaS_le g hv hw hWv
  have hmetric : ∀ (z : N) (v w : ℂ),
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z w) =
        gN.inner z v w := by
    intro z v w
    have hdf := DifferentialGeometry.mfderiv_restrict_open (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N z
    exact (congrArg (fun L : ℂ →L[ℝ] E => g.inner (U z) (L v) (L w)) hdf).symm
  have hmean : ∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, gN.inner q (b i) (b j) = if i = j then 1 else 0) →
      ∑ i : Fin 2, secondFundamentalFormAmbientAt gN g (fun p : N => U p) q (b i) (b i) = 0 :=
    fun q b' hb' => sum_secondFundamentalForm_orthonormal_eq_zero_WS N gN g U hUN hmetric q
      (hu.conformal_of_extension hExt q (hNball q.property))
      (hu.tension_eq_zero_of_extension hExt q (hNball q.property)) b' hb'
  exact DifferentialGeometry.Geometry.stability_inequality_scalar_lower_WS hdim g W γ hExt hW
    hu.trace hmin N hNball hUN hiN hint ν hν hunit hnormal hmean σ

end DifferentialGeometry.Geometry
