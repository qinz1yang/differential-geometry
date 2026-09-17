import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletVariationalLaplacian
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletFormCompletion
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakFormChart
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartPullbackLp
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakFormulation

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure

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

omit [T2Space M] [CompactSpace M] in
private theorem chartCoeffOnE_zero_on_chart
    (α : M) (i : Fin (Module.finrank ℝ EuN)) {y : EuN}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartCoeffOnE (I := I_hs) α 0 i y = 0 := by
  have hx : (extChartAt I_hs α).symm y ∈
      (trivializationAt EuN (TangentSpace I_hs) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I_hs)]
    exact (extChartAt I_hs α).map_target hy
  unfold chartCoeffOnE chartCoeff
  change (chartModelBasis EuN).repr
    ((trivializationAt EuN (TangentSpace I_hs) α)
      ⟨(extChartAt I_hs α).symm y, 0⟩).2 i = 0
  rw [(trivializationAt EuN (TangentSpace I_hs) α).apply_eq_prod_continuousLinearEquivAt
    ℝ _ hx]
  simp only [map_zero, Finsupp.zero_apply]

theorem dirichletWeakFormCompl_zero_h1ComplDirichletChartPullback
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {B : ℝ} (hX : ∀ x : M, q.inner x
      ((0 : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯) x)
      ((0 : Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯) x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x v v ≤ q.inner x v v ∧ q.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_hs) (M := M) q ≤
      Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (u : H1ComplDirichlet q) {ψ : EuStd → ℝ}
    (hψ : Sobolev.Euclidean.MemWkp 1 2 ψ Ω) (hψs : tsupport ψ ⊆ Ω) :
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let v := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hψ hψs
    dirichletWeakFormCompl q 0 0 B hX hCg hequiv Cv hCv0 hCvtop hvol u v =
      -(∑ i, ∑ j, ∫ z in Ω, D i u z *
        (densityOnEuclid q α z * invGramOnEuclid q α i j z) * D j v z) := by
  intro D v
  have hz : ∀ z ∈ Ω, (toEuclidean (E := EuN)).symm z ∈ (extChartAt I_hs α).target := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hΩs (subset_closure hz)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
  have hzero : ∀ i : Fin (Module.finrank ℝ EuN),
      (∫ z in Ω, D i u z * (chartCoeffOnE (I := I_hs) α 0 i
        ((toEuclidean (E := EuN)).symm z) * densityOnEuclid q α z) * ψ z) = 0 := by
    intro i
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hzm
    rw [chartCoeffOnE_zero_on_chart α i (hz z hzm)]
    simp only [zero_mul, mul_zero, Pi.zero_apply]
  have he := dirichletWeakFormCompl_apply_h1ComplDirichletChartPullback_eq_integral_chart
    q α hΩ hΩc hΩs 0 0 B hX hCg hequiv Cv hCv0 hCvtop hvol u hψ hψs
  change dirichletWeakFormCompl q 0 0 B hX hCg hequiv Cv hCv0 hCvtop hvol u v =
    -(∑ i, ∑ j, ∫ z in Ω, D i u z *
      (densityOnEuclid q α z * invGramOnEuclid q α i j z) * D j v z) +
      (∑ i, ∫ z in Ω, D i u z * (chartCoeffOnE (I := I_hs) α 0 i
        ((toEuclidean (E := EuN)).symm z) * densityOnEuclid q α z) * ψ z) -
      (∫ z in Ω, densityOnEuclid q α z * H1ComplDirichletToLp q u
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) * (0 * ψ z)) at he
  simpa only [hzero, Finset.sum_const_zero, zero_mul, mul_zero, integral_zero,
    add_zero, sub_zero] using he

theorem inner_sub_inner_eq_integral_dirichlet_chart
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (u : H1ComplDirichlet q) {ψ : EuStd → ℝ}
    (hψ : Sobolev.Euclidean.MemWkp 1 2 ψ Ω) (hψs : tsupport ψ ⊆ Ω) :
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let v := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hψ hψs
    ⟪u, v⟫_ℝ - ⟪H1ComplDirichletToLp q u, H1ComplDirichletToLp q v⟫_ℝ =
      ∑ i, ∑ j, ∫ z in Ω, D i u z *
        (densityOnEuclid q α z * invGramOnEuclid q α i j z) * D j v z := by
  intro D v
  have hX : ∀ x : M, q.inner x (0 : TangentSpace I_hs x) 0 ≤ 0 := fun x => by simp
  have hequiv : ∀ x : M, ∀ w : TangentSpace I_hs x,
      (1 : ℝ)⁻¹ * q.inner x w w ≤ q.inner x w w ∧
        q.inner x w w ≤ 1 * q.inner x w w := fun x w => by simp
  have hvol : riemannianVolumeMeasure (I := I_hs) (M := M) q ≤
      (1 : ℝ≥0∞) • riemannianVolumeMeasure (I := I_hs) (M := M) q := by simp
  have he := dirichletWeakFormCompl_zero_h1ComplDirichletChartPullback
    q α hΩ hΩc hΩs hX (le_refl (1 : ℝ)) hequiv 1 (by simp) (by simp) hvol u hψ hψs
  dsimp only at he
  rw [dirichletWeakFormCompl_self_zero_apply] at he
  change ⟪H1ComplDirichletToLp q u, H1ComplDirichletToLp q v⟫_ℝ - ⟪u, v⟫_ℝ =
    -(∑ i, ∑ j, ∫ z in Ω, D i u z *
      (densityOnEuclid q α z * invGramOnEuclid q α i j z) * D j v z) at he
  linarith

theorem dirichletLaplacian_inner_chartPullback_eq_neg_integral
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (u : dirichletLaplacianDomain q) {ψ : EuStd → ℝ}
    (hψ : Sobolev.Euclidean.MemWkp 1 2 ψ Ω) (hψs : tsupport ψ ⊆ Ω) :
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    let v := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hψ hψs
    ⟪dirichletLaplacian q u, H1ComplDirichletToLp q v⟫_ℝ =
      -(∑ i, ∑ j, ∫ z in Ω, D i (u : H1ComplDirichlet q) z *
        (densityOnEuclid q α z * invGramOnEuclid q α i j z) * D j v z) := by
  intro D v
  rw [dirichletLaplacian_inner_h1ComplDirichlet]
  have he := inner_sub_inner_eq_integral_dirichlet_chart
    q α hΩ hΩc hΩs (u : H1ComplDirichlet q) hψ hψs
  dsimp only at he
  change ⟪(u : H1ComplDirichlet q), v⟫_ℝ -
    ⟪H1ComplDirichletToLp q (u : H1ComplDirichlet q), H1ComplDirichletToLp q v⟫_ℝ =
    ∑ i, ∑ j, ∫ z in Ω, D i (u : H1ComplDirichlet q) z *
      (densityOnEuclid q α z * invGramOnEuclid q α i j z) * D j v z at he
  linarith

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure

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

private theorem inner_chartPullback_eq_integral
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (F : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    {ψ : EuStd → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    let hψW : MemWkp 1 2 ψ Ω :=
    MemWkp_of_smooth_compactSupport hΩ hψ hψc hψs (by norm_num) 1
    ⟪F, H1ComplDirichletToLp q
      (h1ComplDirichletChartPullback q α hΩ hΩc hΩs hψW hψs)⟫_ℝ =
      ∫ z in Ω, densityOnEuclid q α z *
        F ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) * ψ z := by
  intro hψW
  have hfs : Function.support ψ ⊆ Sobolev.Chart.chartTargetEuclid (I := I_hs) α :=
    (subset_tsupport ψ).trans (hψs.trans
      (subset_closure.trans (hΩs.trans (image_mono interior_subset))))
  have hchart := Sobolev.Chart.integral_mul_chartPullback_eq_integral_euclidean q α
    (Lp.stronglyMeasurable F).measurable hψ.continuous.measurable hfs
  rw [L2.inner_def]
  have hv := h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hψW hψs
  calc
    _ = ∫ x, F x * Sobolev.Chart.chartPullback I_hs α ψ x
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp only [Real.inner_apply, hx]
    _ = ∫ z, densityOnEuclid q α z *
        F ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) * ψ z := hchart
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by rw [image_eq_zero_of_notMem_tsupport (fun hs => hz (hψs hs)),
        mul_zero])).symm

theorem integral_dirichlet_chart_gradient_mul_fderiv
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (u : dirichletLaplacianDomain q)
    {ψ : EuStd → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    (∑ i, ∑ j, ∫ z in Ω, D i (u : H1ComplDirichlet q) z *
      (densityOnEuclid q α z * invGramOnEuclid q α i j z) *
        fderiv ℝ ψ z (EuclideanSpace.single j 1)) =
      -∫ z in Ω, densityOnEuclid q α z *
        dirichletLaplacian q u
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) * ψ z := by
  intro D
  let hψW : MemWkp 1 2 ψ Ω :=
    MemWkp_of_smooth_compactSupport hΩ hψ hψc hψs (by norm_num) 1
  let v := h1ComplDirichletChartPullback q α hΩ hΩc hΩs hψW hψs
  have he := dirichletLaplacian_inner_chartPullback_eq_neg_integral
    q α hΩ hΩc hΩs u hψW hψs
  dsimp only at he
  rw [inner_chartPullback_eq_integral q α hΩ hΩc hΩs (dirichletLaplacian q u)
    hψ hψc hψs] at he
  have hgrad (j : Fin (Module.finrank ℝ EuN)) :
      (D j v : EuStd → ℝ) =ᵐ[volume.restrict Ω]
        fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1) := by
    exact dirichletLocalWeakPartialLp_h1ComplDirichletChartPullback_eq_ae
      q α hΩ hΩc hΩs hψW hψs j
      (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).locallyIntegrable
        |>.mono_measure Measure.restrict_le_self)
      (hasWeakPartialDeriv_of_contDiffOn hΩ (hψ.of_le (by norm_cast)).contDiffOn j)
  have heq : (∑ i, ∑ j, ∫ z in Ω, D i (u : H1ComplDirichlet q) z *
      (densityOnEuclid q α z * invGramOnEuclid q α i j z) * D j v z) =
      ∑ i, ∑ j, ∫ z in Ω, D i (u : H1ComplDirichlet q) z *
      (densityOnEuclid q α z * invGramOnEuclid q α i j z) *
        fderiv ℝ ψ z (EuclideanSpace.single j 1) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact integral_congr_ae ((hgrad j).mono fun z hz => by dsimp only; rw [hz])
  change (∫ z in Ω, densityOnEuclid q α z * dirichletLaplacian q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) * ψ z) =
    -(∑ i, ∑ j, ∫ z in Ω, D i (u : H1ComplDirichlet q) z *
      (densityOnEuclid q α z * invGramOnEuclid q α i j z) * D j v z) at he
  rw [heq] at he
  linarith

theorem hasWeakDiv_dirichlet_chart_gradient
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (u : dirichletLaplacianDomain q) :
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    DeGiorgi.HasWeakDiv
      (fun z => densityOnEuclid q α z * dirichletLaplacian q u
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))
      (fun z => WithLp.toLp 2 (fun j => ∑ i, D i (u : H1ComplDirichlet q) z *
        (densityOnEuclid q α z * invGramOnEuclid q α i j z))) Ω := by
  intro D ψ hψ hψc hψs
  have he := integral_dirichlet_chart_gradient_mul_fderiv q α hΩ hΩc hΩs u hψ hψc hψs
  dsimp only at he
  have htarget : closure Ω ⊆ chartTargetEuclid (I := I_hs) α :=
    hΩs.trans (image_mono interior_subset)
  have hcoeff (i j : Fin (Module.finrank ℝ EuN)) :
      MemLp (fun z => densityOnEuclid q α z * invGramOnEuclid q α i j z)
        ⊤ (volume.restrict Ω) :=
    (((densityOnEuclid_contDiffOn q α).continuousOn.mono htarget).mul
      ((invGramOnEuclid_contDiffOn q α i j).continuousOn.mono htarget))
        |>.memLp_top_of_subset_isCompact hΩc hΩ.measurableSet subset_closure
  have hderiv (j : Fin (Module.finrank ℝ EuN)) :
      MemLp (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) 2
        (volume.restrict Ω) :=
    (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hψc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))).mono_measure
        Measure.restrict_le_self
  have hint (i j : Fin (Module.finrank ℝ EuN)) :
      Integrable (fun z => D i (u : H1ComplDirichlet q) z *
        (densityOnEuclid q α z * invGramOnEuclid q α i j z) *
        fderiv ℝ ψ z (EuclideanSpace.single j 1)) (volume.restrict Ω) := by
    have hi := ((Lp.memLp (D i (u : H1ComplDirichlet q))).mul' (p := ⊤) (r := 2)
      (hcoeff i j)).integrable_mul (hderiv j)
    apply hi.congr
    filter_upwards with z
    dsimp only [Pi.mul_apply]
    rw [mul_comm (densityOnEuclid q α z * invGramOnEuclid q α i j z)]
  change (∫ z in Ω, ∑ j, (WithLp.toLp 2 (fun j => ∑ i,
    D i (u : H1ComplDirichlet q) z *
      (densityOnEuclid q α z * invGramOnEuclid q α i j z))) j *
        fderiv ℝ ψ z (EuclideanSpace.single j 1)) = _
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun i _ => hint i _)]
  rw [Finset.sum_comm]
  exact he

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
