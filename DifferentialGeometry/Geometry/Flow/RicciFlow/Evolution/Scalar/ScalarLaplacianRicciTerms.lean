import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.Scalar
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Laplacian
import DifferentialGeometry.Geometry.Operator.Laplacian.Pullback
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] [T2Space M] in
def scalarEvolutionRate (g : SmoothRiemannianMetric I M) (x : M) : ℝ :=
  laplacian (LeviCivita g) g (metricScalarAt g) x + 2 * normSq0S g x 2 (metricRicciAt g x)

theorem laplacian_scalar_eq_chart_sum (g : SmoothRiemannianMetric I M) (x : M) :
    laplacian (LeviCivita g) g (metricScalarAt g) x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE g x i j (extChartAt I x x) *
          (partialDeriv i (partialDeriv j (scalarOnE (I := I) x (metricScalarAt g)))
              (extChartAt I x x) -
            ∑ k : Fin (Module.finrank ℝ E), chartChristoffel g x i j k (extChartAt I x x) *
              partialDeriv k (scalarOnE (I := I) x (metricScalarAt g)) (extChartAt I x x)) := by
  rw [laplacian_eq_chart_hessian_trace g x (metricScalar_smooth g) (mem_chart_source H x)]
  simp only [chartHessianTensor_def, chartIteratedPartialDeriv_def, chartInvGramOnE_def]
  rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]

theorem normSq_ricci_eq_chart_sum (g : SmoothRiemannianMetric I M) (x : M) :
    normSq0S g x 2 (metricRicciAt g x) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE g x i k (extChartAt I x x) * chartInvGramOnE g x j l (extChartAt I x x) *
            chartRicciTensor g x i j (extChartAt I x x) *
              chartRicciTensor g x k l (extChartAt I x x) := by
  classical
  have hgood : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet hgood
  have hgram : ∀ k l : Fin (Module.finrank ℝ E),
      g.inner x (chartBasisFamily (I := I) x hbase k) (chartBasisFamily (I := I) x hbase l) =
        chartGramMatrix (I := I) g x x k l := by
    intro k l
    rw [chartBasisFamily_apply, chartBasisFamily_apply]
    exact (chartGramMatrix_apply (I := I) g x x k l).symm
  have hinv : MetricInverseInBasis (I := I) g x (chartBasisFamily (I := I) x hbase)
      (fun k l => chartInvGramMatrix (I := I) g x x k l) := by
    intro i j
    refine ⟨?_, ?_⟩
    · simp only [hgram]
      rw [← Matrix.mul_apply, chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hbase,
        Matrix.one_apply]
    · simp only [hgram]
      rw [← Matrix.mul_apply, chartGramMatrix_mul_chartInvGramMatrix (I := I) g x hbase,
        Matrix.one_apply]
  rw [normSq0S_two_eq_coord g x (chartBasisFamily (I := I) x hbase) _ hinv]
  have hric : ∀ i j : Fin (Module.finrank ℝ E),
      metricRicciAt g x (fun a : Fin 2 => if a = 0 then chartBasisFamily (I := I) x hbase i
        else chartBasisFamily (I := I) x hbase j) =
        chartRicciTensor g x i j (extChartAt I x x) := by
    intro i j
    rw [chartBasisFamily_apply, chartBasisFamily_apply]
    exact (metricRicciAt_apply_eq_ricciTensor g x _ _).trans
      (ricciTensor_chartBasisVec_alpha_eq g x i j hgood)
  have hG : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = chartInvGramOnE g x i j (extChartAt I x x) := by
    intro i j
    rw [chartInvGramOnE_def, (extChartAt I x).left_inv (mem_extChartAt_source x)]
  simp only [hric, hG]

theorem continuousWithinAt_laplacian_scalar_of_chartGramFamilySmoothWithinOn
    [BoundarylessManifold I M] (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (x : M) (hG : chartGramFamilySmoothWithinOn (I := I) g x J) {t₀ : ℝ}
    (ht₀ : t₀ ∈ J) :
    ContinuousWithinAt (fun t => laplacian (LeviCivita (g t)) (g t) (metricScalarAt (g t)) x)
      J t₀ := by
  set e₀ := extChartAt I x x with he₀def
  have he₀ : e₀ ∈ interior (extChartAt I x).target := by
    rw [(isOpen_extChartAt_target x).interior_eq]
    exact mem_extChartAt_target x
  have hF :=
    (scalarOnE_contDiffOn_of_chartGramFamilySmoothWithinOn g x hG) (t₀, e₀) ⟨ht₀, he₀⟩
  have hd1 : ∀ k : Fin (Module.finrank ℝ E), ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E =>
        partialDeriv k (fun y => scalarOnE (I := I) x (metricScalarAt (g r.1)) y) r.2)
      (J ×ˢ interior (extChartAt I x).target) (t₀, e₀) := fun k =>
    partialDeriv_joint_contDiffWithinAt
      (fun s y => scalarOnE (I := I) x (metricScalarAt (g s)) y) k
      isOpen_interior ht₀ he₀ hF
  have hd2 : ∀ i j : Fin (Module.finrank ℝ E), ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => partialDeriv i
        (fun y => partialDeriv j
          (fun y' => scalarOnE (I := I) x (metricScalarAt (g r.1)) y') y) r.2)
      (J ×ˢ interior (extChartAt I x).target) (t₀, e₀) := fun i j =>
    partialDeriv_joint_contDiffWithinAt
      (fun s y => partialDeriv j (fun y' => scalarOnE (I := I) x (metricScalarAt (g s)) y') y) i
      isOpen_interior ht₀ he₀ (hd1 j)
  have hΨ : ContDiffWithinAt ℝ ∞ (fun r : ℝ × E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (g r.1) x i j r.2 *
          (partialDeriv i (fun y => partialDeriv j
              (fun y' => scalarOnE (I := I) x (metricScalarAt (g r.1)) y') y) r.2 -
            ∑ k : Fin (Module.finrank ℝ E), chartChristoffel (g r.1) x i j k r.2 *
              partialDeriv k (fun y => scalarOnE (I := I) x (metricScalarAt (g r.1)) y) r.2))
      (J ×ˢ interior (extChartAt I x).target) (t₀, e₀) :=
    ContDiffWithinAt.sum fun i _ => ContDiffWithinAt.sum fun j _ =>
      (chartInvGramOnE_contDiffWithinAt g x hG i j ht₀ he₀).mul ((hd2 i j).sub
        (ContDiffWithinAt.sum fun k _ =>
          (chartChristoffel_contDiffWithinAt g x hG i j k ht₀ he₀).mul (hd1 k)))
  have hc := hΨ.continuousWithinAt.comp (f := fun t : ℝ => (t, e₀)) (x := t₀)
    (continuous_id.prodMk continuous_const).continuousWithinAt (fun t ht => ⟨ht, he₀⟩)
  exact hc.congr (fun t _ => laplacian_scalar_eq_chart_sum (g t) x)
    (laplacian_scalar_eq_chart_sum (g t₀) x)

theorem continuousWithinAt_normSq_ricci_of_chartGramFamilySmoothWithinOn
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (x : M)
    (hG : chartGramFamilySmoothWithinOn (I := I) g x J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ContinuousWithinAt (fun t => normSq0S (g t) x 2 (metricRicciAt (g t) x)) J t₀ := by
  set e₀ := extChartAt I x x with he₀def
  have he₀ : e₀ ∈ interior (extChartAt I x).target := by
    rw [(isOpen_extChartAt_target x).interior_eq]
    exact mem_extChartAt_target x
  have hΨ : ContDiffWithinAt ℝ ∞ (fun r : ℝ × E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (g r.1) x i k r.2 * chartInvGramOnE (g r.1) x j l r.2 *
            chartRicciTensor (g r.1) x i j r.2 * chartRicciTensor (g r.1) x k l r.2)
      (J ×ˢ interior (extChartAt I x).target) (t₀, e₀) :=
    ContDiffWithinAt.sum fun i _ => ContDiffWithinAt.sum fun j _ =>
      ContDiffWithinAt.sum fun k _ => ContDiffWithinAt.sum fun l _ =>
        (((chartInvGramOnE_contDiffWithinAt g x hG i k ht₀ he₀).mul
          (chartInvGramOnE_contDiffWithinAt g x hG j l ht₀ he₀)).mul
          (chartRicciTensor_contDiffWithinAt g x hG i j ht₀ he₀)).mul
          (chartRicciTensor_contDiffWithinAt g x hG k l ht₀ he₀)
  have hc := hΨ.continuousWithinAt.comp (f := fun t : ℝ => (t, e₀)) (x := t₀)
    (continuous_id.prodMk continuous_const).continuousWithinAt (fun t ht => ⟨ht, he₀⟩)
  exact hc.congr (fun t _ => normSq_ricci_eq_chart_sum (g t) x)
    (normSq_ricci_eq_chart_sum (g t₀) x)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem laplacian_scalar_eq_of_local_isometry [BoundarylessManifold I M]
    [BoundarylessManifold I N] (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f)
    (hmetric : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = h.inner (f y) (mfderiv I I f y v) (mfderiv I I f y w)) (x : M) :
    laplacian (LeviCivita g) g (metricScalarAt g) x =
      laplacian (LeviCivita h) h (metricScalarAt h) (f x) := by
  obtain ⟨Φ, hx, hEq⟩ := hf x
  have hg : g = localPullMetric h f hf := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner]
    exact hmetric y v w
  have hfΦ : ∀ y ∈ Φ.source, f =ᶠ[𝓝 y] Φ := fun y hy =>
    Filter.eventually_of_mem (Φ.open_source.mem_nhds hy) fun z hz => hEq hz
  have hR : metricScalarAt g =ᶠ[𝓝 x] (metricScalarAt h ∘ Φ) := by
    filter_upwards [Φ.open_source.mem_nhds hx] with y hy
    rw [Function.comp_apply, ← hEq hy, hg, metricScalarAt_localPull]
  have hΦsmooth : ContMDiffAt I I ∞ Φ x :=
    Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx)
  have hRh : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (metricScalarAt h ∘ Φ) x :=
    (metricScalar_smooth h).contMDiffAt.comp x hΦsmooth
  rw [laplacian_congr_of_eventuallyEq (LeviCivita g) g (metricScalar_smooth g).contMDiffAt hRh hR]
  have hinner : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g.inner y v w = h.inner (Φ y) (mfderiv I I Φ y v) (mfderiv I I Φ y w) := by
    filter_upwards [Φ.open_source.mem_nhds hx] with y hy v w
    have hdf : mfderiv I I f y = mfderiv I I Φ y := (hfΦ y hy).mfderiv_eq
    rw [← hEq hy, ← hdf]
    exact hmetric y v w
  rw [laplacian_eq_of_partialDiffeomorph_inner g h Φ hx hinner
    ((metricScalar_smooth h).contMDiffAt.of_le (by decide)), hEq hx]

theorem normSq_ricci_eq_of_local_isometry (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f)
    (hmetric : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = h.inner (f y) (mfderiv I I f y v) (mfderiv I I f y w)) (x : M) :
    normSq0S g x 2 (metricRicciAt g x) = normSq0S h (f x) 2 (metricRicciAt h (f x)) := by
  classical
  have hg : g = localPullMetric h f hf := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner]
    exact hmetric y v w
  obtain ⟨b, hON⟩ := exists_orthonormal_basis g x
  let d : TangentSpace I x ≃L[ℝ] TangentSpace I (f x) :=
    hf.mfderivToContinuousLinearEquiv (by simp) x
  have hd (z : TangentSpace I x) : d z = mfderiv I I f x z :=
    congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I (f x) => L z)
      (hf.mfderivToContinuousLinearEquiv_coe (x := x) (by simp))
  let b' := b.map d.toLinearEquiv
  have hb' (i) : b' i = mfderiv I I f x (b i) := by
    change (b.map d.toLinearEquiv) i = _
    rw [Module.Basis.map_apply]
    exact hd _
  have hON' : ∀ i j, h.inner (f x) (b' i) (b' j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hb', hb', ← hmetric]
    exact hON i j
  rw [normSq0S_two_eq_coord g x b _ (metricInverseInBasis_of_orthonormal g b hON),
    normSq0S_two_eq_coord h (f x) b' _ (metricInverseInBasis_of_orthonormal h b' hON')]
  have hric : ∀ i j, metricRicciAt g x (fun a : Fin 2 => if a = 0 then b i else b j) =
      metricRicciAt h (f x) (fun a : Fin 2 => if a = 0 then b' i else b' j) := by
    intro i j
    change metricRicciAt g x (vec2 (b i) (b j)) = metricRicciAt h (f x) (vec2 (b' i) (b' j))
    rw [metricRicciAt_apply_eq_ricciTensor g x (b i) (b j),
      metricRicciAt_apply_eq_ricciTensor h (f x) (b' i) (b' j), hb', hb', hg]
    exact ricciTensor_localPull h f hf x (b i) (b j)
  simp only [hric]


omit [I.Boundaryless] [T2Space M] in
theorem scalarEvolutionRate_def (g : SmoothRiemannianMetric I M) (x : M) :
    scalarEvolutionRate g x =
      laplacian (LeviCivita g) g (metricScalarAt g) x + 2 * normSq0S g x 2 (metricRicciAt g x) :=
  rfl

theorem scalarEvolutionRate_eq_of_local_isometry [BoundarylessManifold I M]
    [BoundarylessManifold I N] (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f)
    (hmetric : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = h.inner (f y) (mfderiv I I f y v) (mfderiv I I f y w)) (x : M) :
    scalarEvolutionRate g x = scalarEvolutionRate h (f x) := by
  rw [scalarEvolutionRate_def, scalarEvolutionRate_def,
    laplacian_scalar_eq_of_local_isometry g h f hf hmetric x,
    normSq_ricci_eq_of_local_isometry g h f hf hmetric x]

theorem scalarEvolutionRate_restrictOpen [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) (x : U) :
    scalarEvolutionRate (g.restrictOpen U) x = scalarEvolutionRate g (x : M) :=
  scalarEvolutionRate_eq_of_local_isometry (g.restrictOpen U) g Subtype.val
    (isLocalDiffeomorph_subtype_val U) (fun y v w => by
      rw [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply,
        mfderiv_subtype_val_apply]) x

theorem continuousWithinAt_scalarEvolutionRate_of_chartGramFamilySmoothWithinOn
    [BoundarylessManifold I M] (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (x : M) (hG : chartGramFamilySmoothWithinOn (I := I) g x J) {t₀ : ℝ}
    (ht₀ : t₀ ∈ J) :
    ContinuousWithinAt (fun t => scalarEvolutionRate (g t) x) J t₀ :=
  (continuousWithinAt_laplacian_scalar_of_chartGramFamilySmoothWithinOn g x hG ht₀).add
    ((continuousWithinAt_normSq_ricci_of_chartGramFamilySmoothWithinOn g x hG ht₀).const_mul 2)

end DifferentialGeometry.Geometry.Curvature
