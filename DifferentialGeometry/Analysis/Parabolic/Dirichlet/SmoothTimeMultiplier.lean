import DifferentialGeometry.Analysis.Calculus.ContinuousLinearMapDerivative
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SmoothTimeTest
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMul
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquaredTime
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

open Filter Set
open scoped Topology

noncomputable section

open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private theorem smoothMulH1ComplDirichlet_hasDerivAt_on_smooth
    (q : SmoothRiemannianMetric I_hs M) (ρ ρ' : ℝ → C^∞⟮I_hs, M; ℝ⟯)
    {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ))
    (hρ' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ' p.1 p.2) (J ×ˢ univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => ρ s x) (ρ' t x) t)
    (v : SmoothScalarDirichlet q) {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s => smoothMulH1ComplDirichlet q (ρ s)
      (smoothToH1ComplDirichlet q v))
      (smoothMulH1ComplDirichlet q (ρ' t) (smoothToH1ComplDirichlet q v)) t := by
  let w : ℝ → SmoothScalarDirichlet q := fun t => smoothScalarDirichletMul q (ρ t) v
  let w' : ℝ → SmoothScalarDirichlet q := fun t => smoothScalarDirichletMul q (ρ' t) v
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => v.toFun p.2) (J ×ˢ univ) :=
    (v.smooth.comp contMDiff_snd).contMDiffOn
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (w p.1).toFun p.2) (J ×ˢ univ) := hρ.mul hv
  have hw' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (w' p.1).toFun p.2) (J ×ˢ univ) := hρ'.mul hv
  have hwd : ∀ s ∈ J, ∀ x,
      HasDerivAt (fun r => (w r).toFun x) ((w' s).toFun x) s := by
    intro s hs x
    exact (hd s hs x).mul_const (v.toFun x)
  have hwK : ∀ s ∈ J, tsupport (w' s).toFun ⊆ tsupport v.toFun :=
    fun _ _ => tsupport_mul_subset_right
  have h := hasDerivAt_smoothToH1ComplDirichlet q w w' hJ hw hw' hwd
    (isClosed_tsupport v.toFun) v.interior_support hwK ht
  simpa only [w, w', smoothMulH1ComplDirichlet_smoothToH1ComplDirichlet] using h

private theorem exists_uniform_norm_smoothMulH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (ρ : ℝ → C^∞⟮I_hs, M; ℝ⟯)
    {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ))
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ‖smoothMulH1ComplDirichlet q (ρ t)‖ ≤ C := by
  have hgram : ∀ (α : M) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I_hs) q α p.2 i j)
        (J ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet) := by
    intro α i j
    exact (chartGramMatrix_entry_contMDiffOn (I := I_hs) q α i j).comp
      contMDiffOn_snd (fun p hp => hp.2)
  have hgrad := gradSq_joint (I := I_hs) (fun _ : ℝ => q) hJ hgram
    (fun t x => ρ t x) hρ
  let Q : Set (ℝ × M) := K ×ˢ (univ : Set M)
  have hQ : IsCompact Q := hK.prod isCompact_univ
  have hval : ContinuousOn (fun p : ℝ × M => ρ p.1 p.2 ^ 2) Q :=
    (hρ.continuousOn.mono (Set.prod_mono hKJ Subset.rfl)).pow 2
  have hgr : ContinuousOn (fun p : ℝ × M => q.inner p.2
      (gradientFun (I := I_hs) q (ρ p.1) p.2)
      (gradientFun (I := I_hs) q (ρ p.1) p.2)) Q :=
    hgrad.continuousOn.mono (Set.prod_mono hKJ Subset.rfl)
  obtain ⟨Cv, hCv⟩ := hQ.exists_bound_of_continuousOn hval
  obtain ⟨Cg, hCg⟩ := hQ.exists_bound_of_continuousOn hgr
  let C := max 0 (max Cv Cg)
  have hC : 0 ≤ C := le_max_left 0 _
  refine ⟨Real.sqrt (3 * C), Real.sqrt_nonneg _, ?_⟩
  intro t ht
  apply norm_smoothMulH1ComplDirichlet_le_of_bound q (ρ t) hC
  · intro x
    exact (le_abs_self _).trans ((hCv (t, x) ⟨ht, mem_univ _⟩).trans
      ((le_max_left Cv Cg).trans (le_max_right 0 _)))
  · intro x
    exact (le_abs_self _).trans ((hCg (t, x) ⟨ht, mem_univ _⟩).trans
      ((le_max_right Cv Cg).trans (le_max_right 0 _)))

omit [T2Space M] [CompactSpace M] in
private theorem smoothFamily_deriv_contMDiffOn
    {ρ : ℝ → C^∞⟮I_hs, M; ℝ⟯} {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun t => ρ t p.2) p.1) (J ×ˢ univ) := by
  intro p hp
  exact (DifferentialGeometry.timeDeriv_smoothAt
    (hρ.contMDiffAt ((hJ.prod isOpen_univ).mem_nhds hp)) (by simp)).contMDiffWithinAt

private def smoothFamilyTimeDeriv
    (ρ : ℝ → C^∞⟮I_hs, M; ℝ⟯) {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ)) (t : ℝ) : C^∞⟮I_hs, M; ℝ⟯ := by
  classical
  by_cases ht : t ∈ J
  · refine ⟨fun x => deriv (fun r => ρ r x) t, ?_⟩
    rw [← contMDiffOn_univ]
    exact (smoothFamily_deriv_contMDiffOn hJ hρ).comp
      (contMDiffOn_const.prodMk contMDiffOn_id)
      (fun x _ => ⟨ht, mem_univ x⟩)
  · exact 0

omit [T2Space M] [CompactSpace M] in
private theorem smoothFamilyTimeDeriv_apply
    (ρ : ℝ → C^∞⟮I_hs, M; ℝ⟯) {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ)) {t : ℝ} (ht : t ∈ J) (x : M) :
    smoothFamilyTimeDeriv ρ hJ hρ t x = deriv (fun r => ρ r x) t := by
  classical
  simp [smoothFamilyTimeDeriv, ht]

omit [T2Space M] [CompactSpace M] in
private theorem smoothFamilyTimeDeriv_joint
    (ρ : ℝ → C^∞⟮I_hs, M; ℝ⟯) {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => smoothFamilyTimeDeriv ρ hJ hρ p.1 p.2) (J ×ˢ univ) :=
  (smoothFamily_deriv_contMDiffOn hJ hρ).congr
    (fun p hp => smoothFamilyTimeDeriv_apply ρ hJ hρ hp.1 p.2)

omit [T2Space M] [CompactSpace M] in
private theorem smoothFamilyTimeDeriv_hasDerivAt
    (ρ : ℝ → C^∞⟮I_hs, M; ℝ⟯) {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ)) {t : ℝ} (ht : t ∈ J) (x : M) :
    HasDerivAt (fun s => ρ s x) (smoothFamilyTimeDeriv ρ hJ hρ t x) t := by
  rw [smoothFamilyTimeDeriv_apply ρ hJ hρ ht]
  have hslice : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => ρ s x) J :=
    hρ.comp (contMDiffOn_id.prodMk contMDiffOn_const) (fun s hs => ⟨hs, mem_univ x⟩)
  exact ((hslice.contMDiffAt (hJ.mem_nhds ht)).contDiffAt.differentiableAt (by simp)).hasDerivAt

private theorem continuousOn_smoothMulH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (ρ : ℝ → C^∞⟮I_hs, M; ℝ⟯)
    {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ)) :
    ContinuousOn (fun t => smoothMulH1ComplDirichlet q (ρ t)) J := by
  intro t ht
  let ρ' := smoothFamilyTimeDeriv ρ hJ hρ
  have hρ' := smoothFamilyTimeDeriv_joint ρ hJ hρ
  obtain ⟨r, hr, hrJ⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds ht)
  have hhalf : 0 < r / 2 := half_pos hr
  have hcJ : Metric.closedBall t (r / 2) ⊆ J :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrJ
  obtain ⟨C, hC, hCb⟩ := exists_uniform_norm_smoothMulH1ComplDirichlet q ρ' hJ hρ'
    (isCompact_closedBall t (r / 2)) hcJ
  apply ContinuousAt.continuousWithinAt
  apply ContinuousLinearMap.continuousAt_of_hasDerivAt_apply_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q) hhalf hC
  · intro s hs v
    exact smoothMulH1ComplDirichlet_hasDerivAt_on_smooth q ρ ρ' hJ hρ hρ'
      (fun z hz x => smoothFamilyTimeDeriv_hasDerivAt ρ hJ hρ hz x) v
      (hcJ (Metric.ball_subset_closedBall hs))
  · intro s hs
    exact hCb s (Metric.ball_subset_closedBall hs)

theorem hasDerivAt_smoothMulH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (ρ ρ' : ℝ → C^∞⟮I_hs, M; ℝ⟯)
    {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ))
    (hρ' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ' p.1 p.2) (J ×ˢ univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => ρ s x) (ρ' t x) t)
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s => smoothMulH1ComplDirichlet q (ρ s))
      (smoothMulH1ComplDirichlet q (ρ' t)) t := by
  apply ContinuousLinearMap.hasDerivAt_of_hasDerivAt_apply_of_denseRange
    (denseRange_smoothToH1ComplDirichlet q)
    ((continuousOn_smoothMulH1ComplDirichlet q ρ' hJ hρ').continuousAt (hJ.mem_nhds ht))
  filter_upwards [hJ.mem_nhds ht] with s hs
  intro v
  exact smoothMulH1ComplDirichlet_hasDerivAt_on_smooth q ρ ρ' hJ hρ hρ' hd v hs

theorem contDiffOn_one_smoothMulH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (ρ : ℝ → C^∞⟮I_hs, M; ℝ⟯)
    {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun t => smoothMulH1ComplDirichlet q (ρ t)) J := by
  let : NormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let ρ' := smoothFamilyTimeDeriv ρ hJ hρ
  have hρ' := smoothFamilyTimeDeriv_joint ρ hJ hρ
  have hd (t : ℝ) (ht : t ∈ J) := hasDerivAt_smoothMulH1ComplDirichlet q ρ ρ' hJ hρ hρ'
    (fun s hs x => smoothFamilyTimeDeriv_hasDerivAt ρ hJ hρ hs x) ht
  apply (contDiffOn_one_iff_derivWithin hJ.uniqueDiffOn).mpr
  constructor
  · intro t ht
    exact (hd t ht).differentiableAt.differentiableWithinAt
  · exact (continuousOn_smoothMulH1ComplDirichlet q ρ' hJ hρ').congr
      (fun t ht => (hd t ht).hasDerivWithinAt.derivWithin (hJ.uniqueDiffWithinAt ht))

theorem exists_timeH1_smoothMulH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (ρ ρ' : ℝ → C^∞⟮I_hs, M; ℝ⟯)
    {J : Set ℝ} (hJ : IsOpen J)
    (hρ : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ p.1 p.2) (J ×ˢ univ))
    (hρ' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ρ' p.1 p.2) (J ×ˢ univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => ρ s x) (ρ' t x) t)
    {T : ℝ} (hT : 0 ≤ T) (hTJ : Icc (0 : ℝ) T ⊆ J)
    (u : timeH1 (H1ComplDirichlet q) T) :
    ∃ w : timeH1 (H1ComplDirichlet q) T,
      w.initial = smoothMulH1ComplDirichlet q (ρ 0) u.initial ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        w.toFun t = smoothMulH1ComplDirichlet q (ρ t) (u.toFun t)) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t =>
        smoothMulH1ComplDirichlet q (ρ' t) (u.toFun t) +
          smoothMulH1ComplDirichlet q (ρ t) (u.deriv t)) := by
  let : NormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q) :=
    ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨w, hwi, hw, hwd⟩ := exists_timeH1_clm_apply_of_contDiffOn hT
    ((contDiffOn_one_smoothMulH1ComplDirichlet q ρ hJ hρ).mono hTJ) u
  refine ⟨w, hwi, hw, ?_⟩
  filter_upwards [hwd, ae_restrict_mem measurableSet_Icc] with t hwt ht
  rw [hwt, (hasDerivAt_smoothMulH1ComplDirichlet q ρ ρ' hJ hρ hρ' hd (hTJ ht)).deriv]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_timeH1_smoothMulH1ComplDirichlet_volumeDensity_swap
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (u : timeH1 (H1ComplDirichlet q) T) :
    ∃ w : timeH1 (H1ComplDirichlet q) T,
      w.initial = smoothMulH1ComplDirichlet q
        (riemannianVolumeDensitySmoothMap (G.metric 0) q) u.initial ∧
      (∀ t ∈ Icc (0 : ℝ) T, w.toFun t = smoothMulH1ComplDirichlet q
        (riemannianVolumeDensitySmoothMap (G.metric t) q) (u.toFun t)) ∧
      (∀ᵐ t ∂timeMeasure T,
        H1ComplDirichletToLp q (w.deriv t) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
          (fun x => -(1 / 2) * traceTimeDerivMetric (I := I_hs) G.metric t x *
            riemannianVolumeDensity (G.metric t) q x * H1ComplDirichletToLp q (u.toFun t) x +
            riemannianVolumeDensity (G.metric t) q x * H1ComplDirichletToLp q (u.deriv t) x)) := by
  let ρ : ℝ → C^∞⟮I_hs, M; ℝ⟯ := fun t => riemannianVolumeDensitySmoothMap (G.metric t) q
  have hρ := riemannianVolumeDensity_swap_contMDiffOn_of_metricFamilySmoothOn hG q
  let ρ' := smoothFamilyTimeDeriv ρ D.regular_isOpen hρ
  have hρ' := smoothFamilyTimeDeriv_joint ρ D.regular_isOpen hρ
  have hd : ∀ t ∈ D.regular, ∀ x, HasDerivAt (fun s => ρ s x) (ρ' t x) t :=
    fun t ht x => smoothFamilyTimeDeriv_hasDerivAt ρ D.regular_isOpen hρ ht x
  obtain ⟨w, hwi, hw, hwd⟩ := exists_timeH1_smoothMulH1ComplDirichlet q ρ ρ'
    D.regular_isOpen hρ hρ' hd hT hreg u
  refine ⟨w, hwi, hw, ?_⟩
  filter_upwards [hwd, ae_restrict_mem measurableSet_Icc] with t hwt ht
  rw [hwt, map_add, H1ComplDirichletToLp_smoothMulH1ComplDirichlet,
    H1ComplDirichletToLp_smoothMulH1ComplDirichlet]
  filter_upwards [Lp.coeFn_add (smoothMulLp q (ρ' t) (H1ComplDirichletToLp q (u.toFun t)))
      (smoothMulLp q (ρ t) (H1ComplDirichletToLp q (u.deriv t))),
    smoothMulLp_apply_coeFn q (ρ' t) (H1ComplDirichletToLp q (u.toFun t)),
    smoothMulLp_apply_coeFn q (ρ t) (H1ComplDirichletToLp q (u.deriv t))] with x hsum h1 h2
  rw [hsum, Pi.add_apply, h1, h2]
  have hdρ := hasDerivAt_riemannianVolumeDensity_swap_of_chartGram_contMDiffOn q
    D.regular_isOpen (fun α i j => hG.chartGramMatrix_contDiffOn Subset.rfl α i j) (hreg ht) x
  have heq := (hd t (hreg ht) x).unique hdρ
  change ρ' t x * _ + ρ t x * _ = _
  rw [heq]
  rfl

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
