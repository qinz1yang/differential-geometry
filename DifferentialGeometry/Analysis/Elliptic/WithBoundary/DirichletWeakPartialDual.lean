import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff
import DifferentialGeometry.Analysis.Integration.Lp.Pairing
import DifferentialGeometry.Analysis.Elliptic.MetricExtension

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private def lpMulCLM (c : Lp ℝ ∞ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => c • f
      map_add' := fun f g => Lp.add_smul c f g
      map_smul' := fun r f => (Lp.smul_comm r c f).symm }
    ‖c‖ (fun f => Lp.norm_smul_le c f)

private theorem lpMulCLM_coeFn (c : Lp ℝ ∞ μ) (f : Lp ℝ 2 μ) :
    (lpMulCLM c f : α → ℝ) =ᵐ[μ] fun x => c x * f x := by
  change (c • f : Lp ℝ 2 μ) =ᵐ[μ] fun x => c x * f x
  exact Lp.coeFn_lpSMul c f

end MeasureTheory

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

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

private theorem chart_weak_partial_ibp_smooth
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {c : EuStd → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c) (hcs : tsupport c ⊆ Ω)
    (k : Fin (Module.finrank ℝ EuN))
    (R D : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω))
    (hR : R = (chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q))
    (hD : D = dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k) :
    ∀ (f H : Lp ℝ 2 (volume.restrict Ω)),
      DeGiorgi.HasWeakPartialDeriv k H f Ω → ∀ (v : SmoothScalarDirichlet q),
      -(∫ z in Ω, f z * fderiv ℝ c z (EuclideanSpace.single k 1) * R (smoothToH1ComplDirichlet q v) z) -
        (∫ z in Ω, f z * c z * D (smoothToH1ComplDirichlet q v) z) = ∫ z in Ω, H z * c z * R (smoothToH1ComplDirichlet q v) z := by
  have hcm : MemLp c ∞ (volume.restrict Ω) := hc.continuous.memLp_top_of_hasCompactSupport hcc _
  have hdcm : MemLp (fun z => fderiv ℝ c z (EuclideanSpace.single k 1)) ∞ (volume.restrict Ω) :=
    ((hc.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcc.fderiv_apply ℝ (EuclideanSpace.single k 1)) _
  intro f H hweak v
  let V := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  have hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω := by
    apply (scalarOnE_contDiffOn α v.smooth).comp (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (subset_closure.trans (hΩs.trans (image_mono interior_subset))) hz
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy
  let ψ := fun z => c z * V z
  have hψs : tsupport ψ ⊆ Ω := tsupport_mul_subset_left.trans hcs
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (hc.contDiffOn.mul hV).contDiff_of_tsupport_subset hΩ hψs
  have hψc : HasCompactSupport ψ := hcc.mul_right
  have hw := hweak ψ hψ hψc hψs
  have hRv : (R (smoothToH1ComplDirichlet q v) : EuStd → ℝ) =ᵐ[volume.restrict Ω] V := by
    rw [hR]
    filter_upwards [DifferentialGeometry.Integral.Measure.chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v)),
      ae_chartInverse_of_ae q α hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset))
        v.memLp_two.coeFn_toLp] with z hz hvz
    change (chartRestrictionLp q α hΩ.measurableSet hΩc (hΩs.trans (image_mono interior_subset)) 2
      (H1ComplDirichletToLp q (smoothToH1ComplDirichlet q v))) z = _
    rw [hz, H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact hvz
  have hDv := dirichletLocalWeakPartialLp_smoothToH1ComplDirichlet_coeFn q α hΩ hΩc hΩs k v
  rw [← hD] at hDv
  have hint₀ := MeasureTheory.integrable_weight_mul_lp _ hdcm f (R (smoothToH1ComplDirichlet q v))
  have hint₁ := MeasureTheory.integrable_weight_mul_lp c hcm f (D (smoothToH1ComplDirichlet q v))
  have heleft : (∫ z in Ω, f z * fderiv ℝ c z (EuclideanSpace.single k 1) * R (smoothToH1ComplDirichlet q v) z) +
      (∫ z in Ω, f z * c z * D (smoothToH1ComplDirichlet q v) z) =
      ∫ z in Ω, f z * fderiv ℝ ψ z (EuclideanSpace.single k 1) := by
    rw [← integral_add hint₀ hint₁]
    apply integral_congr_ae
    filter_upwards [hRv, hDv, ae_restrict_mem hΩ.measurableSet] with z hzv hzd hzΩ
    rw [hzv, hzd]
    have hdV := (hV.contDiffAt (hΩ.mem_nhds hzΩ)).differentiableAt (by simp)
    rw [show fderiv ℝ ψ z = c z • fderiv ℝ V z + V z • fderiv ℝ c z from
      fderiv_fun_mul (hc.differentiable (by simp) z) hdV]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have heright : (∫ z in Ω, H z * c z * R (smoothToH1ComplDirichlet q v) z) =
      ∫ z in Ω, H z * ψ z := by
    apply integral_congr_ae
    filter_upwards [hRv] with z hz
    rw [hz]
    ring
  have halg {a b c d : ℝ} (h₁ : a + b = -c) (h₂ : d = c) : -a - b = d := by
    linarith only [h₁, h₂]
  exact halg (heleft.trans hw) heright


private theorem exists_chart_weak_partial_dual
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {c : EuStd → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c) (hcs : tsupport c ⊆ Ω)
    (k : Fin (Module.finrank ℝ EuN))
    (R D : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω))
    (hR : R = (chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q))
    (hD : D = dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k) :
    ∀ (f H : Lp ℝ 2 (volume.restrict Ω)),
      DeGiorgi.HasWeakPartialDeriv k H f Ω → ∀ v : H1ComplDirichlet q,
      -(∫ z in Ω, f z * fderiv ℝ c z (EuclideanSpace.single k 1) * R v z) -
        (∫ z in Ω, f z * c z * D v z) = ∫ z in Ω, H z * c z * R v z := by
  have hcm : MemLp c ∞ (volume.restrict Ω) := hc.continuous.memLp_top_of_hasCompactSupport hcc _
  have hdcm : MemLp (fun z => fderiv ℝ c z (EuclideanSpace.single k 1)) ∞ (volume.restrict Ω) :=
    ((hc.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcc.fderiv_apply ℝ (EuclideanSpace.single k 1)) _
  intro f H hweak
  have hcontl : Continuous (fun v : H1ComplDirichlet q =>
      -(∫ z in Ω, f z * fderiv ℝ c z (EuclideanSpace.single k 1) * R v z) -
      ∫ z in Ω, f z * c z * D v z) :=
    ((MeasureTheory.continuous_integral_weight_mul_lp _ hdcm f).comp R.continuous).neg.sub
      ((MeasureTheory.continuous_integral_weight_mul_lp c hcm f).comp D.continuous)
  have hcontr : Continuous (fun v : H1ComplDirichlet q => ∫ z in Ω, H z * c z * R v z) :=
    (MeasureTheory.continuous_integral_weight_mul_lp c hcm H).comp R.continuous
  apply funext_iff.mp
  apply DenseRange.equalizer (denseRange_smoothToH1ComplDirichlet q) hcontl hcontr
  funext v
  exact chart_weak_partial_ibp_smooth q α hΩ hΩc hΩs hc hcc hcs k R D hR hD f H hweak v

private theorem exists_chart_weak_partial_dual_map
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {c : EuStd → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c) (hcs : tsupport c ⊆ Ω)
    (k : Fin (Module.finrank ℝ EuN))
    (R D : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω))
    (hR : R = (chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q))
    (hD : D = dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k) :
    ∃ L : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ,
      (∀ (f : Lp ℝ 2 (volume.restrict Ω)) (v : H1ComplDirichlet q),
        L f v = -(∫ z in Ω, f z * fderiv ℝ c z (EuclideanSpace.single k 1) * R v z) -
          ∫ z in Ω, f z * c z * D v z) ∧
      ∀ (f H : Lp ℝ 2 (volume.restrict Ω)),
      DeGiorgi.HasWeakPartialDeriv k H f Ω → ∀ v : H1ComplDirichlet q, L f v = ∫ z in Ω, H z * c z * R v z := by
  have hcm : MemLp c ∞ (volume.restrict Ω) := hc.continuous.memLp_top_of_hasCompactSupport hcc _
  have hdcm : MemLp (fun z => fderiv ℝ c z (EuclideanSpace.single k 1)) ∞ (volume.restrict Ω) :=
    ((hc.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcc.fderiv_apply ℝ (EuclideanSpace.single k 1)) _
  let L₀ : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (MeasureTheory.lpMulCLM (hdcm.toLp _)) R
  let L₁ : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (MeasureTheory.lpMulCLM (hcm.toLp c)) D
  have hL₀ (f : Lp ℝ 2 (volume.restrict Ω)) (v : H1ComplDirichlet q) :
      L₀ f v = ∫ z in Ω, f z * fderiv ℝ c z (EuclideanSpace.single k 1) * R v z := by
    change inner ℝ (MeasureTheory.lpMulCLM (hdcm.toLp _) f) (R v) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.lpMulCLM_coeFn (hdcm.toLp _) f, hdcm.coeFn_toLp] with z hz hcz
    simp only [Real.inner_apply, hz, hcz]
    ring
  have hL₁ (f : Lp ℝ 2 (volume.restrict Ω)) (v : H1ComplDirichlet q) :
      L₁ f v = ∫ z in Ω, f z * c z * D v z := by
    change inner ℝ (MeasureTheory.lpMulCLM (hcm.toLp c) f) (D v) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.lpMulCLM_coeFn (hcm.toLp c) f, hcm.coeFn_toLp] with z hz hcz
    simp only [Real.inner_apply, hz, hcz]
    ring
  have hL (f : Lp ℝ 2 (volume.restrict Ω)) (v : H1ComplDirichlet q) :
      (-L₀ - L₁) f v = -(∫ z in Ω, f z * fderiv ℝ c z (EuclideanSpace.single k 1) * R v z) -
        ∫ z in Ω, f z * c z * D v z := by
    change -L₀ f v - L₁ f v = _
    exact congrArg₂ (fun a b : ℝ => -a - b) (hL₀ f v) (hL₁ f v)
  refine ⟨-L₀ - L₁, hL, ?_⟩
  intro f H hweak v
  exact (hL f v).trans (exists_chart_weak_partial_dual q α hΩ hΩc hΩs hc hcc hcs k R D hR hD f H hweak v)

theorem inner_eq_integral_chartPullback_mul
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω)
    (P : Lp ℝ 2 (volume.restrict Ω)) (v z : H1ComplDirichlet q)
    (hv : (H1ComplDirichletToLp q v : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α (fun x => η x * P x)) :
    inner ℝ (H1ComplDirichletToLp q v) (H1ComplDirichletToLp q z) =
      ∫ x in Ω, P x * (MetricExtension.densityOnEuclid q α x * η x) *
        H1ComplDirichletToLp q z ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x)) := by
  have hfs : Function.support (fun x => η x * P x) ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    (Function.support_mul_subset_left η (P : EuStd → ℝ)).trans ((subset_tsupport η).trans
      (hηs.trans (subset_closure.trans (hΩs.trans (image_mono interior_subset)))))
  have hchart := DifferentialGeometry.Analysis.Sobolev.Chart.integral_mul_chartPullback_eq_integral_euclidean q α
    (Lp.stronglyMeasurable (H1ComplDirichletToLp q z)).measurable
    (hη.continuous.measurable.mul (Lp.stronglyMeasurable P).measurable) hfs
  have he : inner ℝ (H1ComplDirichletToLp q v) (H1ComplDirichletToLp q z) =
      ∫ x, H1ComplDirichletToLp q z x *
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α (fun y => η y * P y) x
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp only [Real.inner_apply, hx]
    ring
  apply he.trans
  apply hchart.trans
  have hzero (x : EuStd) (hx : x ∉ Ω) : η x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)
    (fun x hx => by simp only [Pi.mul_apply, hzero x hx, zero_mul, mul_zero])]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [MetricExtension.densityOnEuclid, Pi.mul_apply]
  ring


theorem exists_lp_dual_weak_partial_eq_integral
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {c : EuStd → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcs : tsupport c ⊆ Ω)
    (k : Fin (Module.finrank ℝ EuN)) :
    let R : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
      (chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
    let D : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k
    ∃ L : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ,
      (∀ (f : Lp ℝ 2 (volume.restrict Ω)) (v : H1ComplDirichlet q),
        L f v = -(∫ z in Ω, f z * fderiv ℝ c z (EuclideanSpace.single k 1) * R v z) -
          ∫ z in Ω, f z * c z * D v z) ∧
      ∀ (f H : Lp ℝ 2 (volume.restrict Ω)),
        DeGiorgi.HasWeakPartialDeriv k H f Ω →
        ∀ v : H1ComplDirichlet q, L f v = ∫ z in Ω, H z * c z * R v z := by
  intro R D
  have hcc : HasCompactSupport c :=
    hΩc.of_isClosed_subset (isClosed_tsupport c) (hcs.trans subset_closure)
  exact exists_chart_weak_partial_dual_map q α hΩ hΩc hΩs hc hcc hcs k R D rfl rfl

theorem exists_lp_dual_weak_partial
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {c : EuStd → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c) (hcs : tsupport c ⊆ Ω)
    (k : Fin (Module.finrank ℝ EuN)) :
    let R : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
      (chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
    let D : H1ComplDirichlet q →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
      dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k
    ∃ L : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ,
      (∀ (f : Lp ℝ 2 (volume.restrict Ω)) (v : H1ComplDirichlet q),
        L f v = -(∫ z in Ω, f z * fderiv ℝ c z (EuclideanSpace.single k 1) * R v z) -
          ∫ z in Ω, f z * c z * D v z) ∧
      ∀ u v : H1ComplDirichlet q, L (R u) v = ∫ z in Ω, D u z * c z * R v z := by
  intro R D
  obtain ⟨L, hL, hweak⟩ :=
    exists_chart_weak_partial_dual_map q α hΩ hΩc hΩs hc hcc hcs k R D rfl rfl
  refine ⟨L, hL, ?_⟩
  intro u v
  apply hweak (R u) (D u) ?_ v
  intro ψ hψ hψc hψs
  have hw := hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k u ψ hψ hψc hψs
  rw [← hw]
  apply integral_congr_ae
  filter_upwards [chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q u)] with z hz
  exact congrArg (· * fderiv ℝ ψ z (EuclideanSpace.single k 1)) hz

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
