import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatSecondTimeDerivative
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeSecondWeakDerivative
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeMeasureRestrict

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_contDiffOn_timeH1_chartInverse_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a < b)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z)) :
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    ∀ Df : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω)),
      (∀ k, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv k (fun z => Df k (t, z))
        (fun z => F (t, z)) Ω) →
    ∀ DDf : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω)),
      (∀ i j, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv j
        (fun z => DDf i j (t, z)) (fun z => Df i (t, z)) Ω) →
    let μ := (timeMeasure T).restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω₀)
    ∀ Ft : Lp ℝ 2 ν,
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, F p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, Ft p * φ p ∂ν) →
      ∃ v : timeH1 (Lp ℝ 2 (volume.restrict Ω₀)) (b - a),
        ContDiffOn ℝ 1 v.toFun (Icc (0 : ℝ) (b - a)) ∧
        ∀ᵐ s ∂timeMeasure (b - a),
          (v.toFun s : EuStd → ℝ) =ᵐ[volume.restrict Ω₀] fun z =>
            H1ComplDirichletToLp q (u (a + s))
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
  intro F Df hDf DDf hDDf
  have hI : Icc a b ⊆ Icc (0 : ℝ) T := Icc_subset_Icc ha.le hb.le
  have hμ : (timeMeasure T).restrict (Icc a b) = volume.restrict (Icc a b) :=
    Measure.restrict_restrict_of_subset hI
  dsimp only
  rw [hμ]
  intro Ft hFt
  let μ := volume.restrict (Icc a b)
  let ν := μ.prod (volume.restrict Ω₀)
  have hμle : μ ≤ timeMeasure T := by
    change volume.restrict (Icc a b) ≤ timeMeasure T
    rw [← hμ]
    exact Measure.restrict_le_self
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  let U := dirichletLocalSpacetimeLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u
  have hmeasure : ν ≤ (timeMeasure T).prod (volume.restrict Ω) :=
    Measure.prod_mono hμle (Measure.restrict_mono hsub le_rfl)
  have hU : MemLp U 2 ν := (Lp.memLp U).mono_measure hmeasure
  let U₀ := hU.toLp U
  have hU₀ : U₀ =ᵐ[ν] U := hU.coeFn_toLp
  have hsource := exists_local_lp_weak_time_deriv_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb u f w hwmass hwderiv
  dsimp only at hsource
  rw [hμ] at hsource
  let R := Classical.choose hsource
  have hR := Classical.choose_spec hsource
  have hsecond := exists_second_weak_time_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab.le u f w hwmass hwderiv Df hDf DDf hDDf
  change ∀ Ft : Lp ℝ 2 (((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀)),
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, F p * fderiv ℝ φ p (1, 0) ∂(((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀))) = -∫ p, Ft p * φ p ∂(((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀))) →
    ∀ R : Lp ℝ 2 (((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀)),
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
        (∫ p, U p * fderiv ℝ φ p (1, 0) ∂(((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀))) = -∫ p, R p * φ p ∂(((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀))) →
      ∃ Rt : Lp ℝ 2 (((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀)),
        ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
          (∫ p, R p * fderiv ℝ φ p (1, 0) ∂(((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀))) = -∫ p, Rt p * φ p ∂(((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀)) at hsecond
  rw [hμ] at hsecond
  have hsecondR := hsecond Ft hFt R hR
  let Rt := Classical.choose hsecondR
  have hRt := Classical.choose_spec hsecondR
  have hroot : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω₀ →
      (∫ p, U₀ p * fderiv ℝ φ p (1, 0) ∂ν) = -∫ p, R p * φ p ∂ν := by
    intro φ hφ hφc hφs
    refine (integral_congr_ae ?_).trans (hR φ hφ hφc hφs)
    filter_upwards [hU₀] with p hp
    exact congrArg (fun z => z * fderiv ℝ φ p (1, 0)) hp
  have hregular := exists_contDiffOn_timeH1_of_second_spacetime_weak_deriv
    hab hΩ₀ U₀ R Rt hroot hRt
  let v := Classical.choose hregular
  have hv := Classical.choose_spec (Classical.choose_spec hregular)
  have hP : ∀ᵐ t ∂μ, (fun z => U₀ (t, z)) =ᵐ[volume.restrict Ω₀] fun z =>
      H1ComplDirichletToLp q (u t)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hU₀,
      (dirichletLocalSpacetimeLp_coeFn q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) (timeMeasure T) u).filter_mono (ae_mono hμle)]
      with t ht hu
    exact Filter.EventuallyEq.trans ht
      (hu.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  have hshift : MeasurePreserving (fun s : ℝ => a + s)
      (timeMeasure (b - a)) μ := by
    change MeasurePreserving (fun s : ℝ => a + s) (timeMeasure (b - a)) (volume.restrict (Icc a b))
    rw [← hμ]
    exact measurePreserving_add_right_timeMeasure_restrict hI
  refine ⟨v, hv.2.2.1, ?_⟩
  filter_upwards [hv.1, hshift.quasiMeasurePreserving.ae hP] with s hs hp
  exact Filter.EventuallyEq.trans hs.1 hp

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
