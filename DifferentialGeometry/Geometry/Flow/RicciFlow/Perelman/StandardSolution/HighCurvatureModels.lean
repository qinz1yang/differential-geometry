import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedGoodPointBounds
import DifferentialGeometry.Geometry.Curvature.RicciRayleighOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.SpatialNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds

noncomputable section
open Set
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem PartialStandardSolution.phiAlmostNonnegative
    (S : PartialStandardSolution) {Phi : ℝ → ℝ} (hPhi : ∀ r, 0 ≤ Phi r) :
    PhiAlmostNonnegative S.toSolutionOn S.domain Phi := by
  intro t ht x
  change curvatureOperatorLowerBoundAt (S.metric t) x
    (metricAlgebraicCurvatureTensorAt (S.metric t) x) (Phi (S.toSolutionOn.scalar t x))
  rw [curvatureOperatorLowerBoundAt_iff_neg_leastUpperRicciAt_le]
  exact (neg_nonpos.mpr (S.leastUpperRicciAt_nonneg t ht x)).trans (hPhi _)


private theorem standard_late_slab_spatial_noncollapse
    (S : PartialStandardSolution) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ∈ S.domain) (hb1 : b < 1) :
    SpatiallyKappaNoncollapsedBelowScale
      (S.toSolutionOn.timeRestrict (RealTimeInterval.closed a b hab))
      (standardParabolicNoncollapseCoeff / 1000000) (Real.sqrt (5000 * a)) := by
  refine ⟨by positivity, ?_⟩
  intro t B hr
  have ht : (t : ℝ) ∈ S.domain :=
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mpr
      ⟨ha.le.trans t.property.1, (ENNReal.ofReal_le_ofReal t.property.2).trans_lt
        ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos b).mp hb).2⟩
  let t₀ : (lifetimeInterval S.lifetime S.lifetime_pos).FlowTime := ⟨t, ht⟩
  let B₀ : FlowMetricBall S.toSolutionOn t₀ := ⟨B.center, B.radius, B.radius_pos⟩
  exact S.spatially_noncollapsed_of_time_ge t₀ t.property.1
    (t.property.2.trans_lt hb1) B₀ hr


private theorem standard_late_slab_scaled_properties
    (S : PartialStandardSolution) {a b A : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b ∈ S.domain) (hb1 : b < 1) (hA : 0 < A) :
    let D₀ := RealTimeInterval.closed a b hab.le
    let Q := S.toSolutionOn.timeRestrict D₀
    let ha₀ : a ∈ D₀.carrier := ⟨le_rfl, hab.le⟩
    let D₁ := parabolicInterval D₀ a A ha₀
    let P := parabolicSolution Q a A hA ha₀
    let U := A * (b - a)
    let hU : 0 ≤ U := mul_nonneg hA.le (sub_nonneg.mpr hab.le)
    let D₂ := RealTimeInterval.closed 0 U hU
    let Z := P.timeRestrict D₂
    IsSolutionOn Z ∧
      (∀ s ∈ D₂.carrier, RiemannianMetricComplete (Z.base.metric s)) ∧
      (∀ u v : ℝ, u ≤ v → Icc u v ⊆ D₂.carrier →
        ∃ C : ℝ, ∀ s ∈ Icc u v, ∀ x : E3, FlowMetricBall.rmNormSq Z s x ≤ C) ∧
      SpatiallyKappaNoncollapsedBelowScale Z
        (standardParabolicNoncollapseCoeff / 1000000)
        (Real.sqrt A * Real.sqrt (5000 * a)) ∧
      D₂.carrier ⊆ D₁.carrier ∧
      ∀ s ∈ D₂.carrier, parabolicTime a A s ∈ Icc a b := by
  intro D₀ Q ha₀ D₁ P U hU D₂ Z
  have hbaseSub : D₀.carrier ⊆ S.domain := by
    intro s hs
    exact (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨ha.le.trans hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt
        ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos b).mp hb).2⟩
  have hbaseReg : D₀.regular ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro s hs
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos s).mpr
      ⟨ha.trans hs.1, (ENNReal.ofReal_le_ofReal hs.2.le).trans_lt
        ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos b).mp hb).2⟩
  have hQ : IsSolutionOn Q := isSolutionOn_timeRestrict S.isSolutionOn hbaseSub hbaseReg
  have hP : IsSolutionOn P := parabolicSolution_isSolutionOn Q hQ a A hA ha₀
  have htime (s : ℝ) (hs : s ∈ D₂.carrier) : parabolicTime a A s ∈ Icc a b := by
    change a ≤ a + s / A ∧ a + s / A ≤ b
    constructor
    · have h := div_nonneg hs.1 hA.le
      linarith
    · have h := (div_le_iff₀ hA).mpr (by simpa only [U, mul_comm] using hs.2)
      linarith
  have hsub : D₂.carrier ⊆ D₁.carrier := htime
  have hreg : D₂.regular ⊆ D₁.regular := by
    intro s hs
    change a < a + s / A ∧ a + s / A < b
    constructor
    · have h := div_pos hs.1 hA
      linarith
    · have h := (div_lt_iff₀ hA).mpr (by simpa only [U, mul_comm] using hs.2)
      linarith
  refine ⟨isSolutionOn_timeRestrict hP hsub hreg, ?_, ?_, ?_, hsub, htime⟩
  · intro s hs
    exact (S.complete _ (hbaseSub (htime s hs))).scaleMetric A hA
  · intro u v huv hwindow
    obtain ⟨K, hK, hcurv⟩ := S.curvature_bound b
      ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos b).mp hb).1
      ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos b).mp hb).2
    refine ⟨A⁻¹ ^ 2 * K ^ 2, ?_⟩
    intro s hs x
    have hold := hcurv (parabolicTime a A s)
      ⟨ha.le.trans (htime s (hwindow hs)).1, (htime s (hwindow hs)).2⟩ x
    have hsq := (Real.sqrt_le_iff.mp hold).2
    change FlowMetricBall.rmNormSq P s x ≤ _
    rw [FlowMetricBall.rmNormSq, parabolicRmNormSq]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg A⁻¹)
  · have hspat := standard_late_slab_spatial_noncollapse S ha hab.le hb hb1
    have hpara := parabolic_spatial_noncollapse Q a A hA ha₀
      (standardParabolicNoncollapseCoeff / 1000000) (Real.sqrt (5000 * a)) hspat
    exact spatiallyKappaNoncollapsed_timeRestrict hsub hpara


def standardModelKappa : ℝ := standardParabolicNoncollapseCoeff / 1000000 / modelNoncollapseFactor

theorem standardModelKappa_pos : 0 < standardModelKappa :=
  div_pos (div_pos standardParabolicNoncollapseCoeff_pos (by norm_num)) modelNoncollapseFactor_pos

theorem modelNoncollapseFactor_mul_standardModelKappa :
    modelNoncollapseFactor * standardModelKappa = standardParabolicNoncollapseCoeff / 1000000 :=
  mul_div_cancel₀ _ modelNoncollapseFactor_pos.ne'

theorem exists_standard_high_scalar_model_threshold
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {τ : ℝ} (hτ : 0 < τ) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ (S : PartialStandardSolution)
      (o : Surgery.Topology.TangentOrientationSection E3) (x : E3) (t : ℝ),
      t ∈ S.domain → τ ≤ t → t < 1 → Q₀ ≤ metricScalarAt (S.metric t) x →
      OrientedWitness S.toSolutionOn o ε standardModelKappa x t := by
  let a := τ / 2
  let A := 2 / τ
  have ha : 0 < a := half_pos hτ
  have hA : 0 < A := div_pos (by norm_num) hτ
  let κ := standardModelKappa
  have hκ : 0 < κ := standardModelKappa_pos
  let σ := Real.sqrt A * Real.sqrt (5000 * a)
  have hσ : 0 < σ := mul_pos (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr (by positivity))
  let Φ := rescalePinchingFunction A (fun _ : ℝ => (1 : ℝ))
  have hΦ : AdmissiblePinchingFunction Φ := (admissiblePinchingFunction_const zero_lt_one).rescale hA
  obtain ⟨r, hr, _, hmodel⟩ := abstract_model_theorem (eps := ε) (kappa := κ)
    (sigma := σ) (Phi := Φ) hε hε1 hκ hσ hΦ
  refine ⟨A / r ^ 2, div_pos hA (sq_pos_of_pos hr), ?_⟩
  intro S o x t ht hτt ht1 hQ
  have hat : a < t := lt_of_lt_of_le (half_lt_self hτ) hτt
  let D₀ := RealTimeInterval.closed a t hat.le
  let Q := S.toSolutionOn.timeRestrict D₀
  have ha₀ : a ∈ D₀.carrier := ⟨le_rfl, hat.le⟩
  let D₁ := parabolicInterval D₀ a A ha₀
  let P := parabolicSolution Q a A hA ha₀
  let U := A * (t - a)
  have hU1 : 1 ≤ U := by
    have heq : A * (τ - a) = 1 := by dsimp only [A, a]; field_simp; ring
    rw [← heq]
    exact mul_le_mul_of_nonneg_left (by linarith) hA.le
  have hU : 0 ≤ U := zero_le_one.trans hU1
  let D₂ := RealTimeInterval.closed 0 U hU
  let Z := P.timeRestrict D₂
  obtain ⟨hZ, hcomplete, hcurv, hnoncollapse, hsub, htime⟩ :=
    standard_late_slab_scaled_properties S ha hat ht ht1 hA
  have hbaseSub : D₀.carrier ⊆ S.domain := by
    intro s hs
    exact (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨ha.le.trans hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt
        ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht).2⟩
  have hpinQ : PhiAlmostNonnegative Q D₀.carrier (fun _ : ℝ => (1 : ℝ)) := by
    intro s hs y
    exact S.phiAlmostNonnegative (fun _ => zero_le_one) s (hbaseSub hs) y
  have hpinP := phiAlmostNonnegative_paraSolution Q hA ha₀ hpinQ
  have hpin : PhiAlmostNonnegative Z D₂.carrier Φ := by
    intro s hs y
    exact hpinP s (htime s hs) y
  have hhyp : ClosedModelHypotheses Z κ σ Φ :=
    { isSolution := hZ
      complete := hcomplete
      curvature := hcurv
      pinching := hpin
      noncollapse := by
        change ParabolicallyKappaNoncollapsedBelowScale Z
          (modelNoncollapseFactor * standardModelKappa) σ
        rw [modelNoncollapseFactor_mul_standardModelKappa]
        exact parabolicallyKappaNoncollapsedBelowScale_of_spatially hnoncollapse }
  have htimeU : parabolicTime a A U = t := by
    dsimp only [parabolicTime, U]
    field_simp
    ring
  have hscalar : Z.scalar U x = A⁻¹ * metricScalarAt (S.metric t) x := by
    change P.scalar U x = _
    rw [parabolicSolution_scalar]
    simp only [htimeU]
    rfl
  have hthreshold : r⁻¹ ^ 2 ≤ Z.scalar U x := by
    rw [hscalar]
    calc
      r⁻¹ ^ 2 = A⁻¹ * (A / r ^ 2) := by field_simp
      _ ≤ A⁻¹ * metricScalarAt (S.metric t) x := mul_le_mul_of_nonneg_left hQ (inv_nonneg.mpr hA.le)
  have hw : OrientedWitness Z o ε κ x U :=
    hmodel E3 o U hU1 Z hhyp x U ⟨hU1, le_rfl⟩ hthreshold
  have hwP : OrientedWitness P o ε κ x U := orientedWitness_of_timeRestrict hsub hw
  have hwQ := (orientedWitness_paraSolution_iff Q o hA ha₀ U x ε κ).mp hwP
  rw [htimeU] at hwQ
  exact orientedWitness_of_timeRestrict hbaseSub hwQ


private theorem nonempty_standard_tangent_orientation :
    Nonempty (Surgery.Topology.TangentOrientationSection E3) := by
  let e := (finCongr (by simp : Module.finrank ℝ E3 = 3)).symm
  let o := DifferentialGeometry.Topology.Manifold.euclideanSmoothOrientation E3
    (Orientation.reindex ℝ E3 e ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation))
  obtain ⟨O, _⟩ := DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
    (𝓡 3) o
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  let O₃ : DifferentialGeometry.ManifoldOrientation (𝓡 3) E3 3 :=
    cast (congrArg (fun n => DifferentialGeometry.ManifoldOrientation (𝓡 3) E3 n) hdim) O
  exact ⟨{ orientation := O₃.orientation, locally_constant := O₃.locally_constant }⟩

private theorem standard_regular_window_of_model
    (S : PartialStandardSolution) {a b : ℝ}
    (h : Icc a b ⊆ S.domain) :
    Ioo a b ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
  intro t ht
  have hpoint := h ⟨ht.1.le, ht.2.le⟩
  have hleft := h ⟨le_rfl, (ht.1.trans ht.2).le⟩
  exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
    ⟨((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos a).mp hleft).1.trans_lt ht.1,
      ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp hpoint).2⟩

theorem exists_standard_high_scalar_time_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ →
      ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ (S : PartialStandardSolution) (x : E3) (t : ℝ),
        t ∈ S.domain → τ ≤ t → t < 1 → Q₀ ≤ metricScalarAt (S.metric t) x →
        |deriv (fun s => metricScalarAt (S.metric s) x) t| ≤
          C * metricScalarAt (S.metric t) x ^ 2 := by
  obtain ⟨C, hC, hderiv⟩ := exists_windowedModelWitness_scalar_derivative_bounds
  refine ⟨C, hC, ?_⟩
  intro τ hτ
  obtain ⟨Q₀, hQ₀, hmodels⟩ := exists_standard_high_scalar_model_threshold
    (ε := 1 / 4) (by norm_num) (by norm_num) hτ
  refine ⟨Q₀, hQ₀, ?_⟩
  intro S x t ht hτt ht1 hQ
  obtain ⟨o⟩ := nonempty_standard_tangent_orientation
  obtain ⟨W, _⟩ := hmodels S o x t ht hτt ht1 hQ
  have htime : t ∈ (lifetimeInterval S.lifetime S.lifetime_pos).regular :=
    (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
      ⟨hτ.trans_le hτt, ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht).2⟩
  have hbound := (hderiv S.isSolutionOn W (by norm_num)
    (standard_regular_window_of_model S W.window_mem)).2
  have hdiff := (S.isSolutionOn.scalarTime
    (K := (lifetimeInterval S.lifetime S.lifetime_pos).carrier)
    ((lifetimeInterval S.lifetime S.lifetime_pos).regular_subset htime)
    (fun _ hs => hs) x).differentiableAt
      ((lifetimeInterval S.lifetime S.lifetime_pos).regular_mem_nhds htime)
  rw [hdiff.derivWithin (uniqueDiffWithinAt_Iic t)] at hbound
  exact hbound

theorem exists_standard_high_inverse_scalar_time_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ →
      ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ (S : PartialStandardSolution) (x : E3) (t : ℝ),
        t ∈ S.domain → τ ≤ t → t < 1 → Q₀ ≤ metricScalarAt (S.metric t) x →
        |deriv (fun s => (metricScalarAt (S.metric s) x)⁻¹) t| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_standard_high_scalar_time_derivative_bound
  refine ⟨C, hC, ?_⟩
  intro τ hτ
  obtain ⟨Q₀, hQ₀, hQ⟩ := hbound τ hτ
  refine ⟨Q₀, hQ₀, ?_⟩
  intro S x t ht hτt ht1 hRt
  have hRpos : 0 < metricScalarAt (S.metric t) x := hQ₀.trans_le hRt
  have htime : t ∈ (lifetimeInterval S.lifetime S.lifetime_pos).regular :=
    (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
      ⟨hτ.trans_le hτt, ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht).2⟩
  have hd : DifferentiableAt ℝ (fun s => metricScalarAt (S.metric s) x) t :=
    (S.scalarTime (K := S.domain) ht (fun _ hs => hs) x).differentiableAt
      ((lifetimeInterval S.lifetime S.lifetime_pos).regular_mem_nhds htime)
  have he := (hd.hasDerivAt.inv hRpos.ne').deriv
  change deriv (fun s => (metricScalarAt (S.metric s) x)⁻¹) t = _ at he
  rw [he, abs_div, abs_neg, abs_of_pos (sq_pos_of_pos hRpos)]
  exact (div_le_iff₀ (sq_pos_of_pos hRpos)).mpr (hQ S x t ht hτt ht1 hRt)


theorem exists_standard_high_scalar_model
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {τ : ℝ} (hτ : 0 < τ) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ (S : PartialStandardSolution)
      (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
      t ∈ S.domain → τ ≤ t → t < 1 → Q₀ ≤ metricScalarAt (S.metric t) x →
      Nonempty (WindowedModelWitness ε standardModelKappa S.toSolutionOn x t) := by
  obtain ⟨Q₀, hQ₀, hmodel⟩ := exists_standard_high_scalar_model_threshold hε hε1 hτ
  refine ⟨Q₀, hQ₀, ?_⟩
  intro S x t ht hτt ht1 hQ
  obtain ⟨o⟩ := nonempty_standard_tangent_orientation
  obtain ⟨W, _⟩ := hmodel S o x t ht hτt ht1 hQ
  exact ⟨W⟩


end DifferentialGeometry.PDE.RicciFlow
