import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

set_option autoImplicit false
noncomputable section
open Set
open scoped _root_.Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure _root_.MeasureTheory
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {x : M} {t : ℝ} {U : Set M}

theorem exists_canonicalWitness_of_localCap_of_scalar_pos
    (hpositive : ∀ y ∈ U, 0 < S.scalar t y) (hxU : x ∈ interior U)
    (hcompact : IsCompact U) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ eps : ℝ, ∀ cap : LocalCap S eps x t U, ∀ r : ℝ,
      (Real.sqrt (S.scalar t x))⁻¹ ≤ r →
      riemannianBallOf (S.base.metric t) x r ⊆ U →
      U ⊆ riemannianBallOf (S.base.metric t) x (2 * r) →
      (∀ y ∈ cap.tube,
        10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y) →
      ∃ K : CanonicalWitness S eps (r * Real.sqrt (S.scalar t x)) C x t,
        K.domain.carrier = U ∧ K.radius = r ∧
          ∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap := by
  let : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hx : x ∈ U := interior_subset hxU
  have hUne : U.Nonempty := ⟨x, hx⟩
  have hcont : Continuous (S.scalar t) := (metricScalar_smooth (S.base.metric t)).continuous
  obtain ⟨ymin, hymin, hmin⟩ := hcompact.exists_isMinOn hUne hcont.continuousOn
  obtain ⟨ymax, _, hmax⟩ := hcompact.exists_isMaxOn hUne hcont.continuousOn
  let m := S.scalar t ymin
  let B := S.scalar t ymax
  have hm : 0 < m := hpositive ymin hymin
  let Q := S.scalar t x
  have hQ : 0 < Q := hpositive x hx
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  let curvature : M → ℝ := fun y => Real.sqrt (FlowMetricBall.rmNormSq S t y)
  have hcurvature : Continuous curvature := by
    exact Real.continuous_sqrt.comp
      (DifferentialGeometry.Tensor.RSTensor.normSq0S_smooth
        (S.base.metric t) (metricRm04 (S.base.metric t))).continuous
  obtain ⟨zmax, _, hcurv⟩ := hcompact.exists_isMaxOn hUne hcurvature.continuousOn
  let Bcurv := curvature zmax
  let G := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
    Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3) S 1 t x)
  let T := |derivWithin (fun s => S.scalar s x) (Iic t) t|
  let mu := riemannianVolumeMeasure I3 M (S.base.metric t)
  let : IsLocallyFiniteMeasure mu :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (S.base.metric t)
  let : mu.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure (S.base.metric t)
  have hvol : 0 < mu U :=
    (isOpen_interior.measure_pos mu ⟨x, hxU⟩).trans_le (measure_mono interior_subset)
  have hvfin : mu U ≠ ⊤ := hcompact.measure_lt_top.ne
  let V := (mu U).toReal
  have hV : 0 < V := ENNReal.toReal_pos hvol.ne' hvfin
  obtain ⟨C, hC⟩ := exists_gt (max 1 (max (Q / m) (max (B / Q) (max (Bcurv / Q)
    (max (G / (Q * Real.sqrt Q)) (max (T / Q ^ 2) (V * (Q * Real.sqrt Q))⁻¹))))))
  have hCs : 1 < C ∧ Q / m < C ∧ B / Q < C ∧ Bcurv / Q < C ∧
      G / (Q * Real.sqrt Q) < C ∧ T / Q ^ 2 < C ∧
      (V * (Q * Real.sqrt Q))⁻¹ < C := by simpa only [max_lt_iff] using hC
  obtain ⟨hC1, hCm, hCB, hCrm, hCG, hCT, hCV⟩ := hCs
  have hCp : 0 < C := zero_lt_one.trans hC1
  have hCmin : C⁻¹ * Q ≤ m := by
    rw [← div_eq_inv_mul, div_le_iff₀ hCp]
    simpa only [mul_comm] using (div_le_iff₀ hm).mp hCm.le
  have hCvol : C⁻¹ / (Q * Real.sqrt Q) ≤ V := by
    rw [div_le_iff₀ (mul_pos hQ hroot)]
    exact (inv_le_comm₀ hCp (mul_pos hV (mul_pos hQ hroot))).mpr hCV.le
  refine ⟨C, hC1.le, fun eps cap r hr hinner houter hdepth => ?_⟩
  obtain ⟨Kdomain, hKdomain, hxKdomain⟩ := cap.exists_compactDomain
  let cap' : LocalCap S eps x t Kdomain.carrier := hKdomain.symm ▸ cap
  have hcap' : HEq cap' cap := by cases hKdomain; rfl
  have hdepth' : ∀ y ∈ cap'.tube,
      10000 / Real.sqrt Q ≤ metricDistance (S.base.metric t) x y := by
    cases hKdomain
    exact hdepth
  let j : Fin cap.chain.count := ⟨0, cap.chain.count_pos⟩
  have heps := (cap.chain.necks j).eps_pos
  have heps1 : eps < 1 := (cap.chain.necks j).eps_small.trans (by norm_num)
  let K : CanonicalWitness S eps (r * Real.sqrt Q) C x t := {
    Q_pos := hQ
    time_mem := (cap.chain.necks j).time_domain ⟨by
      linarith [inv_pos.mpr (cap.chain.necks j).Q_pos], le_rfl⟩
    eps_pos := heps
    eps_lt_one := heps1
    domain := Kdomain
    center_inside := hxKdomain
    radius := r
    radius_lower := hr
    radius_upper := by rw [mul_div_cancel_right₀ _ hroot.ne']
    ball_inside := fun y hy => hKdomain.symm ▸ hinner hy
    inside_ball := fun y hy => houter (hKdomain ▸ hy)
    scalar_bounds := fun y hy => ⟨hCmin.trans (hmin (hKdomain ▸ hy)),
      (hmax (hKdomain ▸ hy)).trans ((div_le_iff₀ hQ).mp hCB.le)⟩
    rm_bound := fun y hy => (hcurv (hKdomain ▸ hy)).trans ((div_le_iff₀ hQ).mp hCrm.le)
    alternative := CanonicalAlternative.cap cap' hdepth'
    volume := by
      intro _
      change ENNReal.ofReal (C⁻¹ / (Q * Real.sqrt Q)) ≤ mu Kdomain.carrier
      rw [hKdomain]
      exact (ENNReal.ofReal_le_ofReal hCvol).trans (by rw [ENNReal.ofReal_toReal hvfin])
    gradient := by
      intro v
      have h := abs_scalarDifferential_le (I := I3) S t x v
      have hGQ : G ≤ C * Q * Real.sqrt Q := by
        simpa only [mul_assoc] using (div_le_iff₀ (mul_pos hQ hroot)).mp hCG.le
      exact h.trans (mul_le_mul_of_nonneg_right hGQ (Real.sqrt_nonneg _))
    time_derivative := (div_le_iff₀ (sq_pos_of_pos hQ)).mp hCT.le }
  exact ⟨K, hKdomain, rfl, cap', hdepth', rfl, hcap'⟩

theorem LocalCap.exists_canonicalWitness_of_scalar_pos_of_ball_sandwich
    {eps : ℝ} (cap : LocalCap S eps x t U)
    (hpositive : ∀ y ∈ U, 0 < S.scalar t y) {r : ℝ}
    (hr : (Real.sqrt (S.scalar t x))⁻¹ ≤ r)
    (hinner : riemannianBallOf (S.base.metric t) x r ⊆ U)
    (houter : U ⊆ riemannianBallOf (S.base.metric t) x (2 * r))
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y) :
    1 ≤ r * Real.sqrt (S.scalar t x) ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∃ K : CanonicalWitness S eps (r * Real.sqrt (S.scalar t x)) C x t,
        K.domain.carrier = U ∧ K.radius = r ∧
          ∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap := by
  have hxU : x ∈ interior U := cap.core_inside (interior_subset cap.center_inside)
  have hQ : 0 < S.scalar t x := hpositive x (interior_subset hxU)
  have hroot : 0 < Real.sqrt (S.scalar t x) := Real.sqrt_pos.mpr hQ
  have hC1 : 1 ≤ r * Real.sqrt (S.scalar t x) := by
    have h := mul_le_mul_of_nonneg_right hr hroot.le
    simpa only [inv_mul_cancel₀ hroot.ne'] using h
  obtain ⟨C, hC, hmain⟩ := exists_canonicalWitness_of_localCap_of_scalar_pos
    hpositive hxU cap.isCompact_carrier
  exact ⟨hC1, C, hC, hmain eps cap r hr hinner houter hdepth⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
