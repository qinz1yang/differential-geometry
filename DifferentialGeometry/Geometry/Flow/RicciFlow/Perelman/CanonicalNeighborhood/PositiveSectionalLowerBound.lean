import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorBounds
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciReaction
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (three_bivector_quadratic_realized)

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem secLower_iff_le_leastCurvatureOperatorEigenvalueAt
    (g : SmoothRiemannianMetric I3 M)
    (hdim : Module.finrank ℝ ThreeSpace = 3) (c : ℝ) (U : Set M) :
    SecLower g c U ↔ ∀ x ∈ U, c ≤
      leastCurvatureOperatorEigenvalueAt (I := I3) g x
        (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g x) := by
  constructor
  · intro h x hx
    obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I3) g x hdim
    obtain ⟨cvec, hid, hop⟩ :=
      exists_leastCurvatureOperatorEigenvalueAt_rayleigh_minimizer
        (I := I3) g x basis horth
        (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g x)
    obtain ⟨a, b, hgram, hval⟩ :=
      three_bivector_quadratic_realized (I := I3) g x hdim
        (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g x) cvec
        (fun i => basis (bivectorIndex3 i).1) (fun i => basis (bivectorIndex3 i).2)
    rw [hid] at hgram
    have hsec : c * (g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2) ≤
        metricRm04StandardAt (I := I3) (M := M) g x a b b a := h x hx a b
    have hval' : metricRm04StandardAt (I := I3) (M := M) g x a b b a =
        algebraicCurvatureOperatorQuadraticEval (I := I3) (M := M)
          (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g x) cvec
          (fun i => basis (bivectorIndex3 i).1) (fun i => basis (bivectorIndex3 i).2) := by
      simpa only [metricRm04StandardAt, metricAlgebraicCurvatureTensorAt_coe] using hval
    rw [hval', hop, hgram, mul_one] at hsec
    exact hsec
  · intro h x hx v w
    obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I3) g x hdim
    have hray := leastCurvatureOperatorEigenvalueAt_mul_identity_le (I := I3) g x basis
      horth (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g x)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ => v) (fun _ => w)
    have hnn := algebraicCurvatureIdentityQuadraticEval_nonneg (I := I3) g x
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ => v) (fun _ => w) basis horth
    have hle := (mul_le_mul_of_nonneg_right (h x hx) hnn).trans hray
    have hmain : c * (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2) ≤
        metricRm04StandardAt (I := I3) (M := M) g x v w w v := by
      simpa only [algebraicCurvatureIdentityQuadraticEval,
      algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
      metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt, metricRm04StandardAt_apply,
      g.symm x w v, ← pow_two, one_pow] using hle
    exact hmain

omit [SigmaCompactSpace M] in
theorem secLower_iff_curvatureOperatorLowerBoundAt
    (g : SmoothRiemannianMetric I3 M)
    (hdim : Module.finrank ℝ ThreeSpace = 3) (c : ℝ) (U : Set M) :
    SecLower g c U ↔ ∀ x ∈ U, curvatureOperatorLowerBoundAt (I := I3) g x
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g x) (-c) := by
  rw [secLower_iff_le_leastCurvatureOperatorEigenvalueAt g hdim c U]
  constructor
  · intro h x hx
    obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I3) g x hdim
    refine (curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt
      (I := I3) g x basis horth
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g x) (-c)).mpr ?_
    linarith [h x hx]
  · intro h x hx
    obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I3) g x hdim
    have hle := (curvatureOperatorLowerBoundAt_iff_le_leastCurvatureOperatorEigenvalueAt
      (I := I3) g x basis horth
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g x) (-c)).mp
      (h x hx)
    linarith [hle]

omit [SigmaCompactSpace M] in
theorem secLower_scaleMetric_iff {a c : ℝ} (ha : 0 < a)
    (g : SmoothRiemannianMetric I3 M) (U : Set M) :
    SecLower (scaleMetric (I := I3) a ha g) c U ↔ SecLower g (c * a) U := by
  constructor
  · intro h x hx v w
    have hh : c * (a * g.inner x v v * (a * g.inner x w w) - (a * g.inner x v w) ^ 2) ≤
        metricRm04StandardAt (I := I3) (M := M) (scaleMetric (I := I3) a ha g)
          x v w w v := h x hx v w
    rw [metricRmStandard_scale (I := I3) a ha g x v w w v] at hh
    have hmul : a * (c * a * (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2)) ≤
        a * metricRm04StandardAt (I := I3) (M := M) g x v w w v := by
      nlinarith [hh]
    have hgoal : c * a * (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2) ≤
        metricRm04StandardAt (I := I3) (M := M) g x v w w v :=
      le_of_mul_le_mul_left hmul ha
    exact hgoal
  · intro h x hx v w
    have hh : c * a * (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2) ≤
        metricRm04StandardAt (I := I3) (M := M) g x v w w v := h x hx v w
    have hmul := mul_le_mul_of_nonneg_right hh ha.le
    have hgoal : c * (a * g.inner x v v * (a * g.inner x w w) - (a * g.inner x v w) ^ 2) ≤
        metricRm04StandardAt (I := I3) (M := M) (scaleMetric (I := I3) a ha g)
          x v w w v := by
      rw [metricRmStandard_scale (I := I3) a ha g x v w w v]
      nlinarith [hmul]
    exact hgoal

omit [SigmaCompactSpace M] in
theorem secLower_of_scaleInvariant_lower_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    {x : M} {t c C : ℝ} {U : Set M} (hQ : 0 < S.scalar t x) (hc : C⁻¹ ≤ c)
    (h : ∀ y ∈ U, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
      (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M)
        (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) y)) :
    SecLower (S.base.metric t) (C⁻¹ * S.scalar t x) U := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscaled : SecLower
      (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) c U :=
    (secLower_iff_le_leastCurvatureOperatorEigenvalueAt
      (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) hdim c U).mpr h
  have hunscaled : SecLower (S.base.metric t) (c * S.scalar t x) U :=
    (secLower_scaleMetric_iff hQ (S.base.metric t) U).mp hscaled
  exact hunscaled.mono (mul_le_mul_of_nonneg_right hc hQ.le)

omit [SigmaCompactSpace M] in
theorem canonicalAlternative_positive_of_scaleInvariant_lower_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    {eps C : ℝ} {x : M} {t : ℝ} {U : Set M}
    (hwhole : U = connectedComponent x) (data : PositiveComponent U)
    {c : ℝ} (hQ : 0 < S.scalar t x) (hc : C⁻¹ ≤ c)
    (h : ∀ y ∈ U, c ≤ leastCurvatureOperatorEigenvalueAt (I := I3)
      (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M)
        (scaleMetric (I := I3) (S.scalar t x) hQ (S.base.metric t)) y)) :
    Nonempty (CanonicalAlternative S eps C x t U) :=
  ⟨CanonicalAlternative.positive hwhole data
    (secLower_of_scaleInvariant_lower_bound S hQ hc h)⟩

omit [SigmaCompactSpace M] in
theorem secLower_of_ricci_lower_bound_of_scalar_upper
    (g : SmoothRiemannianMetric I3 M) (hdim : Module.finrank ℝ ThreeSpace = 3)
    {rho S₀ : ℝ} {U : Set M}
    (hric : ∀ y ∈ U, ∀ v : TangentSpace I3 y,
      rho * g.inner y v v ≤ ricciTensor (I := I3) g y v v)
    (hscal : ∀ y ∈ U, metricScalarAt (I := I3) (M := M) g y ≤ S₀) :
    SecLower g (2 * rho - S₀ / 2) U := by
  intro y hy v w
  have hR : metricScalarAt (I := I3) (M := M) g y ≤ S₀ := hscal y hy
  have hA : 0 ≤ g.inner y v v := inner_self_nonneg (I := I3) g y v
  have hB : 0 ≤ g.inner y w w := inner_self_nonneg (I := I3) g y w
  have hgram : 0 ≤ g.inner y v v * g.inner y w w - g.inner y v w ^ 2 := by
    have h := DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
      (I := I3) g y v w
    linarith
  have ha : 0 ≤ ricciTensor (I := I3) g y v v - rho * g.inner y v v := by
    linarith [hric y hy v]
  have hb : 0 ≤ ricciTensor (I := I3) g y w w - rho * g.inner y w w := by
    linarith [hric y hy w]
  have hquad : ∀ t : ℝ, 0 ≤ (ricciTensor (I := I3) g y v v - rho * g.inner y v v)
      + 2 * t * (ricciTensor (I := I3) g y v w - rho * g.inner y v w)
      + t ^ 2 * (ricciTensor (I := I3) g y w w - rho * g.inner y w w) := by
    intro t
    have h := hric y hy (v + t • w)
    have hexp : ricciTensor (I := I3) g y (v + t • w) (v + t • w)
        - rho * g.inner y (v + t • w) (v + t • w)
        = (ricciTensor (I := I3) g y v v - rho * g.inner y v v)
          + 2 * t * (ricciTensor (I := I3) g y v w - rho * g.inner y v w)
          + t ^ 2 * (ricciTensor (I := I3) g y w w - rho * g.inner y w w) := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, g.symm y w v,
        ricciTensor_symm (I := I3) g y w v]
      ring
    linarith [h, hexp]
  have hsCS : (ricciTensor (I := I3) g y v w - rho * g.inner y v w) ^ 2 ≤
      (ricciTensor (I := I3) g y v v - rho * g.inner y v v)
        * (ricciTensor (I := I3) g y w w - rho * g.inner y w w) := by
    by_cases hb0 : ricciTensor (I := I3) g y w w - rho * g.inner y w w = 0
    · have hs0 : ricciTensor (I := I3) g y v w - rho * g.inner y v w = 0 := by
        by_contra hs
        have h := hquad ((ricciTensor (I := I3) g y v v - rho * g.inner y v v + 1) /
          (-(2 * (ricciTensor (I := I3) g y v w - rho * g.inner y v w))))
        have hval : (ricciTensor (I := I3) g y v v - rho * g.inner y v v)
            + 2 * ((ricciTensor (I := I3) g y v v - rho * g.inner y v v + 1) /
              (-(2 * (ricciTensor (I := I3) g y v w - rho * g.inner y v w))))
              * (ricciTensor (I := I3) g y v w - rho * g.inner y v w)
            + ((ricciTensor (I := I3) g y v v - rho * g.inner y v v + 1) /
              (-(2 * (ricciTensor (I := I3) g y v w - rho * g.inner y v w)))) ^ 2
              * (ricciTensor (I := I3) g y w w - rho * g.inner y w w)
            = -1 := by
          rw [hb0]
          field_simp [hs]
          ring
        rw [hval] at h
        linarith [h]
      rw [hs0, hb0]
      norm_num
    · have hbpos : 0 < ricciTensor (I := I3) g y w w - rho * g.inner y w w :=
        lt_of_le_of_ne hb (Ne.symm hb0)
      have h := hquad (-((ricciTensor (I := I3) g y v w - rho * g.inner y v w) /
        (ricciTensor (I := I3) g y w w - rho * g.inner y w w)))
      have hval : (ricciTensor (I := I3) g y v v - rho * g.inner y v v)
          + 2 * (-((ricciTensor (I := I3) g y v w - rho * g.inner y v w) /
              (ricciTensor (I := I3) g y w w - rho * g.inner y w w)))
            * (ricciTensor (I := I3) g y v w - rho * g.inner y v w)
          + (-((ricciTensor (I := I3) g y v w - rho * g.inner y v w) /
              (ricciTensor (I := I3) g y w w - rho * g.inner y w w))) ^ 2
            * (ricciTensor (I := I3) g y w w - rho * g.inner y w w)
          = (ricciTensor (I := I3) g y v v - rho * g.inner y v v)
            - (ricciTensor (I := I3) g y v w - rho * g.inner y v w) ^ 2
              / (ricciTensor (I := I3) g y w w - rho * g.inner y w w) := by
        field_simp
        ring
      rw [hval] at h
      have hmul := mul_nonneg h hbpos.le
      have hval2 : (((ricciTensor (I := I3) g y v v - rho * g.inner y v v)
          - (ricciTensor (I := I3) g y v w - rho * g.inner y v w) ^ 2
            / (ricciTensor (I := I3) g y w w - rho * g.inner y w w))
          * (ricciTensor (I := I3) g y w w - rho * g.inner y w w))
          = (ricciTensor (I := I3) g y v v - rho * g.inner y v v)
            * (ricciTensor (I := I3) g y w w - rho * g.inner y w w)
            - (ricciTensor (I := I3) g y v w - rho * g.inner y v w) ^ 2 := by
        field_simp
      linarith [hmul, hval2]
  have hsC : (ricciTensor (I := I3) g y v w - rho * g.inner y v w) * g.inner y v w ≤
      Real.sqrt ((ricciTensor (I := I3) g y v v - rho * g.inner y v v)
        * (ricciTensor (I := I3) g y w w - rho * g.inner y w w)
        * (g.inner y v v * g.inner y w w)) := by
    have hsq : ((ricciTensor (I := I3) g y v w - rho * g.inner y v w) * g.inner y v w) ^ 2
        ≤ (ricciTensor (I := I3) g y v v - rho * g.inner y v v)
          * (ricciTensor (I := I3) g y w w - rho * g.inner y w w)
          * (g.inner y v v * g.inner y w w) := by
      have hc := DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
        (I := I3) g y v w
      nlinarith [hsCS, hc, ha, hb, hA, hB]
    calc (ricciTensor (I := I3) g y v w - rho * g.inner y v w) * g.inner y v w
        ≤ |(ricciTensor (I := I3) g y v w - rho * g.inner y v w) * g.inner y v w| :=
          le_abs_self _
      _ = Real.sqrt (((ricciTensor (I := I3) g y v w - rho * g.inner y v w)
            * g.inner y v w) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((ricciTensor (I := I3) g y v v - rho * g.inner y v v)
          * (ricciTensor (I := I3) g y w w - rho * g.inner y w w)
          * (g.inner y v v * g.inner y w w)) := Real.sqrt_le_sqrt hsq
  have hspart : 0 ≤ (ricciTensor (I := I3) g y v v - rho * g.inner y v v) * g.inner y w w
      + (ricciTensor (I := I3) g y w w - rho * g.inner y w w) * g.inner y v v
      - 2 * (ricciTensor (I := I3) g y v w - rho * g.inner y v w) * g.inner y v w := by
    have hX : 0 ≤ (ricciTensor (I := I3) g y v v - rho * g.inner y v v) * g.inner y w w :=
      mul_nonneg ha hB
    have hY : 0 ≤ (ricciTensor (I := I3) g y w w - rho * g.inner y w w) * g.inner y v v :=
      mul_nonneg hb hA
    have hid : (Real.sqrt ((ricciTensor (I := I3) g y v v - rho * g.inner y v v)
          * g.inner y w w) - Real.sqrt ((ricciTensor (I := I3) g y w w - rho * g.inner y w w)
            * g.inner y v v)) ^ 2
        = (ricciTensor (I := I3) g y v v - rho * g.inner y v v) * g.inner y w w
          + (ricciTensor (I := I3) g y w w - rho * g.inner y w w) * g.inner y v v
          - 2 * Real.sqrt (((ricciTensor (I := I3) g y v v - rho * g.inner y v v) * g.inner y w w)
              * ((ricciTensor (I := I3) g y w w - rho * g.inner y w w) * g.inner y v v)) := by
      have hsqrt :
          Real.sqrt (((ricciTensor (I := I3) g y v v - rho * g.inner y v v) * g.inner y w w)
              * ((ricciTensor (I := I3) g y w w - rho * g.inner y w w) * g.inner y v v))
            = Real.sqrt ((ricciTensor (I := I3) g y v v - rho * g.inner y v v) * g.inner y w w)
              * Real.sqrt ((ricciTensor (I := I3) g y w w - rho * g.inner y w w)
                  * g.inner y v v) :=
        Real.sqrt_mul hX _
      rw [sub_sq, Real.sq_sqrt hX, Real.sq_sqrt hY, hsqrt]
      ring
    have hsquare : 0 ≤ (Real.sqrt ((ricciTensor (I := I3) g y v v - rho * g.inner y v v)
          * g.inner y w w) - Real.sqrt ((ricciTensor (I := I3) g y w w - rho * g.inner y w w)
            * g.inner y v v)) ^ 2 := sq_nonneg _
    rw [hid] at hsquare
    have hkey : Real.sqrt (((ricciTensor (I := I3) g y v v - rho * g.inner y v v)
          * g.inner y w w) * ((ricciTensor (I := I3) g y w w - rho * g.inner y w w)
            * g.inner y v v))
        = Real.sqrt ((ricciTensor (I := I3) g y v v - rho * g.inner y v v)
          * (ricciTensor (I := I3) g y w w - rho * g.inner y w w)
          * (g.inner y v v * g.inner y w w)) := by
      congr 1
      ring
    rw [hkey] at hsquare
    nlinarith [hsquare, hsC]
  have hRm := metricRm04StdAt_eq_ricci3 (I := I3) (M := M) g y hdim v w w v
  have hRic (a b : TangentSpace I3 y) : metricRicciAt (I := I3) (M := M) g y (vec2 a b)
      = ricciTensor (I := I3) g y a b := metricRicciAt_apply_eq_ricciTensor (I := I3) g y a b
  simp only [hRic] at hRm
  rw [g.symm y w v, ricciTensor_symm (I := I3) g y w v] at hRm
  change (2 * rho - S₀ / 2) * (g.inner y v v * g.inner y w w - g.inner y v w ^ 2) ≤
    metricRm04StandardAt (I := I3) (M := M) g y v w w v
  rw [hRm]
  nlinarith [hspart, hgram, mul_nonneg (sub_nonneg.mpr hR) hgram]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
