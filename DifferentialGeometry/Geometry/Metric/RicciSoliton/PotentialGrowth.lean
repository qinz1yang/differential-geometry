import DifferentialGeometry.Geometry.Metric.LipschitzGradient
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Operator.LaplacianMinimum

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open Riemannian
open Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedGradientRicciSoliton_potential_le_sq_distance
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (p x : M) :
    f x ≤ 1 / 4 * ((riemannianEDistOf (I := I) g p x).toReal +
      2 * Real.sqrt (f p)) ^ 2 := by
  classical
  let : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let d : Real := (riemannianEDistOf (I := I) g p x).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hf_nonneg (y : M) : 0 ≤ f y :=
    normalizedGradientRicciSoliton_potential_nonneg (I := I) h y
  have hε (ε : Real) (hεpos : 0 < ε) :
      f x ≤ 1 / 4 * (d + 2 * Real.sqrt (f p + ε)) ^ 2 - ε := by
    let q : M → Real := fun y => f y + ε
    let u : M → Real := fun y => 2 * Real.sqrt (q y)
    have hq_pos (y : M) : 0 < q y := by
      dsimp only [q]
      linarith [hf_nonneg y]
    have hq_smooth : ContMDiff I (modelWithCornersSelf Real Real)
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) q := by
      dsimp only [q]
      exact f.contMDiff.add contMDiff_const
    have hu_smooth : ContMDiff I (modelWithCornersSelf Real Real)
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) u := by
      intro y
      exact contMDiffAt_const.mul
        ((Real.contDiffAt_sqrt (hq_pos y).ne').contMDiffAt.comp y
          (hq_smooth y))
    have hgrad_q (y : M) :
        gradFun (I := I) g q y = gradFun (I := I) g f y := by
      have hf_diff := (f.contMDiff y).mdifferentiableAt (by simp)
      change gradFun (I := I) g
        ((f : M → Real) + (fun _ : M => ε)) y = _
      rw [Operator.gradFun_add (I := I) g hf_diff mdifferentiableAt_const,
        Operator.gradFun_const]
      simp
    have hgrad_u (y : M) :
        gradFun (I := I) g u y =
          (Real.sqrt (q y))⁻¹ • gradFun (I := I) g f y := by
      have hq_diff := (hq_smooth y).mdifferentiableAt (by simp)
      have hsqrt_diff : DifferentiableAt Real Real.sqrt (q y) :=
        (Real.hasDerivAt_sqrt (hq_pos y).ne').differentiableAt
      have hcomp := Operator.gradFun_comp (I := I) g hsqrt_diff hq_diff
      have hsqrt_mdiff : MDifferentiableAt I (modelWithCornersSelf Real Real)
          (fun z : M => Real.sqrt (q z)) y :=
        ((Real.contDiffAt_sqrt (hq_pos y).ne').contMDiffAt.comp y
          (hq_smooth y)).mdifferentiableAt (by simp)
      have hscale := Operator.gradFun_const_smul (I := I) g 2
        hsqrt_mdiff
      have hu_eq : u = (2 : Real) • (fun z : M => Real.sqrt (q z)) := by
        funext z
        simp only [u, Pi.smul_apply, smul_eq_mul]
      calc
        gradFun (I := I) g u y =
            gradFun (I := I) g
              ((2 : Real) • (fun z : M => Real.sqrt (q z))) y :=
          congrArg (fun v : M → Real => gradFun (I := I) g v y) hu_eq
        _ = (2 : Real) • gradFun (I := I) g
            (fun z : M => Real.sqrt (q z)) y :=
          hscale
        _ = (Real.sqrt (q y))⁻¹ • gradFun (I := I) g f y := by
          rw [hcomp, hgrad_q,
            (Real.hasDerivAt_sqrt (hq_pos y).ne').deriv]
          rw [smul_smul]
          congr 1
          field_simp [(Real.sqrt_pos.2 (hq_pos y)).ne']
    have hgrad_u_bound (y : M) :
        Real.sqrt (g.inner y (gradFun (I := I) g u y)
          (gradFun (I := I) g u y)) ≤ 1 := by
      have hR := normalizedGradientRicciSoliton_scalar_nonneg (I := I) h y
      have hpot := normalizedGradientRicciSoliton_potential_equation
        (I := I) h y
      have hinner : g.inner y (gradFun (I := I) g f y)
          (gradFun (I := I) g f y) ≤ q y := by
        dsimp only [q]
        linarith
      have hsqrt := Real.sqrt_le_sqrt hinner
      rw [hgrad_u, sqrt_inner_smul, abs_inv,
        abs_of_pos (Real.sqrt_pos.2 (hq_pos y))]
      calc
        (Real.sqrt (q y))⁻¹ * Real.sqrt
            (g.inner y (gradFun (I := I) g f y)
              (gradFun (I := I) g f y)) ≤
            (Real.sqrt (q y))⁻¹ * Real.sqrt (q y) := by
          exact mul_le_mul_of_nonneg_left hsqrt
            (inv_nonneg.mpr (Real.sqrt_nonneg _))
        _ = 1 := inv_mul_cancel₀ (Real.sqrt_pos.2 (hq_pos y)).ne'
    let K : NNReal := 1
    have hu_lip : ∀ y z : M, edist (u y) (u z) ≤
        (K : ENNReal) * riemannianEDistOf (I := I) g y z := by
      apply lip_of_grad_norm_le (I := I) g h.1 hu_smooth
      intro y
      simpa only [K, NNReal.coe_one] using hgrad_u_bound y
    have hfin : riemannianEDistOf (I := I) g p x ≠ (∞ : ENNReal) :=
      riemannianEDist_ne_top (I := I) p x
    have hu_real : |u p - u x| ≤ d := by
      have hrhs :
          (K : ENNReal) * riemannianEDistOf (I := I) g p x ≠
            (∞ : ENNReal) :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
      have hreal := ENNReal.toReal_mono hrhs (hu_lip p x)
      rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
        ENNReal.toReal_mul, ENNReal.coe_toReal, Real.dist_eq] at hreal
      simpa only [K, NNReal.coe_one, one_mul, d] using hreal
    have hu_nonneg (y : M) : 0 ≤ u y := by
      dsimp only [u]
      positivity
    have hu_growth : u x ≤ u p + d := by
      have habs : u x - u p ≤ |u p - u x| := by
        rw [abs_sub_comm]
        exact le_abs_self (u x - u p)
      linarith
    have hsq : u x ^ 2 ≤ (u p + d) ^ 2 := by
      exact (sq_le_sq₀ (hu_nonneg x)
        (add_nonneg (hu_nonneg p) hd)).2 hu_growth
    have hux_sq : u x ^ 2 = 4 * (f x + ε) := by
      dsimp only [u, q]
      rw [mul_pow, Real.sq_sqrt]
      · ring
      · linarith [hf_nonneg x]
    dsimp only [u, q] at hsq
    rw [hux_sq] at hsq
    nlinarith
  have hseq : Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have htend : Tendsto
      (fun n : Nat =>
        1 / 4 * (d + 2 * Real.sqrt
          (f p + (1 : Real) / ((n : Real) + 1))) ^ 2 -
            (1 : Real) / ((n : Real) + 1))
      atTop (𝓝 (1 / 4 * (d + 2 * Real.sqrt (f p)) ^ 2)) := by
    have hcont : ContinuousAt
      (fun ε : Real => 1 / 4 * (d + 2 * Real.sqrt (f p + ε)) ^ 2 - ε)
        0 := by
      fun_prop
    have htend' : Tendsto
        (fun n : Nat =>
          1 / 4 * (d + 2 * Real.sqrt
            (f p + (1 : Real) / ((n : Real) + 1))) ^ 2 -
              (1 : Real) / ((n : Real) + 1))
        atTop
        (𝓝 ((fun ε : Real =>
          1 / 4 * (d + 2 * Real.sqrt (f p + ε)) ^ 2 - ε) 0)) := by
      apply Filter.Tendsto.congr'
        (Filter.Eventually.of_forall fun n => rfl)
      exact hcont.tendsto.comp hseq
    simpa only [add_zero, sub_zero] using htend'
  have hlim : f x ≤ 1 / 4 * (d + 2 * Real.sqrt (f p)) ^ 2 := by
    apply ge_of_tendsto htend
    exact Filter.Eventually.of_forall fun n => hε _ (by positivity)
  simpa only [d] using hlim

omit [NeZero (Module.finrank Real E)] [ConnectedSpace M] in
theorem normalizedGradientRicciSoliton_potential_eq_scalar_of_isLocalMin
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) {o : M}
    (ho : IsLocalMin (f : M → Real) o) :
    f o = metricScalarAt (I := I) g o := by
  have hgrad : gradFun (I := I) g f o = 0 :=
    gradientFun_eq_zero_at_spatial_min (I := I) g ho
      ((f.contMDiff o).mdifferentiableAt (by simp))
  have hpot := normalizedGradientRicciSoliton_potential_equation (I := I) h o
  rw [hgrad] at hpot
  simpa only [map_zero, add_zero] using hpot.symm

omit [NeZero (Module.finrank Real E)] [ConnectedSpace M] in
theorem normalizedGradientRicciSoliton_potential_le_finrank_div_two_of_isLocalMin
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) {o : M}
    (ho : IsLocalMin (f : M → Real) o) :
    f o ≤ (Module.finrank Real E : Real) / 2 := by
  have hf_mdiff : MDifferentiableAt I 𝓘(Real, Real) (f : M → Real) o :=
    (f.contMDiff o).mdifferentiableAt (by simp)
  have hf_eventually : ∀ᶠ y in 𝓝 o,
      MDifferentiableAt I 𝓘(Real, Real) (f : M → Real) y :=
    Filter.Eventually.of_forall fun y =>
      (f.contMDiff y).mdifferentiableAt (by simp)
  have hgrad : MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) g f y) o :=
    (gradientFun_contMDiffAt (I := I) g (f.contMDiff o)).mdifferentiableAt
      (by simp)
  have hmetric : IsMetricCompatibleGen (I := I)
      (LeviCivita (I := I) g) g := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  have hlap : 0 ≤ ΔG (I := I) g f o := by
    have hlap' : 0 ≤ laplacian (I := I) (LeviCivita (I := I) g) g f o :=
      laplacian_nonneg_at_spatial_min_of_metricCompatible
        (I := I) (LeviCivita (I := I) g) g hmetric
          ho hf_mdiff hf_eventually hgrad
    rw [laplacian_levi_eq (I := I) g f.contMDiff o] at hlap'
    exact hlap'
  have htrace := gradientRicciSoliton_trace (I := I) h.2.1 o
  have hfo :=
    normalizedGradientRicciSoliton_potential_eq_scalar_of_isLocalMin
      (I := I) h ho
  rw [hfo]
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedGradientRicciSoliton_potential_le_sq_distance_of_isMinOn
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) {o : M}
    (ho : IsMinOn (f : M → Real) Set.univ o) (x : M) :
    f x ≤ 1 / 4 * ((riemannianEDistOf (I := I) g o x).toReal +
      Real.sqrt (2 * (Module.finrank Real E : Real))) ^ 2 := by
  have hlocal : IsLocalMin (f : M → Real) o := ho.isLocalMin univ_mem
  have hfo :=
    normalizedGradientRicciSoliton_potential_le_finrank_div_two_of_isLocalMin
      (I := I) h hlocal
  have hfo_nonneg := normalizedGradientRicciSoliton_potential_nonneg
    (I := I) h o
  have hn : 0 ≤ (Module.finrank Real E : Real) := by positivity
  have hsqrt : 2 * Real.sqrt (f o) ≤
      Real.sqrt (2 * (Module.finrank Real E : Real)) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hfo_nonneg, Real.sq_sqrt (by positivity)]
    nlinarith
  have hbase := normalizedGradientRicciSoliton_potential_le_sq_distance
    (I := I) h o x
  have hd : 0 ≤ (riemannianEDistOf (I := I) g o x).toReal :=
    ENNReal.toReal_nonneg
  have hsq :
      ((riemannianEDistOf (I := I) g o x).toReal +
          2 * Real.sqrt (f o)) ^ 2 ≤
        ((riemannianEDistOf (I := I) g o x).toReal +
          Real.sqrt (2 * (Module.finrank Real E : Real))) ^ 2 := by
    apply (sq_le_sq₀ (add_nonneg hd (by positivity))
      (add_nonneg hd (Real.sqrt_nonneg _))).2
    linarith
  exact hbase.trans (mul_le_mul_of_nonneg_left hsq (by norm_num))

end DifferentialGeometry.Geometry
