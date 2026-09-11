import DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.SpeedDerivative
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.LengthVariation
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
theorem abs_deriv_arcLength_le_of_abs_ricciTensor_le
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b t A : Real}
    (hab : a ≤ b)
    (ht : t ∈ D.regular)
    (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hvel : ∀ u ∈ Set.Icc a b,
      mfderiv 𝓘(Real, Real) I gamma u (1 : Real) ≠ 0)
    (hRic : ∀ u ∈ Set.Icc a b,
      |ricciTensor (I := I) (S.base.metric t) (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))| ≤
        A * (S.base.metric t).inner (gamma u)
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))) :
    |deriv
        (fun s ↦ Variation.arcLength
          (I := I) (S.base.metric s) gamma a b) t| ≤
      A * Variation.arcLength
        (I := I) (S.base.metric t) gamma a b := by
  let v : (u : Real) → TangentSpace I (gamma u) :=
    fun u ↦ mfderiv 𝓘(Real, Real) I gamma u (1 : Real)
  let G : Real → Real :=
    fun u ↦ (S.base.metric t).inner (gamma u) (v u) (v u)
  let Ric : Real → Real :=
    fun u ↦ ricciTensor (I := I) (S.base.metric t) (gamma u) (v u) (v u)
  let Q : Real → Real := fun u ↦ -Ric u / Real.sqrt (G u)
  have hspeedInt : IntervalIntegrable (fun u ↦ Real.sqrt (G u))
      MeasureTheory.volume a b := by
    apply MeasureTheory.IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact Geodesic.speedSqrt_integrableOn_Icc_of_C1 (S.base.metric t) hab hgamma.contMDiffOn
  have hpoint : ∀ u ∈ Set.Icc a b, ‖Q u‖ ≤ A * Real.sqrt (G u) := by
    intro u hu
    have hGpos : 0 < G u :=
      (S.base.metric t).pos (gamma u) (v u) (hvel u hu)
    dsimp only [Q]
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _),
      div_le_iff₀ (Real.sqrt_pos.2 hGpos), mul_assoc, Real.mul_self_sqrt hGpos.le]
    exact hRic u hu
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hab
    (MeasureTheory.ae_of_all _ fun u hu ↦ hpoint u ⟨hu.1.le, hu.2⟩)
    (hspeedInt.const_mul A)
  have hderiv := pathLength_timeDeriv_of_ricciFlow S hS hab ht gamma hgamma hvel
  rw [hderiv.deriv, Variation.arcLength, ← intervalIntegral.integral_const_mul]
  simpa only [Real.norm_eq_abs, Q, Ric, G, v] using hbound


end

omit [IsManifold I 2 M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem intrinsicGeo_velocity_ne
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p)
    (hv : 0 < g.inner p v v) (u : Real) :
    mfderiv 𝓘(Real, Real) I
        (intrinsicGeodesic (I := I) g hEnorm p v) u (1 : Real) ≠ 0 := by
  intro hzero
  have hspeed :=
    intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v u
  have hinner0 :
      g.inner (intrinsicGeodesic (I := I) g hEnorm p v u)
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm p v) u (1 : Real))
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm p v) u (1 : Real)) = 0 := by
    have h := congrArg
      (fun w : TangentSpace I
          (intrinsicGeodesic (I := I) g hEnorm p v u) =>
        g.inner (intrinsicGeodesic (I := I) g hEnorm p v u) w w)
      hzero
    simpa only [map_zero] using h
  exact hv.ne' (hspeed.symm.trans hinner0)

private structure ScaledDistanceSupport
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (O : M) (T t : Real) (x : M) (d Λ r : Real) where
  rho : Real → M → Real
  eq_at : rho t x = Real.exp (Λ * t) * r
  upper_nhds :
    ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
      Real.exp (Λ * p.1) *
          (riemannianEDistOf (I := I)
            (S.base.metric p.1) O p.2).toReal ≤
        rho p.1 p.2
  time_diff :
    DifferentiableWithinAt Real
      (fun s => rho s x) (Set.Icc 0 T) t
  space_diff_nhds :
    ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) (rho t) y
  grad_diff :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (S.base.metric t) (rho t) y) x
  grad_sq :
    (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) (rho t) x)
        (gradientFun (I := I) (S.base.metric t) (rho t) x) ≤
      Real.exp (2 * Λ * t)
  par_lower :
    -Real.exp (Λ * t) *
        (2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ)) ≤
      parabolicOperatorWithDrift
        (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y)) rho t x

omit [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] in
private theorem exists_calabi_coeff
    (g : SmoothRiemannianMetric I M)
    {Λ : Real}
    (hΛ : 0 ≤ Λ)
    (hricQuad : ∀ y : M, ∀ v : TangentSpace I y,
      |ricciTensor (I := I) g y v v| ≤
        Λ * g.inner y v v) :
    let dNat : Nat := Module.finrank Real E
    let d : Real := (dNat : Real)
    let nNat : Nat := dNat - 1
    let n : Real := (nNat : Real)
    ∃ q : Real,
      0 ≤ q ∧
      Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) g (-(n * q ^ 2)) ∧
      n * q = Real.sqrt ((d - 1) * Λ) := by
  dsimp only
  let dNat : Nat := Module.finrank Real E
  let d : Real := (dNat : Real)
  let nNat : Nat := dNat - 1
  let n : Real := (nNat : Real)
  have hdNat_pos : 0 < dNat := by
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  have hdNat_one : 1 ≤ dNat := hdNat_pos
  have hdn : d - 1 = n := by
    dsimp only [d, n, nNat]
    rw [Nat.cast_sub hdNat_one]
    norm_num
  let q : Real :=
    if nNat = 0 then 0 else Real.sqrt (Λ / n)
  have hq : 0 ≤ q := by
    dsimp only [q]
    split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  have hRicLower :
      Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) g (-(n * q ^ 2)) := by
    by_cases hn0 : nNat = 0
    · have hd1 : dNat = 1 := by omega
      simpa only [q, hn0, if_pos, zero_pow, zero_mul, mul_zero, neg_zero,
        n, nNat, hd1, Nat.cast_zero] using
        (Geometry.Riemannian.BonnetMyers.ricciLower_dim1
          (I := I) g hd1)
    · have hnNat_pos : 0 < nNat := Nat.pos_of_ne_zero hn0
      have hn : 0 < n := by
        dsimp only [n]
        exact_mod_cast hnNat_pos
      have hq_sq : q ^ 2 = Λ / n := by
        dsimp only [q]
        rw [if_neg hn0, Real.sq_sqrt (div_nonneg hΛ hn.le)]
      intro y v
      have habs := hricQuad y v
      have hneg :
          -(Λ * g.inner y v v) ≤
            ricciTensor (I := I) g y v v :=
        neg_le_of_abs_le habs
      rw [hq_sq]
      have hcoeff : n * (Λ / n) = Λ := by
        field_simp
      rw [hcoeff]
      simpa only [neg_mul] using hneg
  have hnq :
      n * q = Real.sqrt ((d - 1) * Λ) := by
    by_cases hn0 : nNat = 0
    · simp only [q, hn0, if_pos, n, Nat.cast_zero, zero_mul, mul_zero,
        hdn, Real.sqrt_zero]
    · rw [hdn]
      have hnNat_pos : 0 < nNat := Nat.pos_of_ne_zero hn0
      have hn : 0 < n := by
        dsimp only [n]
        exact_mod_cast hnNat_pos
      have hq_def : q = Real.sqrt (Λ / n) := by
        simp only [q, hn0, if_false]
      have hq_nonneg : 0 ≤ q := hq
      have hq_sq : q ^ 2 = Λ / n := by
        rw [hq_def, Real.sq_sqrt (div_nonneg hΛ hn.le)]
      have hright_sq :
          (Real.sqrt (n * Λ)) ^ 2 = n * Λ :=
        Real.sq_sqrt (mul_nonneg hn.le hΛ)
      have hleft_nonneg : 0 ≤ n * q := mul_nonneg hn.le hq_nonneg
      have hright_nonneg :
          0 ≤ Real.sqrt (n * Λ) := Real.sqrt_nonneg _
      have hscale : n * q ^ 2 = Λ := by
        rw [hq_sq]
        field_simp
      have hleft_sq : (n * q) ^ 2 = n * Λ := by
        nlinarith
      nlinarith
  exact ⟨q, hq, hRicLower, hnq⟩

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem ricci_quad_of_curv
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {T K : Real}
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K) :
    let d : Real := Module.finrank Real E
    let Λ : Real := d ^ 2 * Real.sqrt K
    0 ≤ Λ ∧
    (∀ s ∈ Set.Icc 0 T, ∀ y : M,
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          Λ * (S.base.metric s).inner y v v) := by
  dsimp only
  let dNat : Nat := Module.finrank Real E
  let d : Real := (dNat : Real)
  let Λ : Real := d ^ 2 * Real.sqrt K
  have hsqrtK : 0 ≤ Real.sqrt K := by
    rcases hK.eq_or_lt with hK0 | hKpos
    · rw [← hK0]
      norm_num
    · exact (Real.sqrt_pos.2 hKpos).le
  have hΛ : 0 ≤ Λ := by
    dsimp only [Λ, d]
    exact mul_nonneg (sq_nonneg _) hsqrtK
  have hcurv0 : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric s) y 4
        (S.base.rm04 s y) ≤ K := by
    intro s hs y
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      Nat.add_zero] using hcurv s hs y
  have hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          Λ * (S.base.metric s).inner y v v := by
    intro s hs y v
    simpa only [Λ, d, dNat] using
      (ricci_quadratic_form_bound_of_solution_curvature_bound
        (I := I) S y v (hcurv0 s hs y))
  exact ⟨hΛ, hricQuad⟩

private structure CalabiFlowCore
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (O : M) (T t : Real) (x : M) (Λ r n q : Real) where
  rho0 : M → Real
  support : Real → M → Real
  support_t : support t = rho0
  rho0_x : rho0 x = r
  upper_nhds :
    ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
      (riemannianEDistOf (I := I)
        (S.base.metric p.1) O p.2).toReal ≤
        support p.1 p.2
  time_diff :
    DifferentiableAt Real (fun s => support s x) t
  time_lower :
    -Λ * support t x ≤ deriv (fun s => support s x) t
  space_diff_nhds :
    ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) rho0 y
  grad_diff :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (S.base.metric t) rho0 y) x
  grad_sq :
    (S.base.metric t).inner x
        (gradientFun (I := I) (S.base.metric t) rho0 x)
        (gradientFun (I := I) (S.base.metric t) rho0 x) = 1
  lap_upper :
    laplacian
        (I := I) (LeviCivita (I := I) (S.base.metric t))
        (S.base.metric t) rho0 x ≤
      2 * n / r + n * q

omit [IsManifold I 2 M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem calabi_core_of_solution
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E
      (fun y : M => TangentSpace I y)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T Λ t r n q : Real}
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          Λ * (S.base.metric s).inner y v v)
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite : Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal))
    (hOx : O ≠ x)
    (hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t))
    (hq : 0 ≤ q)
    (hRicLower :
      Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) (S.base.metric t) (-(n * q ^ 2)))
    (hr : r = (Manifold.riemannianEDist I O x).toReal)
    (hn :
      n = ((Module.finrank Real E - 1 : Nat) : Real)) :
    Nonempty (CalabiFlowCore (I := I) S O T t x Λ r n q) := by
  classical
  have hRicLower' :
      Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) (S.base.metric t)
          (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)) := by
    simpa only [← hn] using hRicLower
  obtain ⟨tail, _, hrho0_x, _, hrho0_ev,
      hgrad0, hgrad0_norm, hlap0⟩ :=
    exists_calabiData
      (I := I) (S.base.metric t) hEnorm q hq hRicLower' hOx hfinite
  let rho0 : M → Real := fun y =>
    tail.initialLength +
      branchRadius (I := I) (S.base.metric t) tail.branch y
  have hleft_fin :
      Manifold.riemannianEDist I O tail.splitPoint ≠ (⊤ : ENNReal) := by
    rw [tail.initial_edist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨vLeft, hvLeft_exp, hvLeft_norm⟩ :=
    minExp_of_ne_top
      (I := I) (S.base.metric t) hEnorm O tail.splitPoint hleft_fin
  have hvLeft_norm' :
      Real.sqrt ((S.base.metric t).inner O vLeft vLeft) =
        tail.initialLength := by
    rw [hvLeft_norm, tail.initial_edist,
      ENNReal.toReal_ofReal tail.initialLength_nonneg]
  have hvLeft_pos :
      0 < (S.base.metric t).inner O vLeft vLeft := by
    apply Real.sqrt_pos.mp
    rw [hvLeft_norm']
    exact tail.initialLength_pos
  let γ : Real → M :=
    intrinsicGeodesic (I := I) (S.base.metric t) hEnorm O vLeft
  let δ : M → Real → M := fun y =>
    intrinsicGeodesic (I := I) (S.base.metric t) hEnorm tail.splitPoint
      ((tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm
        (tail.branch.inv y))
  let L₁ : Real → Real := fun s =>
    Geometry.Riemannian.Variation.arcLength
      (I := I) (S.base.metric s) γ 0 1
  let L₂ : Real → M → Real := fun s y =>
    Geometry.Riemannian.Variation.arcLength
      (I := I) (S.base.metric s) (δ y) 0 1
  let vSupport : Real → M → Real := fun s y => L₁ s + L₂ s y
  have hγ_smooth : ContMDiff 𝓘(Real, Real) I 1 γ := by
    exact contMDiffOn_univ.mp
      (intrinsicGeodesic_contMDiffOn
        (I := I) (S.base.metric t) hEnorm O vLeft)
  have hδ_smooth : ∀ y : M, ContMDiff 𝓘(Real, Real) I 1 (δ y) := by
    intro y
    exact contMDiffOn_univ.mp
      (intrinsicGeodesic_contMDiffOn
        (I := I) (S.base.metric t) hEnorm tail.splitPoint
          ((tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm
            (tail.branch.inv y)))
  have hγ_zero : γ 0 = O := by
    exact intrinsicGeodesic_zero
      (I := I) (S.base.metric t) hEnorm O vLeft
  have hγ_one : γ 1 = tail.splitPoint := by
    simpa only [γ, expMapIntrinsic_def] using hvLeft_exp
  have hδ_zero : ∀ y : M, δ y 0 = tail.splitPoint := by
    intro y
    exact intrinsicGeodesic_zero
      (I := I) (S.base.metric t) hEnorm tail.splitPoint
        ((tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm
          (tail.branch.inv y))
  have hδ_one : ∀ y ∈ tail.branch.dom, δ y 1 = y := by
    intro y hy
    simpa only [δ, expMapIntrinsic_def] using
      tail.branch.right_inv hy
  have hL₁_t : L₁ t = tail.initialLength := by
    rw [show L₁ t =
        Geometry.Riemannian.Variation.arcLength
          (I := I) (S.base.metric t)
          (intrinsicGeodesic
            (I := I) (S.base.metric t) hEnorm O vLeft) 0 1 by
      rfl]
    rw [arcLength_radial, sub_zero, one_mul, hvLeft_norm']
  have hL₂_t : ∀ y : M,
      L₂ t y =
        branchRadius (I := I) (S.base.metric t) tail.branch y := by
    intro y
    rw [show L₂ t y =
        Geometry.Riemannian.Variation.arcLength
          (I := I) (S.base.metric t)
          (intrinsicGeodesic
            (I := I) (S.base.metric t) hEnorm tail.splitPoint
              ((tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm
                (tail.branch.inv y))) 0 1 by
      rfl]
    rw [arcLength_radial, sub_zero, one_mul]
    rfl
  have hvSupport_t : ∀ y : M, vSupport t y = rho0 y := by
    intro y
    rw [show vSupport t y = L₁ t + L₂ t y by rfl,
      hL₁_t, hL₂_t]
  have htarget_ev :
      ∀ᶠ p : Real × M in 𝓝 (t, x), p.2 ∈ tail.branch.dom := by
    exact continuousAt_snd.preimage_mem_nhds
      (tail.branch.hom.open_target.mem_nhds tail.target_mem)
  have hupper :
      ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
        (riemannianEDistOf
          (I := I) (S.base.metric p.1) O p.2).toReal ≤
          vSupport p.1 p.2 := by
    filter_upwards [htarget_ev.filter_mono inf_le_left] with p hp
    have hdist :
        riemannianEDistOf (I := I) (S.base.metric p.1) O p.2 ≤
          ENNReal.ofReal (L₁ p.1) + ENNReal.ofReal (L₂ p.1 p.2) := by
      calc
        riemannianEDistOf (I := I) (S.base.metric p.1) O p.2 =
            riemannianEDistOf (I := I) (S.base.metric p.1)
              (γ 0) (δ p.2 1) := by rw [hγ_zero, hδ_one p.2 hp]
        _ ≤ ENNReal.ofReal (L₁ p.1) +
              ENNReal.ofReal (L₂ p.1 p.2) := by
          exact edistOf_le_two_arcs
            (I := I) (S.base.metric p.1)
              (a := 0) (b := 1) (c := 0) (d := 1)
              zero_le_one zero_le_one
              (hγ_smooth.contMDiffOn)
              ((hδ_smooth p.2).contMDiffOn)
              (hγ_one.trans (hδ_zero p.2).symm)
    have hL₁_nonneg : 0 ≤ L₁ p.1 := by
      dsimp only [L₁]
      unfold Geometry.Riemannian.Variation.arcLength
      exact intervalIntegral.integral_nonneg zero_le_one
        (fun u _ => Real.sqrt_nonneg _)
    have hL₂_nonneg : 0 ≤ L₂ p.1 p.2 := by
      dsimp only [L₂]
      unfold Geometry.Riemannian.Variation.arcLength
      exact intervalIntegral.integral_nonneg zero_le_one
        (fun u _ => Real.sqrt_nonneg _)
    have hreal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hdist
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hL₁_nonneg,
      ENNReal.toReal_ofReal hL₂_nonneg] at hreal
    exact hreal
  have htreg : t ∈ D.regular :=
    hreg ⟨htpos, ht.2⟩
  have hγ_velocity : ∀ u ∈ Set.Icc (0 : Real) 1,
      mfderiv 𝓘(Real, Real) I γ u (1 : Real) ≠ 0 := by
    intro u _hu
    simpa only [γ] using
      intrinsicGeo_velocity_ne
        (I := I) (S.base.metric t) hEnorm O vLeft hvLeft_pos u
  have hinv_x : tail.branch.inv x = (tail.endpointVector : E) := by
    have hleft := tail.branch.left_inv tail.source_mem
    have hexp :
        expMapIntrinsic (I := I) (S.base.metric t) hEnorm tail.splitPoint
          ((tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm
            (tail.endpointVector : E)) = x := by
      convert! tail.exp_eq using 1
    rw [hexp] at hleft
    exact hleft
  have hu_pos :
      0 < (S.base.metric t).inner tail.splitPoint tail.endpointVector tail.endpointVector := by
    apply Real.sqrt_pos.mp
    rw [tail.endpointVector_norm]
    exact tail.terminalLength_pos
  have hinv_pos :
      0 < (S.base.metric t).inner tail.splitPoint
        ((tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm
          (tail.branch.inv x))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm
          (tail.branch.inv x)) := by
    rw [hinv_x]
    have hu_round :
        (tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm
          (tail.endpointVector : E) = tail.endpointVector := by
      with_unfolding_all
        exact (tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm_apply_apply
          tail.endpointVector
    rw [hu_round]
    exact hu_pos
  have hδx_velocity : ∀ u ∈ Set.Icc (0 : Real) 1,
      mfderiv 𝓘(Real, Real) I (δ x) u (1 : Real) ≠ 0 := by
    intro u _hu
    simpa only [δ] using
      intrinsicGeo_velocity_ne
        (I := I) (S.base.metric t) hEnorm tail.splitPoint
          ((tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm
            (tail.branch.inv x))
          hinv_pos u
  have hL₁_deriv :=
    pathLength_timeDeriv_of_ricciFlow
      (I := I) S hS zero_le_one htreg γ hγ_smooth hγ_velocity
  have hL₂_deriv :=
    pathLength_timeDeriv_of_ricciFlow
      (I := I) S hS zero_le_one htreg (δ x) (hδ_smooth x) hδx_velocity
  have hL₁_diff : DifferentiableAt Real L₁ t := by
    simpa only [L₁] using hL₁_deriv.differentiableAt
  have hL₂_diff : DifferentiableAt Real (fun s => L₂ s x) t := by
    simpa only [L₂] using hL₂_deriv.differentiableAt
  have hL₁_lower :
      -Λ * L₁ t ≤ deriv L₁ t := by
    simpa only [L₁] using
      pathLength_deriv_ge
        (I := I) S hS (A := Λ) zero_le_one htreg γ hγ_smooth hγ_velocity
          (fun u _hu => hricQuad t ht (γ u)
            (mfderiv 𝓘(Real, Real) I γ u (1 : Real)))
  have hL₂_lower :
      -Λ * L₂ t x ≤ deriv (fun s => L₂ s x) t := by
    simpa only [L₂] using
      pathLength_deriv_ge
        (I := I) S hS (A := Λ) zero_le_one htreg (δ x)
          (hδ_smooth x) hδx_velocity
          (fun u _hu => hricQuad t ht (δ x u)
            (mfderiv 𝓘(Real, Real) I (δ x) u (1 : Real)))
  have hv_diffAt :
      DifferentiableAt Real (fun s => vSupport s x) t := by
    change DifferentiableAt Real (fun s => L₁ s + L₂ s x) t
    exact hL₁_diff.add hL₂_diff
  have hv_lower :
      -Λ * vSupport t x ≤ deriv (fun s => vSupport s x) t := by
    change -Λ * (L₁ t + L₂ t x) ≤
      deriv (fun s => L₁ s + L₂ s x) t
    have hderiv_add :
        deriv (fun s => L₁ s + L₂ s x) t =
          deriv L₁ t + deriv (fun s => L₂ s x) t := by
      with_unfolding_all exact deriv_add hL₁_diff hL₂_diff
    rw [hderiv_add]
    linarith
  have hrho0_ev' :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) rho0 y := by
    simpa only [rho0] using hrho0_ev
  have hgrad0' :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) (S.base.metric t) rho0 y) x := by
    simpa only [rho0] using hgrad0
  have hgrad0_norm' :
      (S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) rho0 x)
          (gradientFun (I := I) (S.base.metric t) rho0 x) = 1 := by
    simpa only [rho0] using hgrad0_norm
  have hlap0' :
      laplacian
          (I := I) (LeviCivita (I := I) (S.base.metric t))
          (S.base.metric t) rho0 x ≤
        2 * n / r + n * q := by
    rw [hr, hn]
    simpa only [rho0] using hlap0
  refine ⟨{
    rho0 := rho0
    support := vSupport
    support_t := ?_
    rho0_x := ?_
    upper_nhds := hupper
    time_diff := hv_diffAt
    time_lower := hv_lower
    space_diff_nhds := hrho0_ev'
    grad_diff := hgrad0'
    grad_sq := hgrad0_norm'
    lap_upper := hlap0'
  }⟩
  · funext y
    exact hvSupport_t y
  · exact hrho0_x.trans hr.symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem CalabiFlowCore.scale
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {O x : M} {T t d Λ r n q : Real}
    (C : CalabiFlowCore (I := I) S O T t x Λ r n q)
    (hT : 0 < T)
    (ht : t ∈ Set.Icc 0 T)
    (hcoef :
      2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ) =
        2 * n / r + n * q) :
    Nonempty (ScaledDistanceSupport (I := I) S O T t x d Λ r) := by
  let rho : Real → M → Real := fun s y =>
    Real.exp (Λ * s) * C.support s y
  have hrho_t : ∀ y : M,
      rho t y = Real.exp (Λ * t) * C.rho0 y := by
    intro y
    rw [show rho t y = Real.exp (Λ * t) * C.support t y by rfl,
      C.support_t]
  have hrho_tx : rho t x = Real.exp (Λ * t) * r := by
    rw [hrho_t, C.rho0_x]
  have hupper :
      ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
        Real.exp (Λ * p.1) *
            (riemannianEDistOf
              (I := I) (S.base.metric p.1) O p.2).toReal ≤
          rho p.1 p.2 := by
    filter_upwards [C.upper_nhds] with p hp
    exact mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
  have hrho_t_fun :
      rho t = Real.exp (Λ * t) • C.rho0 := by
    funext y
    simpa only [Pi.smul_apply, smul_eq_mul] using hrho_t y
  have hrho_space :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) (rho t) y := by
    rw [hrho_t_fun]
    filter_upwards [C.space_diff_nhds] with y hy
    exact hy.const_smul _
  have hgrad_ev :
      (fun y : M =>
        gradientFun (I := I) (S.base.metric t) (rho t) y) =ᶠ[𝓝 x]
        (fun y : M =>
          Real.exp (Λ * t) •
            gradientFun (I := I) (S.base.metric t) C.rho0 y) := by
    filter_upwards [C.space_diff_nhds] with y hy
    rw [hrho_t_fun]
    exact
      gradientFun_const_smul
        (I := I) (S.base.metric t) (Real.exp (Λ * t)) hy
  have hgrad_scaled :
      MDiffAt
        (T% fun y : M =>
          Real.exp (Λ * t) •
            gradientFun (I := I) (S.base.metric t) C.rho0 y) x := by
    simpa only [Pi.smul_apply] using
      C.grad_diff.smul_const_section (a := Real.exp (Λ * t))
  have hgrad_total :
      (T% fun y : M =>
        gradientFun (I := I) (S.base.metric t) (rho t) y) =ᶠ[𝓝 x]
        (T% fun y : M =>
          Real.exp (Λ * t) •
            gradientFun (I := I) (S.base.metric t) C.rho0 y) := by
    filter_upwards [hgrad_ev] with y hy
    change TotalSpace.mk' E y _ = TotalSpace.mk' E y _
    rw [hy]
  have hrho_grad :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) (S.base.metric t) (rho t) y) x :=
    hgrad_scaled.congr_of_eventuallyEq hgrad_total
  have hgrad_x :
      gradientFun (I := I) (S.base.metric t) (rho t) x =
        Real.exp (Λ * t) •
          gradientFun (I := I) (S.base.metric t) C.rho0 x :=
    hgrad_ev.self_of_nhds
  have hexp_sq :
      Real.exp (Λ * t) ^ 2 = Real.exp (2 * Λ * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hrho_grad_norm :
      (S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) (rho t) x)
          (gradientFun (I := I) (S.base.metric t) (rho t) x) ≤
        Real.exp (2 * Λ * t) := by
    rw [hgrad_x, gInner_smul_self (I := I) (S.base.metric t) x,
      C.grad_sq, mul_one, hexp_sq]
  have huniq :=
    uniqueDiffOn_Icc hT t ht
  have hv_time :
      DifferentiableWithinAt Real
        (fun s => C.support s x) (Set.Icc 0 T) t :=
    C.time_diff.differentiableWithinAt
  have hcancel :
      0 ≤
        derivWithin (fun s => C.support s x) (Set.Icc 0 T) t +
          Λ * C.support t x := by
    rw [C.time_diff.derivWithin huniq]
    linarith [C.time_lower]
  have hlin :
      HasDerivAt (fun s : Real => Λ * s) Λ t := by
    simpa using (hasDerivAt_id t).const_mul Λ
  have hexp :
      HasDerivAt (fun s : Real => Real.exp (Λ * s))
        (Real.exp (Λ * t) * Λ) t :=
    hlin.exp
  have hrho_time :
      DifferentiableWithinAt Real
        (fun s => rho s x) (Set.Icc 0 T) t := by
    change DifferentiableWithinAt Real
      (fun s => Real.exp (Λ * s) * C.support s x) _ t
    exact hexp.differentiableAt.differentiableWithinAt.mul hv_time
  have hrho_deriv :
      derivWithin (fun s => rho s x) (Set.Icc 0 T) t =
        Real.exp (Λ * t) *
          (derivWithin (fun s => C.support s x) (Set.Icc 0 T) t +
            Λ * C.support t x) := by
    change derivWithin
      (fun s => Real.exp (Λ * s) * C.support s x) _ t = _
    rw [derivWithin_fun_mul
      hexp.differentiableAt.differentiableWithinAt hv_time,
      hexp.differentiableAt.derivWithin huniq, hexp.deriv]
    ring
  have hlap_rho :
      laplacianAt (I := I) (flowG (I := I) S) t (rho t) x =
        Real.exp (Λ * t) *
          laplacian
            (I := I) (LeviCivita (I := I) (S.base.metric t))
            (S.base.metric t) C.rho0 x := by
    rw [hrho_t_fun, laplacianAt_eq]
    simpa only [flowG, SolutionFamily.connection, LeviCivita] using
      (laplacian_smul_at
        (I := I) (LeviCivita (I := I) (S.base.metric t))
          (S.base.metric t) (Real.exp (Λ * t))
          C.space_diff_nhds C.grad_diff)
  have hpar :
      -Real.exp (Λ * t) * (2 * n / r + n * q) ≤
        parabolicOperatorWithDrift
          (I := I) (flowG (I := I) S) T
          (fun _ y => (0 : TangentSpace I y)) rho t x := by
    rw [parabolicOperatorWithDrift_eq,
      heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt,
      hrho_deriv, hlap_rho]
    have htime_mul :=
      mul_nonneg (Real.exp_pos (Λ * t)).le hcancel
    have hlap_mul :=
      mul_le_mul_of_nonneg_left C.lap_upper (Real.exp_pos (Λ * t)).le
    linarith
  refine ⟨{
    rho := rho
    eq_at := hrho_tx
    upper_nhds := hupper
    time_diff := hrho_time
    space_diff_nhds := hrho_space
    grad_diff := hrho_grad
    grad_sq := hrho_grad_norm
    par_lower := ?_
  }⟩
  rw [hcoef]
  exact hpar

omit [IsManifold I 2 M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_scaled_distance_support_of_ricci_bound
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T t Λ : Real}
    (hT : 0 < T)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hΛ : 0 ≤ Λ)
    (hricQuad : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          Λ * (S.base.metric s).inner y v v)
    (hcomplete_t :
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite :
      riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (hOx : O ≠ x) :
    let d : Real := Module.finrank Real E
    let r : Real :=
      (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    Nonempty (ScaledDistanceSupport (I := I) S O T t x d Λ r) := by
  classical
  dsimp only
  let dNat : Nat := Module.finrank Real E
  let d : Real := (dNat : Real)
  let nNat : Nat := dNat - 1
  let n : Real := (nNat : Real)
  let r : Real :=
    (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
  have hdNat_pos : 0 < dNat := by
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  have hdNat_one : 1 ≤ dNat := hdNat_pos
  have hdn : d - 1 = n := by
    dsimp only [d, n, nNat]
    rw [Nat.cast_sub hdNat_one]
    norm_num
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨(S.base.metric t).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun y : M => TangentSpace I y) :=
    ⟨⟨(S.base.metric t).inner,
      (S.base.metric t).contMDiff.continuous,
      by intro y v w; rfl⟩⟩
  let : PseudoEMetricSpace M :=
    PseudoEMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete_t.complete
  have hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal
          (Real.sqrt ((S.base.metric t).inner y w w)) := by
    intro y w
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  have hfinite' :
      Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    simpa only [riemannianEDistOf] using hfinite
  obtain ⟨q, hq, hRicLower, hnq⟩ :=
    exists_calabi_coeff
      (I := I) (S.base.metric t) hΛ (hricQuad t ht)
  have hr : r = (Manifold.riemannianEDist I O x).toReal := by
    simp only [r, riemannianEDistOf]
  have hnDim :
      n = ((Module.finrank Real E - 1 : Nat) : Real) := by
    rfl
  obtain ⟨core⟩ :=
    calabi_core_of_solution
      (I := I) S hS O hreg hricQuad ht htpos x hfinite' hOx
        hEnorm hq hRicLower hr hnDim
  have hcoef :
      2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ) =
        2 * n / r + n * q := by
    calc
      2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ) =
          2 * n / r + Real.sqrt ((d - 1) * Λ) := by rw [hdn]
      _ = 2 * n / r + n * q := by rw [hnq]
  exact core.scale hT ht hcoef

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem scaledDist_support
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T K t : Real}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite :
      riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (hOx : O ≠ x) :
    let d : Real := Module.finrank Real E
    let Λ : Real := d ^ 2 * Real.sqrt K
    let r : Real :=
      (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    Nonempty (ScaledDistanceSupport (I := I) S O T t x d Λ r) := by
  classical
  dsimp only
  obtain ⟨hΛ, hricQuad⟩ :=
    ricci_quad_of_curv (I := I) S hK hcurv
  have hcomplete_t :
      RiemannianMetricComplete (I := I) (S.base.metric t) :=
    complete_of_ricBound
      (I := I) (D := D) (a := 0) (b := T)
        (K := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K)
        (s := t) S hS hslab hreg hΛ hricQuad hcomplete ht
  exact exists_scaled_distance_support_of_ricci_bound
    (I := I) (D := D) (T := T) (t := t)
      (Λ := (Module.finrank Real E : Real) ^ 2 * Real.sqrt K)
      S hS O hT hreg hΛ hricQuad hcomplete_t ht htpos x hfinite hOx

theorem exists_scaled_distance_calabi_upper_support_of_solution
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T K t : Real}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hK : 0 ≤ K)
    (hcurv : ∀ s ∈ Set.Icc 0 T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K)
    (ht : t ∈ Set.Icc 0 T)
    (htpos : 0 < t)
    (x : M)
    (hfinite :
      riemannianEDistOf (I := I) (S.base.metric t) O x ≠ ⊤)
    (hOx : O ≠ x) :
    let d : Real := Module.finrank Real E
    let Λ : Real := d ^ 2 * Real.sqrt K
    let r : Real :=
      (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal
    ∃ ρ : Real → M → Real,
      ρ t x = Real.exp (Λ * t) * r ∧
      (∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
        Real.exp (Λ * p.1) *
            (riemannianEDistOf (I := I)
              (S.base.metric p.1) O p.2).toReal ≤
          ρ p.1 p.2) ∧
      DifferentiableWithinAt Real
        (fun s => ρ s x) (Set.Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) (ρ t) y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (T% fun y : M =>
          gradientFun (I := I) (S.base.metric t) (ρ t) y) x ∧
      (S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) (ρ t) x)
          (gradientFun (I := I) (S.base.metric t) (ρ t) x) ≤
        Real.exp (2 * Λ * t) ∧
      -Real.exp (Λ * t) *
          (2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ)) ≤
        parabolicOperatorWithDrift
          (I := I) (flowG (I := I) S) T
          (fun _ y => (0 : TangentSpace I y)) ρ t x := by
  dsimp only
  obtain ⟨h⟩ :=
    scaledDist_support
      (I := I) S hS O hT hslab hreg hcomplete hK hcurv
        ht htpos x hfinite hOx
  exact
    ⟨h.rho, h.eq_at, h.upper_nhds, h.time_diff, h.space_diff_nhds,
      h.grad_diff, h.grad_sq, h.par_lower⟩

end DifferentialGeometry.PDE.RicciFlow

end
