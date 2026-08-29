import DifferentialGeometry.Geometry.Comparison.DistanceCalabi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.Barrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.RicciBound

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle Filter Manifold Set Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_ballCalabi
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : Real}
    (ht : t ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t))
    {x : M} (hOx : B.center ≠ x)
    (hx : x ∈ Metric.eball B.center (ENNReal.ofReal (B.radius / 2))) :
    let n : Real := Module.finrank Real E
    let q : Real := n / B.radius
    let r := riemannianEDist I B.center x |>.toReal
    ∃ tail : CalabiTailData (I := I) (S.base.metric t) hEnorm B.center x r,
      tail.left + tail.ell * tail.b < B.radius ∧
      let rho : M → Real := fun y =>
        tail.left + branchRadius (I := I) (S.base.metric t) tail.branch y
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      rho x = r ∧
      (∀ᶠ y in 𝓝 x, (riemannianEDist I B.center y).toReal ≤ rho y) ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) rho y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (T% fun y : M => gradientFun (I := I) (S.base.metric t) rho y) x ∧
      (S.base.metric t).inner x
          (gradientFun (I := I) (S.base.metric t) rho x)
          (gradientFun (I := I) (S.base.metric t) rho x) = 1 ∧
      laplacian (I := I) (LeviCivita (I := I) (S.base.metric t))
          (S.base.metric t) rho x ≤
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  classical
  dsimp only
  let n : Real := Module.finrank Real E
  let q : Real := n / B.radius
  have hxriem :
      riemannianEDist I B.center x < ENNReal.ofReal (B.radius / 2) := by
    have hx' := hx
    rw [Metric.mem_eball',
      IsRiemannianManifold.out (I := I) B.center x] at hx'
    exact hx'
  have hfinite :
      riemannianEDist I B.center x ≠ (⊤ : ENNReal) := by
    intro htop
    rw [htop] at hxriem
    exact (not_lt_of_ge le_top) hxriem
  have hrHalf :
      (riemannianEDist I B.center x).toReal < B.radius / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal hxriem
  have hr : (riemannianEDist I B.center x).toReal < B.radius := by
    linarith [B.radius_pos]
  have hq : 0 ≤ q := by
    exact div_nonneg (Nat.cast_nonneg _) B.radius_pos.le
  have hsqrt : Real.sqrt (1 / B.radius ^ 4) = 1 / B.radius ^ 2 := by
    rw [show B.radius ^ 4 = (B.radius ^ 2) ^ 2 by ring]
    rw [show 1 / (B.radius ^ 2) ^ 2 =
        (1 / B.radius ^ 2) ^ 2 by field_simp]
    rw [Real.sqrt_sq_eq_abs,
      abs_of_pos (one_div_pos.mpr (sq_pos_of_pos B.radius_pos))]
  have hRic : 0 < Module.finrank Real E - 1 →
      ∀ y ∈ Metric.eball B.center (ENNReal.ofReal B.radius),
        ∀ w : TangentSpace I y,
          -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
              (S.base.metric t).inner y w w ≤
            ricciTensor (I := I) (S.base.metric t) y w w := by
    intro hd y hy w
    have hyriem :
        riemannianEDist I B.center y < ENNReal.ofReal B.radius := by
      have hy' := hy
      rw [Metric.mem_eball',
        IsRiemannianManifold.out (I := I) B.center y] at hy'
      exact hy'
    have hyset : y ∈ B.setAt t := by
      change riemannianEDistOf (I := I) (S.base.metric t) B.center y <
        ENNReal.ofReal B.radius
      rw [riemannianEDistOf_eq_riemannianEDist
        (I := I) (S.base.metric t) hEnorm]
      exact hyriem
    have hbase := ricci_ge_of_rm (I := I) B hB ht hyset w
    have hdOneNat : 1 ≤ Module.finrank Real E - 1 := hd
    have hdOne :
        (1 : Real) ≤ ((Module.finrank Real E - 1 : Nat) : Real) := by
      exact_mod_cast hdOneNat
    have hcoeff :
        n ^ 2 * Real.sqrt (1 / B.radius ^ 4) ≤
          ((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2 := by
      rw [hsqrt]
      have hscale : n ^ 2 * (1 / B.radius ^ 2) = q ^ 2 := by
        dsimp only [q]
        field_simp [ne_of_gt B.radius_pos]
      rw [hscale]
      calc
        q ^ 2 = 1 * q ^ 2 := (one_mul _).symm
        _ ≤ ((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2 :=
          mul_le_mul_of_nonneg_right hdOne (sq_nonneg q)
    have hinner : 0 ≤ (S.base.metric t).inner y w w := by
      rcases eq_or_ne w 0 with rfl | hw
      · simp
      · exact ((S.base.metric t).pos y w hw).le
    have hmul := mul_le_mul_of_nonneg_right hcoeff hinner
    calc
      -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
            (S.base.metric t).inner y w w =
          -((((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
            (S.base.metric t).inner y w w) := by ring
      _ ≤ -(n ^ 2 * Real.sqrt (1 / B.radius ^ 4) *
            (S.base.metric t).inner y w w) := neg_le_neg hmul
      _ = -(n ^ 2 * Real.sqrt (1 / B.radius ^ 4)) *
            (S.base.metric t).inner y w w := by ring
      _ ≤ ricciTensor (I := I) (S.base.metric t) y w w := by
        simpa only [n] using hbase
  exact exists_calabiData_lt (I := I) (S.base.metric t) hEnorm q hq
    hRic hOx hfinite hr

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_ballFlow
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {T t : Real}
    (hT : 0 < T)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    (htB : t ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    (hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t))
    {x : M} (hOx : B.center ≠ x)
    (hx : x ∈ Metric.eball B.center (ENNReal.ofReal (B.radius / 2))) :
    let d : Real := Module.finrank Real E
    let Λ : Real := d ^ 2 / B.radius ^ 2
    let r := riemannianEDist I B.center x |>.toReal
    Nonempty
      (DistanceBarrierCore.ScaledDistSupport
        (I := I) S B.center T t x d Λ r) := by
  classical
  dsimp only
  let dNat : Nat := Module.finrank Real E
  let d : Real := (dNat : Real)
  let nNat : Nat := dNat - 1
  let n : Real := (nNat : Real)
  let Λ : Real := d ^ 2 / B.radius ^ 2
  let r : Real := (riemannianEDist I B.center x).toReal
  have hdNat_pos : 0 < dNat := Nat.pos_of_ne_zero (NeZero.ne _)
  have hdNat_one : 1 ≤ dNat := hdNat_pos
  have hdn : d - 1 = n := by
    dsimp only [d, n, nNat]
    rw [Nat.cast_sub hdNat_one]
    norm_num
  have hΛ : 0 ≤ Λ := by
    exact div_nonneg (sq_nonneg d) (sq_nonneg B.radius)
  let q : Real :=
    if nNat = 0 then 0 else Real.sqrt (Λ / n)
  have hq : 0 ≤ q := by
    dsimp only [q]
    split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  have hscale : 0 < nNat → n * q ^ 2 = Λ := by
    intro hnNat_pos
    have hn0 : nNat ≠ 0 := Nat.ne_of_gt hnNat_pos
    have hn : 0 < n := by
      dsimp only [n]
      exact_mod_cast hnNat_pos
    have hq_sq : q ^ 2 = Λ / n := by
      dsimp only [q]
      rw [if_neg hn0, Real.sq_sqrt (div_nonneg hΛ hn.le)]
    rw [hq_sq]
    field_simp
  have hnq : n * q = Real.sqrt ((d - 1) * Λ) := by
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
      have hq_sq : q ^ 2 = Λ / n := by
        rw [hq_def, Real.sq_sqrt (div_nonneg hΛ hn.le)]
      have hright_sq :
          (Real.sqrt (n * Λ)) ^ 2 = n * Λ :=
        Real.sq_sqrt (mul_nonneg hn.le hΛ)
      have hleft_nonneg : 0 ≤ n * q := mul_nonneg hn.le hq
      have hright_nonneg : 0 ≤ Real.sqrt (n * Λ) := Real.sqrt_nonneg _
      have hleft_sq : (n * q) ^ 2 = n * Λ := by
        have hs := hscale hnNat_pos
        nlinarith
      nlinarith
  obtain ⟨tail, hreach, _⟩ :=
    exists_ballCalabi (I := I) B hB htB hEnorm hOx hx
  have hsqrt : Real.sqrt (1 / B.radius ^ 4) = 1 / B.radius ^ 2 := by
    rw [show B.radius ^ 4 = (B.radius ^ 2) ^ 2 by ring]
    rw [show 1 / (B.radius ^ 2) ^ 2 =
        (1 / B.radius ^ 2) ^ 2 by field_simp]
    rw [Real.sqrt_sq_eq_abs,
      abs_of_pos (one_div_pos.mpr (sq_pos_of_pos B.radius_pos))]
  have hricBall : ∀ y ∈ Metric.eball B.center (ENNReal.ofReal B.radius),
      ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric t) y v v| ≤
          Λ * (S.base.metric t).inner y v v := by
    intro y hy v
    have hyriem :
        riemannianEDist I B.center y < ENNReal.ofReal B.radius := by
      have hy' := hy
      rw [Metric.mem_eball',
        IsRiemannianManifold.out (I := I) B.center y] at hy'
      exact hy'
    have hyset : y ∈ B.setAt t := by
      change riemannianEDistOf (I := I) (S.base.metric t) B.center y <
        ENNReal.ofReal B.radius
      rw [riemannianEDistOf_eq_riemannianEDist
        (I := I) (S.base.metric t) hEnorm]
      exact hyriem
    have habs := ricci_abs_of_rm (I := I) B hB htB hyset v
    rw [hsqrt] at habs
    simpa only [Λ, d, dNat, one_div, div_eq_mul_inv, one_mul] using habs
  have hRicTail : 0 < Module.finrank Real E - 1 →
      let γ : Real → M :=
        intrinsicGeodesic
          (I := I) (S.base.metric t) hEnorm tail.p tail.u
      ∀ u ∈ Set.Ioo (0 : Real) tail.b,
        -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
              (S.base.metric t).inner (γ u)
                (Geometry.Riemannian.Variation.curveVelocity
                  (I := I) γ u)
                (Geometry.Riemannian.Variation.curveVelocity
                  (I := I) γ u) ≤
          ricciTensor (I := I) (S.base.metric t) (γ u)
            (Geometry.Riemannian.Variation.curveVelocity
              (I := I) γ u)
            (Geometry.Riemannian.Variation.curveVelocity
              (I := I) γ u) := by
    intro hd
    dsimp only
    intro u hu
    have hnNat_pos : 0 < nNat := by
      simpa only [nNat, dNat] using hd
    have huBall := tail.mem_eball hreach ⟨hu.1.le, hu.2.le⟩
    have habs := hricBall _ huBall
      (Geometry.Riemannian.Variation.curveVelocity
        (I := I)
        (intrinsicGeodesic
          (I := I) (S.base.metric t) hEnorm tail.p tail.u) u)
    have hneg := neg_le_of_abs_le habs
    rw [show ((Module.finrank Real E - 1 : Nat) : Real) = n by rfl,
      hscale hnNat_pos]
    simpa only [neg_mul] using hneg
  have hcoef :
      2 * (d - 1) / r + Real.sqrt ((d - 1) * Λ) =
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
    have hnq' : n * q = Real.sqrt (n * Λ) := by
      simpa only [hdn] using hnq
    rw [show ((Module.finrank Real E - 1 : Nat) : Real) = n by rfl,
      hdn, hnq']
  exact DistanceBarrierCore.scaled_of_tail
    (I := I) S hS B.center hT hreg ht htpos x hEnorm tail hreach hq
      hRicTail hricBall hcoef

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
