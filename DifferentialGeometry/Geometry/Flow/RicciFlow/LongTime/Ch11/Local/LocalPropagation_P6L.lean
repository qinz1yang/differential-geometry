import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation

/-!
# L6-A 叶子：`scalar_le_on_ball_of_gradient_bound` 的局部化（`_P6L`）

局部化合同 `docs/geometrization/chapter8/design-C11-P6-localization-contract-20261006.md` §1–§2：
原 `CN/LocalPropagation.lean:347` 的前提 `hgrad : ∀ w, 2Q ≤ R(w) → |dR| ≤ …`（carrier 上全局）
在证明里只于连接 `z`、`y` 的路径点 `gam w` 求值。路径由
`exists_path_lintegral_speed_lt_of_mem_closedBall` 给出、长度 `< 2·radius`，
所以路径点都在 `B(z, 2·radius)` 内。这里：
* `exists_path_lintegral_speed_lt_of_mem_closedBall_P6L`：同一路径，结论多一条
  "`d(z, γ τ) < r + η`，`τ ∈ [0,1]`"
  （`riemannianEDist_le_pathELength` + `pathELength_mono`）；
* `scalar_le_on_ball_of_gradient_bound_P6L`：`hgrad` 只要求在区域 `U ⊇ B(z, 2·radius)` 上，证明体照抄。
-/

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open Bundle DifferentialGeometry.Tensor0SBundle
open Filter
open scoped _root_.Manifold ContDiff ENNReal _root_.Topology

section PathP6L

open MeasureTheory

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- `exists_path_lintegral_speed_lt_of_mem_closedBall` 加上路径点到起点的距离界。 -/
theorem exists_path_lintegral_speed_lt_of_mem_closedBall_P6L
    (g : SmoothRiemannianMetric I M) {z y : M} {r eta : Real}
    (hr : 0 ≤ r) (heta : 0 < eta)
    (hy : y ∈ riemannianClosedBallOf (I := I) g z r) :
    ∃ gamma : Real → M, ContMDiff 𝓘(Real, Real) I 1 gamma ∧ gamma 0 = z ∧ gamma 1 = y ∧
      (∫⁻ tau in Set.Icc (0 : Real) 1, ENNReal.ofReal (Real.sqrt
        (g.inner (gamma tau) (mfderiv 𝓘(Real, Real) I gamma tau (realTangentOne tau))
          (mfderiv 𝓘(Real, Real) I gamma tau (realTangentOne tau))))) <
        ENNReal.ofReal (r + eta) ∧
      ∀ tau ∈ Set.Icc (0 : Real) 1,
        riemannianEDistOf (I := I) g z (gamma tau) < ENNReal.ofReal (r + eta) := by
  have hball : riemannianEDistOf (I := I) g z y ≤ ENNReal.ofReal r := hy
  have hlt : riemannianEDistOf (I := I) g z y < ENNReal.ofReal (r + eta) :=
    lt_of_le_of_lt hball ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).2 (by linarith))
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hlt' : Manifold.riemannianEDist I z y < ENNReal.ofReal (r + eta) := hlt
  obtain ⟨gamma, h0, h1, hsm, hlen, -, -⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hlt' zero_lt_one
  refine ⟨gamma, hsm, h0, h1, ?_, ?_⟩
  · have hlen' := hlen
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc] at hlen'
    refine lt_of_le_of_lt (le_of_eq ?_) hlen'
    refine lintegral_congr fun tau => ?_
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  · intro tau htau
    have hd : Manifold.riemannianEDist I z (gamma tau) ≤ Manifold.pathELength I gamma 0 tau :=
      Manifold.riemannianEDist_le_pathELength hsm.contMDiffOn h0 rfl htau.1
    have hm : Manifold.pathELength I gamma 0 tau ≤ Manifold.pathELength I gamma 0 1 :=
      Manifold.pathELength_mono le_rfl htau.2
    have hfin : Manifold.riemannianEDist I z (gamma tau) < ENNReal.ofReal (r + eta) :=
      (hd.trans hm).trans_lt hlen
    exact hfin

end PathP6L

section ScalarBoundP6L

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M]
variable {D : RealTimeInterval}

/-- **`_P6L`**：原 `scalar_le_on_ball_of_gradient_bound`（`LocalPropagation:347`），`hgrad` 只在区域
`U ⊇ B(z, 2·localPropagationRadius CStar / √Q)` 上；其余前提、结论、证明体照抄。 -/
theorem scalar_le_on_ball_of_gradient_bound_P6L
    (S : SolutionOn (I := I) (M := M) D)
    {CStar Q s : ℝ} {z y : M} (hCStar : 0 ≤ CStar) (hQ : 0 < Q) (U : Set M)
    (hU : riemannianBallOf (I := I) (S.base.metric s) z
      (2 * (localPropagationRadius CStar / Real.sqrt Q)) ⊆ U)
    (hgrad : ∀ w ∈ U, 2 * Q ≤ S.scalar s w → ∀ v : TangentSpace I w,
      |scalarDifferential (I := I) S s w v| ≤
        2 * CStar * (S.scalar s w * Real.sqrt (S.scalar s w)) *
          Real.sqrt ((S.base.metric s).inner w v v))
    (hz : S.scalar s z ≤ Q)
    (hy : y ∈ riemannianClosedBallOf (S.base.metric s) z
      (localPropagationRadius CStar / Real.sqrt Q)) :
    S.scalar s y ≤ 3 * Q := by
  have hcpos : 0 < localPropagationRadius CStar := localPropagationRadius_pos hCStar
  have hcsmall : CStar * localPropagationRadius CStar < 1 / 20 :=
    mul_localPropagationRadius_lt hCStar
  have hradpos : 0 < localPropagationRadius CStar / Real.sqrt Q :=
    div_pos hcpos (Real.sqrt_pos.2 hQ)
  have hsqP : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  obtain ⟨gam, hgam, hgam0, hgam1, hspeed, hgamdist⟩ :=
    exists_path_lintegral_speed_lt_of_mem_closedBall_P6L (I := I) (S.base.metric s)
      hradpos.le hradpos hy
  have hgamU : ∀ w ∈ Set.Icc (0 : Real) 1, gam w ∈ U := by
    intro w hw
    apply hU
    change riemannianEDistOf (I := I) (S.base.metric s) z (gam w) <
      ENNReal.ofReal (2 * (localPropagationRadius CStar / Real.sqrt Q))
    rw [two_mul]
    exact hgamdist w hw
  have hspeed2 := hspeed.le
  rw [show localPropagationRadius CStar / Real.sqrt (Q) +
        localPropagationRadius CStar / Real.sqrt (Q) =
      2 * (localPropagationRadius CStar / Real.sqrt (Q)) from by ring] at hspeed2
  have hbudnn : (0 : Real) ≤ 2 * (localPropagationRadius CStar / Real.sqrt (Q)) := by
    positivity
  have hstep1 : S.scalar s y ≤ 3 * (Q) := by
    have hcont : ContinuousOn (fun sig : Real => S.scalar s (gam sig)) (Set.Icc 0 1) :=
      (((scalarSmoothOfSolution (I := I) S s).continuous).comp hgam.continuous).continuousOn
    have hkey : ∀ t ∈ Set.Icc (0 : Real) 1,
        (fun sig : Real => S.scalar s (gam sig)) t ≤ 3 * (Q) := by
      refine forall_le_of_no_crossing (B := 2 * Q) (by linarith) hcont ?_
      intro uu vv h0u huv hv1 hge hstart hend
      have hsub : Set.Icc uu vv ⊆ Set.Icc (0 : Real) 1 := Set.Icc_subset_Icc h0u hv1
      have hpos : ∀ w ∈ Set.Icc uu vv, 0 < S.scalar s (gam w) := by
        intro w hw
        exact lt_of_lt_of_le (by linarith) (hge w hw)
      have hderiv : ∀ w ∈ Set.Icc uu vv,
          HasDerivAt (fun sig : Real => (Real.sqrt (S.scalar s (gam sig)))⁻¹)
            (-(1 / (2 * Real.sqrt (S.scalar s (gam w))) *
                scalarDifferential (I := I) S s (gam w)
                  (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) /
                Real.sqrt (S.scalar s (gam w)) ^ 2) w := by
        intro w hw
        exact hasDerivAt_inv_sqrt (hasDerivAt_scalar_comp (I := I) S s hgam w) (hpos w hw)
      have hbdd : ∀ w ∈ Set.Icc uu vv,
          |-(1 / (2 * Real.sqrt (S.scalar s (gam w))) *
              scalarDifferential (I := I) S s (gam w)
                (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) /
              Real.sqrt (S.scalar s (gam w)) ^ 2| ≤
            CStar * Real.sqrt ((S.base.metric s).inner (gam w)
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) := by
        intro w hw
        refine abs_deriv_inv_sqrt_le (hpos w hw) ?_
        have hgd := hgrad (gam w) (hgamU w (hsub hw)) (hge w hw)
          (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
        have hring : 2 * (CStar * Real.sqrt ((S.base.metric s).inner (gam w)
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w)))) *
            (S.scalar s (gam w) * Real.sqrt (S.scalar s (gam w))) =
          2 * CStar * (S.scalar s (gam w) * Real.sqrt (S.scalar s (gam w))) *
            Real.sqrt ((S.base.metric s).inner (gam w)
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) := by
          ring
        rw [hring]
        exact hgd
      have hbud : |(Real.sqrt (S.scalar s (gam vv)))⁻¹ -
          (Real.sqrt (S.scalar s (gam uu)))⁻¹| ≤
            CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q))) :=
        abs_sub_le_of_hasDerivAt_of_lintegral_le
          (f := fun sig : Real => (Real.sqrt (S.scalar s (gam sig)))⁻¹)
          (a := uu) (b := vv)
          (v := fun w : Real => Real.sqrt ((S.base.metric s).inner (gam w)
            (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
            (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))))
          huv hsub hCStar hbudnn hderiv hbdd hspeed2
      have huupos : 0 < S.scalar s (gam uu) := hpos uu (Set.left_mem_Icc.2 huv)
      have hstart' : S.scalar s (gam uu) ≤ max (2 * Q) (S.scalar s (gam 0)) := hstart
      rw [hgam0] at hstart'
      have hend' : 3 * (Q) ≤ S.scalar s (gam vv) := hend
      have hstart2 : S.scalar s (gam uu) ≤ 2 * Q := by
        exact hstart'.trans (max_le le_rfl (hz.trans (by linarith)))
      have hA : (Real.sqrt (2 * (Q)))⁻¹ ≤ (Real.sqrt (S.scalar s (gam uu)))⁻¹ := by
        have h2 := one_div_le_one_div_of_le (Real.sqrt_pos.2 huupos)
          (Real.sqrt_le_sqrt hstart2)
        rwa [one_div, one_div] at h2
      have hB : (Real.sqrt (S.scalar s (gam vv)))⁻¹ ≤ (Real.sqrt (3 * (Q)))⁻¹ := by
        have h2 := one_div_le_one_div_of_le
          (Real.sqrt_pos.2 (by linarith : (0 : Real) < 3 * (Q)))
          (Real.sqrt_le_sqrt hend')
        rwa [one_div, one_div] at h2
      have hgapEq : (Real.sqrt (2 * (Q)))⁻¹ - (Real.sqrt (3 * (Q)))⁻¹ =
          ((Real.sqrt 2)⁻¹ - (Real.sqrt 3)⁻¹) * (Real.sqrt (Q))⁻¹ := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2),
          Real.sqrt_mul (by norm_num : (0 : Real) ≤ 3), mul_inv, mul_inv]
        ring
      have hbudEq : CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q))) =
          2 * (CStar * localPropagationRadius CStar) * (Real.sqrt (Q))⁻¹ := by
        rw [div_eq_mul_inv]
        ring
      have hnum : 2 * (CStar * localPropagationRadius CStar) <
          (Real.sqrt 2)⁻¹ - (Real.sqrt 3)⁻¹ := by
        linarith [one_div_ten_lt_inv_sqrt_two_sub_inv_sqrt_three]
      have hfin : CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q))) <
          (Real.sqrt (2 * (Q)))⁻¹ - (Real.sqrt (3 * (Q)))⁻¹ := by
        rw [hgapEq, hbudEq]
        exact mul_lt_mul_of_pos_right hnum (inv_pos.2 hsqP)
      have hdrop : (Real.sqrt (2 * (Q)))⁻¹ - (Real.sqrt (3 * (Q)))⁻¹ ≤
          CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q))) := by
        refine le_trans ?_ hbud
        linarith [hA, hB, neg_le_abs ((Real.sqrt (S.scalar s (gam vv)))⁻¹ -
          (Real.sqrt (S.scalar s (gam uu)))⁻¹)]
      linarith
    have h1 : S.scalar s (gam 1) ≤ 3 * (Q) := hkey 1 ⟨by norm_num, le_rfl⟩
    rwa [hgam1] at h1
  exact hstep1

/-- consumer：原定理（全局 `hgrad`）由 `_P6L` 版（`U = univ`）推出。 -/
example (S : SolutionOn (I := I) (M := M) D)
    {CStar Q s : ℝ} {z y : M} (hCStar : 0 ≤ CStar) (hQ : 0 < Q)
    (hgrad : ∀ w, 2 * Q ≤ S.scalar s w → ∀ v : TangentSpace I w,
      |scalarDifferential (I := I) S s w v| ≤
        2 * CStar * (S.scalar s w * Real.sqrt (S.scalar s w)) *
          Real.sqrt ((S.base.metric s).inner w v v))
    (hz : S.scalar s z ≤ Q)
    (hy : y ∈ riemannianClosedBallOf (S.base.metric s) z
      (localPropagationRadius CStar / Real.sqrt Q)) :
    S.scalar s y ≤ 3 * Q :=
  scalar_le_on_ball_of_gradient_bound_P6L S hCStar hQ Set.univ (Set.subset_univ _)
    (fun w _ => hgrad w) hz hy

end ScalarBoundP6L

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
