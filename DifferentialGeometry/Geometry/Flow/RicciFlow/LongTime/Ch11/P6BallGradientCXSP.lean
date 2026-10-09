import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabGradientScalarControlC11X
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal

set_option autoImplicit false

/-!
# CX-SPINE G6：只在两倍球上需要梯度界的标量传播

将 SlabGradientScalarControlC11XPortC11P:55–161 的全域梯度证明局部化。
在半径 r 的闭球中测试，近最短路径误差取 min(r,η₀)，用真实 path length
证明路径始终在半径 2r 的开球内。阈值以上的梯度供给只需在该开球。
这给首次接触论证的局部端点球输入，不声称已经得到跨手术 footprint。
源文件 SHA-256: ec793979b371bb1c50bdf6848a98d6400bcbfc3fe2862f1863c08a47e56ba517
-/

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [T2Space M] {D : RealTimeInterval}

/-- 两倍开球上的阈值梯度控制足以约束内层闭球的标量曲率。 -/
theorem scalar_le_four_mul_max_of_ball_gradient_CXSP (S : SolutionOn (I := I) (M := M) D)
    {Cgrad : ℝ≥0} {qcan t r : ℝ} {x y : M}
    (hgrad : ∀ w ∈ riemannianBallOf (S.base.metric t) x (2 * r),
      qcan < S.scalar t w → ∀ v : TangentSpace I w,
      |scalarDifferential (I := I) S t w v| ≤
        Cgrad * S.scalar t w * Real.sqrt (S.scalar t w) *
          Real.sqrt ((S.base.metric t).inner w v v))
    (hrpos : 0 < r) (hmax : 0 < max (S.scalar t x) qcan)
    (hr : (Cgrad : ℝ) * r * Real.sqrt (max (S.scalar t x) qcan) ≤ 1 / 4)
    (hy : y ∈ riemannianClosedBallOf (I := I) (S.base.metric t) x r) :
    S.scalar t y ≤ 4 * max (S.scalar t x) qcan := by
  obtain ⟨N, hNdef⟩ : ∃ N, N = max (S.scalar t x) qcan := ⟨_, rfl⟩
  rw [← hNdef] at hmax hr ⊢
  have hN : 0 < N := hmax
  set m := Real.sqrt N with hmdef
  have hm : 0 < m := Real.sqrt_pos.2 hN
  have hmsq : m ^ 2 = N := Real.sq_sqrt hN.le
  have hC : (0 : ℝ) ≤ Cgrad := Cgrad.coe_nonneg
  set η₀ := 1 / (16 * ((Cgrad : ℝ) + 1) * m) with hη₀def
  have hη₀ : 0 < η₀ := by positivity
  set η := min r η₀ with hηdef
  have hη : 0 < η := lt_min hrpos hη₀
  have hηr : η ≤ r := min_le_left _ _
  have hηb : (Cgrad : ℝ) * η * m ≤ 1 / 16 := by
    have hη₀b : (Cgrad : ℝ) * η₀ * m ≤ 1 / 16 := by
      rw [hη₀def, show (Cgrad : ℝ) * (1 / (16 * ((Cgrad : ℝ) + 1) * m)) * m =
        (Cgrad : ℝ) / (16 * ((Cgrad : ℝ) + 1)) by field_simp]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_right r η₀) hC) hm.le).trans hη₀b
  obtain ⟨gam, hgam, hgam0, hgam1, hspeed⟩ :=
    exists_path_lintegral_speed_lt_of_mem_closedBall (I := I) (S.base.metric t) hrpos.le hη hy
  have hlength : metricPathELength (S.base.metric t) gam 0 1 < ENNReal.ofReal (r + η) := by
    rw [metricPathELength_eq]
    exact (MeasureTheory.lintegral_mono_set Ioo_subset_Icc_self).trans_lt hspeed
  have hstay : ∀ w ∈ Icc (0 : ℝ) 1,
      gam w ∈ riemannianBallOf (S.base.metric t) x (2 * r) := by
    intro w hw
    have hpref := edistOf_le_metricPathELength (S.base.metric t) hw.1 hgam.contMDiffOn
    rw [hgam0] at hpref
    exact (hpref.trans (metricPathELength_mono (S.base.metric t) gam le_rfl hw.2)).trans_lt
      (hlength.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))
  have hcont : ContinuousOn (fun sig : ℝ => S.scalar t (gam sig)) (Icc 0 1) :=
    (((scalarSmoothOfSolution (I := I) S t).continuous).comp hgam.continuous).continuousOn
  have hkey : ∀ τ ∈ Icc (0 : ℝ) 1, (fun sig : ℝ => S.scalar t (gam sig)) τ ≤ 4 * N := by
    refine forall_le_of_no_crossing (B := 9 / 4 * N) (by linarith) hcont ?_
    intro uu vv h0u huv hv1 hge hstart hend
    have hsub : Icc uu vv ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc h0u hv1
    have hpos : ∀ w ∈ Icc uu vv, 0 < S.scalar t (gam w) := fun w hw =>
      lt_of_lt_of_le (by positivity) (hge w hw)
    have hqw : ∀ w ∈ Icc uu vv, qcan < S.scalar t (gam w) := fun w hw =>
      lt_of_lt_of_le (by linarith [le_max_right (S.scalar t x) qcan]) (hge w hw)
    have hderiv : ∀ w ∈ Icc uu vv,
        HasDerivAt (fun sig : ℝ => (Real.sqrt (S.scalar t (gam sig)))⁻¹)
          (-(1 / (2 * Real.sqrt (S.scalar t (gam w))) *
              scalarDifferential (I := I) S t (gam w)
                (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) /
              Real.sqrt (S.scalar t (gam w)) ^ 2) w := fun w hw =>
      hasDerivAt_inv_sqrt (hasDerivAt_scalar_comp (I := I) S t hgam w) (hpos w hw)
    have hbdd : ∀ w ∈ Icc uu vv,
        |-(1 / (2 * Real.sqrt (S.scalar t (gam w))) *
            scalarDifferential (I := I) S t (gam w)
              (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) /
            Real.sqrt (S.scalar t (gam w)) ^ 2| ≤
          (Cgrad : ℝ) / 2 * Real.sqrt ((S.base.metric t).inner (gam w)
            (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
            (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) := by
      intro w hw
      refine abs_deriv_inv_sqrt_le (hpos w hw) ?_
      have hgd := hgrad (gam w) (hstay w (hsub hw)) (hqw w hw)
        (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
      refine hgd.trans_eq ?_
      ring
    have hbud := abs_sub_le_of_hasDerivAt_of_lintegral_le
      (f := fun sig : ℝ => (Real.sqrt (S.scalar t (gam sig)))⁻¹)
      (a := uu) (b := vv)
      (v := fun w : ℝ => Real.sqrt ((S.base.metric t).inner (gam w)
        (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
        (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))))
      huv hsub (by positivity) (by positivity) hderiv hbdd hspeed.le
    have hstart' : S.scalar t (gam uu) ≤ max (9 / 4 * N) (S.scalar t (gam 0)) := hstart
    rw [hgam0] at hstart'
    have hstart2 : S.scalar t (gam uu) ≤ 9 / 4 * N :=
      hstart'.trans (max_le le_rfl ((le_max_left (S.scalar t x) qcan).trans (by linarith)))
    have hend' : 4 * N ≤ S.scalar t (gam vv) := hend
    have hsu : Real.sqrt (S.scalar t (gam uu)) ≤ 3 / 2 * m := by
      calc Real.sqrt (S.scalar t (gam uu)) ≤ Real.sqrt ((3 / 2 * m) ^ 2) :=
            Real.sqrt_le_sqrt (by rw [mul_pow, hmsq]; linarith)
        _ = 3 / 2 * m := Real.sqrt_sq (by positivity)
    have hsv : 2 * m ≤ Real.sqrt (S.scalar t (gam vv)) := by
      calc 2 * m = Real.sqrt ((2 * m) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (S.scalar t (gam vv)) :=
            Real.sqrt_le_sqrt (by rw [mul_pow, hmsq]; linarith)
    have hA : (3 / 2 * m)⁻¹ ≤ (Real.sqrt (S.scalar t (gam uu)))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 (hpos uu (left_mem_Icc.2 huv))) hsu
    have hB : (Real.sqrt (S.scalar t (gam vv)))⁻¹ ≤ (2 * m)⁻¹ :=
      inv_anti₀ (by positivity) hsv
    have hgap : (3 / 2 * m)⁻¹ - (2 * m)⁻¹ ≤ (Cgrad : ℝ) / 2 * (r + η) := by
      have := neg_abs_le ((Real.sqrt (S.scalar t (gam vv)))⁻¹ -
        (Real.sqrt (S.scalar t (gam uu)))⁻¹)
      linarith
    have hgapm : (3 / 2 * m)⁻¹ - (2 * m)⁻¹ = 1 / 6 * m⁻¹ := by
      field_simp
      ring
    rw [hgapm] at hgap
    have hmul := mul_le_mul_of_nonneg_right hgap hm.le
    rw [mul_assoc, inv_mul_cancel₀ hm.ne'] at hmul
    nlinarith
  have h1 := hkey 1 ⟨by norm_num, le_rfl⟩
  simp only [hgam1] at h1
  exact h1

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
