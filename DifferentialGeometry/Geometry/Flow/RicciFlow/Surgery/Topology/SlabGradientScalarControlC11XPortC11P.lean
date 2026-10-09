import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabGradientScalarControl

/-!
# SlabGradientScalarControlC11X（S-CH11-EXT2）

extension of 已跟踪 `Topology/SlabGradientScalarControl.lean`。

astra 新增 `scalar_le_four_mul_max_of_gradient_bound_of_max_pos` 与
`OrientedThreeStage.IncomingSlab.scalar_le_four_mul_max_of_gradient_bound_at_time_of_max_pos`
（center scalar 可以非正，只要求 `max (S.scalar t x) qcan > 0`）；旧 `…_of_gradient_bound{,_at_time}`
在 donor 里改写成它们的推论。W8 宿主保持不变；本文件逐字抄写两个新增定理。直接用户：
`SmallTestLargeReserveVolume`、`PreparedSpatialReserveBall`（EXT1 的 port）。
-/

/-!
## O-CH11-FIX3 port（`PortC11P`）

上面 S-CH11-EXT2 的文本（quarantine 原文 `build-logs/scratch/S-CH11-EXT2/quarantine/`
`SlabGradientScalarControlC11X.lean`）在本树 elaboration 失败：
`scalar_le_four_mul_max_of_gradient_bound_of_max_pos` 证明里 `set N := max (S.scalar t x) qcan
with hNdef` 之后多处 whnf deterministic timeout（`set` 把 `N` 作为 let 变量留在 context，
`positivity` 等反复展开）。

本 port 只有一处 elaboration 层面修补（no statement / definition / proof idea altered；
S-CH11-EXT2 `diag/SlabDiag2.lean` 已验证）：
* `set N := max (S.scalar t x) qcan with hNdef` 改为
  `obtain ⟨N, hNdef⟩ : ∃ N, N = max (S.scalar t x) qcan := ⟨_, rfl⟩` 加
  `rw [← hNdef] at hmax hr ⊢`（`N` 成为不透明变量 + 等式，后续证明逐字不变）。

原路径 `SlabGradientScalarControlC11X` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [T2Space M] {D : RealTimeInterval}

/-- The scalar-gradient ball estimate only needs positivity of the same maximum;
the center scalar itself may be nonpositive. -/
theorem scalar_le_four_mul_max_of_gradient_bound_of_max_pos (S : SolutionOn (I := I) (M := M) D)
    {Cgrad : ℝ≥0} {qcan t r : ℝ} {x y : M}
    (hgrad : ∀ w, qcan < S.scalar t w → ∀ v : TangentSpace I w,
      |scalarDifferential (I := I) S t w v| ≤
        Cgrad * S.scalar t w * Real.sqrt (S.scalar t w) *
          Real.sqrt ((S.base.metric t).inner w v v))
    (hmax : 0 < max (S.scalar t x) qcan)
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
  set r0 := max r 0 with hr0def
  have hr0 : 0 ≤ r0 := le_max_right _ _
  have hy0 : y ∈ riemannianClosedBallOf (I := I) (S.base.metric t) x r0 :=
    riemannianClosedBallOf_mono (I := I) _ _ (le_max_left _ _) hy
  have hr0b : (Cgrad : ℝ) * r0 * m ≤ 1 / 4 := by
    rcases le_total r 0 with h | h
    · rw [hr0def, max_eq_right h]
      norm_num
    · rwa [hr0def, max_eq_left h]
  set η := 1 / (16 * ((Cgrad : ℝ) + 1) * m) with hηdef
  have hη : 0 < η := by positivity
  have hηb : (Cgrad : ℝ) * η * m ≤ 1 / 16 := by
    rw [hηdef, show (Cgrad : ℝ) * (1 / (16 * ((Cgrad : ℝ) + 1) * m)) * m =
      (Cgrad : ℝ) / (16 * ((Cgrad : ℝ) + 1)) by field_simp]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨gam, hgam, hgam0, hgam1, hspeed⟩ :=
    exists_path_lintegral_speed_lt_of_mem_closedBall (I := I) (S.base.metric t) hr0 hη hy0
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
      have hgd := hgrad (gam w) (hqw w hw) (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
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
    have hgap : (3 / 2 * m)⁻¹ - (2 * m)⁻¹ ≤ (Cgrad : ℝ) / 2 * (r0 + η) := by
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

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

/-- The same incoming-slab estimate with positive scalar threshold maximum. -/
theorem scalar_le_four_mul_max_of_gradient_bound_at_time_of_max_pos
    {Cgrad : ℝ≥0} {qcan t r : ℝ} {x y : P.Carrier}
    (hgrad : ∀ w, qcan < G.flow.scalar t w → ∀ v : TangentSpace I3 w,
      |scalarDifferential G.flow t w v| ≤
        Cgrad * G.flow.scalar t w * Real.sqrt (G.flow.scalar t w) *
          Real.sqrt ((G.flow.base.metric t).inner w v v))
    (hmax : 0 < max (G.flow.scalar t x) qcan)
    (hr : (Cgrad : ℝ) * r * Real.sqrt (max (G.flow.scalar t x) qcan) ≤ 1 / 4)
    (hy : y ∈ riemannianClosedBallOf (I := I3) (G.flow.base.metric t) x r) :
    G.flow.scalar t y ≤ 4 * max (G.flow.scalar t x) qcan := by
  have : IsManifold I3 1 P.Carrier := IsManifold.of_le (n := ∞) (by decide)
  exact scalar_le_four_mul_max_of_gradient_bound_of_max_pos G.flow hgrad hmax hr hy

end OrientedThreeStage.IncomingSlab

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
