import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeRayNeckC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeStrongTracedCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6MinimizerStrongNeckCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageEscapeRayCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeFlowNC11SP

set_option autoImplicit false

/-!
# G2：hPlN′ 的 (b) ray neck 子句（O-CH11-NATIVE-RAYNECK，后缀 `_C11SP`）

路线（lead 01:0x 批准 (a)）：不 recenter traced region（G47 常数刚性），而在 `x_i = Phi.map i (ray v)`
处直接用 G47 的 witness，并以 **near-minimizer G33 孪生** 排除其 cap alternative：
`x_i` 与 G56 实段内点 `γ_i v` 的 scaled 距离 → 0（`tendsto_edist_map_zero` + ambient quadratic
control，由 `M` 的 canonical domain 支付），scalar 收敛（`pointedScalar_tendsto_*`）给比值与双端 gap。

* `alternative_eq_neck_of_near_minimizing_C11SP`（PROVED）：near-minimizer G33。
* `slice_traced_of_near_segment_C11SP`（PROVED）：G47 + near-G33 ⇒ slice 顶层 traced region
  （scaled 段数据，任意 HEq 表示的 stage / metric）。
* `rayNeck_of_segment_C11SP`（PROVISIONAL[hseg, hbr, hQnr]）：ray neck 子句。
  `hseg` = G56 `exists_stage_escape_scalar_ray_CXSP` 的段输出沿 `Phi` 的指标；`hbr` = 每个 `t'` 是
  RegularSlice 时刻 + G1 精确桥合同 `SliceTowerTraceAt_C11SP`（`idx' = ⌈t'⌉` 时由 G1 PROVED）；
  `hQnr` = `nr(t')⁻² ≤ Q`（native 尺度）。Phi 近等距 / scalar 收敛**不是** binder（由 `M` 证）。
-/

noncomputable section

open Set Filter Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {v : M}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- G33 private band 引理的逐字孪生。 -/
theorem minimizer_mem_boundary_neck_band_C11SP
    (nk : SpatialNeck g eps v) (heps : eps < 1 / 20000)
    {K : Set M}
    (hfront : frontier K = range (fun z : Sphere 2 => nk.map (z, 0)))
    {gamma : ℝ → M} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hmin : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b,
      riemannianEDistOf g (gamma s) (gamma u) = ENNReal.ofReal |s - u|)
    (ha : gamma a ∉ interior K) (hb : gamma b ∉ interior K)
    (ht : gamma t ∈ interior K) :
    gamma t ∈ nk.map '' (univ ×ˢ Icc (-50 : ℝ) 50) := by
  let _ : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I3
  let _ : RegularSpace M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (TangentSpace I3 : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  by_contra hband
  have hlen : (50 : ℝ) < eps⁻¹ := by
    apply (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
    linarith
  have hroot : 0 < Real.sqrt (metricScalarAt g v) := Real.sqrt_pos.mpr nk.Q_pos
  have hrootlow : 9 / 10 ≤ Real.sqrt (1 - eps) := by
    apply (Real.le_sqrt (by norm_num) (by linarith [nk.eps_pos])).mpr
    nlinarith
  have hfar : ENNReal.ofReal (45 / Real.sqrt (metricScalarAt g v)) ≤
      riemannianEDistOf g v (gamma t) := by
    have hnot : ¬ riemannianEDistOf g v (gamma t) <
        ENNReal.ofReal (50 * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g v)) := by
      intro hnear
      exact hband (nk.ball_subset_image_slab (by norm_num) hlen hnear)
    exact (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by linarith) hroot.le)).trans (le_of_not_gt hnot)
  have hboundary (z : M) (hz : z ∈ frontier K) :
      edist v z ≤ ENNReal.ofReal (14 / Real.sqrt (metricScalarAt g v)) := by
    rw [hfront] at hz
    obtain ⟨w, rfl⟩ := hz
    have hbound := nk.central_sphere_subset_closedBall
      ⟨(w, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    exact hbound.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by norm_num) hroot.le))
  have hgap : ENNReal.ofReal (2 * (14 / Real.sqrt (metricScalarAt g v))) <
      edist v (gamma t) := by
    have hstrict : 2 * (14 / Real.sqrt (metricScalarAt g v)) <
        45 / Real.sqrt (metricScalarAt g v) := by
      rw [← mul_div_assoc]
      exact div_lt_div_of_pos_right (by norm_num) hroot
    exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hstrict).trans_le hfar
  exact (EMetric.not_mem_interior_of_minimizing_of_frontier_edist_lt hat htb hmin ha hb
    (fun x hx y hy => EMetric.edist_lt_edist_add_edist_of_close_to_center (by positivity)
      (hboundary x hx) (hboundary y hy) hgap)) ht

theorem coneAccuracy_lt_twenty_thousandth_C11SP :
    coneAccuracy < 1 / 20000 := by
  have hu : coneAccuracy ≤
      (1 / 4000000 / 26000 / 64) / (13000 * 13000) := by
    unfold coneAccuracy
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  exact hu.trans_lt (by norm_num)

variable [SigmaCompactSpace M] {C1 C2 : ℝ} {x : M}

omit [T2Space M] [SigmaCompactSpace M] in
/-- cap core 的内部包含 `x` 的 `1/√R(x)` 球：tube（含 core frontier）距 `x` 至少 `10000/√R(x)`。 -/
theorem SpatialLocalCap.ball_subset_interior_core_C11SP {U : Set M}
    (data : SpatialLocalCap g eps x U)
    (deep : ∀ y ∈ data.tube, 10000 / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y)
    (hQ : 0 < metricScalarAt g x) :
    riemannianBallOf g x (1 / Real.sqrt (metricScalarAt g x)) ⊆ interior data.core.carrier := by
  have hroot : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr hQ
  have hconn : IsPreconnected (riemannianBallOf g x (1 / Real.sqrt (metricScalarAt g x))) :=
    (isPathConnected_riemannianBallOf g x
      (div_pos one_pos hroot)).isConnected.isPreconnected
  have hxB : x ∈ riemannianBallOf g x (1 / Real.sqrt (metricScalarAt g x)) := by
    change riemannianEDistOf g x x < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos one_pos hroot)
  have hsub : riemannianBallOf g x (1 / Real.sqrt (metricScalarAt g x)) ⊆
      interior data.core.carrier ∪ (closure data.core.carrier)ᶜ := by
    intro z hzB
    by_contra hzuv
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hzuv
    have hzcore : z ∈ frontier data.core.carrier := ⟨hzuv.2, hzuv.1⟩
    have hztube : z ∈ data.tube := by
      rw [← data.overlap_eq] at hzcore
      exact hzcore.2
    have hdeep := deep z hztube
    have hlt : metricDistance g x z < 1 / Real.sqrt (metricScalarAt g x) := by
      change riemannianEDistOf g x z < _ at hzB
      rw [metricDistance]
      exact ENNReal.toReal_lt_of_lt_ofReal hzB
    have hle : 1 / Real.sqrt (metricScalarAt g x) ≤
        10000 / Real.sqrt (metricScalarAt g x) :=
      div_le_div_of_nonneg_right (by norm_num) hroot.le
    linarith
  exact hconn.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset_closure) hsub ⟨x, hxB, data.center_inside⟩

/-- **near-minimizer G33 孪生**：`x` 只需 `1/√R(x)`-靠近最短段内点 `gamma t`。 -/
theorem SpatialCanonicalWitness.alternative_eq_neck_of_near_minimizing_C11SP
    (W : SpatialCanonicalWitness g eps C1 C2 x)
    (hW : W.capTubeHasNeckChart eps) (heps : eps ≤ coneAccuracy)
    {gamma : ℝ → M} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hmin : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b,
      riemannianEDistOf g (gamma s) (gamma u) = ENNReal.ofReal |s - u|)
    (hnear : riemannianEDistOf g x (gamma t) <
      ENNReal.ofReal (1 / Real.sqrt (metricScalarAt g x)))
    (hratio : metricScalarAt g x ≤ 2 * metricScalarAt g (gamma t))
    (hleft : C2 * metricScalarAt g (gamma a) < metricScalarAt g x)
    (hright : C2 * metricScalarAt g x < metricScalarAt g (gamma b)) :
    ∃ neck : SpatialLocalNeck g eps x W.domain.carrier,
      W.alternative = SpatialCanonicalAlternative.neck neck := by
  have hepssmall : eps < 1 / 20000 :=
    heps.trans_lt coneAccuracy_lt_twenty_thousandth_C11SP
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hnotA : gamma a ∉ W.domain.carrier := by
    intro h
    have hlow := mul_le_mul_of_nonneg_left (W.scalar_bounds _ h).1 hC2.le
    rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at hlow
    linarith
  have hnotB : gamma b ∉ W.domain.carrier := by
    intro h
    linarith [(W.scalar_bounds _ h).2]
  have hcomp : gamma a ∈ connectedComponent x := by
    have hfin : riemannianEDistOf g x (gamma a) <
        ENNReal.ofReal (1 / Real.sqrt (metricScalarAt g x) + |t - a| + 1) := by
      calc riemannianEDistOf g x (gamma a)
          ≤ riemannianEDistOf g x (gamma t) + riemannianEDistOf g (gamma t) (gamma a) :=
            riemannianEDistOf_triangle g _ _ _
        _ < ENNReal.ofReal (1 / Real.sqrt (metricScalarAt g x)) +
              ENNReal.ofReal (|t - a| + 1) := by
            rw [hmin t ⟨hat.le, htb.le⟩ a ⟨le_rfl, (hat.trans htb).le⟩]
            exact ENNReal.add_lt_add_of_lt_of_le ENNReal.ofReal_ne_top hnear
              (ENNReal.ofReal_le_ofReal (by linarith))
        _ = _ := by
            rw [← ENNReal.ofReal_add (div_nonneg zero_le_one (Real.sqrt_nonneg _))
              (add_nonneg (abs_nonneg _) zero_le_one), add_assoc]
    have hball : gamma a ∈ {y : M | riemannianEDistOf g x y <
        ENNReal.ofReal (1 / Real.sqrt (metricScalarAt g x) + |t - a| + 1)} := hfin
    exact Geometry.Metric.edistOf_ball_subset_connCompOpen g x _ hball
  cases halt : W.alternative with
  | neck data => exact ⟨data, rfl⟩
  | positive whole _ _ => exact (hnotA (whole.symm ▸ hcomp)).elim
  | round whole _ => exact (hnotA (whole.symm ▸ hcomp)).elim
  | cap data deep =>
    exfalso
    obtain ⟨v, nk, hmap⟩ := hW data deep halt
    have hfront : frontier data.core.carrier =
        range (fun z : Sphere 2 => nk.map (z, 0)) := by
      rw [← data.inner_boundary]
      ext y
      constructor
      · rintro ⟨⟨z, w⟩, ⟨_, hw⟩, rfl⟩
        have hw0 : w = 0 := hw
        subst w
        exact ⟨z, (hmap _).symm⟩
      · rintro ⟨z, rfl⟩
        exact ⟨(z, 0), ⟨mem_univ _, rfl⟩, hmap _⟩
    have hcoreU : data.core.carrier ⊆ W.domain.carrier := fun y hy => by
      rw [data.union_eq]
      exact Or.inl hy
    have hxt : gamma t ∈ interior data.core.carrier := by
      apply data.ball_subset_interior_core_C11SP deep W.Q_pos
      exact hnear
    have hband : gamma t ∈ nk.map '' (univ ×ˢ Icc (-50 : ℝ) 50) :=
      minimizer_mem_boundary_neck_band_C11SP nk hepssmall hfront
        hat htb hmin (fun h => hnotA (hcoreU (interior_subset h)))
        (fun h => hnotB (hcoreU (interior_subset h))) hxt
    have hlen : (50 : ℝ) < eps⁻¹ := by
      apply (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
      linarith
    have hwindow : gamma t ∈ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
      apply image_mono _ hband
      intro z hz
      exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    have hRt : metricScalarAt g (gamma t) ≤ 2 * metricScalarAt g v := by
      have hcoef : 1 + 4323 * eps ≤ 2 := by linarith
      exact (nk.scalar_bounds_on_image_window hwindow).2.trans
        (mul_le_mul_of_nonneg_right hcoef nk.Q_pos.le)
    have hvTube : v ∈ data.tube := by
      rw [← data.tube_eq]
      exact ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, (hmap _).trans nk.center_eq⟩
    have hbound := nk.image_slab_subset_closedBall (by norm_num) hlen hband
    have hsqrt : Real.sqrt (1 + eps) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · norm_num
      · linarith [nk.eps_small]
    have hrootv : 0 < Real.sqrt (metricScalarAt g v) := Real.sqrt_pos.mpr nk.Q_pos
    have hrootx : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr W.Q_pos
    have hedist : riemannianEDistOf g v (gamma t) ≤
        ENNReal.ofReal (112 / Real.sqrt (metricScalarAt g v)) := by
      exact hbound.trans (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)))
    -- `R(x) ≤ 4 R(v)` ⇒ `1/√R(v) ≤ 2/√R(x)`。
    have hxv : Real.sqrt (metricScalarAt g x) ≤ 2 * Real.sqrt (metricScalarAt g v) := by
      have h4 : metricScalarAt g x ≤ 4 * metricScalarAt g v := by linarith
      calc Real.sqrt (metricScalarAt g x) ≤ Real.sqrt (4 * metricScalarAt g v) :=
            Real.sqrt_le_sqrt h4
        _ = 2 * Real.sqrt (metricScalarAt g v) := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
    have h112 : 112 / Real.sqrt (metricScalarAt g v) ≤
        224 / Real.sqrt (metricScalarAt g x) := by
      rw [div_le_div_iff₀ hrootv hrootx]
      nlinarith
    have hvx : riemannianEDistOf g x v ≤
        ENNReal.ofReal (225 / Real.sqrt (metricScalarAt g x)) := by
      calc riemannianEDistOf g x v
          ≤ riemannianEDistOf g x (gamma t) + riemannianEDistOf g (gamma t) v :=
            riemannianEDistOf_triangle g _ _ _
        _ ≤ ENNReal.ofReal (1 / Real.sqrt (metricScalarAt g x)) +
              ENNReal.ofReal (224 / Real.sqrt (metricScalarAt g x)) := by
            refine add_le_add hnear.le ?_
            rw [riemannianEDistOf_comm]
            exact hedist.trans (ENNReal.ofReal_le_ofReal h112)
        _ = _ := by
            rw [← ENNReal.ofReal_add (div_nonneg zero_le_one (Real.sqrt_nonneg _))
              (div_nonneg (by norm_num) (Real.sqrt_nonneg _)), ← add_div]
            norm_num
    have hdist : metricDistance g x v ≤ 225 / Real.sqrt (metricScalarAt g x) := by
      rw [metricDistance]
      exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) hvx
    have hdeep := (deep v hvTube).trans hdist
    have : (10000 : ℝ) ≤ 225 := by
      have := (div_le_div_iff_of_pos_right hrootx).mp hdeep
      exact this
    norm_num at this

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- scaled 单位速度段在 unscaled metric 下的 `√c` 重参数化。 -/
theorem edist_reparam_of_scaled_C11SP {Z : OrientedThreeStage.{u}} (h : Z.Metric)
    {c : ℝ} (hc : 0 < c) (gamma : ℝ → Z.Carrier) {L : ℝ}
    (hmin : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      riemannianEDistOf (scaleMetric c hc h) (gamma a) (gamma b) = ENNReal.ofReal |a - b|) :
    ∀ σ ∈ Icc (0 : ℝ) (L / Real.sqrt c), ∀ τ ∈ Icc (0 : ℝ) (L / Real.sqrt c),
      riemannianEDistOf h (gamma (Real.sqrt c * σ)) (gamma (Real.sqrt c * τ)) =
        ENNReal.ofReal |σ - τ| := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hmem : ∀ σ ∈ Icc (0 : ℝ) (L / Real.sqrt c), Real.sqrt c * σ ∈ Icc (0 : ℝ) L := by
    intro σ hσ
    refine ⟨mul_nonneg hsc.le hσ.1, ?_⟩
    have := mul_le_mul_of_nonneg_left hσ.2 hsc.le
    rwa [mul_div_cancel₀ _ hsc.ne'] at this
  intro σ hσ τ hτ
  have h1 := hmin _ (hmem σ hσ) _ (hmem τ hτ)
  rw [edistOf_scale, ← mul_sub, abs_mul, abs_of_pos hsc, ENNReal.ofReal_mul hsc.le] at h1
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hsc).ne' ENNReal.ofReal_ne_top).mp h1

/-- **G2b（PROVED）**：G47 的 witness 在 near-minimizer 点上是 neck ⇒ slice 顶层 traced region。
stage / metric 以任意 HEq 表示给出（供 G1 桥使用），段数据是 scaled（因子 `c`）单位速度。 -/
theorem slice_traced_of_near_segment_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γf : ClosedBirthConstants} {C1 C2 : ℝ}
    (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    (hC1 : C1ceil_C11SC.{u} Γf ≤ C1) (hC2 : C2ceil_C11SC.{u} Γf ≤ C2) :
    ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (Z : OrientedThreeStage.{u}), s.stage = Z → ∀ h : Z.Metric, HEq s.metric h →
      ∀ (c : ℝ) (hc : 0 < c) (y : Z.Carrier) (gamma : ℝ → Z.Carrier) (L v : ℝ),
        0 < v → v < L →
        (q.neckRadius s.time ^ 2)⁻¹ < metricScalarAt h y →
        (∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
          riemannianEDistOf (scaleMetric c hc h) (gamma a) (gamma b) =
            ENNReal.ofReal |a - b|) →
        riemannianEDistOf (scaleMetric c hc h) y (gamma v) <
          ENNReal.ofReal (1 / Real.sqrt (metricScalarAt (scaleMetric c hc h) y)) →
        metricScalarAt h y ≤ 2 * metricScalarAt h (gamma v) →
        C2 * metricScalarAt h (gamma 0) < metricScalarAt h y →
        C2 * metricScalarAt h y < metricScalarAt h (gamma L) →
        ∀ yt : (s.history.stageAt ⟨s.time, s.positive.le, le_rfl⟩).Carrier, HEq yt y →
          s.history.isTracedRegion ⟨s.time, s.positive.le, le_rfl⟩ yt
            (1 / (2 * Real.sqrt (metricScalarAt h y))) (metricScalarAt h y)⁻¹
            (1200 * metricScalarAt h y) := by
  obtain ⟨T, hT⟩ := native_chosen_neck_traced_of_chain_CXSP S F hTower q hdiag hC1 hC2
  refine ⟨T, ?_⟩
  intro s hs Z hZ h hh c hc y gamma L v hv hvL hR hmin hnear hratio hleft hright yt hyt
  subst hZ
  cases hh
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hQy : 0 < metricScalarAt s.metric y :=
    lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR
  obtain ⟨W, hW, hneck⟩ := hT s hs y hR
  have hg0 : gamma (Real.sqrt c * 0) = gamma 0 := by rw [mul_zero]
  have hgv : gamma (Real.sqrt c * (v / Real.sqrt c)) = gamma v := by
    rw [mul_div_cancel₀ _ hsc.ne']
  have hgL : gamma (Real.sqrt c * (L / Real.sqrt c)) = gamma L := by
    rw [mul_div_cancel₀ _ hsc.ne']
  have hmin' := edist_reparam_of_scaled_C11SP s.metric hc gamma hmin
  have hnear' : riemannianEDistOf s.metric y (gamma (Real.sqrt c * (v / Real.sqrt c))) <
      ENNReal.ofReal (1 / Real.sqrt (metricScalarAt s.metric y)) := by
    rw [hgv]
    rw [edistOf_scale, metricScalarAt_scaleMetric] at hnear
    have hrw : 1 / Real.sqrt (c⁻¹ * metricScalarAt s.metric y) =
        Real.sqrt c * (1 / Real.sqrt (metricScalarAt s.metric y)) := by
      rw [Real.sqrt_mul (inv_nonneg.mpr hc.le), Real.sqrt_inv]
      field_simp
    rw [hrw, ENNReal.ofReal_mul hsc.le] at hnear
    refine lt_of_not_ge fun hge => ?_
    exact (not_lt.mpr (mul_le_mul' le_rfl hge)) hnear
  have hv0 : (0 : ℝ) < v / Real.sqrt c := div_pos hv hsc
  have hvL' : v / Real.sqrt c < L / Real.sqrt c := div_lt_div_of_pos_right hvL hsc
  obtain ⟨nk, hnk⟩ := W.alternative_eq_neck_of_near_minimizing_C11SP
    (gamma := fun σ => gamma (Real.sqrt c * σ)) hW Γf.epsilon_cone
    hv0 hvL' hmin' hnear' (by rw [hgv]; exact hratio) (by rw [hg0]; exact hleft)
    (by rw [hgL]; exact hright)
  exact hneck nk hnk yt hyt


section Convergence

variable {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
  {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {σ : ℕ → ℕ}
  {Φ : PointedRiemannianConvergenceMaps X L σ}

/-- canonical domain 的 metric convergence ⇒ 映射的度量上界（`PointedSegmentNecks` 的同款推导）。 -/
theorem metric_upper_of_canonical_C11SP (M : MetricConvergenceData Φ)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n) :
    ∀ K : Set L.M, IsCompact K → ∀ D : ℝ, 1 < D → ∀ᶠ n in atTop,
      ∀ y ∈ K, ∀ w : TangentSpace ThreeModel y,
        (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n y)
          (mfderiv ThreeModel ThreeModel (Φ.partialDiffeomorph n) y w)
          (mfderiv ThreeModel ThreeModel (Φ.partialDiffeomorph n) y w) ≤
            D ^ 2 * L.metric.inner y w w := by
  have hreference (n : ℕ) : (M.domain n).referenceMetric = (M.domain n).limitMetric := by
    rw [hcanonical n]
    rfl
  intro K hK D hD
  obtain ⟨N, hN⟩ := Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control
    M hreference K hK (D ^ 2 - 1) (by nlinarith)
  filter_upwards [eventually_ge_atTop N] with n hn
  intro y hy w
  have hh := (abs_le.mp ((hN n hn).2 y hy w)).2
  change (X.obj (σ n)).metric.inner (Φ.partialDiffeomorph n y)
      (mfderiv ThreeModel ThreeModel (Φ.partialDiffeomorph n) y w)
      (mfderiv ThreeModel ThreeModel (Φ.partialDiffeomorph n) y w) - L.metric.inner y w w ≤
    (D ^ 2 - 1) * L.metric.inner y w w at hh
  nlinarith

/-- 映射的极限点与逆像收敛到它的源点：scaled 距离 → 0。 -/
theorem tendsto_edist_map_of_inverse_C11SP (M : MetricConvergenceData Φ)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n)
    {x : L.M} (y : ∀ n, (X.obj (σ n)).M) (hy : ∀ᶠ n in atTop, y n ∈ Φ.target n)
    (hz : Tendsto (fun n => (Φ.partialDiffeomorph n).symm (y n)) atTop (𝓝 x)) :
    Tendsto (fun n => riemannianEDistOf (X.obj (σ n)).metric (Φ.map n x) (y n))
      atTop (𝓝 0) := by
  have hdist := Φ.tendsto_edist_map_zero (metric_upper_of_canonical_C11SP M hcanonical) hz
  apply hdist.congr'
  filter_upwards [hy] with n hn
  have hinv : Φ.partialDiffeomorph n ((Φ.partialDiffeomorph n).symm (y n)) = y n :=
    (Φ.partialDiffeomorph n).right_inv hn
  change riemannianEDistOf _ _ (Φ.partialDiffeomorph n
    ((Φ.partialDiffeomorph n).symm (y n))) = _
  rw [hinv]
  rfl

end Convergence

/-- 主体的单点代数：scaled 收敛数据给出 G2b 的五个点条件（unscaled 形）。 -/
theorem near_conditions_of_scaled_C11SP {C2 Q Rx Rg Rg0 Rgl c0 Lv : ℝ} (hQ : 0 < Q)
    (hL : max 2 (|C2| * (|c0| + 1) + 1) < Lv)
    (hx : Rx / Q ∈ Ioo (Lv - 1 / 2) (Lv + 1 / 2)) (hg : Rg / Q ∈ Ioo (Lv - 1 / 2) (Lv + 1 / 2))
    (hg0 : Rg0 / Q ∈ Ioo (c0 - 1 / 2) (c0 + 1 / 2)) (hgl : |C2| * (Lv + 1) < Rgl / Q) :
    Rx ≤ 2 * Rg ∧ C2 * Rg0 < Rx ∧ C2 * Rx < Rgl ∧ 1 < Rx / Q ∧ Rx / Q < Lv + 1 := by
  have h2 : 2 < Lv := (le_max_left _ _).trans_lt hL
  have hC : |C2| * (|c0| + 1) + 1 < Lv := (le_max_right _ _).trans_lt hL
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨h01, h02⟩ := hg0
  have hRx : Rx = Q * (Rx / Q) := by field_simp
  have hRg : Rg = Q * (Rg / Q) := by field_simp
  have hRg0 : Rg0 = Q * (Rg0 / Q) := by field_simp
  have hRgl : Rgl = Q * (Rgl / Q) := by field_simp
  have habs0 : |Rg0 / Q| ≤ |c0| + 1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le c0, le_abs_self c0]
  have habsx : |Rx / Q| ≤ Lv + 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hC2abs : 0 ≤ |C2| := abs_nonneg C2
  have hleft' : C2 * (Rg0 / Q) < Rx / Q := by
    calc C2 * (Rg0 / Q) ≤ |C2 * (Rg0 / Q)| := le_abs_self _
      _ = |C2| * |Rg0 / Q| := abs_mul _ _
      _ ≤ |C2| * (|c0| + 1) := mul_le_mul_of_nonneg_left habs0 hC2abs
      _ < Rx / Q := by linarith
  have hright' : C2 * (Rx / Q) < Rgl / Q := by
    calc C2 * (Rx / Q) ≤ |C2 * (Rx / Q)| := le_abs_self _
      _ = |C2| * |Rx / Q| := abs_mul _ _
      _ ≤ |C2| * (Lv + 1) := mul_le_mul_of_nonneg_left habsx hC2abs
      _ < Rgl / Q := hgl
  refine ⟨?_, ?_, ?_, by linarith, by linarith⟩
  · rw [hRx, hRg]
    nlinarith
  · rw [hRx, hRg0]
    nlinarith
  · rw [hRx, hRgl]
    nlinarith

/-- **G2（PROVISIONAL[hseg, hbr, hQnr]）**：hPlN′ / hneckRay 的 ray neck 子句。
`hseg` = (`ell γ hell hmin hstay hconv hhigh`)：G56 `exists_stage_escape_scalar_ray_CXSP`
的段输出沿 `Phi` 的指标；`hbr` = `t i` 为 RegularSlice 时刻 + G1 桥合同；`hQnr` = `nr⁻² ≤ Q`。 -/
theorem rayNeck_of_segment_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γf : ClosedBirthConstants} {C1 C2 : ℝ}
    (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    (hC1 : C1ceil_C11SC.{u} Γf ≤ C1) (hC2 : C2ceil_C11SC.{u} Γf ≤ C2)
    (idx : ℕ → ℕ) (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).toHistory.horizon)
    (anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
    (htlim : Tendsto (fun i => (t i : ℝ)) atTop atTop)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQnr : ∀ i, (q.neckRadius (t i) ^ 2)⁻¹ ≤ Q i)
    (sl : ℕ → RegularSlice F.observation) (hsl : ∀ i, (sl i).time = (t i : ℝ))
    (hbr : ∀ i, SliceTowerTraceAt_C11SP F (sl i) (idx i) (t i))
    (f : ℕ → ℕ) (hf : StrictMono f) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (Phi : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier
            basepoint := anchor i
            metric := scaleMetric (Q i) (hQ i)
              ((F.tower.history (idx i)).toHistory.stageMetric
                ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData Phi)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n)
    {rho : ℝ} (hrho : 0 < rho) (ray : Ico (0 : ℝ) rho → Pl.M)
    (hblow : Tendsto (fun v => metricScalarAt Pl.metric (ray v))
      (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop)
    (ell : ℕ → ℝ)
    (γ : ∀ n, ℝ → ((F.tower.history (idx (f n))).toHistory.stageAt (t (f n))).Carrier)
    (hell : Tendsto ell atTop (𝓝 rho))
    (hmin : ∀ n, ∀ v ∈ Icc (0 : ℝ) (ell n), ∀ w ∈ Icc (0 : ℝ) (ell n),
      riemannianEDistOf (scaleMetric (Q (f n)) (hQ (f n))
        ((F.tower.history (idx (f n))).toHistory.stageMetric
          ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n))))
        (γ n v) (γ n w) = ENNReal.ofReal |v - w|)
    (hstay : ∀ v : Ico (0 : ℝ) rho, ∀ᶠ n in atTop, γ n v ∈ Phi.target n)
    (hconv : ∀ v : Ico (0 : ℝ) rho,
      Tendsto (fun n => (Phi.partialDiffeomorph n).symm (γ n v)) atTop (𝓝 (ray v)))
    (hhigh : Tendsto (fun n => metricScalarAt
      ((F.tower.history (idx (f n))).toHistory.stageMetric
        ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n)))
      (γ n (ell n)) / Q (f n)) atTop atTop) :
    ∀ times : ℕ → Ico (0 : ℝ) rho, Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho) →
      ∀ᶠ m in atTop, ∀ᶠ i in atTop,
        (F.tower.history (idx (f i))).toHistory.isTracedRegion (t (f i))
          (Phi.map i (ray (times m)))
          (1 / (2 * Real.sqrt (metricScalarAt
            ((F.tower.history (idx (f i))).toHistory.stageMetric
              ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
            (Phi.map i (ray (times m))))))
          (metricScalarAt ((F.tower.history (idx (f i))).toHistory.stageMetric
              ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
            (Phi.map i (ray (times m))))⁻¹
          (1200 * metricScalarAt ((F.tower.history (idx (f i))).toHistory.stageMetric
              ((F.tower.history (idx (f i))).toHistory.activeStage (t (f i))) (t (f i)))
            (Phi.map i (ray (times m)))) := by
  obtain ⟨T, hT⟩ := slice_traced_of_near_segment_C11SP S F hTower q hdiag hC1 hC2
  intro times htimes
  have htimes' : Tendsto times atTop (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) :=
    tendsto_comap_iff.mpr htimes
  let G : ∀ n, ((F.tower.history (idx (f n))).toHistory.stageAt (t (f n))).Metric :=
    fun n => (F.tower.history (idx (f n))).toHistory.stageMetric
      ((F.tower.history (idx (f n))).toHistory.activeStage (t (f n))) (t (f n))
  have hnorm (n : ℕ) (z : ((F.tower.history (idx (f n))).toHistory.stageAt (t (f n))).Carrier) :
      metricScalarAt (scaleMetric (Q (f n)) (hQ (f n)) (G n)) z =
        metricScalarAt (G n) z / Q (f n) := by
    rw [metricScalarAt_scaleMetric, inv_mul_eq_div]
  have hsx (v : Ico (0 : ℝ) rho) : Tendsto (fun n => metricScalarAt (G n) (Phi.map n (ray v)) /
      Q (f n)) atTop (𝓝 (metricScalarAt Pl.metric (ray v))) := by
    have h := Perelman.KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
      M hcanonical (ray v)
    exact h.congr fun n => hnorm n _
  have hsg (v : Ico (0 : ℝ) rho) : Tendsto (fun n => metricScalarAt (G n) (γ n v) /
      Q (f n)) atTop (𝓝 (metricScalarAt Pl.metric (ray v))) := by
    have h := pointedScalar_tendsto_of_inverse_tendsto M hcanonical (fun n => γ n v)
      (hstay v) (hconv v)
    exact h.congr fun n => hnorm n _
  have hdist (v : Ico (0 : ℝ) rho) : Tendsto (fun n => riemannianEDistOf
      (scaleMetric (Q (f n)) (hQ (f n)) (G n)) (Phi.map n (ray v)) (γ n v)) atTop (𝓝 0) :=
    tendsto_edist_map_of_inverse_C11SP M hcanonical (fun n => γ n v) (hstay v) (hconv v)
  let v0 : Ico (0 : ℝ) rho := ⟨0, le_rfl, hrho⟩
  let c0 : ℝ := metricScalarAt Pl.metric (ray v0)
  have hvpos : ∀ᶠ v : Ico (0 : ℝ) rho in comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
      0 < (v : ℝ) :=
    (tendsto_comap : Tendsto (Subtype.val : Ico (0 : ℝ) rho → ℝ) _ (𝓝 rho)).eventually
      (Ioi_mem_nhds hrho)
  have hev : ∀ᶠ v : Ico (0 : ℝ) rho in comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
      ∀ᶠ n in atTop,
        (F.tower.history (idx (f n))).toHistory.isTracedRegion (t (f n)) (Phi.map n (ray v))
          (1 / (2 * Real.sqrt (metricScalarAt (G n) (Phi.map n (ray v)))))
          (metricScalarAt (G n) (Phi.map n (ray v)))⁻¹
          (1200 * metricScalarAt (G n) (Phi.map n (ray v))) := by
    filter_upwards [hblow.eventually_gt_atTop (max 2 (|C2| * (|c0| + 1) + 1)), hvpos]
      with v hv hv0
    set Lv := metricScalarAt Pl.metric (ray v) with hLv
    have hL2 : 2 < Lv := (le_max_left _ _).trans_lt hv
    have hLpos : 0 < Lv + 1 := by linarith
    have hroot : 0 < Real.sqrt (Lv + 1) := Real.sqrt_pos.mpr hLpos
    filter_upwards [(hsx v).eventually (Ioo_mem_nhds (show Lv - 1 / 2 < Lv by linarith)
        (show Lv < Lv + 1 / 2 by linarith)),
      (hsg v).eventually (Ioo_mem_nhds (show Lv - 1 / 2 < Lv by linarith)
        (show Lv < Lv + 1 / 2 by linarith)),
      (hsg v0).eventually (Ioo_mem_nhds (show c0 - 1 / 2 < c0 by linarith)
        (show c0 < c0 + 1 / 2 by linarith)),
      hhigh.eventually_gt_atTop (|C2| * (Lv + 1)),
      (hdist v).eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (div_pos one_pos hroot))),
      hell.eventually_const_lt v.property.2,
      ((htlim.comp hf.tendsto_atTop).eventually_ge_atTop T : ∀ᶠ n in atTop, T ≤ (t (f n) : ℝ))]
      with n hx hg hg0 hgl hd hvell hTn
    obtain ⟨h1, h2, h3, h4, h5⟩ := near_conditions_of_scaled_C11SP (Q := Q (f n)) (hQ (f n))
      hv hx hg hg0 hgl
    have hQx : Q (f n) < metricScalarAt (G n) (Phi.map n (ray v)) :=
      (one_lt_div (hQ (f n))).mp h4
    have hR : (q.neckRadius (sl (f n)).time ^ 2)⁻¹ <
        metricScalarAt (G n) (Phi.map n (ray v)) := by
      rw [hsl]
      exact (hQnr (f n)).trans_lt hQx
    have hpos : 0 < metricScalarAt (G n) (Phi.map n (ray v)) / Q (f n) := by linarith
    have hnear : riemannianEDistOf (scaleMetric (Q (f n)) (hQ (f n)) (G n)) (Phi.map n (ray v))
        (γ n v) < ENNReal.ofReal (1 / Real.sqrt (metricScalarAt
          (scaleMetric (Q (f n)) (hQ (f n)) (G n)) (Phi.map n (ray v)))) := by
      rw [hnorm]
      refine hd.trans_le (ENNReal.ofReal_le_ofReal ?_)
      apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos)
      exact Real.sqrt_le_sqrt h5.le
    have hTs : T ≤ (sl (f n)).time := by
      rw [hsl]
      exact hTn
    obtain ⟨hZ, hh, htr⟩ := hbr (f n)
    have key := hT (sl (f n)) hTs _ hZ _ hh (Q (f n)) (hQ (f n)) (Phi.map n (ray v)) (γ n)
      (ell n) v hv0 hvell hR (hmin n) hnear h1 h2 h3
    exact htr (cast (congrArg OrientedThreeStage.Carrier hZ.symm) (Phi.map n (ray v)))
      (Phi.map n (ray v)) (cast_heq _ _) _ _ _ (fun xt hxt => key xt (hxt.trans (cast_heq _ _)))
  exact htimes'.eventually hev


/-- **G2 consumer（PROVISIONAL[hPlSeg]）**：NATIVE-NJ G4 的 `hPlN′` 退为 (a) 分量 + 本车道的段 / slice 数据。
`hPlSeg` = `hPlN′` 的 (a) 分量（十条 + 第一层数据 + canonical，逐字）∧ `r' < nr(t')` ∧ slices + G1 桥合同
∧ G56 段数据沿 `Phi` 的指标；(b) ray neck 子句由 `rayNeck_of_segment_C11SP` 支付。 -/
theorem hPlN'_of_PlSeg_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hPlSeg :
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
          {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
          (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
          (q : CutoffParameters), F.tower = S.tower →
          (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
            q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
          pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
          2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
          ε ≤ coneAccuracy →
          C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
        ∀ A : ℝ, 0 < A →
        ∀ idx : ℕ → ℕ,
        let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
          (∀ i, (s i).time = (t i : ℝ)) →
        ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, x i ∈ riemannianBallOf
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
          Tendsto (fun i => (t i : ℝ)) atTop atTop →
          Tendsto (fun i => metricScalarAt
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
          (∀ i, r i < q.neckRadius (t i)) →
          Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
          Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
        ∃ (rho : ℝ) (hrho : 0 < rho),
          ∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
          let _ : EMetricSpace Pl.M := Pl.emetricSpace
          ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
            (metricScalarAt Pl.metric Pl.basepoint = 1 ∧
             (∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
               algebraicCurvatureOperatorNonnegativeCone) ∧
             (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
             (∀ R : ℝ, 0 ≤ R → R < rho →
               IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
             Isometry ray ∧ ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
             Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
               (cocompact Pl.M) ∧
             (∀ y : Pl.M, ¬ Tendsto ray
               (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 y)) ∧
             Tendsto (fun v => metricScalarAt Pl.metric (ray v))
               (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop ∧
             ∀ᶠ v : Ico (0 : ℝ) rho in
                 comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
               Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v))) ∧
            ∃ (A' : ℝ) (_ : 0 < A') (Hbase : ℝ) (_ : 4 ≤ Hbase)
              (_ : rho + 2 ≤ A' * Real.sqrt Hbase + 3) (idx' : ℕ → ℕ)
              (t' : ∀ i, Icc (0 : ℝ) (F.tower.history (idx' i)).toHistory.horizon)
              (p' anchor : ∀ i, ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier)
              (r' : ℕ → ℝ) (_ : ∀ i, 0 < r' i) (_ : Tendsto (fun i => (t' i : ℝ)) atTop atTop)
              (_ : ∀ i, 2 * r' i ^ 2 < (t' i : ℝ))
              (_ : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx' i)).toHistory (t' i)
                (p' i) (r' i))
              (_ : ∀ i, ENNReal.ofReal (A'⁻¹ * r' i ^ 3) ≤
                ballVolume ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i) (r' i))
              (_ : ∀ i, riemannianEDistOf ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i)
                  (anchor i) ≤ ENNReal.ofReal (A' * r' i))
              (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (_ : ∀ i, Q i = Hbase * (r' i ^ 2)⁻¹)
              (f : ℕ → ℕ) (_ : StrictMono f)
              (Phi : PointedRiemannianConvergenceMaps
                ({ obj := fun i =>
                    { M := ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier
                      basepoint := anchor i
                      metric := scaleMetric (Q i) (hQ i)
                        ((F.tower.history (idx' i)).toHistory.stageMetric
                          ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) } } :
                  PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
              (M : MetricConvergenceData Phi),
              (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) ∧
              (∀ i, r' i < q.neckRadius (t' i)) ∧
              (∃ sl : ℕ → RegularSlice F.observation, (∀ i, (sl i).time = (t' i : ℝ)) ∧
                ∀ i, SliceTowerTraceAt_C11SP F (sl i) (idx' i) (t' i)) ∧
              ∃ (ell : ℕ → ℝ) (γ : ∀ n, ℝ →
                  ((F.tower.history (idx' (f n))).toHistory.stageAt (t' (f n))).Carrier),
                Tendsto ell atTop (𝓝 rho) ∧
                (∀ n, ∀ v ∈ Icc (0 : ℝ) (ell n), ∀ w ∈ Icc (0 : ℝ) (ell n),
                  riemannianEDistOf (scaleMetric (Q (f n)) (hQ (f n))
                    ((F.tower.history (idx' (f n))).toHistory.stageMetric
                      ((F.tower.history (idx' (f n))).toHistory.activeStage (t' (f n)))
                      (t' (f n)))) (γ n v) (γ n w) = ENNReal.ofReal |v - w|) ∧
                (∀ v : Ico (0 : ℝ) rho, ∀ᶠ n in atTop, γ n v ∈ Phi.target n) ∧
                (∀ v : Ico (0 : ℝ) rho, Tendsto (fun n => (Phi.partialDiffeomorph n).symm (γ n v))
                  atTop (𝓝 (ray v))) ∧
                Tendsto (fun n => metricScalarAt
                  ((F.tower.history (idx' (f n))).toHistory.stageMetric
                    ((F.tower.history (idx' (f n))).toHistory.activeStage (t' (f n))) (t' (f n)))
                  (γ n (ell n)) / Q (f n)) atTop atTop) :
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
          {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
          (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
          (q : CutoffParameters), F.tower = S.tower →
          (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
            q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
          pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
          2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
          ε ≤ coneAccuracy →
          C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
        ∀ A : ℝ, 0 < A →
        ∀ idx : ℕ → ℕ,
        let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
          (∀ i, (s i).time = (t i : ℝ)) →
        ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, x i ∈ riemannianBallOf
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
          Tendsto (fun i => (t i : ℝ)) atTop atTop →
          Tendsto (fun i => metricScalarAt
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
          (∀ i, r i < q.neckRadius (t i)) →
          Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
          Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
        ∃ (rho : ℝ) (hrho : 0 < rho),
          ∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
          let _ : EMetricSpace Pl.M := Pl.emetricSpace
          ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
            (metricScalarAt Pl.metric Pl.basepoint = 1 ∧
             (∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
               algebraicCurvatureOperatorNonnegativeCone) ∧
             (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
             (∀ R : ℝ, 0 ≤ R → R < rho →
               IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
             Isometry ray ∧ ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
             Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
               (cocompact Pl.M) ∧
             (∀ y : Pl.M, ¬ Tendsto ray
               (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 y)) ∧
             Tendsto (fun v => metricScalarAt Pl.metric (ray v))
               (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop ∧
             ∀ᶠ v : Ico (0 : ℝ) rho in
                 comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
               Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v))) ∧
            ∃ (A' : ℝ) (_ : 0 < A') (Hbase : ℝ) (_ : 4 ≤ Hbase)
              (_ : rho + 2 ≤ A' * Real.sqrt Hbase + 3) (idx' : ℕ → ℕ)
              (t' : ∀ i, Icc (0 : ℝ) (F.tower.history (idx' i)).toHistory.horizon)
              (p' anchor : ∀ i, ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier)
              (r' : ℕ → ℝ) (_ : ∀ i, 0 < r' i) (_ : Tendsto (fun i => (t' i : ℝ)) atTop atTop)
              (_ : ∀ i, 2 * r' i ^ 2 < (t' i : ℝ))
              (_ : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx' i)).toHistory (t' i)
                (p' i) (r' i))
              (_ : ∀ i, ENNReal.ofReal (A'⁻¹ * r' i ^ 3) ≤
                ballVolume ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i) (r' i))
              (_ : ∀ i, riemannianEDistOf ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i)
                  (anchor i) ≤ ENNReal.ofReal (A' * r' i))
              (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (_ : ∀ i, Q i = Hbase * (r' i ^ 2)⁻¹)
              (f : ℕ → ℕ) (_ : StrictMono f)
              (Phi : PointedRiemannianConvergenceMaps
                ({ obj := fun i =>
                    { M := ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier
                      basepoint := anchor i
                      metric := scaleMetric (Q i) (hQ i)
                        ((F.tower.history (idx' i)).toHistory.stageMetric
                          ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) } } :
                  PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
              (M : MetricConvergenceData Phi),
              (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) ∧
              ∀ times : ℕ → Ico (0 : ℝ) rho, Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho) →
                ∀ᶠ m in atTop, ∀ᶠ i in atTop,
                  (F.tower.history (idx' (f i))).toHistory.isTracedRegion (t' (f i))
                    (Phi.map i (ray (times m)))
                    (1 / (2 * Real.sqrt (metricScalarAt
                      ((F.tower.history (idx' (f i))).toHistory.stageMetric
                        ((F.tower.history (idx' (f i))).toHistory.activeStage (t' (f i)))
                        (t' (f i))) (Phi.map i (ray (times m))))))
                    (metricScalarAt ((F.tower.history (idx' (f i))).toHistory.stageMetric
                        ((F.tower.history (idx' (f i))).toHistory.activeStage (t' (f i)))
                        (t' (f i))) (Phi.map i (ray (times m))))⁻¹
                    (1200 * metricScalarAt ((F.tower.history (idx' (f i))).toHistory.stageMetric
                        ((F.tower.history (idx' (f i))).toHistory.activeStage (t' (f i)))
                        (t' (f i))) (Phi.map i (ray (times m)))) := by
  obtain ⟨ε₀, hε₀, h⟩ := hPlSeg
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hcore hε hC1 hC2 A hA idx H t s hs
    p x r htime hsmall hvol hx htlim hblowx hnr hrnr hrt
  obtain ⟨rho, hrho, Pl, ray, hten, A', hA', Hbase, hHbase, hfit, idx', t', p', anchor, r', hr',
    ht', htime', hsmall', hvol', hanchor', Q, hQ, hQdef, f, hf, Phi, M, hcan, hnr', hsl,
    ell, γ, hell, hmin, hstay, hconv, hhigh⟩ := h S F q hTower hdiag hacc hrad hord hcore hε hC1
    hC2 A hA idx t s hs p x r htime hsmall hvol hx htlim hblowx hnr hrnr hrt
  obtain ⟨sl, hsl, hbr⟩ := hsl
  have hQnr (i : ℕ) : (q.neckRadius (t' i) ^ 2)⁻¹ ≤ Q i := by
    rw [hQdef i]
    have hr0 := hr' i
    have hlt : r' i ^ 2 < q.neckRadius (t' i) ^ 2 := by
      have := hnr' i
      nlinarith
    have h1 : (q.neckRadius (t' i) ^ 2)⁻¹ ≤ (r' i ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hlt.le
    have h2 : (r' i ^ 2)⁻¹ ≤ Hbase * (r' i ^ 2)⁻¹ :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    exact h1.trans h2
  refine ⟨rho, hrho, Pl, ray, hten, A', hA', Hbase, hHbase, hfit, idx', t', p', anchor, r', hr',
    ht', htime', hsmall', hvol', hanchor', Q, hQ, hQdef, f, hf, Phi, M, hcan, ?_⟩
  exact rayNeck_of_segment_C11SP S F hTower q (fun t ht => (hdiag t ht).2) hC1 hC2 idx' t' anchor
    ht' Q hQ hQnr sl hsl hbr f hf Pl Phi M hcan hrho ray hten.2.2.2.2.2.2.2.2.1 ell γ hell hmin
    hstay hconv hhigh

/-- consumer：`hPlSeg` ⇒ `hnzero`（经 NATIVE-NJ G4 `native_hnzero_of_PlData_C11SP`）。 -/
theorem native_hnzero_of_PlSeg_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hPlSeg :
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
          {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
          (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
          (q : CutoffParameters), F.tower = S.tower →
          (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
            q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
          pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
          2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
          ε ≤ coneAccuracy →
          C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
        ∀ A : ℝ, 0 < A →
        ∀ idx : ℕ → ℕ,
        let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
          (∀ i, (s i).time = (t i : ℝ)) →
        ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, x i ∈ riemannianBallOf
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
          Tendsto (fun i => (t i : ℝ)) atTop atTop →
          Tendsto (fun i => metricScalarAt
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
          (∀ i, r i < q.neckRadius (t i)) →
          Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
          Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
        ∃ (rho : ℝ) (hrho : 0 < rho),
          ∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
          let _ : EMetricSpace Pl.M := Pl.emetricSpace
          ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
            (metricScalarAt Pl.metric Pl.basepoint = 1 ∧
             (∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
               algebraicCurvatureOperatorNonnegativeCone) ∧
             (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
             (∀ R : ℝ, 0 ≤ R → R < rho →
               IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
             Isometry ray ∧ ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
             Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
               (cocompact Pl.M) ∧
             (∀ y : Pl.M, ¬ Tendsto ray
               (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 y)) ∧
             Tendsto (fun v => metricScalarAt Pl.metric (ray v))
               (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop ∧
             ∀ᶠ v : Ico (0 : ℝ) rho in
                 comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
               Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v))) ∧
            ∃ (A' : ℝ) (_ : 0 < A') (Hbase : ℝ) (_ : 4 ≤ Hbase)
              (_ : rho + 2 ≤ A' * Real.sqrt Hbase + 3) (idx' : ℕ → ℕ)
              (t' : ∀ i, Icc (0 : ℝ) (F.tower.history (idx' i)).toHistory.horizon)
              (p' anchor : ∀ i, ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier)
              (r' : ℕ → ℝ) (_ : ∀ i, 0 < r' i) (_ : Tendsto (fun i => (t' i : ℝ)) atTop atTop)
              (_ : ∀ i, 2 * r' i ^ 2 < (t' i : ℝ))
              (_ : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx' i)).toHistory (t' i)
                (p' i) (r' i))
              (_ : ∀ i, ENNReal.ofReal (A'⁻¹ * r' i ^ 3) ≤
                ballVolume ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i) (r' i))
              (_ : ∀ i, riemannianEDistOf ((F.tower.history (idx' i)).toHistory.stageMetric
                  ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) (p' i)
                  (anchor i) ≤ ENNReal.ofReal (A' * r' i))
              (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (_ : ∀ i, Q i = Hbase * (r' i ^ 2)⁻¹)
              (f : ℕ → ℕ) (_ : StrictMono f)
              (Phi : PointedRiemannianConvergenceMaps
                ({ obj := fun i =>
                    { M := ((F.tower.history (idx' i)).toHistory.stageAt (t' i)).Carrier
                      basepoint := anchor i
                      metric := scaleMetric (Q i) (hQ i)
                        ((F.tower.history (idx' i)).toHistory.stageMetric
                          ((F.tower.history (idx' i)).toHistory.activeStage (t' i)) (t' i)) } } :
                  PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
              (M : MetricConvergenceData Phi),
              (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData Phi n) ∧
              (∀ i, r' i < q.neckRadius (t' i)) ∧
              (∃ sl : ℕ → RegularSlice F.observation, (∀ i, (sl i).time = (t' i : ℝ)) ∧
                ∀ i, SliceTowerTraceAt_C11SP F (sl i) (idx' i) (t' i)) ∧
              ∃ (ell : ℕ → ℝ) (γ : ∀ n, ℝ →
                  ((F.tower.history (idx' (f n))).toHistory.stageAt (t' (f n))).Carrier),
                Tendsto ell atTop (𝓝 rho) ∧
                (∀ n, ∀ v ∈ Icc (0 : ℝ) (ell n), ∀ w ∈ Icc (0 : ℝ) (ell n),
                  riemannianEDistOf (scaleMetric (Q (f n)) (hQ (f n))
                    ((F.tower.history (idx' (f n))).toHistory.stageMetric
                      ((F.tower.history (idx' (f n))).toHistory.activeStage (t' (f n)))
                      (t' (f n)))) (γ n v) (γ n w) = ENNReal.ofReal |v - w|) ∧
                (∀ v : Ico (0 : ℝ) rho, ∀ᶠ n in atTop, γ n v ∈ Phi.target n) ∧
                (∀ v : Ico (0 : ℝ) rho, Tendsto (fun n => (Phi.partialDiffeomorph n).symm (γ n v))
                  atTop (𝓝 (ray v))) ∧
                Tendsto (fun n => metricScalarAt
                  ((F.tower.history (idx' (f n))).toHistory.stageMetric
                    ((F.tower.history (idx' (f n))).toHistory.activeStage (t' (f n))) (t' (f n)))
                  (γ n (ell n)) / Q (f n)) atTop atTop) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
        ε ≤ coneAccuracy →
        C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
      ∀ A : ℝ, 0 < A →
      ∀ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
        (∀ i, (s i).time = (t i : ℝ)) →
      ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
        Tendsto (fun i => (t i : ℝ)) atTop atTop →
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
        (∀ i, r i < q.neckRadius (t i)) →
        Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
      False :=
  native_hnzero_of_PlData_C11SP P g (hPlN'_of_PlSeg_C11SP P g hPlSeg)

end GC.LongTime.Ch11

end
