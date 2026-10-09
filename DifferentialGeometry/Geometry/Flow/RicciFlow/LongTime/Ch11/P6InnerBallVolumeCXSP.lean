import DifferentialGeometry.Geometry.Comparison.Volume.BallChainVolumeCXSP
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciPointwise
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CompactBallChainCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalScalarGapVolumeCXSP

set_option autoImplicit false

/-!
# CX-SPINE G11：有限曲率域内从基点传播全部内球中心体积

N 先于 stage/metric/测试点选定，沿原 S 闭球内的实际链逐次使用 local Bishop–Gromov。
每个 2δ 球包含于 B(p,S+2δ)，故适用于任意正厚度的有限 escape buffer。
canonical-base consumer 用 G10 实际生产基点 volume，再得到全部内球中心（可低曲率）的下界。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 只在 S+2δ 球控制 Ricci，即可由基点 δ 球体积控制全部 S 内球中心。 -/
theorem exists_inner_ball_volume_ratio_CXSP {S δ q : ℝ}
    (hS : 0 ≤ S) (hδ : 0 < δ) (hq : 0 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ {P : OrientedThreeStage.{u}} (g : P.Metric) (p : P.Carrier),
      (∀ z ∈ riemannianBallOf g p (S + 2 * δ), ∀ w : TangentSpace ThreeModel z,
        -(2 * q ^ 2) * g.inner z w w ≤ ricciTensor g z w w) →
      ∀ x ∈ riemannianClosedBallOf g p S,
        ENNReal.ofReal c * ballVolume g p δ ≤ ballVolume g x δ := by
  obtain ⟨N, -, hchain⟩ := exists_uniform_compact_ball_chain_CXSP.{u} hS hδ
  let c₀ := Real.exp (-2 * q * 2 * δ) / (4 : ℝ) ^ 3
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀ ^ N, pow_pos hc₀ N, ?_⟩
  intro P g p hRic x hx
  obtain ⟨points, hstart, hend, hinside, hstep⟩ := hchain g p x hx
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hlocal : ∀ k < N, ∀ z ∈ riemannianBallOf g (points (k + 1)) (2 * δ),
      ∀ w : TangentSpace ThreeModel z,
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * q ^ 2) * g.inner z w w ≤
        ricciTensor g z w w := by
    intro k hk z hz w
    have hcenter := hinside (k + 1) (Nat.succ_le_of_lt hk)
    have hpz : z ∈ riemannianBallOf g p (S + 2 * δ) := by
      change riemannianEDistOf g p z < ENNReal.ofReal (S + 2 * δ)
      calc
        _ ≤ riemannianEDistOf g p (points (k + 1)) +
            riemannianEDistOf g (points (k + 1)) z := riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal S + ENNReal.ofReal (2 * δ) :=
          ENNReal.add_lt_add_of_le_of_lt
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcenter) hcenter hz
        _ = _ := (ENNReal.ofReal_add hS (by positivity)).symm
    simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin,
      Nat.reduceSub, Nat.cast_ofNat] using hRic z hpz w
  have hvol := ball_volume_lower_of_chain_CXSP g (RiemannianMetricComplete.of_compact g)
    points N hq hδ hstep hlocal
  simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    Nat.cast_ofNat, hstart, hend, c₀, ballVolume] using hvol

/-- canonical 基点和同分支 scalar gap 支付基点体积，内球测试中心无需 canonical 或高曲率。 -/
theorem exists_inner_ball_volume_of_canonical_base_CXSP (ε C1 C2 : ℝ) {S δ q : ℝ}
    (hS : 0 ≤ S) (hδ : 0 < δ) (hq : 0 ≤ q) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {p : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 p), W.capTubeHasNeckChart ε →
      ∀ y ∈ connectedComponent p, C2 * metricScalarAt g y < metricScalarAt g p →
      δ ^ 4 * normSq0S g p 4 (metricRm04At g p) ≤ 1 →
      (∀ z ∈ riemannianBallOf g p (S + 2 * δ), ∀ w : TangentSpace ThreeModel z,
        -(2 * q ^ 2) * g.inner z w w ≤ ricciTensor g z w w) →
      ∀ x ∈ riemannianClosedBallOf g p S,
        ENNReal.ofReal (κ * δ ^ 3) ≤ ballVolume g x δ := by
  obtain ⟨κ₀, hκ₀, hbase⟩ :=
    exists_ball_volume_of_spatialCanonicalWitness_of_scalar_gap_CXSP.{u} ε C1 C2
  obtain ⟨c, hc, hratio⟩ := exists_inner_ball_volume_ratio_CXSP.{u} hS hδ hq
  refine ⟨c * κ₀, mul_pos hc hκ₀, ?_⟩
  intro P g p W hchart y hy hgap hcurv hRic x hx
  have hv := hbase W hchart y hy hgap δ hδ hcurv
  calc
    _ = ENNReal.ofReal c * ENNReal.ofReal (κ₀ * δ ^ 3) := by
      rw [← ENNReal.ofReal_mul hc.le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal c * ballVolume g p δ := mul_le_mul' le_rfl hv
    _ ≤ _ := hratio g p hRic x hx

/-- canonical 基点与较大内球的曲率界生产 compactness 所需的统一半径及全中心 volume。 -/
theorem exists_inner_ball_volume_of_canonical_curvature_CXSP (ε C1 C2 : ℝ)
    {S R J C : ℝ} (hS : 0 ≤ S) (hSR : S < R) (hJ : 0 ≤ J) (hC : 0 ≤ C) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ S + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {p : P.Carrier}
        (W : SpatialCanonicalWitness g ε C1 C2 p), W.capTubeHasNeckChart ε →
        ∀ y ∈ connectedComponent p, C2 * metricScalarAt g y < metricScalarAt g p →
        (∀ z ∈ riemannianClosedBallOf g p R,
          Real.sqrt (normSq0S g z 4 (metricRm04At g z)) ≤ J) →
        ∀ x ∈ riemannianClosedBallOf g p S,
          ENNReal.ofReal (κ * a ^ 3) ≤ ballVolume g x a := by
  have hgapR : 0 < R - S := sub_pos.mpr hSR
  let a := min ((R - S) / 4) (min 1 (1 / (J + C + 1)))
  have ha : 0 < a := by dsimp [a]; positivity
  have haR : a ≤ (R - S) / 4 := min_le_left _ _
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have haden : a ≤ 1 / (J + C + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hamul : a * (J + C + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp haden
  have hasq : a ^ 2 ≤ a := by nlinarith
  have hbudget (B : ℝ) (hB : 0 ≤ B) (hBsum : B ≤ J + C + 1) : a ^ 4 * B ^ 2 ≤ 1 := by
    have h1 : a ^ 2 * B ≤ 1 :=
      (mul_le_mul_of_nonneg_right hasq hB).trans
        ((mul_le_mul_of_nonneg_left hBsum ha.le).trans hamul)
    have h2 := pow_le_pow_left₀ (mul_nonneg (sq_nonneg a) hB) h1 2
    nlinarith only [h2]
  have haJ := hbudget J hJ (by linarith)
  have haC := hbudget C hC (by linarith)
  let q := 3 * Real.sqrt J
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq2 : q ^ 2 = 9 * J := by dsimp [q]; rw [mul_pow, Real.sq_sqrt hJ]; norm_num
  obtain ⟨κ, hκ, hvol⟩ := exists_inner_ball_volume_of_canonical_base_CXSP.{u}
    ε C1 C2 hS ha hq
  refine ⟨a, κ, ha, hκ, by linarith, haC, ?_⟩
  intro P g p W hchart y hy hgap hRm x hx
  have hpR : p ∈ riemannianClosedBallOf g p R := by
    change riemannianEDistOf g p p ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact bot_le
  have hbase := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hRm p hpR) 2
  rw [Real.sq_sqrt (normSq0S_nonneg _ _ _ _)] at hbase
  have hcurv : a ^ 4 * normSq0S g p 4 (metricRm04At g p) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hbase (pow_nonneg ha.le 4)).trans haJ
  apply hvol W hchart y hy hgap hcurv ?_ x hx
  intro z hz w
  have hzR : z ∈ riemannianClosedBallOf g p R :=
    hz.le.trans (ENNReal.ofReal_le_ofReal (by linarith : S + 2 * a ≤ R))
  have hRic := Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm g (hRm z hzR) w
  have hi : 0 ≤ g.inner z w w := by
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · exact (g.pos z w hw).le
  have hRic' : -(9 * J) * g.inner z w w ≤ ricciTensor g z w w := by
    simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
      show (3 : ℝ) ^ 2 = 9 by norm_num] using hRic
  rw [hq2]
  exact (mul_le_mul_of_nonneg_right (by linarith : -(2 * (9 * J)) ≤ -(9 * J)) hi).trans hRic'

end GC.LongTime.Ch11
