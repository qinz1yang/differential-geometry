import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialBoundedCurvatureAtDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StageBallVolumeRatio

/-!
# S-CH11-FIX5 port of astra `WholeCanonicalComponentSeedVolume`（`PortC11P`）

来源：donor `WholeCanonicalComponentSeedVolume.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（`linarith failed`，系数比较一步）。

本 port 只有 elaboration 层面修补（no statement / definition / proof idea altered）：
* `hcoef` 的最后一步 `nlinarith only [hdiv]` 之前补两个 `ring` 等式把 `9 * (3 * C2 ^ 2 / r ^ 2)`
  与 `2 * (36 * (C2 + 1) ^ 2 / r ^ 2)` 改写成 `hdiv` 的两侧，再 `linarith`
  （`norm_num` 之后目标里是 `9 * (3 * C2 ^ 2 / r ^ 2)`，`linarith` 把它与 `hdiv` 里的
  `27 * C2 ^ 2 / r ^ 2` 当作不同原子，所以显式给出两条 `ring` 等式）。

原路径 `WholeCanonicalComponentSeedVolume` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private local instance wholeCanonicalThreeSpaceNeZero :
    NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

/-- Transfer the actual seed volume within one whole canonical component, using
the same metric and the general Ricci-lower Bishop comparison. -/
theorem exists_ball_volume_lower_of_whole_canonical_component_and_seed
    (ε C1 C2 A : ℝ) (hA : 0 < A) :
    ∃ κ : ℝ, 0 < κ ∧
    ∀ {P : OrientedThreeStage.{u}} (g : P.Metric) (p x : P.Carrier)
      (r ρ : ℝ), 0 < r → 0 < ρ → ρ ≤ r →
      x ∈ riemannianBallOf g p (A * r) →
      metricScalarAt g p ≤ 3 / r ^ 2 →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p r) →
      ∀ W : SpatialCanonicalWitness g ε C1 C2 x,
        W.alternative.isWholeComponent →
        ENNReal.ofReal (κ * ρ ^ 3) ≤
          riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x ρ) := by
  let κ : ℝ := Real.exp (-12 * (C2 + 1) * (A + 1)) / (8 * A * (A + 1) ^ 3)
  refine ⟨κ, by dsimp [κ]; positivity, ?_⟩
  intro P g p x r ρ hr hρ hρr hx hseedScalar hseedVolume W hwhole
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have hxp : riemannianEDistOf g x p < ENNReal.ofReal (A * r) := by
    rw [riemannianEDistOf_comm]
    exact hx
  have hxpTop : riemannianEDistOf g x p < ⊤ :=
    hxp.trans ENNReal.ofReal_lt_top
  have hscalarLower : C2⁻¹ * metricScalarAt g x ≤ 3 / r ^ 2 :=
    (W.scalar_bounds_of_isWholeComponent hwhole hxpTop).1.trans hseedScalar
  have hscalar : metricScalarAt g x ≤ 3 * C2 / r ^ 2 := by
    calc
      metricScalarAt g x = C2 * (C2⁻¹ * metricScalarAt g x) := by
        rw [← mul_assoc, mul_inv_cancel₀ hC2pos.ne', one_mul]
      _ ≤ C2 * (3 / r ^ 2) := mul_le_mul_of_nonneg_left hscalarLower hC2pos.le
      _ = 3 * C2 / r ^ 2 := by ring
  let R : ℝ := (A + 1) * r
  have hrR : r < R := by
    dsimp [R]
    nlinarith [mul_pos hA hr]
  have hR : 0 < R := hr.trans hrR
  have hρR : ρ ≤ R := hρr.trans hrR.le
  have hRm : ∀ y ∈ riemannianBallOf g x R,
      Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ 3 * C2 ^ 2 / r ^ 2 := by
    intro y hy
    have hyTop : riemannianEDistOf g x y < ⊤ :=
      (show riemannianEDistOf g x y < ENNReal.ofReal R from hy).trans
        ENNReal.ofReal_lt_top
    have hyDomain : y ∈ W.domain.carrier := by
      rw [W.alternative.eq_connectedComponent_of_isWholeComponent hwhole]
      exact mem_connectedComponent_of_riemannianEDistOf_lt_top g hyTop
    calc
      Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ C2 * metricScalarAt g x :=
        W.rm_bound y hyDomain
      _ ≤ C2 * (3 * C2 / r ^ 2) := mul_le_mul_of_nonneg_left hscalar hC2pos.le
      _ = 3 * C2 ^ 2 / r ^ 2 := by ring
  let q : ℝ := 6 * (C2 + 1) / r
  have hq : 0 < q := by dsimp [q]; positivity
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  have hRic : ∀ y ∈ riemannianBallOf g x R, ∀ v : TangentSpace ThreeModel y,
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y v v ≤
        ricciTensor (I := ThreeModel) g y v v := by
    intro y hy v
    have hlow := Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm
      (I := ThreeModel) g (hRm y hy) v
    have hinner : 0 ≤ g.inner y v v := by
      rcases eq_or_ne v 0 with hv | hv
      · subst v
        simp
      · exact (g.pos y v hv).le
    have hq2 : q ^ 2 = 36 * (C2 + 1) ^ 2 / r ^ 2 := by
      dsimp [q]
      rw [div_pow]
      ring
    have hnum : 27 * C2 ^ 2 ≤ 72 * (C2 + 1) ^ 2 := by
      nlinarith only [sq_nonneg C2, hC2pos.le]
    have hdiv : 27 * C2 ^ 2 / r ^ 2 ≤ 72 * (C2 + 1) ^ 2 / r ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg r)
    rw [hdim] at hlow ⊢
    have hcoef : -(((3 - 1 : ℕ) : ℝ) * q ^ 2) ≤
        -(((3 : ℕ) : ℝ) ^ 2 * (3 * C2 ^ 2 / r ^ 2)) := by
      rw [hq2]
      norm_num
      have h27 : 9 * (3 * C2 ^ 2 / r ^ 2) = 27 * C2 ^ 2 / r ^ 2 := by ring
      have h72 : 2 * (36 * (C2 + 1) ^ 2 / r ^ 2) = 72 * (C2 + 1) ^ 2 / r ^ 2 := by ring
      linarith only [hdiv, h27, h72]
    exact (mul_le_mul_of_nonneg_right hcoef hinner).trans hlow
  have hmain := Geometry.Riemannian.VolumeComparison.riemannianBallOf_volume_ratio_ge_of_ricci_lower
    g (RiemannianMetricComplete.of_compact g) x hq.le hρ hρR hRic
  have hsubset : riemannianBallOf g p r ⊆ riemannianBallOf g x R := by
    intro y hy
    change riemannianEDistOf g x y < ENNReal.ofReal R
    calc
      riemannianEDistOf g x y ≤ riemannianEDistOf g x p + riemannianEDistOf g p y :=
        riemannianEDistOf_triangle g x p y
      _ < ENNReal.ofReal (A * r) + ENNReal.ofReal r := ENNReal.add_lt_add hxp hy
      _ = ENNReal.ofReal R := by
        rw [← ENNReal.ofReal_add (mul_nonneg hA.le hr.le) hr.le]
        congr 1
        dsimp [R]
        ring
  have hlarge : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x R) :=
    hseedVolume.trans (measure_mono hsubset)
  have hcoefficient : κ * ρ ^ 3 =
      (Real.exp (-(q * ((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * R)) *
        (ρ / (2 * R)) ^ Module.finrank ℝ ThreeSpace) * (A⁻¹ * r ^ 3) := by
    rw [hdim]
    have hexponent : q * ((3 - 1 : ℕ) : ℝ) * R = 12 * (C2 + 1) * (A + 1) := by
      dsimp [q, R]
      field_simp [hr.ne']
      ring
    rw [hexponent, show -(12 * (C2 + 1) * (A + 1)) =
      -12 * (C2 + 1) * (A + 1) by ring]
    dsimp [κ, R]
    have hA1 : A + 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp [hA.ne', hA1, hr.ne']
    ring
  rw [hcoefficient, ENNReal.ofReal_mul (by positivity)]
  exact (mul_le_mul' le_rfl hlarge).trans hmain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
