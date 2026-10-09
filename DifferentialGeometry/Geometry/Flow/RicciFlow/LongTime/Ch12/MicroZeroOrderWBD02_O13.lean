import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13
import DifferentialGeometry.Geometry.Metric.Distance.Ball

/-!
# CH12-O13, group 3: whole-ball zero order at micro balls from Z1 and a test-ball-free kernel

Blueprint WBD02 (`lem:collapse-microscopic-whole-ball`, master207A.tex l.31378–31427) in the
unrescaled form.  Inputs: `hZ1` (the Z1 low point, shape of CH12-S33's
`micro_low_scalar_point_S33`) and `hKcan`, the bounded-curvature-at-bounded-distance kernel
(KL70.2) WITHOUT a volume-test premise and WITHOUT a cap alternative, uniform at late times.
O3's local kernel does not have this form (it needs the level point inside a `w`-test ball and
`Λ(A) ≤ (r/8)√R`); `hKcan` is the target of the K-can route recorded in `state-CH12-O13.md`.

Proof: low point `y₀ ∈ B(p, ρ/8)` with `R(y₀) ≤ D/ρ²`; if `R(q) > D/ρ²` the path-connected ball
contains `z` with `R(z) = D/ρ²` (intermediate values); the kernel at `z` with `A = 2√D` covers
`B(z, 2ρ) ∋ q`, so `R(q) ≤ Q D / ρ²`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- Intermediate values of the scalar curvature on a (path-connected) metric ball. -/
theorem exists_level_point_O13 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (p : M) {ρ c : ℝ} (hρ : 0 < ρ)
    {y₁ y₂ : M} (hy₁ : y₁ ∈ riemannianBallOf g p ρ) (hy₂ : y₂ ∈ riemannianBallOf g p ρ)
    (h₁ : metricScalarAt g y₁ ≤ c) (h₂ : c ≤ metricScalarAt g y₂) :
    ∃ z ∈ riemannianBallOf g p ρ, metricScalarAt g z = c := by
  have hpc := isPathConnected_riemannianBallOf (I := ThreeModel) g p hρ
  have hcont : Continuous (metricScalarAt g) := (metricScalar_smooth g).continuous
  exact hpc.isConnected.isPreconnected.intermediate_value hy₁ hy₂ hcont.continuousOn ⟨h₁, h₂⟩

/-- **Z0 (WBD02) from Z1 and the test-ball-free kernel `hKcan`.** -/
theorem micro_zero_order_of_kernel_O13 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hZ1 : ∀ w : ℝ, 0 < w → ∃ D : ℝ, 1 ≤ D ∧
      ∀ s : RegularSlice F.observation, ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        ρ ≤ Hp.parameters.neckRadius s.time →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∃ y ∈ riemannianBallOf s.metric p (ρ / 8), metricScalarAt s.metric y ≤ D / ρ ^ 2)
    (hKcan : ∀ A : ℝ, 0 < A → ∃ Q T : ℝ, 1 ≤ Q ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y) :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∃ C₀ T : ℝ, 0 < C₀ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∀ q ∈ riemannianBallOf s.metric p ρ, metricScalarAt s.metric q ≤ C₀ / ρ ^ 2 := by
  intro w hw Λ hΛ
  obtain ⟨D, T₁, hD, -, hlow⟩ := micro_low_point_O13 Hp hZ1 w hw Λ hΛ
  obtain ⟨T₂, -, hsc⟩ := micro_scale_le_neckRadius_O13 Hp Λ 1 (by linarith) one_pos
  have hD0 : 0 < D := by linarith
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  obtain ⟨Q, T₃, hQ, hker⟩ := hKcan (2 * Real.sqrt D) (by positivity)
  refine ⟨Q * D, max T₁ (max T₂ T₃), by positivity, ?_⟩
  intro s hs p ρ hρ hmic hneg hsec hvol q hq
  have hs1 : T₁ ≤ s.time := le_trans (le_max_left _ _) hs
  have hs2 : T₂ ≤ s.time := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs3 : T₃ ≤ s.time := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hρ2 : 0 < ρ ^ 2 := by positivity
  obtain ⟨y₀, hy₀, hRy₀⟩ := hlow s hs1 p ρ hρ hmic hneg hsec hvol
  by_cases hq' : metricScalarAt s.metric q ≤ D / ρ ^ 2
  · calc metricScalarAt s.metric q ≤ D / ρ ^ 2 := hq'
      _ ≤ Q * D / ρ ^ 2 := by
          apply div_le_div_of_nonneg_right _ hρ2.le
          nlinarith
  · push Not at hq'
    have hy₀' : y₀ ∈ riemannianBallOf s.metric p ρ := by
      change riemannianEDistOf s.metric p y₀ < ENNReal.ofReal ρ
      exact lt_of_lt_of_le hy₀ (ENNReal.ofReal_le_ofReal (by linarith))
    obtain ⟨z, hz, hRz⟩ := exists_level_point_O13 s.metric p hρ hy₀' hq hRy₀ hq'.le
    have hrad : ρ ≤ Hp.parameters.neckRadius s.time := by simpa using hsc s hs2 ρ hmic
    have hthr : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric z := by
      rw [hRz]
      have h1 : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ (ρ ^ 2)⁻¹ :=
        inv_anti₀ hρ2 (pow_le_pow_left₀ hρ.le hrad 2)
      have h2 : (ρ ^ 2)⁻¹ ≤ D / ρ ^ 2 := by
        rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr hρ2]
      exact h1.trans h2
    have hrad2 : 2 * Real.sqrt D / Real.sqrt (metricScalarAt s.metric z) = 2 * ρ := by
      rw [hRz, Real.sqrt_div' _ hρ2.le, Real.sqrt_sq hρ.le]
      field_simp
    have hqz : q ∈ riemannianBallOf s.metric z
        (2 * Real.sqrt D / Real.sqrt (metricScalarAt s.metric z)) := by
      rw [hrad2]
      change riemannianEDistOf s.metric z q < ENNReal.ofReal (2 * ρ)
      have hzp : riemannianEDistOf s.metric z p < ENNReal.ofReal ρ := by
        rw [riemannianEDistOf_comm]; exact hz
      have hpq : riemannianEDistOf s.metric p q < ENNReal.ofReal ρ := hq
      calc riemannianEDistOf s.metric z q
          ≤ riemannianEDistOf s.metric z p + riemannianEDistOf s.metric p q :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal ρ + ENNReal.ofReal ρ := ENNReal.add_lt_add hzp hpq
        _ = ENNReal.ofReal (2 * ρ) := by
            rw [← ENNReal.ofReal_add hρ.le hρ.le]; ring_nf
    have hb := hker s hs3 z hthr q hqz
    rw [hRz] at hb
    calc metricScalarAt s.metric q ≤ Q * (D / ρ ^ 2) := hb
      _ = Q * D / ρ ^ 2 := by ring

end GC.LongTime.Ch12
