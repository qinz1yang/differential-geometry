import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroZeroOrderWBD02_O13

/-!
# CH12-O14, adapter: Z0 (WBD02) from Z1 and the corrected kernel `hKcan_v2`

`[FROZEN v2] CH12-O14`: the test-ball-free kernel of `[FROZEN] CH12-O13 G3` gets the extra
premise `Λ ≤ R(y)` (the tree's KL70.2 limit needs `Q_n → ∞` for the time-independent pinching;
`neckRadius` is only antitone, so `(neckRadius t)⁻² ≤ R(y)` does not force it).  The WBD02 level
point still satisfies it: `R(z) = D/ρ²` and `ρ ≤ c · neckRadius t ≤ c · neckRadius 0` for any
`c > 0` at late micro balls (`micro_scale_le_neckRadius_O13`).

* `hKcan_v2_of_hKcan_O14`: O13's shape implies the v2 shape (v2 is weaker).
* `hKcan_v2_of_branches_O14`: v2 from the K-can core and the cap branch (S44), split by a
  common predicate `capPt`.
* `micro_zero_order_of_kernel_v2_O14`: the conclusion of `micro_zero_order_of_kernel_O13`
  verbatim, from `hZ1` and `hKcan_v2`.
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

/-- O13's frozen `hKcan` implies the corrected v2 shape. -/
theorem hKcan_v2_of_hKcan_O14 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hKcan : ∀ A : ℝ, 0 < A → ∃ Q T : ℝ, 1 ≤ Q ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y) :
    ∀ A : ℝ, 0 < A → ∃ Q Λ T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y := by
  intro A hA
  obtain ⟨Q, T, hQ, h⟩ := hKcan A hA
  exact ⟨Q, 1, T, hQ, le_rfl, fun s hs y hy _ => h s hs y hy⟩

/-- **hKcan_v2 from the two branches** (lead L2 decision, 2026-10-06): the K-can core `hcore`
(points outside `capPt`) and the cap branch `hcap` (points in `capPt`, lane S44).  `capPt` is the
recent-cap-window predicate on which both branches agree; it must not depend on `A`. -/
theorem hKcan_v2_of_branches_O14 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (capPt : ∀ s : RegularSlice F.observation, s.stage.Carrier → Prop)
    (hcore : ∀ A : ℝ, 0 < A → ∃ Q Λ T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y → ¬ capPt s y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y)
    (hcap : ∀ A : ℝ, 0 < A → ∃ Q Λ T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y → capPt s y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y) :
    ∀ A : ℝ, 0 < A → ∃ Q Λ T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y := by
  intro A hA
  obtain ⟨Q₁, Λ₁, T₁, hQ₁, hΛ₁, h₁⟩ := hcore A hA
  obtain ⟨Q₂, Λ₂, T₂, hQ₂, hΛ₂, h₂⟩ := hcap A hA
  refine ⟨max Q₁ Q₂, max Λ₁ Λ₂, max T₁ T₂, le_trans hQ₁ (le_max_left _ _),
    le_trans hΛ₁ (le_max_left _ _), ?_⟩
  intro s hs y hy hΛy z hz
  have hR0 : 0 ≤ metricScalarAt s.metric y := by
    have : (0 : ℝ) < max Λ₁ Λ₂ := lt_of_lt_of_le one_pos (le_trans hΛ₁ (le_max_left _ _))
    linarith
  by_cases hc : capPt s y
  · exact (h₂ s (le_trans (le_max_right _ _) hs) y hy
      (le_trans (le_max_right _ _) hΛy) hc z hz).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hR0)
  · exact (h₁ s (le_trans (le_max_left _ _) hs) y hy
      (le_trans (le_max_left _ _) hΛy) hc z hz).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0)

/-- **Z0 (WBD02) from Z1 and the corrected test-ball-free kernel `hKcan_v2`.** -/
theorem micro_zero_order_of_kernel_v2_O14 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hZ1 : ∀ w : ℝ, 0 < w → ∃ D : ℝ, 1 ≤ D ∧
      ∀ s : RegularSlice F.observation, ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        ρ ≤ Hp.parameters.neckRadius s.time →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∃ y ∈ riemannianBallOf s.metric p (ρ / 8), metricScalarAt s.metric y ≤ D / ρ ^ 2)
    (hKcan : ∀ A : ℝ, 0 < A → ∃ Q Λ T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y →
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
  have hD0 : 0 < D := by linarith
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  obtain ⟨Q, Λk, T₃, hQ, hΛk, hker⟩ := hKcan (2 * Real.sqrt D) (by positivity)
  have hr₀ : 0 < Hp.parameters.neckRadius 0 := Hp.parameters.neckRadius_pos 0 le_rfl
  set c : ℝ := min 1 (Real.sqrt (D / Λk) / Hp.parameters.neckRadius 0) with hcdef
  have hc : 0 < c :=
    lt_min one_pos (div_pos (Real.sqrt_pos.mpr (div_pos hD0 (by linarith))) hr₀)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcr : c * Hp.parameters.neckRadius 0 ≤ Real.sqrt (D / Λk) := by
    have := min_le_right 1 (Real.sqrt (D / Λk) / Hp.parameters.neckRadius 0)
    rw [← hcdef] at this
    calc c * Hp.parameters.neckRadius 0
        ≤ Real.sqrt (D / Λk) / Hp.parameters.neckRadius 0 * Hp.parameters.neckRadius 0 :=
          mul_le_mul_of_nonneg_right this hr₀.le
      _ = Real.sqrt (D / Λk) := by field_simp
  obtain ⟨T₂, -, hsc⟩ := micro_scale_le_neckRadius_O13 Hp Λ c (by linarith) hc
  refine ⟨Q * D, max T₁ (max (max T₂ 0) T₃), by positivity, ?_⟩
  intro s hs p ρ hρ hmic hneg hsec hvol q hq
  have hs1 : T₁ ≤ s.time := le_trans (le_max_left _ _) hs
  have hs2 : T₂ ≤ s.time :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hs
  have hs0 : (0 : ℝ) ≤ s.time :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hs
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
    have hρc : ρ ≤ c * Hp.parameters.neckRadius s.time := hsc s hs2 ρ hmic
    have hrad : ρ ≤ Hp.parameters.neckRadius s.time := by
      have := Hp.parameters.neckRadius_pos s.time hs0
      nlinarith
    have hanti : Hp.parameters.neckRadius s.time ≤ Hp.parameters.neckRadius 0 :=
      Hp.radius_antitone (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs0) hs0
    have hρΛ : ρ ≤ Real.sqrt (D / Λk) :=
      hρc.trans ((mul_le_mul_of_nonneg_left hanti hc.le).trans hcr)
    have hΛz : Λk ≤ metricScalarAt s.metric z := by
      rw [hRz]
      have h1 : ρ ^ 2 ≤ D / Λk := by
        have := pow_le_pow_left₀ hρ.le hρΛ 2
        rwa [Real.sq_sqrt (div_nonneg hD0.le (by linarith))] at this
      have hΛ0 : 0 < Λk := by linarith
      rw [le_div_iff₀ hρ2]
      rw [le_div_iff₀ hΛ0] at h1
      linarith
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
    have hb := hker s hs3 z hthr hΛz q hqz
    rw [hRz] at hb
    calc metricScalarAt s.metric q ≤ Q * (D / ρ ^ 2) := hb
      _ = Q * D / ρ ^ 2 := by ring

end GC.LongTime.Ch12
