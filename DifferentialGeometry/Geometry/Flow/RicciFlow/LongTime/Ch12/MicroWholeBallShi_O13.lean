import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MacroWholeBallWbd01

/-!
# CH12-O13, group 2: micro glue — micro scale, low point at micro balls, D (Shi, pointwise)

* `micro_scale_le_neckRadius_O13`: late, a micro test ball (`ρ < Λ h` for a recent cutoff radius
  `h`) has `ρ ≤ c · r_can(t)` for any prescribed `c > 0` (`recent_cutoff_smallness`).
* `micro_low_point_O13`: the Z1 low point (inline binder `hZ1`, exactly the shape of CH12-S33's
  `micro_low_scalar_point_S33`) at every late micro test ball.
* `microWholeBall_of_pointwise_O13` (D): `MicroWholeBall_O2` (ALL orders on the WHOLE ball) from a
  pointwise alternative at each `q ∈ B(p, ρ)`: either a traced backward region about `q` of radius
  `2aρ`, depth `τ(aρ)²`, curvature `C/(aρ)²` (Shi via `wholeBall_of_traced_S8`), or a direct
  all-order bound `B k ρ^{-(k+2)}` (the recent-cap branch, from cap-window jets).
* `hMicro_of_pointwise_O13`: the `hMicro` argument of `hW1_of_enhanced_O2`, verbatim type.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

theorem mem_riemannianBallOf_self_O13 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (p : M) {r : ℝ} (hr : 0 < r) :
    p ∈ riemannianBallOf g p r := by
  change riemannianEDistOf g p p < ENNReal.ofReal r
  rw [riemannianEDistOf_self]
  exact ENNReal.ofReal_pos.mpr hr

/-- Late micro test balls are below any fixed multiple of the canonical radius. -/
theorem micro_scale_le_neckRadius_O13 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (Λ c : ℝ) (hΛ : 0 < Λ) (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧ ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ ρ : ℝ,
      (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
        (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
        ρ < Λ * (Hp.records n i).nominalRadius h) →
      ρ ≤ c * Hp.parameters.neckRadius s.time := by
  obtain ⟨T, hT, hrec⟩ := Hp.recent_cutoff_smallness (c / Λ) (div_pos hc hΛ)
  refine ⟨T, hT, fun s hs ρ ⟨n, i, h, hi, hlt⟩ => ?_⟩
  have h1 := hrec s.time hs n i hi h
  have h2 : Λ * (Hp.records n i).nominalRadius h ≤ c * Hp.parameters.neckRadius s.time := by
    calc Λ * (Hp.records n i).nominalRadius h
        ≤ Λ * (c / Λ * Hp.parameters.neckRadius s.time) :=
          mul_le_mul_of_nonneg_left h1 hΛ.le
      _ = c * Hp.parameters.neckRadius s.time := by field_simp
  linarith

/-- **Z1 at micro test balls.**  `hZ1` is the frozen Z1 shape (= CH12-S33's
`micro_low_scalar_point_S33 Hp`, quantified over `w`). -/
theorem micro_low_point_O13 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hZ1 : ∀ w : ℝ, 0 < w → ∃ D : ℝ, 1 ≤ D ∧
      ∀ s : RegularSlice F.observation, ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        ρ ≤ Hp.parameters.neckRadius s.time →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∃ y ∈ riemannianBallOf s.metric p (ρ / 8), metricScalarAt s.metric y ≤ D / ρ ^ 2)
    (w : ℝ) (hw : 0 < w) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ D T : ℝ, 1 ≤ D ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∃ y ∈ riemannianBallOf s.metric p (ρ / 8), metricScalarAt s.metric y ≤ D / ρ ^ 2 := by
  obtain ⟨D, hD, hz⟩ := hZ1 w hw
  obtain ⟨T, hT, hsc⟩ := micro_scale_le_neckRadius_O13 Hp Λ 1 (by linarith) one_pos
  refine ⟨D, T, hD, hT, fun s hs p ρ hρ hmic hneg hsec hvol => ?_⟩
  have hrad : ρ ≤ Hp.parameters.neckRadius s.time := by
    simpa using hsc s hs ρ hmic
  exact hz s p ρ hρ hrad hneg hsec hvol

/-- The Shi constant of `wholeBall_of_traced_S8` (traced radius `2r`, depth `τ r²`,
curvature `C r⁻²`), order `k`. -/
def shiTracedConst_O13 (τ C : ℝ) (k : ℕ) : ℝ :=
  shiLocalUniformBound 3 k (C * τ / 2)
      (Real.sqrt C / (8 * Real.exp ((3 : ℝ) ^ 2 * (C * τ / 2)))) * C / Real.sqrt (τ / 2) ^ k

/-- **D (orders `k ≥ 0` on the whole ball), pointwise form.**  At every late micro test ball and
every `q ∈ B(p, ρ)`: a traced backward region about `q` at scale `aρ` (non-cap points), or a direct
all-order bound (recent-cap points) ⇒ `MicroWholeBall_O2 Hp`, with
`A k = max (shiTracedConst_O13 τ C k · a^{-(k+2)}) (B k)`. -/
theorem microWholeBall_of_pointwise_O13 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hpt : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∃ (b T a τ C : ℝ) (B : ℕ → ℝ),
      0 < b ∧ 0 < a ∧ 0 < τ ∧ 0 < C ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          (∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
            s.history.isTracedRegion (sliceTop_S8 s) q' (2 * (a * ρ)) (τ * (a * ρ) ^ 2)
              (C / (a * ρ) ^ 2)) ∨
          ∀ k : ℕ, curvatureDerivativeNorm s.metric k q ≤ B k * (ρ ^ (k + 2))⁻¹) :
    MicroWholeBall_O2 Hp := by
  intro w hw Λ hΛ
  obtain ⟨b, T, a, τ, C, B, hb, ha, hτ, hC, hpt⟩ := hpt w hw Λ hΛ
  refine ⟨b, T, fun k => max (shiTracedConst_O13 τ C k * (a ^ (k + 2))⁻¹) (B k), hb, ?_⟩
  intro s hs p ρ hρ hρb hmic hneg hsec hvol k q hq
  have hpos : (0 : ℝ) ≤ (ρ ^ (k + 2))⁻¹ := inv_nonneg.mpr (pow_nonneg hρ.le _)
  rcases hpt s hs p ρ hρ hρb hmic hneg hsec hvol q hq with htr | hcap
  · have haρ : 0 < a * ρ := mul_pos ha hρ
    have hqq : q ∈ riemannianBallOf s.metric q (a * ρ) :=
      mem_riemannianBallOf_self_O13 s.metric q haρ
    have h := wholeBall_of_traced_S8 s (Fin.last _) s.history.activeStage_at_horizon q hτ haρ hC
      htr k q hqq
    calc curvatureDerivativeNorm s.metric k q
        ≤ shiTracedConst_O13 τ C k * ((a * ρ) ^ (k + 2))⁻¹ := h
      _ = (shiTracedConst_O13 τ C k * (a ^ (k + 2))⁻¹) * (ρ ^ (k + 2))⁻¹ := by
          rw [mul_pow, mul_inv]; ring
      _ ≤ max (shiTracedConst_O13 τ C k * (a ^ (k + 2))⁻¹) (B k) * (ρ ^ (k + 2))⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  · exact (hcap k).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos)

/-- **`hMicro` of `hW1_of_enhanced_O2`, verbatim type**, from the pointwise traced / cap-bound
alternative (the W4, W5 arguments are not needed once the alternative is supplied). -/
theorem hMicro_of_pointwise_O13 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hpt : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∃ (b T a τ C : ℝ) (B : ℕ → ℝ),
      0 < b ∧ 0 < a ∧ 0 < τ ∧ 0 < C ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          (∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
            s.history.isTracedRegion (sliceTop_S8 s) q' (2 * (a * ρ)) (τ * (a * ρ) ^ 2)
              (C / (a * ρ) ^ 2)) ∨
          ∀ k : ℕ, curvatureDerivativeNorm s.metric k q ≤ B k * (ρ ^ (k + 2))⁻¹)
    (Ctime : ℝ≥0) :
    P2_O2 Hp Ctime → (∀ κ : ℝ, 0 < κ → ∀ (Cgrad : ℝ≥0) (phi : ℝ → ℝ),
        Perelman.AdmissiblePinchingFunction phi → W4Output_O2 Hp κ Ctime Cgrad phi) →
      (∀ N : ℕ, capWindowJets_O2 Hp N) → MicroWholeBall_O2 Hp :=
  fun _ _ _ => microWholeBall_of_pointwise_O13 Hp hpt

end GC.LongTime.Ch12
