import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroZeroOrderDoubled_O23

/-!
# CH12-O29, group 1: the escape-radius reduction of the K-core (KL70.2, first step)

The K-core binder `hcore` of `hKcan_v2_of_branchesA_O23` (`[FROZEN] CH12-O23` (1)) is reduced to
the statement `hNoEsc` (`[FROZEN] CH12-O29`): no sequence of late slices with base points
`y n` of curvature `→ ∞`, outside `capPt A`, has normalized curvature bounded on every normalized
ball `B(y n, r / √R(y n))`, `r < ρ`, while points `z n` of normalized curvature `→ ∞` escape
exactly at normalized distance `ρ ≤ A`.

* `hcore_of_noEscape_O29`: the reduction (contradiction sequence at `Q = Λ = T = n + 1`,
  `ρ := sInf` of the upward closed escape set, re-indexing with radii `min A (ρ + 1 / (k + 1))`).
* `hKcan_of_noEscape_O29`: `hKcan_v2` from `hNoEsc` and the K-cap binder `hcap`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- A ball of nonpositive radius is empty. -/
theorem not_mem_riemannianBallOf_of_nonpos_O29 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g' : SmoothRiemannianMetric ThreeModel M) (x w : M) {r : ℝ}
    (hr : r ≤ 0) : w ∉ riemannianBallOf (I := ThreeModel) g' x r := by
  intro hw
  have hw' : riemannianEDistOf (I := ThreeModel) g' x w < ENNReal.ofReal r := hw
  rw [ENNReal.ofReal_of_nonpos hr] at hw'
  exact ENNReal.not_lt_zero hw'

/-- **Escape-radius reduction of the K-core** (`[FROZEN] CH12-O29`, G1). -/
theorem hcore_of_noEscape_O29 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (capPt : ℝ → ∀ s : RegularSlice F.observation, s.stage.Carrier → Prop)
    (hNoEsc : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPt A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      (∀ n, z n ∈ riemannianBallOf (s n).metric (y n)
        (A / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      False) :
    ∀ A : ℝ, 0 < A → ∃ Q Λ T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y → ¬ capPt A s y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y := by
  intro A hA
  by_contra hfail
  -- the contradiction sequence at `Q = Λ = T = n + 1`
  have key : ∀ n : ℕ, ∃ s : RegularSlice F.observation, (n : ℝ) + 1 ≤ s.time ∧
      ∃ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y ∧
        (n : ℝ) + 1 ≤ metricScalarAt s.metric y ∧ ¬ capPt A s y ∧
        ∃ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          ((n : ℝ) + 1) * metricScalarAt s.metric y < metricScalarAt s.metric z := by
    intro n
    by_contra hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine hfail ⟨(n : ℝ) + 1, (n : ℝ) + 1, (n : ℝ) + 1, h1, h1, ?_⟩
    intro s hs y hy hΛ hc z hz
    by_contra hlt
    exact hn ⟨s, hs, y, hy, hΛ, hc, z, hz, lt_of_not_ge hlt⟩
  choose s hs y hy hΛ hc z0 hz0 hR using key
  set Rn : ℕ → ℝ := fun n => metricScalarAt (s n).metric (y n) with hRn
  have hRpos : ∀ n, 0 < Rn n := fun n =>
    lt_of_lt_of_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (hΛ n)
  -- the escape set
  set E : Set ℝ := {r | 0 ≤ r ∧ ∀ C : ℝ, ∃ᶠ n in atTop,
    ∃ w ∈ riemannianBallOf (s n).metric (y n) (r / Real.sqrt (Rn n)),
      C * Rn n < metricScalarAt (s n).metric w} with hE
  have hAE : A ∈ E := by
    refine ⟨hA.le, fun C => ?_⟩
    refine (eventually_ge_atTop ⌈C⌉₊).frequently.mono fun n hn => ⟨z0 n, hz0 n, ?_⟩
    have hCn : C ≤ (n : ℝ) + 1 := by
      have := Nat.le_ceil C
      have h2 : (⌈C⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCn (hRpos n).le) (hR n)
  have hup : ∀ r r', r ∈ E → r ≤ r' → r' ∈ E := by
    intro r r' hr hrr
    refine ⟨hr.1.trans hrr, fun C => (hr.2 C).mono fun n ⟨w, hw, hlt⟩ => ⟨w, ?_, hlt⟩⟩
    exact riemannianBallOf_mono _ _
      (div_le_div_of_nonneg_right hrr (Real.sqrt_nonneg _)) hw
  have hbdd : BddBelow E := ⟨0, fun r hr => hr.1⟩
  set ρ : ℝ := sInf E with hρ
  have hρ0 : 0 ≤ ρ := le_csInf ⟨A, hAE⟩ fun r hr => hr.1
  have hρA : ρ ≤ A := csInf_le hbdd hAE
  have hgt : ∀ r, ρ < r → r ∈ E := by
    intro r hr
    obtain ⟨r₀, hr₀, hlt⟩ := exists_lt_of_csInf_lt ⟨A, hAE⟩ hr
    exact hup r₀ r hr₀ hlt.le
  -- the escape radii
  set rk : ℕ → ℝ := fun k => min A (ρ + 1 / ((k : ℝ) + 1)) with hrk
  have hεpos : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hrkE : ∀ k, rk k ∈ E := by
    intro k
    rcases lt_or_eq_of_le hρA with hlt | heq
    · exact hgt _ (lt_min hlt (by linarith [hεpos k]))
    · have : rk k = A := by
        simp only [hrk]
        rw [← heq]
        exact min_eq_left (by linarith [hεpos k])
      rw [this]
      exact hAE
  have hpick : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      ∃ w ∈ riemannianBallOf (s n).metric (y n) (rk k / Real.sqrt (Rn n)),
        ((k : ℝ) + 1) * Rn n < metricScalarAt (s n).metric w := by
    intro k
    obtain ⟨n, hn, hk⟩ := (((hrkE k).2 ((k : ℝ) + 1)).and_eventually
      (eventually_ge_atTop k)).exists
    exact ⟨n, hk, hn⟩
  choose φ hφ w hw hwR using hpick
  have hφt : Tendsto φ atTop atTop := tendsto_atTop_mono hφ tendsto_id
  have hcast : ∀ k : ℕ, (k : ℝ) ≤ (φ k : ℝ) + 1 := fun k => by
    have : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφ k
    linarith
  refine hNoEsc A hA (fun k => s (φ k)) (fun k => y (φ k)) w ρ ?_ (fun k => hy (φ k)) ?_
    (fun k => hc (φ k)) hρ0 hρA ?_ ?_ ?_ ?_
  · exact tendsto_atTop_mono (fun k => (hcast k).trans (hs (φ k))) tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono (fun k => (hcast k).trans (hΛ (φ k))) tendsto_natCast_atTop_atTop
  · intro k
    exact riemannianBallOf_mono _ _
      (div_le_div_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)) (hw k)
  · refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    have h1 := hwR k
    rw [le_div_iff₀ (hRpos (φ k))]
    have : (k : ℝ) * Rn (φ k) ≤ ((k : ℝ) + 1) * Rn (φ k) :=
      mul_le_mul_of_nonneg_right (by linarith) (hRpos (φ k)).le
    exact (this.trans h1.le)
  · intro r hr
    rcases le_or_gt r 0 with hr0 | hr0
    · refine ⟨0, Eventually.of_forall fun k v hv => ?_⟩
      exact absurd hv (not_mem_riemannianBallOf_of_nonpos_O29 _ _ _
        (div_nonpos_of_nonpos_of_nonneg hr0 (Real.sqrt_nonneg _)))
    · have hrE : r ∉ E := fun h => absurd (csInf_le hbdd h) (not_le.mpr hr)
      have : ¬ ∀ C : ℝ, ∃ᶠ n in atTop,
          ∃ w ∈ riemannianBallOf (s n).metric (y n) (r / Real.sqrt (Rn n)),
            C * Rn n < metricScalarAt (s n).metric w := fun h => hrE ⟨hr0.le, h⟩
      obtain ⟨C, hC⟩ := not_forall.mp this
      refine ⟨C, (hφt.eventually (Filter.not_frequently.mp hC)).mono fun k hk v hv => ?_⟩
      by_contra hlt
      exact hk ⟨v, hv, lt_of_not_ge hlt⟩
  · intro r hr
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt (sub_pos.mpr hr)
    refine (eventually_ge_atTop k₀).mono fun k hk => ?_
    have hle : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) := by
      have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
      gcongr
    have hrkr : rk k ≤ r := (min_le_right _ _).trans (by linarith)
    exact riemannianBallOf_mono _ _
      (div_le_div_of_nonneg_right hrkr (Real.sqrt_nonneg _)) (hw k)

/-- `hKcan_v2` from the escape statement `hNoEsc` and the K-cap binder (`[FROZEN] CH12-O29`). -/
theorem hKcan_of_noEscape_O29 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (capPt : ℝ → ∀ s : RegularSlice F.observation, s.stage.Carrier → Prop)
    (hNoEsc : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPt A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      (∀ n, z n ∈ riemannianBallOf (s n).metric (y n)
        (A / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      False)
    (hcap : ∀ A : ℝ, 0 < A → ∃ Q Λ T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y → capPt A s y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y) :
    ∀ A : ℝ, 0 < A → ∃ Q Λ T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y :=
  hKcan_v2_of_branchesA_O23 Hp capPt (hcore_of_noEscape_O29 Hp capPt hNoEsc) hcap

end GC.LongTime.Ch12
