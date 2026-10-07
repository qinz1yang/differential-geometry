import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreA1Seq_O45
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86RmBoundSlice_O22

/-!
# CH12-O45, group 2: slice-side inputs of the A2 limit (`[FROZEN] CH12-O45 G2`)

Along a sequence as in the `hA2` binder of `hNoEscPos_of_ABC_O38` (`R(y n) → ∞`, `R ≤ C(r) R(y n)`
on the normalized balls `B(y n, r/√R(y n))`, `r < ρ`):

* `rm_bound_on_ball_O45`: `|Rm| ≤ C R(y n)` on those balls (pinching, `slice_rm_bound_of_scalar_O22`);
* `sectional_almost_nonneg_on_ball_O45`: `sec ≥ -ε R(y n)` there, for every `ε > 0` eventually
  (`Rm ≥ -Φ(R)`, `Φ(C' R(y))/R(y) → 0`) — the input that gives `sec ≥ 0` in the limit.

Generic: `sectional_of_curvatureOperatorLowerBound_O45` (`Rm ≥ -K` ⇒ `sec ≥ -K`) and
`sectionalBoundedBelowAt_mono_O45` (Cauchy–Schwarz).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian Set Filter Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

section Generic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Curvature operator `≥ -K` gives sectional curvature `≥ -K`. -/
theorem sectional_of_curvatureOperatorLowerBound_O45 (g : SmoothRiemannianMetric I M) (q : M)
    {K : ℝ} (hRm : curvatureOperatorLowerBoundAt g q (metricAlgebraicCurvatureTensorAt g q) K) :
    SectionalBoundedBelowAt g q (-K) := by
  intro v w
  have h := hRm 1 (fun _ => 1) (fun _ => v) (fun _ => w)
  simp only [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
    Fin.sum_univ_one, one_mul, metricAlgebraicCurvatureTensorAt_coe] at h
  simp only [metricRm04StandardAt]
  rw [g.symm q w v] at h
  linarith

end Generic

section Three

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]

/-- Lowering the sectional lower bound (Cauchy–Schwarz). -/
theorem sectionalBoundedBelowAt_mono_O45 (g : SmoothRiemannianMetric ThreeModel M) (x : M)
    {K K' : ℝ} (h : SectionalBoundedBelowAt g x K) (hK : K' ≤ K) :
    SectionalBoundedBelowAt g x K' := by
  intro v w
  have h1 := h v w
  have cs := metric_inner_sq_le g x v w
  linarith [mul_le_mul_of_nonneg_right hK (sub_nonneg.mpr cs)]

end Three

section Slice

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- `slice_rm_bound_of_scalar_O22` read on the slice metric. -/
theorem slice_rm_bound_O45 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (s : RegularSlice F.observation) (x : s.stage.Carrier) (Mb : ℝ),
      1 ≤ Mb → metricScalarAt s.metric x ≤ Mb →
      Real.sqrt (normSq0S s.metric x 4 (metricRm04At s.metric x)) ≤ C0 * Mb := by
  obtain ⟨C0, hC0, hb⟩ := slice_rm_bound_of_scalar_O22 Hp
  refine ⟨C0, hC0, fun s => ?_⟩
  have key : ∀ (j : Fin (s.history.eventCount + 1)),
      s.history.activeStage (sliceTop_S8 s) = j → ∀ (x : (s.history.stage j).Carrier) (Mb : ℝ),
      1 ≤ Mb → metricScalarAt (s.history.stageMetric j s.time) x ≤ Mb →
      Real.sqrt (normSq0S (s.history.stageMetric j s.time) x 4
        (metricRm04At (s.history.stageMetric j s.time) x)) ≤ C0 * Mb := by
    intro j hj
    subst hj
    exact hb s (sliceTop_S8 s) le_rfl
  exact key (Fin.last _) s.history.activeStage_at_horizon

/-- **`|Rm| ≤ C R(y)` on the normalized balls of radius `< ρ`.** -/
theorem rm_bound_on_ball_O45 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : ℕ → RegularSlice F.observation) (y : ∀ n, (s n).stage.Carrier) (ρ : ℝ)
    (hRy : Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop)
    (hbdd : ∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ w ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
        metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) :
    ∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ w ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
        Real.sqrt (normSq0S (s n).metric w 4 (metricRm04At (s n).metric w)) ≤
          C * metricScalarAt (s n).metric (y n) := by
  obtain ⟨C0, -, hb⟩ := slice_rm_bound_O45 Hp
  intro r hr
  obtain ⟨C, hC⟩ := hbdd r hr
  refine ⟨C0 * max C 1, ?_⟩
  filter_upwards [hC, hRy.eventually (eventually_ge_atTop 1)] with n hn h1 w hw
  have hM : 1 ≤ max C 1 * metricScalarAt (s n).metric (y n) :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) h1
  have hle := hb (s n) w _ hM ((hn w hw).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans h1)))
  calc _ ≤ C0 * (max C 1 * metricScalarAt (s n).metric (y n)) := hle
    _ = C0 * max C 1 * metricScalarAt (s n).metric (y n) := by ring

/-- **Almost nonnegative sectional curvature on the normalized balls of radius `< ρ`.** -/
theorem sectional_almost_nonneg_on_ball_O45 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : ℕ → RegularSlice F.observation) (y : ∀ n, (s n).stage.Carrier) (ρ : ℝ)
    (hRy : Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop)
    (hbdd : ∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ w ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
        metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) :
    ∀ r : ℝ, r < ρ → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ w ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
        SectionalBoundedBelowAt (s n).metric w (-(ε * metricScalarAt (s n).metric (y n))) := by
  obtain ⟨Phi, hPhi, hpin⟩ := slice_pinch_O45 Hp
  intro r hr ε hε
  obtain ⟨C, hC⟩ := hbdd r hr
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C 1 := ⟨_, rfl⟩
  have hC'pos : 0 < C' := hC' ▸ lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCC' : C ≤ C' := hC' ▸ le_max_left _ _
  have hT : Tendsto (fun n => C' * metricScalarAt (s n).metric (y n)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hC'pos hRy
  have hq := (hPhi.quotientTendsto.comp hT).eventually (gt_mem_nhds (div_pos hε hC'pos))
  filter_upwards [hC, hRy.eventually (eventually_ge_atTop 1), hq] with n hn h1 hqn w hw
  simp only [Function.comp] at hqn
  have hRyp : 0 < metricScalarAt (s n).metric (y n) := lt_of_lt_of_le one_pos h1
  have hden : 0 < C' * metricScalarAt (s n).metric (y n) := mul_pos hC'pos hRyp
  rw [div_lt_iff₀ hden] at hqn
  have he : ε / C' * (C' * metricScalarAt (s n).metric (y n)) =
      ε * metricScalarAt (s n).metric (y n) := by field_simp
  have hmono : Phi (metricScalarAt (s n).metric w) ≤
      Phi (C' * metricScalarAt (s n).metric (y n)) :=
    hPhi.mono ((hn w hw).trans (mul_le_mul_of_nonneg_right hCC' hRyp.le))
  exact sectionalBoundedBelowAt_mono_O45 _ _
    (sectional_of_curvatureOperatorLowerBound_O45 _ _ (hpin (s n) w)) (by linarith)

end Slice

end GC.LongTime.Ch12
