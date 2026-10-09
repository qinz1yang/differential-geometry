import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86Spatial_O10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83Core_CX7
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerSeed_S21
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNbhdLarge_S22

/-!
# CH12-S33, group Z1: the micro low point

In a micro test ball `B(p, ρ)` of a regular slice (`ρ ≤ neckRadius(t)`, `sec ≥ -ρ⁻²` on the ball,
`vol ≥ w ρ³`) some point `y ∈ B(p, ρ/8)` has `R(y) ≤ D ρ⁻²`, with `D` depending only on the
profile constants and on `w`.

Route: Bishop--Gromov scale-down to `B(p, ρ/8)` (`seed_scale_down_S21`), KL83.1 with `ε = 1/4`
(`almost_euclidean_subball_CX7`) giving `y₀` with `(1 - ε)`-Euclidean subballs on
`B(y₀, θ ρ/8) ⊆ B(p, ρ/8)`, then the spatial step of KL Sublemma 86.3
(`scalar_le_of_almost_euclidean_O10`, applied directly to the slice metric, the canonical
neighbourhood hypothesis being `slice_canonical_above_neck_S22`) at `x₀ = y₀`, `r₀ = θ ρ/8`.
The negative-plane guard is carried as a hypothesis but not used.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- A ball of positive radius contains its centre. -/
theorem mem_riemannianBallOf_self_S33 {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (p : M) {r : ℝ} (hr : 0 < r) :
    p ∈ riemannianBallOf g p r := by
  change riemannianEDistOf g p p < ENNReal.ofReal r
  rw [riemannianEDistOf_self]
  exact ENNReal.ofReal_pos.mpr hr

theorem micro_low_scalar_point_S33 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (w : ℝ) (hw : 0 < w) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ s : RegularSlice F.observation, ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        ρ ≤ Hp.parameters.neckRadius s.time →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∃ y ∈ riemannianBallOf s.metric p (ρ / 8), metricScalarAt s.metric y ≤ D / ρ ^ 2 := by
  obtain ⟨c, hc, hBG⟩ := seed_scale_down_S21.{u}
  obtain ⟨θ, hθ, hAE⟩ := almost_euclidean_subball_CX7.{u} (c * w) (by positivity) (1 / 4)
    (by norm_num)
  obtain ⟨A, hA, hS⟩ := scalar_le_of_almost_euclidean_O10.{u} Hp.C1 Hp.C2
  refine ⟨max 1 (64 * A / θ ^ 2), le_max_left _ _, ?_⟩
  intro s p ρ hρ hrad _hneg hsec hvol
  have hρ8 : 0 < ρ / 8 := by positivity
  -- Bishop--Gromov down to `B(p, ρ/8)`
  obtain ⟨hsec8, hvol8⟩ := hBG s.stage.Carrier s.metric p w ρ (ρ / 8) hw hρ8 (by linarith)
    hsec hvol
  -- KL83.1 with `ε = 1/4`
  obtain ⟨y, hsub, hEuc⟩ := hAE s.stage.Carrier s.metric p (ρ / 8) hρ8 hsec8 hvol8
  have hr0 : 0 < θ * (ρ / 8) := by positivity
  have hyy : y ∈ riemannianBallOf s.metric y (θ * (ρ / 8)) :=
    mem_riemannianBallOf_self_S33 s.metric y hr0
  refine ⟨y, hsub hyy, ?_⟩
  -- the spatial step of Sublemma 86.3 on the slice
  have hcan : ∀ x : s.stage.Carrier, (Hp.parameters.neckRadius s.time ^ 2)⁻¹ <
      metricScalarAt s.metric x →
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon :=
    fun x hx => slice_canonical_above_neck_S22 Hp s x hx
  have hcomplete : RiemannianMetricComplete (I := ThreeModel) s.metric :=
    RiemannianMetricComplete.of_compact _
  have hy34 : y ∈ riemannianBallOf s.metric y (3 * (θ * (ρ / 8)) / 4) :=
    mem_riemannianBallOf_self_S33 s.metric y (by positivity)
  have h := hS s.metric hcomplete Hp.epsilon_small _ hcan (ε := 1 / 4) (by norm_num) y hr0 hEuc
    y hy34
  refine h.trans (max_le ?_ ?_)
  · have hsq : ρ ^ 2 ≤ Hp.parameters.neckRadius s.time ^ 2 := pow_le_pow_left₀ hρ.le hrad 2
    calc (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ (ρ ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
      _ = 1 / ρ ^ 2 := by rw [one_div]
      _ ≤ max 1 (64 * A / θ ^ 2) / ρ ^ 2 :=
        div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  · have e : A / (θ * (ρ / 8)) ^ 2 = 64 * A / θ ^ 2 / ρ ^ 2 := by
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The same, with a (vacuous) late-time threshold `T`. -/
theorem micro_low_scalar_point_T_S33 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (w : ℝ) (hw : 0 < w) :
    ∃ (D T : ℝ), 1 ≤ D ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
        ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
        ρ ≤ Hp.parameters.neckRadius s.time →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∃ y ∈ riemannianBallOf s.metric p (ρ / 8), metricScalarAt s.metric y ≤ D / ρ ^ 2 := by
  obtain ⟨D, hD, h⟩ := micro_low_scalar_point_S33 Hp w hw
  exact ⟨D, 0, hD, fun s _ => h s⟩

end GC.LongTime.Ch12
