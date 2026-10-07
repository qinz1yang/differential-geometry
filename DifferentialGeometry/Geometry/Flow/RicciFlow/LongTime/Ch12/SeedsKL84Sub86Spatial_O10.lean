import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84VolumeDeficit_O10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Metric.Completeness

/-!
# CH12-O10, Group S: the spatial step of KL Sublemma 86.3

If every point of scalar curvature above a threshold `Λ` has a canonical neighbourhood witness
(as `AnalyticSurgeryProfile.canonical` provides above `neckRadius(t)⁻²`), and every ball
`B(z, b)` with `z ∈ B(x0, r0)`, `b ≤ r0` is `(1 - ε)`-Euclidean (`ε ≤ 3/4`; this is the output
shape of KL83.1 / `almost_euclidean_subball_O4`), then `R ≤ max Λ (A r0⁻²)` on `B(x0, 3r0/4)` (KL's radius),
with `A` depending only on the canonical-neighbourhood constants.  Proof: at a point with larger
curvature the witness gives (Group V, `canonical_volume_deficit_O10`) a ball of radius
`< r0/16` within distance `< r0/16` whose volume is `< ρ³ ≤ (1 - ε) ω₃ ρ³`.

`slice_scalar_le_of_almost_euclidean_O10` is the profile form on the post-surgery slice at time
`t` with `r0 ≤ neckRadius t`: `R ≤ A r0⁻²` on `B(x0, 3r0/4)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **S.** Spatial Sublemma 86.3: canonical neighbourhoods above `Λ` and `(1-ε)`-Euclidean balls
at scales `≤ r0` force `R ≤ max Λ (A / r0²)` on `B(x0, 3r0/4)`. -/
theorem scalar_le_of_almost_euclidean_O10 (C1 C2 : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I3 M),
        RiemannianMetricComplete (I := I3) g → ∀ {eps : ℝ}, eps < 1 / 100 → ∀ Λ : ℝ,
        (∀ y : M, Λ < metricScalarAt g y →
          ∃ W : SpatialCanonicalWitness g eps C1 C2 y, W.capTubeHasNeckChart eps) →
        ∀ {ε : ℝ}, ε ≤ 3 / 4 → ∀ (x0 : M) {r0 : ℝ}, 0 < r0 →
        (∀ z ∈ riemannianBallOf g x0 r0, ∀ b : ℝ, 0 < b → b ≤ r0 →
          ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3) ≤ ballVolume g z b) →
        ∀ y ∈ riemannianBallOf g x0 (3 * r0 / 4), metricScalarAt g y ≤ max Λ (A / r0 ^ 2) := by
  obtain ⟨L, hL, hV⟩ := canonical_volume_deficit_O10.{u} C1 C2
  refine ⟨256 * L ^ 2 + 1, by nlinarith, ?_⟩
  intro M _ _ _ _ _ g hg eps heps Λ hcan ε hε x0 r0 hr0 hEuc y hy
  by_contra hcon
  push Not at hcon
  have hΛ : Λ < metricScalarAt g y := (le_max_left _ _).trans_lt hcon
  have hA : (256 * L ^ 2 + 1) / r0 ^ 2 < metricScalarAt g y :=
    (le_max_right _ _).trans_lt hcon
  obtain ⟨W, hW⟩ := hcan y hΛ
  obtain ⟨z, ρ, hdz, hρ0, hρ, hvol⟩ := hV g hg heps W hW
  have hRy : 0 < metricScalarAt g y := W.Q_pos
  have hsR : 0 < Real.sqrt (metricScalarAt g y) := Real.sqrt_pos.mpr hRy
  -- `L / √R(y) < r0 / 16`
  have h8 : 16 * L / r0 < Real.sqrt (metricScalarAt g y) := by
    apply Real.lt_sqrt_of_sq_lt
    rw [div_pow]
    calc (16 * L) ^ 2 / r0 ^ 2 = 256 * L ^ 2 / r0 ^ 2 := by ring
      _ < (256 * L ^ 2 + 1) / r0 ^ 2 :=
        div_lt_div_of_pos_right (by linarith) (by positivity)
      _ < _ := hA
  have hsmall : L / Real.sqrt (metricScalarAt g y) < r0 / 16 := by
    rw [div_lt_iff₀ hsR]
    rw [div_lt_iff₀ hr0] at h8
    linarith
  have hzball : z ∈ riemannianBallOf g x0 r0 := by
    change riemannianEDistOf g x0 z < ENNReal.ofReal r0
    calc riemannianEDistOf g x0 z
        ≤ riemannianEDistOf g x0 y + riemannianEDistOf g y z :=
          DifferentialGeometry.riemannianEDistOf_triangle g x0 y z
      _ < ENNReal.ofReal (3 * r0 / 4) + ENNReal.ofReal (r0 / 16) := by
          have h2 := hdz.trans (ENNReal.ofReal_le_ofReal hsmall.le)
          exact ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2) hy h2
      _ = ENNReal.ofReal (3 * r0 / 4 + r0 / 16) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal r0 := ENNReal.ofReal_le_ofReal (by linarith)
  have hρr0 : ρ ≤ r0 := by linarith
  have hE := hEuc z hzball ρ hρ0 hρr0
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hcoef : 1 ≤ (1 - ε) * euclideanUnitBallVolume 3 := by
    rw [euclideanUnitBallVolume_three_eq]
    nlinarith
  have hle : ENNReal.ofReal (ρ ^ 3) ≤
      ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) := by
    apply ENNReal.ofReal_le_ofReal
    have : 0 < ρ ^ 3 := by positivity
    nlinarith
  exact absurd (hle.trans hE) (not_le.mpr hvol)

/-- Profile form on the post-surgery slice at time `t`, for `r0 ≤ neckRadius t`. -/
theorem slice_scalar_le_of_almost_euclidean_O10 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ t : ℝ, 0 ≤ t →
      ∀ (x0 : (GC.LongTime.postStage F.observation t).Carrier) {r0 : ℝ}, 0 < r0 →
        r0 ≤ Hp.parameters.neckRadius t → ∀ {ε : ℝ}, ε ≤ 3 / 4 →
        (∀ z ∈ riemannianBallOf (GC.LongTime.postMetric F.observation t) x0 r0, ∀ b : ℝ,
          0 < b → b ≤ r0 →
          ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3) ≤
            ballVolume (GC.LongTime.postMetric F.observation t) z b) →
        ∀ y ∈ riemannianBallOf (GC.LongTime.postMetric F.observation t) x0 (3 * r0 / 4),
          metricScalarAt (GC.LongTime.postMetric F.observation t) y ≤ A / r0 ^ 2 := by
  obtain ⟨A, hA, hS⟩ := scalar_le_of_almost_euclidean_O10.{u} Hp.C1 Hp.C2
  refine ⟨A, hA, ?_⟩
  intro t ht x0 r0 hr0 hrad ε hε hEuc y hy
  have hg : RiemannianMetricComplete (I := I3) (GC.LongTime.postMetric F.observation t) :=
    RiemannianMetricComplete.of_compact _
  have h := hS (GC.LongTime.postMetric F.observation t) hg Hp.epsilon_small
    ((Hp.parameters.neckRadius t ^ 2)⁻¹) (fun x hx => Hp.canonical t ht x hx) hε x0 hr0 hEuc y hy
  refine h.trans (max_le ?_ le_rfl)
  have hsq : r0 ^ 2 ≤ Hp.parameters.neckRadius t ^ 2 := pow_le_pow_left₀ hr0.le hrad 2
  calc (Hp.parameters.neckRadius t ^ 2)⁻¹ ≤ (r0 ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
    _ = 1 / r0 ^ 2 := by rw [one_div]
    _ ≤ A / r0 ^ 2 := div_le_div_of_nonneg_right hA (by positivity)

end GC.LongTime.Ch12
