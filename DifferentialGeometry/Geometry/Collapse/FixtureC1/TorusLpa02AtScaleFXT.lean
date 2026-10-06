import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusLpa02ChartFXT
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterFamilyFXR
import DifferentialGeometry.Geometry.Collapse.RiemannianConeAtInfinity
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.BufferedRadialFunctionAtScale
import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeSectional
import DifferentialGeometry.Geometry.Metric.Approximation.ConeAtInfinity
import DifferentialGeometry.Geometry.Metric.InnerProductRadialCone
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

/-!
# LPA02 on the flat torus, part 2: the joint witness at ONE scale (S-LPA02-TOR, G2)

Lane S-LPA02-TOR (suffix `_FXT`). `Lpa02WitnessAtV2 g K ε e δ p r s hr hs` on the flat torus
`T³_Λ` (metric `torMetric_FXC1 Λ`), at the scale `ρ = s r`, in the two regimes where the rescaled
torus is close to a cone:

* **Regime S (small scale)**, `torAtSmall_FXT`: `s r ≤ δ f/4`, `f` a lower bound of all periods.
  Model `N = Ns = E3` (flat), cone `C = E3`, the Kleiner–Lott map is the inverse lift of
  `TorusLpa02ChartFXT` (`klSmall_FXT`), the balls `B(p, ρ' s r)`, `ρ' ∈ [1/5, 2]`, are cells
  (`exists_ballDiffeo_FXT`).
* **Regime B (large scale)**, `torAtBig_FXT`: `diam T³ ≤ δ s r`. Model `N = Ns = T³` itself, cone
  `C` = the one-point cone (`klPoint_FXT`), all balls `B(p, ρ' s r)` are the whole torus.

In both regimes the radial function with LC31's cutoff (13 clauses) is NOT built by hand: it is
`exists_buffered_radial_cutoff_at_scale` (LC67 + LC31) applied to the Kleiner–Lott map, the
flat curvature buffer and `δ < radialSmoothingConeError (ε/4)`. The model `(N, G, q)` carries
the smooth metric weakened to order `K - 1` (`weakMetric_FXT`); flatness gives `sec ≥ 0`
(`weakMetric_sectional_FXT`), `fourPointComparison 0` and metric segments come from
`RiemannianConeAtInfinity`.

Between the two regimes (`s r` comparable to the shortest period) LPA02's witness is FALSE on the
torus (the balls `B(p, ρ' s r)` change topology inside `ρ' ∈ [1/5, 2]`); the final assembly chooses
`s ∈ [T₀, V]` outside it, which needs `V` large (`TorusLpa02WitnessFXT`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold GC.Endpoint Bundle GC.MetricGeometry Metric
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
local notation "gE3" => DifferentialGeometry.euclideanMetric (E := EuclideanSpace ℝ (Fin 3))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

def weakMetric_FXT {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
    (n : ℕ∞ω) (hn : n ≤ ∞) (g : SmoothRiemannianMetric I3 X) :
    ContMDiffRiemannianMetric I3 n E3 (TangentSpace I3 : X → Type _) where
  inner := g.inner
  symm := g.symm
  pos := g.pos
  isVonNBounded := g.isVonNBounded
  contMDiff := g.contMDiff.of_le hn

theorem weakMetric_sectional_FXT {X : Type} [TopologicalSpace X] [T2Space X]
    [ChartedSpace E3 X] [IsManifold I3 ∞ X] (n : ℕ∞ω) (hn : n ≤ ∞)
    (g : SmoothRiemannianMetric I3 X)
    (hg : ∀ y, SectionalBoundedBelowAt g y 0) (x : X) (v w : TangentSpace I3 x) :
    0 ≤ (weakMetric_FXT n hn g).sectionalCurvature x v w :=
  MetricSmoothing.sectionalCurvature_nonneg_of_sectionalBoundedBelow_zero g hg x v w

theorem isRiemannianManifold_weak_FXT {Y : Type} [MetricSpace Y] [ChartedSpace E3 Y]
    [IsManifold I3 ∞ Y] (n : ℕ∞ω) (hn : n ≤ ∞) (g : SmoothRiemannianMetric I3 Y)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) :
    letI : RiemannianBundle (fun x : Y => TangentSpace I3 x) :=
      ⟨(weakMetric_FXT n hn g).toRiemannianMetric⟩
    IsRiemannianManifold I3 Y := by
  let instRB_FXT : RiemannianBundle (fun x : Y => TangentSpace I3 x) :=
    ⟨(weakMetric_FXT n hn g).toRiemannianMetric⟩
  constructor
  intro a b
  change edist a b = riemannianEDistOf g a b
  rw [edist_dist, hmetric]

theorem klPoint_FXT {N : Type*} [mN : MetricSpace N] (n : N)
    (hb : Bornology.IsBounded (univ : Set N)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (R : ℝ)
    (hR : 0 < R) (hRε : Metric.diam (univ : Set N) ≤ ε * R) :
    Nonempty (@KleinerLottApprox N PUnit.{1} (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n PUnit.unit
      ε) := by
  refine ⟨@KleinerLottApprox.mk N PUnit.{1} (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n PUnit.unit ε
    hε hε1 (fun _ => PUnit.unit) rfl ?_ ?_⟩
  · intro x _ x' _
    rw [dist_self, zero_sub, abs_neg, MetricSpace.rescale_dist,
      abs_of_nonneg (mul_nonneg (inv_pos.mpr hR).le dist_nonneg)]
    have hd : dist x x' ≤ Metric.diam (univ : Set N) :=
      Metric.dist_le_diam_of_mem hb (mem_univ x) (mem_univ x')
    rw [inv_mul_le_iff₀ hR]
    linarith
  · intro y _
    have hmem : y ∈ (fun _ : N => PUnit.unit) ''
        @Metric.ball N (mN.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace n ε⁻¹ :=
      ⟨n, @Metric.mem_ball_self N (mN.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace _ _
        (inv_pos.mpr hε), Subsingleton.elim _ _⟩
    rw [Metric.infDist_zero_of_mem hmem]
    exact hε.le

/-- **Regime B (large scale)**. -/
theorem torAtBig_FXT (Λ : TorusPeriods_FXC1) (K : ℕ) {ε e δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (he : 0 < e) (he1 : e < 1 / 40) (hδ : 0 < δ) (hδ2 : δ < radialSmoothingConeError (ε / 4))
    (p : Tor_FXC1 Λ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hdiam : Metric.diam (univ : Set (Tor_FXC1 Λ)) ≤ δ * (s * r)) :
    Lpa02WitnessAtV2 (torMetric_FXC1 Λ) K ε e δ p r s hr hs := by
  have hδ1 : δ < 1 := hδ2.trans_le ((min_le_left _ _).trans (by norm_num))
  have hn : ((K - 1 : ℕ) : ℕ∞ω) ≤ ∞ := by simp
  have hsr : 0 < s * r := mul_pos hs hr
  have hsec : ∀ y, SectionalBoundedBelowAt (torMetric_FXC1 Λ) y 0 := fun y =>
    torMetric_sectional_FXC1 Λ y le_rfl
  obtain ⟨φ⟩ := klPoint_FXT p (isCompact_univ.isBounded) hδ hδ1 (s * r) hsr hdiam
  have hF := exists_buffered_radial_cutoff_at_scale (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ)
    hsr φ RadialConeData.punit
    (fun y _ => torMetric_sectional_FXC1 Λ y (by
      have : 0 ≤ ((1 / 60 : ℝ) ^ 2 * ((s * r)⁻¹) ^ 2) := by positivity
      linarith))
    hε hε1 hδ2 he he1
  have hδ5 : δ < 1 / 5 := hδ2.trans_le ((min_le_left _ _).trans (by norm_num))
  have hΨ : ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (Tor_FXC1 Λ)
      (Tor_FXC1 Λ) ∞, Ψ.source = Metric.ball p (ρ' * (s * r)) ∧ Ψ.target = univ := by
    intro ρ' hρ'
    refine ⟨(Diffeomorph.refl I3 (Tor_FXC1 Λ) ∞).toPartialDiffeomorph, ?_, rfl⟩
    symm
    refine eq_univ_of_forall fun x => ?_
    rw [Metric.mem_ball]
    have h1 : dist x p ≤ Metric.diam (univ : Set (Tor_FXC1 Λ)) :=
      Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ p)
    nlinarith [hρ'.1]
  have : NeZero (Module.finrank ℝ E3) := ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  unfold Lpa02WitnessAtV2
  refine ⟨Tor_FXC1 Λ, torMS_FXC1 Λ, inferInstance, inferInstance,
    weakMetric_FXT _ hn (torMetric_FXC1 Λ), p, inferInstance, inferInstance,
    isRiemannianManifold_weak_FXT _ hn (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ),
    weakMetric_sectional_FXT _ hn (torMetric_FXC1 Λ) hsec,
    fourPointComparison_zero_univ_of_sectional_nonneg (torMetric_FXC1 Λ)
      (torMS_hmetric_FXC1 Λ) hsec,
    segments_of_riemannianEDistOf_eq (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ),
    PUnit.{1}, inferInstance, PUnit.unit, ⟨RadialConeData.punit⟩, inferInstance,
    fun τ hτ hτ1 => exists_kleinerLottApprox_rescale_point_of_compactSpace p hτ hτ1,
    Tor_FXC1 Λ, inferInstance, inferInstance, inferInstance, Homeomorph.refl _,
    fun y _ => torMetric_sectional_FXC1 Λ y (by
      have : 0 ≤ ((1 / 60 : ℝ) ^ 2 * ((s * r)⁻¹) ^ 2) := by positivity
      linarith), ⟨φ⟩, hF, hΨ⟩

theorem euclid_hmetric_FXT (a b : E3) :
    riemannianEDistOf (gE3) a b = ENNReal.ofReal (dist a b) := by
  rw [riemannianEDistOf_euclid_FXC1, dist_eq_norm]

theorem euclid_sec_FXT (x : E3) : SectionalBoundedBelowAt (gE3) x 0 := by
  intro v w
  simp only [zero_mul, metricRm04StandardAt_apply, euclideanMetric_metricRm04At_eq_zero,
    zero_apply, le_refl]

/-- **Regime S (small scale)**: `s r ≤ δ f/4` with `f` a lower bound of the periods. -/
theorem torAtSmall_FXT (Λ : TorusPeriods_FXC1) {f : ℝ} (hf0 : 0 < f) (hf : ∀ i, f ≤ Λ.L i)
    (K : ℕ) {ε e δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e) (he1 : e < 1 / 40) (hδ : 0 < δ)
    (hδ2 : δ < radialSmoothingConeError (ε / 4)) (p : Tor_FXC1 Λ) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) (hsr : s * r ≤ δ * (f / 4)) :
    Lpa02WitnessAtV2 (torMetric_FXC1 Λ) K ε e δ p r s hr hs := by
  have hδ1 : δ < 1 := hδ2.trans_le ((min_le_left _ _).trans (by norm_num))
  have hn : ((K - 1 : ℕ) : ℕ∞ω) ≤ ∞ := by simp
  have hsr0 : 0 < s * r := mul_pos hs hr
  have hsec : ∀ y, SectionalBoundedBelowAt (torMetric_FXC1 Λ) y 0 := fun y =>
    torMetric_sectional_FXC1 Λ y le_rfl
  have hbuf : ∀ y ∈ Metric.ball p (400 * (s * r)),
      SectionalBoundedBelowAt (torMetric_FXC1 Λ) y (-((1 / 60) ^ 2 * (s * r)⁻¹ ^ 2)) :=
    fun y _ => torMetric_sectional_FXC1 Λ y (by
      have : 0 ≤ ((1 / 60 : ℝ) ^ 2 * ((s * r)⁻¹) ^ 2) := by positivity
      linarith)
  obtain ⟨pt, rfl⟩ := torPi_surjective_FXC1 Λ p
  obtain ⟨φ⟩ := klSmall_FXT Λ hf0 hf (torPi_FXC1 Λ pt) hsr0 hδ hδ1 hsr
  have hF := exists_buffered_radial_cutoff_at_scale (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ)
    hsr0 φ (RadialConeData.ofInnerProductSpace E3) hbuf hε hε1 hδ2 he he1
  have hΨ : ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (Tor_FXC1 Λ) E3 ∞,
      Ψ.source = Metric.ball (torPi_FXC1 Λ pt) (ρ' * (s * r)) ∧ Ψ.target = univ := by
    intro ρ' hρ'
    refine exists_ballDiffeo_FXT Λ hf0 hf pt (mul_pos (by linarith [hρ'.1]) hsr0) ?_
    nlinarith [hρ'.2]
  have : NeZero (Module.finrank ℝ E3) := ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  unfold Lpa02WitnessAtV2
  refine ⟨E3, inferInstance, inferInstance, inferInstance,
    weakMetric_FXT _ hn (gE3), 0, inferInstance, inferInstance,
    isRiemannianManifold_weak_FXT _ hn (gE3) euclid_hmetric_FXT,
    weakMetric_sectional_FXT _ hn (gE3) euclid_sec_FXT,
    fourPointComparison_zero_univ_of_sectional_nonneg (gE3)
      euclid_hmetric_FXT euclid_sec_FXT,
    segments_of_riemannianEDistOf_eq (gE3) euclid_hmetric_FXT,
    E3, inferInstance, 0, ⟨RadialConeData.ofInnerProductSpace E3⟩, inferInstance,
    fun τ hτ hτ1 => ⟨0, fun R' hR' _ =>
      RadialConeData.nonempty_kleinerLottApprox_rescale_self
        (RadialConeData.ofInnerProductSpace E3) R' hR' hτ hτ1⟩,
    E3, inferInstance, inferInstance, inferInstance, Homeomorph.refl _, hbuf, ⟨φ⟩, hF, hΨ⟩

end DifferentialGeometry.Geometry.Collapse
