import DifferentialGeometry.Geometry.Collapse.EventualAnnularCutoff
import DifferentialGeometry.Geometry.Collapse.GoodAnnulusConeScaleRiemannian

/-!
# LC31 with its Riemannian limit models

Blueprint 207A, LC31 (`thm:collapse-eventual-radial-cutoff`, A:21294–21355): "Retain LC24's fixed
data, smooth compactness and Tits-cone inputs, and the smoothing/comparison inputs of LC30." The
metric form `exists_eventual_annularCutoff` (`EventualAnnularCutoff.lean`) composes the METRIC form of
LC24; its cone is the cone of a metric limit. Here the same argument is run on the Riemannian
binding of LC24, `exists_good_annulus_riemannian_cone_scale` (smooth compactness input in the form of
LC56's item (1): a family of complete Riemannian limit models with `sec ≥ 0`), so the cone map,
the LC30 radial function `η` and the cutoff `ζ = Φ ∘ η` are attached to the cone of an actual
Riemannian limit model `N_b` (identified by its Kleiner–Lott maps from the blow-downs of `N_b`).
The curvature input of LC30 is the standing buffer `sec ≥ -(L_α ρ_α(p))⁻²` on
`B(p, L_α ρ_α(p))`, `L_α → ∞`, transferred to `sec_ĝ ≥ -(1/60)²` on `B_ĝ(p, 400)` on a tail chosen
AFTER `V` (`L_α ≥ 400 V`, the blueprint's `H > 400 V`); LC31 at the supplied scale
(`exists_annularCutoff_of_kleinerLottApprox`) is applied to the SAME cone map.

The conclusion is stated in the rescaled units `d̂ = (r_p^0)⁻¹ d` of `ĝ = (r_p^0)⁻² g^α`, with the
scale written as `r_p^0 ∈ [T ρ_α(p), V ρ_α(p)]`. Deviations as in the metric form: `ε < 1`,
`e < 1/40`, `T > 0` (the row: `ε < 1/4`, `e < min(ε, 1/40)`, `T > 1`).

* `exists_eventual_annularCutoff_riemannian`: LC31 with the Riemannian limit models.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal Topology
open Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u w z

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type u} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
  [∀ α, IsManifold I ∞ (M α)]
  [∀ α, SigmaCompactSpace (M α)] [∀ α, CompleteSpace (M α)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]

/-- **LC31 with the Riemannian limit models.** Standing buffer `sec ≥ -(L_α ρ_α(p))⁻²` on
`B(p, L_α ρ_α(p))` with `L_α → ∞`, and LC24's smooth compactness input with Riemannian limit models
`(N_b, g_b, n_b)` (complete, `sec ≥ 0`). For `0 < ε < 1`, `0 < e < 1/40`, `T > 0` there are `V ≥ T`
and `α₀` such that every `α > α₀` and `p ∈ M^α` have a scale `r ∈ [T ρ_α(p), V ρ_α(p)]` at which,
in the metric `ĝ = r⁻² g^α` (distance `d̂ = r⁻¹ d`): a model `b`, the cone `(C, o)` of `(N_b, n_b)`
with AC82 data and an actual Kleiner–Lott map with error `δ₀(ε)/2` (LC24), an LC30 radial function
`η = F` and the cutoff `ζ = Φ ∘ η`, globally smooth, compactly supported, `[0,1]`-valued, one on
`η⁻¹[3/10, 4/5]`, supported in `{1/5 - e < d̂_p < 9/10 + e}`, `‖∇ζ‖_ĝ ≤ L_Φ (1 + ε)`. -/
theorem exists_eventual_annularCutoff_riemannian (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hsec : ∀ α (p : M α), ∀ y ∈ riemannianBallOf (g α) p (L α * ρ α p),
      SectionalBoundedBelowAt (g α) y (-((L α * ρ α p) ^ 2)⁻¹))
    {ι : Type w} {N : ι → Type z} [mN : ∀ b, MetricSpace (N b)] [∀ b, ChartedSpace H' (N b)]
    [∀ b, IsManifold I' ∞ (N b)] [∀ b, SigmaCompactSpace (N b)] [∀ b, CompleteSpace (N b)]
    (gN : ∀ b, SmoothRiemannianMetric I' (N b))
    (hmetricN : ∀ b x y, riemannianEDistOf (gN b) x y = ENNReal.ofReal (dist x y))
    (hsecN : ∀ b y, SectionalBoundedBelowAt (gN b) y 0) (n : ∀ b, N b)
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b))
    {ε e T : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e) (he1 : e < 1 / 40) (hT : 0 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ r : ℝ, ∃ hr : 0 < r, T * ρ α p ≤ r ∧ r ≤ V * ρ α p ∧
      letI : MetricSpace (M α) := (mM α).rescale r⁻¹ (inv_pos.mpr hr)
      let ĝ : SmoothRiemannianMetric I (M α) := scaleMetric (r⁻¹ ^ 2)
        (pow_pos (inv_pos.mpr hr) 2) (g α)
      (∀ x y, riemannianEDistOf ĝ x y = ENNReal.ofReal (dist x y)) ∧
      (∃ b : ι, ∃ (C : Type z) (mC : MetricSpace C) (o : C), Nonempty (@RadialConeData C mC o) ∧
        (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
          Nonempty (@KleinerLottApprox (N b) C ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) mC
            (n b) o τ)) ∧
        Nonempty (@KleinerLottApprox (M α) C _ mC p o (radialSmoothingConeError (ε / 4) / 2))) ∧
      ∃ F : M α → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        (∃ O : Set (M α), IsOpen O ∧ {x : M α | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
        (∀ x, |F x - Metric.infDist x {p}| < e) ∧
        (∀ x, x ∉ {x : M α | 1 / 20 < dist x p ∧ dist x p < 20} → F x = Metric.infDist x {p}) ∧
        (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤ ε * dist x y) ∧
        (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
        (∀ q ∈ {x : M α | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
          1 - ε ≤ Real.sqrt (ĝ.inner q (gradFun ĝ F q) (gradFun ĝ F q)) ∧
            Real.sqrt (ĝ.inner q (gradFun ĝ F q) (gradFun ĝ F q)) ≤ 1 + ε) ∧
        F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M α | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
        HasCompactSupport (fun x => annularCutoff cutoffProfile (F x)) ∧
        (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
        tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
          {x : M α | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
        ∀ q, Real.sqrt (ĝ.inner q (gradFun ĝ (fun x => annularCutoff cutoffProfile (F x)) q)
          (gradFun ĝ (fun x => annularCutoff cutoffProfile (F x)) q)) ≤
            (⨆ t, |deriv (annularCutoff cutoffProfile) t|) * (1 + ε) := by
  have hrsce := radialSmoothingConeError_pos (θ := ε / 4) (by positivity)
  have hrsce1 : radialSmoothingConeError (ε / 4) ≤ 1 / 600 := min_le_left _ _
  have hδ0 : 0 < radialSmoothingConeError (ε / 4) / 2 := by positivity
  have hδ1 : radialSmoothingConeError (ε / 4) / 2 < 1 := by linarith
  have hδr : radialSmoothingConeError (ε / 4) / 2 < radialSmoothingConeError (ε / 4) := by
    linarith
  obtain ⟨V, hTV, α₁, h24⟩ := exists_good_annulus_riemannian_cone_scale g hmetric ρ hρ gN
    hmetricN hsecN n hmodel hδ0 hδ1 hT
  obtain ⟨α₂, hα₂⟩ := eventually_atTop.mp (hL.eventually (eventually_ge_atTop (400 * V)))
  refine ⟨V, hTV, max α₁ α₂, fun α hα p => ?_⟩
  obtain ⟨r, hr, hTr, hrV, b, C, mC, o, ⟨Hc⟩, -, -, -, -, -, hK, hid, ⟨φ⟩⟩ :=
    h24 α ((le_max_left _ _).trans_lt hα) p
  have hLα : 400 * V ≤ L α := hα₂ α ((le_max_right _ _).trans hα.le)
  have hρpos := hρ α p
  have h400 : 400 * r ≤ L α * ρ α p := by
    have h1 : 400 * V * ρ α p ≤ L α * ρ α p := mul_le_mul_of_nonneg_right hLα hρpos.le
    nlinarith
  -- the curvature transfer to the cone scale (before the rescaled metric is installed)
  have hsec' : ∀ y ∈ @Metric.ball (M α) ((mM α).rescale r⁻¹
      (inv_pos.mpr hr)).toPseudoMetricSpace p 400,
      SectionalBoundedBelowAt (scaleMetric (r⁻¹ ^ 2)
        (pow_pos (inv_pos.mpr hr) 2) (g α)) y (-(1 / 60) ^ 2) := by
    intro y hy
    change r⁻¹ * dist y p < 400 at hy
    rw [inv_mul_lt_iff₀ hr] at hy
    have hyL : dist p y < L α * ρ α p := by
      rw [dist_comm]
      linarith
    have hmem : y ∈ riemannianBallOf (g α) p (L α * ρ α p) := by
      change riemannianEDistOf (g α) p y < ENNReal.ofReal (L α * ρ α p)
      rw [hmetric]
      have hLpos : 0 < L α * ρ α p := by linarith
      exact (ENNReal.ofReal_lt_ofReal_iff hLpos).mpr hyL
    rw [sectionalBoundedBelowAt_scaleMetric_iff]
    refine (hsec α p y hmem).mono ?_
    have h60 : 60 * r ≤ L α * ρ α p := by linarith
    have hsq : (60 * r) ^ 2 ≤ (L α * ρ α p) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h60 2
    have hinv : ((L α * ρ α p) ^ 2)⁻¹ ≤ ((60 * r) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hsq
    have heq : -(1 / 60 : ℝ) ^ 2 * r⁻¹ ^ 2 = -((60 * r) ^ 2)⁻¹ := by
      field_simp
    rw [heq]
    linarith
  refine ⟨r, hr, hTr, hrV, ?_⟩
  -- the Riemannian package of the metric `ĝ` at the cone scale
  let mR : MetricSpace (M α) := (mM α).rescale r⁻¹ (inv_pos.mpr hr)
  let ĝ : SmoothRiemannianMetric I (M α) := scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) (g α)
  let : RiemannianBundle (fun x : M α => TangentSpace I x) := ⟨ĝ.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun x : M α => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric ĝ
  have hEnorm : IsMetricNorm (I := I) ĝ := isMetricNorm_of_smoothRiemannianMetric ĝ
  have : IsRiemannianManifold I (M α) := ⟨fun x y => by
    rw [← riemannianEDistOf_eq_riemannianEDist ĝ hEnorm, hid x y, edist_dist]⟩
  have : CompleteSpace (M α) :=
    (MetricSpace.rescale_completeSpace_iff (mM α) _ (inv_pos.mpr hr)).mpr inferInstance
  obtain ⟨F, hF⟩ := exists_annularCutoff_of_kleinerLottApprox ĝ hEnorm φ Hc hsec' hε hε1 hδr
    he he1
  exact ⟨hid, ⟨b, C, mC, o, ⟨Hc⟩, hK, ⟨φ⟩⟩, F, hF⟩

end DifferentialGeometry.Geometry.Collapse
