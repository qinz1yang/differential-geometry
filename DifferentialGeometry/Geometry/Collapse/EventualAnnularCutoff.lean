import DifferentialGeometry.Geometry.Collapse.GoodAnnulusConeScaleFull
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.RadialFunction
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry

/-!
# LC31: the eventual radial function and compact annular cutoff

Blueprint 207A, LC31 (`thm:collapse-eventual-radial-cutoff`, A:21294–21355). LC24 selects, on a
tail of the standing sequence, a cone scale `r_p^0 = s ρ_α(p)` with `s ∈ [T, V]`, an AC82 cone and an
actual Kleiner–Lott `δ`-map in the metric `ĝ = (r_p^0)⁻² g_α`
(`exists_good_annulus_cone_scale`, now unconditional through the Tits-cone producer). On a later
tail (`L_α ≥ 400 V`, chosen after `V`) the curvature buffer transfers to `sec_ĝ ≥ -(1/60)²` on
`B_ĝ(p, 400)` (the blueprint's `H > 400 V`), and LC31 at a supplied cone scale
(`exists_annularCutoff_of_kleinerLottApprox`, lane W3-LC28) applies to the SAME cone map in the
metric `ĝ`: its Riemannian package (bundle `⟨ĝ⟩`, `IsRiemannianManifold` from LC24's identity
`riemannianEDistOf ĝ = d̂`, completeness of the rescaled metric) is installed inside the proof.

The conclusion is stated in the rescaled units: within the `letI`, `dist`, balls, `infDist` and
Lipschitz constants refer to the metric `d̂ = (r_p^0)⁻¹ d`, which LC24's identity shows to be the
distance of `ĝ`.
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

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type u} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
  [∀ α, IsManifold I ∞ (M α)] [∀ α, T2Space (TangentBundle I (M α))]
  [∀ α, SigmaCompactSpace (M α)] [∀ α, CompleteSpace (M α)]

/-- **LC31** (eventual clause): with the curvature buffer of the standing sequence, for every
`0 < ε < 1`, `0 < e < 1/40` and `T > 0` there are `V ≥ T` and `α₀` such that for `α > α₀` and every
`p ∈ M^α` there is a cone scale `r_p^0 = s ρ_α(p)`, `s ∈ [T, V]`, at which (in the metric
`ĝ = (r_p^0)⁻² g_α`, whose distance is the rescaled `d̂`): an AC82 cone and an actual
Kleiner–Lott map with error `δ₀(ε)/2` (LC24), an LC30 radial function `η = F` and the cutoff
`ζ = Φ ∘ η`, globally smooth, compactly supported, `[0,1]`-valued, one on `η⁻¹[3/10, 4/5]`,
topologically supported in `{1/5 - e < d̂_p < 9/10 + e}`, with `‖∇ζ‖_ĝ ≤ L_Φ (1 + ε)`. -/
theorem exists_eventual_annularCutoff (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hsec : ∀ α (p : M α), ∀ y ∈ riemannianBallOf (g α) p (L α * ρ α p),
      SectionalBoundedBelowAt (g α) y (-((L α * ρ α p) ^ 2)⁻¹))
    {ε e T : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e) (he1 : e < 1 / 40) (hT : 0 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ s : ℝ, ∃ hs : 0 < s, T ≤ s ∧ s ≤ V ∧
      letI : MetricSpace (M α) :=
        (mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))
      let ĝ : SmoothRiemannianMetric I (M α) := scaleMetric ((s * ρ α p)⁻¹ ^ 2)
        (pow_pos (inv_pos.mpr (mul_pos hs (hρ α p))) 2) (g α)
      (∀ x y, riemannianEDistOf ĝ x y = ENNReal.ofReal (dist x y)) ∧
      (∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (@RadialConeData C mC o) ∧
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
  obtain ⟨V, hTV, α₁, h24⟩ := exists_good_annulus_cone_scale g hmetric ρ hρ hL hsec hδ0 hδ1 hT
  obtain ⟨α₂, hα₂⟩ := eventually_atTop.mp (hL.eventually (eventually_ge_atTop (400 * V)))
  refine ⟨V, hTV, max α₁ α₂, fun α hα p => ?_⟩
  obtain ⟨s, hs, hTs, hsV, C, mC, o, ⟨Hc⟩, hid, ⟨φ⟩⟩ :=
    h24 α ((le_max_left _ _).trans_lt hα) p
  have hLα : 400 * V ≤ L α := hα₂ α ((le_max_right _ _).trans hα.le)
  have hcpos : 0 < s * ρ α p := mul_pos hs (hρ α p)
  have hρpos := hρ α p
  -- the curvature transfer to the cone scale (before the rescaled metric is installed)
  have hsec' : ∀ y ∈ @Metric.ball (M α) ((mM α).rescale (s * ρ α p)⁻¹
      (inv_pos.mpr hcpos)).toPseudoMetricSpace p 400,
      SectionalBoundedBelowAt (scaleMetric ((s * ρ α p)⁻¹ ^ 2)
        (pow_pos (inv_pos.mpr hcpos) 2) (g α)) y (-(1 / 60) ^ 2) := by
    intro y hy
    change (s * ρ α p)⁻¹ * dist y p < 400 at hy
    rw [inv_mul_lt_iff₀ hcpos] at hy
    have hyL : dist p y < L α * ρ α p := by
      rw [dist_comm]
      nlinarith
    have hmem : y ∈ riemannianBallOf (g α) p (L α * ρ α p) := by
      change riemannianEDistOf (g α) p y < ENNReal.ofReal (L α * ρ α p)
      rw [hmetric]
      have hV : 0 < V := hT.trans_le hTV
      have hLpos : 0 < L α * ρ α p := mul_pos (by linarith) hρpos
      exact (ENNReal.ofReal_lt_ofReal_iff hLpos).mpr hyL
    rw [sectionalBoundedBelowAt_scaleMetric_iff]
    refine (hsec α p y hmem).mono ?_
    have h60 : 60 * (s * ρ α p) ≤ L α * ρ α p := by nlinarith
    have hsq : (60 * (s * ρ α p)) ^ 2 ≤ (L α * ρ α p) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h60 2
    have hinv : ((L α * ρ α p) ^ 2)⁻¹ ≤ ((60 * (s * ρ α p)) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hsq
    have heq : -(1 / 60 : ℝ) ^ 2 * (s * ρ α p)⁻¹ ^ 2 = -((60 * (s * ρ α p)) ^ 2)⁻¹ := by
      field_simp
    rw [heq]
    linarith
  refine ⟨s, hs, hTs, hsV, ?_⟩
  -- the Riemannian package of the metric `ĝ` at the cone scale
  let mR : MetricSpace (M α) := (mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr hcpos)
  let ĝ : SmoothRiemannianMetric I (M α) := scaleMetric ((s * ρ α p)⁻¹ ^ 2)
    (pow_pos (inv_pos.mpr hcpos) 2) (g α)
  let : RiemannianBundle (fun x : M α => TangentSpace I x) := ⟨ĝ.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun x : M α => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric ĝ
  have hEnorm : IsMetricNorm (I := I) ĝ := isMetricNorm_of_smoothRiemannianMetric ĝ
  have : IsRiemannianManifold I (M α) := ⟨fun x y => by
    rw [← riemannianEDistOf_eq_riemannianEDist ĝ hEnorm, hid x y, edist_dist]⟩
  have : CompleteSpace (M α) :=
    (MetricSpace.rescale_completeSpace_iff (mM α) _ (inv_pos.mpr hcpos)).mpr inferInstance
  obtain ⟨F, hF⟩ := exists_annularCutoff_of_kleinerLottApprox ĝ hEnorm φ Hc hsec' hε hε1 hδr
    he he1
  exact ⟨hid, ⟨C, mC, o, ⟨Hc⟩, ⟨φ⟩⟩, F, hF⟩

end DifferentialGeometry.Geometry.Collapse
