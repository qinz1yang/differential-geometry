import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChart

/-!
# Producers and a consumer of the LC85 slim chart

* `SlimChart.ofCoordinate`: every coordinate with LFR19's displayed estimates, for a splitting with
  `diam Y ≤ 10³Δ` and `β ≤ 10⁻⁸Δ⁻¹`, is a slim chart (LFR20 items 2 and 4 except the fibre type);
* `exists_slimChart` (LC85's producer from LFR19 + LFR20, threshold form): for `Δ ≥ 1`,
  `0 < σ ≤ 1/100` there is `β₀ > 0` such that every complete pointed manifold with
  `sec ≥ -β²` on `B(p, β⁻¹)` and every normalized `(1, β)`-splitting with `diam Y ≤ 10³Δ`,
  `β < β₀`, carries a slim chart;
* consumer `SlimChart.isCompact_zeroLevel`: the ENTIRE zero level `{x ∈ B(p, L) | η x = 0}` is
  compact and nonempty, and lies in `B(p, 0.91L)`; the cutoff is one on it.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Producer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LFR20 → LC85.** A coordinate with LFR19's displayed estimates is a slim chart. -/
def SlimChart.ofCoordinate (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {Δ σ β : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100) (hβΔ : β * (10 ^ 8 * Δ) ≤ 1)
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y}
    (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β)
    (hD : ∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ)
    (η : M → ℝ) (O : Set M) (hO : IsOpen O) (hLO : closedBall p (10 ^ 6 * Δ) ⊆ O)
    (hη : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η O) (hηp : η p = 0)
    (hηl : LipschitzWith (Real.toNNReal (1 + σ)) η)
    (hval : ∀ x ∈ ball p (10 ^ 6 * Δ), |η x - (α.toFun x).fst| < Δ / 100)
    (h19 : ∀ x ∈ ball p (10 ^ 6 * Δ), ∀ x' ∈ ball p (10 ^ 6 * Δ / σ), 10 ^ 6 * Δ < dist x x' →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x x') = x' →
      |mvfderiv (I := I) η x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) :
    SlimChart g hEnorm Δ σ α :=
  have hcl := slimPacket_clauses_of_coordinate g hEnorm hΔ hσ hσ1 hβΔ α hD hO hLO hη hηl hval h19
  have hψ := exists_slim_profile (by linarith : (0 : ℝ) < Δ)
  let ψ := Classical.choose hψ
  have hψs := Classical.choose_spec hψ
  have hcut := hcl.2.2.2.2 ψ (89 * 10 ^ 4 * Δ) hψs.1 (by nlinarith)
    (fun s hs => by
      by_contra hne
      exact (not_lt.mpr hs.le) (hψs.2.2.2 s hne))
  { coord := η
    domain := O
    isOpen_domain := hO
    closedBall_subset_domain := hLO
    contMDiffOn_coord := hη
    coord_center := hηp
    lipschitz := hηl
    value := hval
    test := h19
    enclosure := hcl.1
    derivative := hcl.2.1
    surjective := hcl.2.2.1
    regular := Classical.choose hcl.2.2.2.1
    isProperMap := (Classical.choose_spec hcl.2.2.2.1).1
    trivial := (Classical.choose_spec hcl.2.2.2.1).2
    cutoff := (ball p (10 ^ 6 * Δ)).indicator (ψ ∘ η)
    contMDiff_cutoff := hcut.1
    hasCompactSupport_cutoff := hcut.2.1
    cutoff_mem_Icc := fun x => by
      by_cases hx : x ∈ ball p (10 ^ 6 * Δ)
      · rw [Set.indicator_of_mem hx]
        exact hψs.2.1 (η x)
      · rw [Set.indicator_of_notMem hx]
        exact ⟨le_rfl, zero_le_one⟩
    cutoff_eq_one := fun x hx hxη => by
      rw [Set.indicator_of_mem hx]
      exact hψs.2.2.1 (η x) hxη
    cutoff_ne_zero := fun x hx => by
      by_cases hxL : x ∈ ball p (10 ^ 6 * Δ)
      · rw [Set.indicator_of_mem hxL] at hx
        exact ⟨hxL, hψs.2.2.2 (η x) hx⟩
      · exact absurd (Set.indicator_of_notMem hxL _) hx
    tsupport_cutoff := hcut.2.2 }

end Producer

universe uE uH u v

/-- **LC85's producer (LFR19 + LFR20, threshold form).** For `Δ ≥ 1`, `0 < σ ≤ 1/100` there is
`β₀ > 0` such that, for `β < β₀`, every complete pointed smooth manifold with `sec ≥ -β²` on
`B(p, β⁻¹)` and every normalized `(1, β)`-splitting with factor of diameter `≤ 10³Δ` carries a
slim chart. (LFR20's noncollapse and derivative hypotheses are not needed for these clauses.) -/
theorem exists_slimChart {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type v) [MetricSpace Y] (p : M) (y₀ : Y)
        (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ) →
        (∀ y ∈ Metric.ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        Nonempty (SlimChart g hEnorm Δ σ α) := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨β₁, hβ₁, h19⟩ := exists_rankOne_coordinate_value_tolerance
    (L := 10 ^ 6 * Δ) (T := 10 ^ 6 * Δ / σ) (e := Δ / 100) (σ := σ) (by positivity)
    (by rw [lt_div_iff₀ hσ]; nlinarith) (by positivity) hσ (by linarith)
  refine ⟨min β₁ (1 / (10 ^ 8 * Δ)), lt_min hβ₁ (by positivity), ?_⟩
  intro β hβ hβ₀ E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α hD hsec
  have hβΔ : β * (10 ^ 8 * Δ) ≤ 1 := by
    have h := (hβ₀.trans_le (min_le_right _ _)).le
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨η, O, hO, hLO, hη, hηp, hηl, hval, -, -, htest⟩ :=
    h19 β hβ (hβ₀.trans_le (min_le_left _ _)) E H I M g hEnorm Y p y₀ α hsec
  exact ⟨SlimChart.ofCoordinate g hEnorm hΔ hσ hσ1 hβΔ α hD η O hO hLO hη hηp hηl hval htest⟩

section Consumer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Consumer.** The ENTIRE zero level of a slim chart in `B(p, L)` is compact, nonempty, lies
in `B(p, 0.91L)`, and the cutoff equals one on it. -/
theorem SlimChart.isCompact_zeroLevel {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g}
    {Δ σ : ℝ} (hΔ : 0 < Δ) {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β} (c : SlimChart g hEnorm Δ σ α) :
    IsCompact {x | x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = 0} ∧
      {x | x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = 0}.Nonempty ∧
      (∀ x ∈ ball p (10 ^ 6 * Δ), c.coord x = 0 → dist x p < 91 / 100 * (10 ^ 6 * Δ)) ∧
      ∀ x ∈ ball p (10 ^ 6 * Δ), c.coord x = 0 → c.cutoff x = 1 := by
  have ha : (0 : ℝ) < 905 * 10 ^ 3 * Δ := by positivity
  set f := realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
    c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
  have h0 : IsCompact (f ⁻¹' {⟨0, zero_mem_lineBallOpens ha⟩}) :=
    c.isProperMap.isCompact_preimage isCompact_singleton
  have heq : Subtype.val '' (f ⁻¹' {⟨0, zero_mem_lineBallOpens ha⟩}) =
      {x | x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = 0} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(mem_realSlabOpens_iff.mp u.2).1, congrArg Subtype.val hu⟩
    · rintro ⟨hx, hx0⟩
      have hxS : x ∈ realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
          c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) :=
        mem_realSlabOpens_iff.mpr ⟨hx, by rw [hx0, abs_zero]; exact ha⟩
      exact ⟨⟨x, hxS⟩, Subtype.ext hx0, rfl⟩
  refine ⟨heq ▸ h0.image continuous_subtype_val, ?_, ?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := c.surjective ⟨by linarith, ha.le⟩
    exact ⟨x, hx, hx0⟩
  · intro x hx hx0
    exact c.enclosure x hx (by rw [hx0, abs_zero]; exact ha.le)
  · intro x hx hx0
    exact c.cutoff_eq_one x hx (by rw [hx0, abs_zero]; positivity)

end Consumer

end DifferentialGeometry.Geometry.Collapse
