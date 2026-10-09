import DifferentialGeometry.Geometry.Collapse.GoodAnnulusConeScale
import DifferentialGeometry.Geometry.Collapse.RiemannianConeScale
import DifferentialGeometry.Geometry.Metric.Approximation.RayConeAtInfinity

/-!
# LC24: good annulus cone scales for actual rescaled sequences (unconditional)

Blueprint 207A, LC24 (`cor:collapse-kl-metric-cone-scale`, A:20898–20951). The blueprint applies
LC23 to the standing sequence at the modified scales, using the pointed Gromov–Hausdorff limits of
KL 6.10(3) and the Tits-cone input LC21 for those limits.

Both inputs are now produced:

* the limits: `sequentialModelProperty_of_sectional_buffer` (lane W3-F4, from W3-F1's
  `exists_rescaled_pointed_limit_of_sectional_buffer`) — complete proper geodesic spaces with
  nonnegative four-point comparison;
* the LC21 package for every such limit: `exists_cone_at_infinity_of_fourPointComparison_zero`
  (tier T3 of the Tits-cone producer, the metric form of LFR55–LFR58), which needs only
  properness, segments and `fourPointComparison 0`.

`exists_good_annulus_cone_scale` is the conditional composition of `build-logs/resume/
LC24-conditional-draft.lean.txt` with the hypothesis `htits` replaced by the producer. The exact
producer statement that lane W3-F4 required (`exists_tits_cone_package`, sheet-W3-F4.md
Addendum 3) is checked verbatim below as an `example`: its hypotheses `hdim` and
`CompleteSpace Y` are not needed, so the library theorem is the stronger (F).
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

/-- The producer statement required by lane W3-F4 (sheet-W3-F4.md Addendum 3), verbatim; it is
(F) with two unused hypotheses and without the properness of the cone. -/
example : ∀ {n : ℕ} (Y : Type) [MetricSpace Y] (q : Y) [CompleteSpace Y] [ProperSpace Y]
    (hdim : dimH (univ : Set Y) ≤ n) (hcomp : fourPointComparison 0 (univ : Set Y))
    (hseg : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧
      f ⟨1, by norm_num⟩ = b ∧ ∀ s t, dist (f s) (f t) = dist a b * dist s t),
    ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (@RadialConeData C mC o) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox Y C ((inferInstance : MetricSpace Y).rescale R⁻¹
          (inv_pos.mpr hR)) mC q o ε) := by
  intro n Y _ q _ _ _ hcomp hseg
  obtain ⟨C, mC, o, hH, -, hK⟩ := exists_cone_at_infinity_of_fourPointComparison_zero hcomp hseg q
  exact ⟨C, mC, o, hH, hK⟩

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type u} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
  [∀ α, IsManifold I ∞ (M α)] [∀ α, T2Space (TangentBundle I (M α))]
  [∀ α, SigmaCompactSpace (M α)] [∀ α, CompleteSpace (M α)]

/-- LC24 on actual rescaled sequences: with the curvature buffer of the standing sequence, for
every `0 < δ < 1` and `T > 0` there are `V ≥ T` and a tail on which every point has a cone scale
`r_p^0 = s ρ_α(p)`, `s ∈ [T, V]`, an AC82 cone `(C, o)` and an actual Kleiner–Lott `δ`-map from the
manifold with metric tensor `(r_p^0)⁻² g_α` (its metric rescaling, which realizes that distance)
to `(C, o)`. The Tits-cone input is produced by `exists_cone_at_infinity_of_fourPointComparison_zero`. -/
theorem exists_good_annulus_cone_scale (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hsec : ∀ α (p : M α), ∀ y ∈ riemannianBallOf (g α) p (L α * ρ α p),
      SectionalBoundedBelowAt (g α) y (-((L α * ρ α p) ^ 2)⁻¹))
    {δ T : ℝ} (hδ : 0 < δ) (hδone : δ < 1) (hT : 0 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ s : ℝ, ∃ hs : 0 < s, T ≤ s ∧ s ≤ V ∧
        ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (@RadialConeData C mC o) ∧
        (∀ x y, riemannianEDistOf (scaleMetric ((s * ρ α p)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (mul_pos hs (hρ α p))) 2) (g α)) x y =
          ENNReal.ofReal (@dist (M α) ((mM α).rescale (s * ρ α p)⁻¹
            (inv_pos.mpr (mul_pos hs (hρ α p)))).toDist x y)) ∧
        Nonempty (@KleinerLottApprox (M α) C ((mM α).rescale (s * ρ α p)⁻¹
          (inv_pos.mpr (mul_pos hs (hρ α p)))) mC p o δ) := by
  -- the limit class, indexed by pointed metric spaces with the producer's hypotheses
  let ι : Type 1 := {b : Σ Y : Type, MetricSpace Y × Y //
    @ProperSpace b.1 b.2.1.toPseudoMetricSpace ∧
    @fourPointComparison b.1 b.2.1 0 (univ : Set b.1) ∧
    ∀ x y : b.1, ∃ f : Icc (0 : ℝ) 1 → b.1, Continuous[_, b.2.1.toUniformSpace.toTopologicalSpace] f ∧
      f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, @dist b.1 b.2.1.toDist (f s) (f t) = @dist b.1 b.2.1.toDist x y * dist s t}
  have hcone (b : ι) := @exists_cone_at_infinity_of_fourPointComparison_zero b.1.1 b.1.2.1 b.2.1
    b.2.2.1 b.2.2.2 b.1.2.2
  choose C mC o hH _ hK using hcone
  obtain ⟨V, hTV, α₀, h⟩ := exists_riemannian_bounded_cone_scale g hmetric ρ hρ
    (N := fun b : ι => b.1.1) (mN := fun b => b.1.2.1) (C := C) (mC := mC)
    (fun b => b.1.2.2) o
    (fun a ha z => by
      obtain ⟨Y, m, q, k, hk, -, hp, hconv, -, h4, hseg⟩ :=
        sequentialModelProperty_of_sectional_buffer g hmetric ρ hρ hL hsec a ha z
      exact ⟨⟨⟨Y, m, q⟩, hp, h4, hseg⟩, k, hk, hconv⟩)
    hK hδ hδone hT
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨s, hs, hTs, hsV, b, hid, hk⟩ := h α hα p
  exact ⟨s, hs, hTs, hsV, C b, mC b, o b, hH b, hid, hk⟩

end DifferentialGeometry.Geometry.Collapse
