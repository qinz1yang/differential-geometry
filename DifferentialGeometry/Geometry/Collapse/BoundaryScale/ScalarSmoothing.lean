import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Boundary.Assembly
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.AnalyticData

/-!
# Smoothing scalars up to the boundary of a compact carrier (BSA03.a, BSA05 smoothing step)

Blueprint 207B, BSA03.a (`B:7764–7781`, proof `B:7810–7836`) and the smoothing step of BSA05
(`B:7915–7973`), on a `CompactCarrier` (closed or with boundary), for the `g`-length distance
`riemannianEDistOf g`.

* `CompactCarrier.exists_smooth_scalar_approx` (BSA03.a): an `L₀`-Lipschitz `f` has, for every
  `ε > 0`, a smooth (up to the boundary) `ε`-close approximation with Lipschitz constant
  `L < L₀ + ε`. Strengthening: the blueprint's `0 ≤ L₀` is not needed (for `L₀ < 0` the function is
  constant); the verbatim form is kept as an `example`.
* `exists_smooth_scale_of_envelope` (BSA05 smoothing step): from the pairwise envelope inequality
  `l p - (Λ/2) d(p, q) ≤ u q` with `l > 0` there is a smooth positive `Λ`-Lipschitz `ρ` with
  `l / 2 ≤ ρ ≤ 2 u` (MC19 `exists_lipschitz_between_of_envelope`, then BSA03.a with error
  `min (min f / 2) (Λ / 2)`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- BSA03.a on a compact carrier: Lipschitz smoothing up to the boundary, with a strictly smaller
Lipschitz constant than `L₀ + ε` (the blueprint's `0 ≤ L₀` is not needed). -/
theorem CompactCarrier.exists_smooth_scalar_approx (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) {f : W.Carrier → ℝ} {L₀ : ℝ}
    (hf : ∀ x y, ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal L₀ * riemannianEDistOf g x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧ (∀ x, |F x - f x| < ε) ∧
      ∃ L < L₀ + ε, ∀ x y,
        ENNReal.ofReal |F x - F y| ≤ ENNReal.ofReal L * riemannianEDistOf g x y := by
  rcases lt_or_ge L₀ 0 with hL | hL
  · -- a negative constant forces `f` to be constant
    have hconst : ∀ x y, f x = f y := by
      intro x y
      have h := hf x y
      rw [ENNReal.ofReal_of_nonpos hL.le, zero_mul, nonpos_iff_eq_zero,
        ENNReal.ofReal_eq_zero] at h
      exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
    refine ⟨f, ?_, fun x => by simpa using hε, L₀ + ε / 2, by linarith, fun x y => ?_⟩
    · rcases isEmpty_or_nonempty W.Carrier with hM | ⟨⟨x₀⟩⟩
      · exact fun x => (IsEmpty.false x).elim
      · have hfx : f = fun _ => f x₀ := funext fun x => hconst x x₀
        rw [hfx]
        exact contMDiff_const
    · rw [hconst x y, sub_self, abs_zero, ENNReal.ofReal_zero]
      exact bot_le
  · obtain ⟨F, hF, hclose, hlip⟩ :=
      exists_contMDiff_edist_lipschitz_approx g (K := Real.toNNReal L₀) hf (half_pos hε)
    refine ⟨F, hF, fun x => (hclose x).trans (by linarith), L₀ + ε / 2, by linarith,
      fun x y => ?_⟩
    have h := hlip x y
    rwa [Real.coe_toNNReal _ hL] at h

/-- BSA03.a in the blueprint's verbatim form (with the unused hypothesis `0 ≤ L₀`). -/
example (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
    {f : W.Carrier → ℝ} {L₀ : ℝ} (_hL₀ : 0 ≤ L₀)
    (hf : ∀ x y, ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal L₀ * riemannianEDistOf g x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧ (∀ x, |F x - f x| < ε) ∧
      ∃ L < L₀ + ε, ∀ x y,
        ENNReal.ofReal |F x - F y| ≤ ENNReal.ofReal L * riemannianEDistOf g x y :=
  CompactCarrier.exists_smooth_scalar_approx W g hf hε

/-- BSA05 smoothing step: a pairwise envelope `l p - (Λ/2) d(p, q) ≤ u q` with `l > 0` gives a
smooth (up to the boundary) positive `Λ`-Lipschitz scale `ρ` with `l / 2 ≤ ρ ≤ 2 u`. -/
theorem exists_smooth_scale_of_envelope (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {l u : W.Carrier → ℝ} {Λ : ℝ} (hΛ : 0 < Λ)
    (hl : ∀ p, 0 < l p)
    (henv : ∀ p q, l p - Λ / 2 * (riemannianEDistOf g p q).toReal ≤ u q) :
    ∃ ρ : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ p, 0 < ρ p) ∧
      (∀ p, l p / 2 ≤ ρ p ∧ ρ p ≤ 2 * u p) ∧
      ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y := by
  obtain ⟨f, hfc, hf, hlf⟩ : ∃ f : W.Carrier → ℝ, Continuous f ∧
      (∀ x y, ENNReal.ofReal |f x - f y| ≤
        ENNReal.ofReal (Λ / 2) * riemannianEDistOf g x y) ∧
      ∀ p, l p ≤ f p ∧ f p ≤ u p := by
    let := inducedMetricSpace g
    obtain ⟨f, hflip, hlf⟩ :=
      exists_lipschitz_between_of_envelope (by positivity : (0 : ℝ) ≤ Λ / 2) henv
    refine ⟨f, hflip.continuous, fun x y => ?_, hlf⟩
    have h := hflip.edist_le_mul x y
    rw [edist_dist, Real.dist_eq] at h
    exact h
  rcases isEmpty_or_nonempty W.Carrier with hM | hM
  · exact ⟨fun _ => 0, fun x => (IsEmpty.false x).elim, fun x => (IsEmpty.false x).elim,
      fun x => (IsEmpty.false x).elim, fun x => (IsEmpty.false x).elim⟩
  obtain ⟨x₀, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hfc.continuousOn
  have hm : 0 < f x₀ := (hl x₀).trans_le (hlf x₀).1
  have hmf : ∀ p, f x₀ ≤ f p := fun p => hmin (mem_univ p)
  set ε : ℝ := min (f x₀ / 2) (Λ / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨ρ, hρ, hclose, L, hL, hlip⟩ :=
    CompactCarrier.exists_smooth_scalar_approx W g hf hε0
  have hεm : ε ≤ f x₀ / 2 := min_le_left _ _
  have hεΛ : ε ≤ Λ / 2 := min_le_right _ _
  have hlow : ∀ p, l p / 2 ≤ ρ p := by
    intro p
    have h1 := (abs_lt.mp (hclose p)).1
    have h2 := hmf p
    have h3 := (hlf p).1
    linarith
  refine ⟨ρ, hρ, fun p => (half_pos (hl p)).trans_le (hlow p), fun p => ⟨hlow p, ?_⟩,
    fun x y => (hlip x y).trans ?_⟩
  · have h1 := (abs_lt.mp (hclose p)).2
    have h2 := hmf p
    have h3 := (hlf p).2
    linarith
  · gcongr
    linarith

end DifferentialGeometry.Geometry.Collapse
