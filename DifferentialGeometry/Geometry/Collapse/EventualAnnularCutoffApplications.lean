import DifferentialGeometry.Geometry.Collapse.EventualAnnularCutoff

/-!
# Consumer of LC31 (eventual clause): smooth annular bumps at the cone scale

`exists_eventual_annular_bump`: on a tail of the standing sequence every point has a cone scale
`r_p^0 = s ρ_α(p)`, `s ∈ [T, V]`, and a globally smooth compactly supported `ζ : M^α → [0, 1]`
that equals one on the rescaled annulus `{3/10 + e ≤ d̂_p ≤ 4/5 - e}` and is topologically
supported in `{1/5 - e < d̂_p < 9/10 + e}`, `d̂ = (r_p^0)⁻¹ d`. It is `ζ = Φ ∘ η` of
`exists_eventual_annularCutoff`, with `|η - d̂_p| < e`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type u} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
  [∀ α, IsManifold I ∞ (M α)] [∀ α, T2Space (TangentBundle I (M α))]
  [∀ α, SigmaCompactSpace (M α)] [∀ α, CompleteSpace (M α)]

/-- Smooth annular bumps at the eventual cone scale (consumer of LC31's eventual clause). -/
theorem exists_eventual_annular_bump (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hsec : ∀ α (p : M α), ∀ y ∈ riemannianBallOf (g α) p (L α * ρ α p),
      SectionalBoundedBelowAt (g α) y (-((L α * ρ α p) ^ 2)⁻¹))
    {ε e T : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e) (he1 : e < 1 / 40) (hT : 0 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ s : ℝ, ∃ hs : 0 < s, T ≤ s ∧ s ≤ V ∧
      letI : MetricSpace (M α) :=
        (mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))
      ∃ ζ : M α → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
        (∀ x, ζ x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, 3 / 10 + e ≤ dist x p → dist x p ≤ 4 / 5 - e → ζ x = 1) ∧
        tsupport ζ ⊆ {x : M α | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} := by
  obtain ⟨V, hTV, α₀, h⟩ :=
    exists_eventual_annularCutoff g hmetric ρ hρ hL hsec hε hε1 he he1 hT
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨s, hs, hTs, hsV, -, -, F, -, -, hclose, -, -, -, -, -, -, hsmooth, hcpt, hrange, hone,
    hsupp, -⟩ := h α hα p
  refine ⟨s, hs, hTs, hsV, fun x => annularCutoff cutoffProfile (F x), hsmooth, hcpt, hrange,
    fun x h1 h2 => hone x ?_, hsupp⟩
  let : MetricSpace (M α) := (mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))
  have hx := hclose x
  rw [Metric.infDist_singleton, abs_lt] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- LC31 with the row's own parameter ranges (`0 < ε < 1/4`, `0 < e < min ε (1/40)`, `T > 1`):
`exists_eventual_annularCutoff` holds under these (it needs only `ε < 1`, `e < 1/40`, `T > 0`). -/
example (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hsec : ∀ α (p : M α), ∀ y ∈ riemannianBallOf (g α) p (L α * ρ α p),
      SectionalBoundedBelowAt (g α) y (-((L α * ρ α p) ^ 2)⁻¹))
    {ε e T : ℝ} (hε : 0 < ε) (hε4 : ε < 1 / 4) (he : 0 < e) (hemin : e < min ε (1 / 40))
    (hT : 1 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ s : ℝ, ∃ hs : 0 < s, T ≤ s ∧ s ≤ V ∧
      letI : MetricSpace (M α) :=
        (mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))
      ∃ ζ : M α → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
        (∀ x, ζ x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, 3 / 10 + e ≤ dist x p → dist x p ≤ 4 / 5 - e → ζ x = 1) ∧
        tsupport ζ ⊆ {x : M α | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} :=
  exists_eventual_annular_bump g hmetric ρ hρ hL hsec hε (by linarith) he
    (hemin.trans_le (min_le_right _ _)) (by linarith)

end DifferentialGeometry.Geometry.Collapse
