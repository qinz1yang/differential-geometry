import DifferentialGeometry.Geometry.Collapse.EventualAnnularCutoffRiemannian

/-!
# Consumer: the LC31 cutoff of a Riemannian limit model in physical units

`exists_eventual_annularCutoff_riemannian` read in the ORIGINAL distance of the source: every late
point `p` has a scale `r ∈ [T ρ_α(p), V ρ_α(p)]` and a smooth `[0, 1]`-valued cutoff `ζ` that vanishes
outside the physical annulus `(1/5 - e) r < d(x, p) < (9/10 + e) r`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
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

/-- The LC31 cutoff at the cone scale of a Riemannian limit model, in physical units: smooth,
`[0, 1]`-valued, nonzero only on `(1/5 - e) r < d(x, p) < (9/10 + e) r`, `r ∈ [T ρ_α(p), V ρ_α(p)]`. -/
theorem eventual_riemannian_cutoff_physical_annulus (g : ∀ α, SmoothRiemannianMetric I (M α))
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
      ∃ r : ℝ, T * ρ α p ≤ r ∧ r ≤ V * ρ α p ∧ ∃ ζ : M α → ℝ,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ (∀ x, ζ x ∈ Icc (0 : ℝ) 1) ∧
        ∀ x, ζ x ≠ 0 → (1 / 5 - e) * r < dist x p ∧ dist x p < (9 / 10 + e) * r := by
  obtain ⟨V, hTV, α₀, h⟩ := exists_eventual_annularCutoff_riemannian g hmetric ρ hρ hL hsec gN
    hmetricN hsecN n hmodel hε hε1 he he1 hT
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨r, hr, hTr, hrV, -, -, F, -, -, -, -, -, -, -, -, -, hsmooth, -, h01, -, htsupp, -⟩ :=
    h α hα p
  refine ⟨r, hTr, hrV, fun x => annularCutoff cutoffProfile (F x), hsmooth, h01, fun x hx => ?_⟩
  have hmem := htsupp (subset_tsupport _ (Function.mem_support.mpr hx))
  change 1 / 5 - e < r⁻¹ * dist x p ∧ r⁻¹ * dist x p < 9 / 10 + e at hmem
  have hd : r⁻¹ * dist x p * r = dist x p := by field_simp
  constructor
  · have h1 := mul_lt_mul_of_pos_right hmem.1 hr
    rwa [hd] at h1
  · have h2 := mul_lt_mul_of_pos_right hmem.2 hr
    rwa [hd] at h2

end DifferentialGeometry.Geometry.Collapse
