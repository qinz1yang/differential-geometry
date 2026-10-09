import DifferentialGeometry.Geometry.Collapse.GoodAnnulusConeScaleRiemannian

/-!
# Consumer: the good-annulus cone map in physical units

`exists_good_annulus_riemannian_cone_scale` read in the ORIGINAL distance of the source: every
late point `p` has a scale `r ∈ [T ρ_α(p), V ρ_α(p)]`, a limit model `b` and a map `φ` to the cone
`(C, o)` of `(N_b, n_b)` (Hausdorff dimension at most `dim N_b`) whose radial error is at most `δ`
on the physical ball `B(p, r/δ)`: `|d(φ x, o) - d(x, p)/r| ≤ δ`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u w z

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]

/-- The LC24 cone map of a Riemannian limit model, in physical units: radial error at most `δ`
on `B(p, r/δ)` with `r ∈ [T ρ_α(p), V ρ_α(p)]`. -/
theorem exists_good_annulus_riemannian_radial_error {M : ℕ → Type u}
    [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)] [∀ α, IsManifold I ∞ (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
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
    {δ T : ℝ} (hδ : 0 < δ) (hδone : δ < 1) (hT : 0 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ r : ℝ, T * ρ α p ≤ r ∧ r ≤ V * ρ α p ∧ ∃ b : ι,
        ∃ (C : Type z) (mC : MetricSpace C) (o : C),
          dimH (univ : Set C) ≤ Module.finrank ℝ E' ∧
          (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
            Nonempty (@KleinerLottApprox (N b) C ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) mC
              (n b) o ε)) ∧ ∃ φ : M α → C,
            ∀ x : M α, dist x p < r / δ → |dist (φ x) o - dist x p / r| ≤ δ := by
  obtain ⟨V, hTV, α₀, h⟩ := exists_good_annulus_riemannian_cone_scale g hmetric ρ hρ gN hmetricN
    hsecN n hmodel hδ hδone hT
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨r, hr, hTr, hrV, b, C, mC, o, -, -, -, -, -, hdim, hK, -, ⟨f⟩⟩ := h α hα p
  refine ⟨r, hTr, hrV, b, C, mC, o, hdim, hK,
    @KleinerLottApprox.toFun (M α) C ((mM α).rescale r⁻¹ (inv_pos.mpr hr)) mC p o δ f,
    fun x hx => ?_⟩
  have hlt : r⁻¹ * dist x p < δ⁻¹ :=
    calc r⁻¹ * dist x p < r⁻¹ * (r / δ) := mul_lt_mul_of_pos_left hx (inv_pos.mpr hr)
      _ = δ⁻¹ := by field_simp
  have herr := @KleinerLottApprox.radial_error (M α) C ((mM α).rescale r⁻¹ (inv_pos.mpr hr)) mC
    p o δ f x hlt
  change |dist (@KleinerLottApprox.toFun (M α) C ((mM α).rescale r⁻¹ (inv_pos.mpr hr)) mC p o δ
    f x) o - r⁻¹ * dist x p| ≤ δ at herr
  rwa [inv_mul_eq_div] at herr

end DifferentialGeometry.Geometry.Collapse
