import DifferentialGeometry.Geometry.Collapse.RescaledLimits.PointedLimit

/-!
# LC24: the model property of actual rescaled sequences (unconditional part)

Blueprint 207A, LC24 (`cor:collapse-kl-metric-cone-scale`, A:20898–20951). The blueprint applies
LC23 to the standing sequence at the modified scales, retaining the smooth compactness of KL
6.10(3) (used only through its pointed Gromov–Hausdorff component) and the Tits-cone input LC21
for the limits.

This file PRODUCES LC23's sequential model property for aligned complete Riemannian sources with a
positive scale function `ρ` and the buffered curvature bound `sec ≥ -(L_α ρ_α(p))⁻²` on
`B(p, L_α ρ_α(p))`, `L_α → ∞`, from the central producer
`exists_rescaled_pointed_limit_of_sectional_buffer` (lane W3-F1, LC05): the limits are complete
proper geodesic spaces with nonnegative four-point comparison and Hausdorff dimension at most
`dim E` (`sequentialModelProperty_of_sectional_buffer`). Combined with the LC23 binding
`exists_riemannian_bounded_cone_scale` it gives LC24's conclusion for every model class that
carries LC21 packages.

LC24 itself is BLOCKED on the LC21 Tits-cone producer (existence of an LC21 package for every such
limit; no blueprint row proves it). The composition is kept outside the library, see
`build-logs/resume/sheet-W3-F4.md`, Addendum 3.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type u} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
  [∀ α, IsManifold I ∞ (M α)] [∀ α, T2Space (TangentBundle I (M α))]
  [∀ α, SigmaCompactSpace (M α)] [∀ α, CompleteSpace (M α)]

/-- LC23's sequential model property for actual rescaled sequences (unconditional): every
sequence of indices `a j → ∞` and points `z j` has a subsequence along which the normalized
manifolds `(M^{a j}, ρ(z j)⁻² g, z j)` converge pointedly to a complete proper geodesic space with
nonnegative four-point comparison and Hausdorff dimension at most `dim E`. -/
theorem sequentialModelProperty_of_sectional_buffer (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hsec : ∀ α (p : M α), ∀ y ∈ riemannianBallOf (g α) p (L α * ρ α p),
      SectionalBoundedBelowAt (g α) y (-((L α * ρ α p) ^ 2)⁻¹))
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (z : ∀ j, M (a j)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (k : ℕ → ℕ), StrictMono k ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
          Y m (fun j => z (k j)) q ∧
        dimH (univ : Set Y) ≤ Module.finrank ℝ E ∧ fourPointComparison 0 (univ : Set Y) ∧
        ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  obtain ⟨Y, m, q, k, hk, hc, hp, hconv, hdim, h4, hseg, -⟩ :=
    exists_rescaled_pointed_limit_of_sectional_buffer (X := fun j => M (a j))
      (fun j => g (a j)) (fun j => hmetric (a j)) z (ρ := fun j => ρ (a j) (z j))
      (L := fun j => L (a j)) (fun j => hρ (a j) (z j)) (hL.comp ha)
      (fun j => hsec (a j) (z j))
  exact ⟨Y, m, q, k, hk, hc, hp, hconv, hdim, h4, hseg⟩

end DifferentialGeometry.Geometry.Collapse
