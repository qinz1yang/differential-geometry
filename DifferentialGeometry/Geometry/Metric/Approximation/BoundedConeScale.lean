import DifferentialGeometry.Geometry.Metric.Approximation.BoundedRescaling
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

/-!
# LC23 in the blueprint's normalization: a bounded interval containing a cone scale

Blueprint 207A, LC23 (`thm:collapse-bounded-cone-scale`, A:20853–20896). The sources are pointed
metric spaces `M α` with a positive scale function `ρ α`; the sequential model property is stated
for the normalized spaces `(ρ_α(p)⁻¹ M^α, p)`, and every model `(N b, n b)` carries the
approximation clause of an LC21 package with target `(C b, o b)`. The conclusion is stated at
the composite scale `s ρ_α(p)` with `s ∈ [T, V]`, uniformly in `p` on one tail.

The proof is the existing metric argument `exists_uniform_bounded_rescaling` (LC22 inside a
compactness contradiction) together with the composition of rescalings. Completeness and
properness of the models and cones, and the AC82 radial maps of the cones, are not used by the
argument and are therefore not assumed; the returned index `b` lets a consumer use its own radial
data `H b`. The scale lower bound is `0 < T` (the blueprint has `T > 1`).
-/

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace MetricSpace

/-- Rescaling by equal factors gives equal metric structures. -/
theorem rescale_congr {X : Type*} (m : MetricSpace X) {c c' : ℝ} (h : c = c') (hc : 0 < c)
    (hc' : 0 < c') : m.rescale c hc = m.rescale c' hc' := by
  subst h
  rfl

end MetricSpace

namespace GC.MetricGeometry

universe u w z

/-- LC23: under the sequential model property for the normalized spaces and LC21 approximation
clauses for the models, every `0 < δ < 1` and `T > 0` admit `V ≥ T` and a tail on which every
point has a scale `s ∈ [T, V]` and a model index `b` with an actual pointed Kleiner–Lott
`δ`-approximation `((s ρ_α(p))⁻¹ M^α, p) → (C b, o b)`. -/
theorem exists_bounded_cone_scale {M : ℕ → Type u} [mM : ∀ α, MetricSpace (M α)]
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
    {ι : Type w} {N C : ι → Type z} [mN : ∀ b, MetricSpace (N b)] [mC : ∀ b, MetricSpace (C b)]
    (n : ∀ b, N b) (o : ∀ b, C b)
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b))
    (hcone : ∀ b : ι, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox (N b) (C b)
          ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) (mC b) (n b) (o b) ε))
    {δ T : ℝ} (hδ : 0 < δ) (hδone : δ < 1) (hT : 0 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ s : ℝ, ∃ hs : 0 < s, T ≤ s ∧ s ≤ V ∧ ∃ b : ι,
        Nonempty (@KleinerLottApprox (M α) (C b)
          ((mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))) (mC b)
          p (o b) δ) := by
  obtain ⟨V, hTV, α₀, hα₀⟩ := exists_uniform_bounded_rescaling (P := M) (X := fun α _ => M α)
    (mX := fun α x => (mM α).rescale (ρ α x)⁻¹ (inv_pos.mpr (hρ α x))) (fun _ x => x)
    (Y := N) (C := C) n o hmodel hcone hδ hδone hT
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨s, hs, hTs, hsV, b, hb⟩ := hα₀ α hα.le p
  refine ⟨s, hs, hTs, hsV, b, ?_⟩
  have heq : ((mM α).rescale (ρ α p)⁻¹ (inv_pos.mpr (hρ α p))).rescale s⁻¹ (inv_pos.mpr hs) =
      (mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p))) := by
    rw [MetricSpace.rescale_mul]
    exact MetricSpace.rescale_congr _ (mul_inv s (ρ α p)).symm _ _
  rw [heq] at hb
  exact hb

end GC.MetricGeometry
