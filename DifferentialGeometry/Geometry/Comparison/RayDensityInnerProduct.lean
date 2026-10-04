import DifferentialGeometry.Geometry.Comparison.RayDensity
import DifferentialGeometry.Geometry.Comparison.RayChordInnerProduct
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Ray density in closed convex subsets of Euclidean space

The concrete consumer of `RayDensity` (Tits-cone tier T2). A subset `C` of a real inner product
space `V`, with the induced metric, satisfies `fourPointComparison 0 univ`
(`fourPointComparison_zero_subtype`); a convex subset has the segments that I5 needs
(`segments_of_convex`); a closed subset of a finite-dimensional space is proper. So the tier-2
statements apply to every closed convex `C ⊆ V`:

* I5 `exists_ray_near_of_convex`: every far point of `C` is within `η |qx|` of a ray of `C` from
  `q`. This is not trivial: the half-line from `q` through `x` need not stay in `C` (a quadrant
  with `q` in its interior), and the ray is then only asymptotically close.
* I6 `exists_uniform_rayChord_of_isClosed`, the error budget `exists_uniform_dist_le_of_ray_of_isClosed`
  and I7 `isClosed_rayUnion_of_isClosed`, for closed (not necessarily convex) `C`.

The closed half-line `Ici 0 ⊆ ℝ` (one of the test spaces of the truth check) is spelled out as an
`example`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped NNReal Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Every subset of a real inner product space, with the induced metric, satisfies the four-point
comparison at curvature `0`. -/
theorem fourPointComparison_zero_subtype (C : Set V) : fourPointComparison 0 (univ : Set C) := by
  rintro x - a - b - c - hax hbx hcx
  exact fourPointComparison_zero_of_innerProductSpace (x : V) trivial (a : V) trivial (b : V)
    trivial (c : V) trivial (fun h => hax (Subtype.ext h)) (fun h => hbx (Subtype.ext h))
    (fun h => hcx (Subtype.ext h))

/-- A convex subset of a real inner product space has linear segments, in the form I5 consumes. -/
theorem segments_of_convex {C : Set V} (hC : Convex ℝ C) (a b : C) :
    ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  refine ⟨fun t => ⟨(a : V) + (t : ℝ) • ((b : V) - a), hC.add_smul_sub_mem a.2 b.2 t.2⟩,
    ?_, ?_, ?_, ?_⟩
  · exact (continuous_const.add (continuous_subtype_val.smul continuous_const)).subtype_mk _
  · ext
    simp
  · ext
    simp
  · intro s t
    rw [Subtype.dist_eq, Subtype.dist_eq, Subtype.dist_eq, dist_add_left, dist_eq_norm,
      ← sub_smul, norm_smul, Real.norm_eq_abs, dist_eq_norm, norm_sub_rev, Real.dist_eq,
      mul_comm]

variable [FiniteDimensional ℝ V]

/-- I5 in a closed convex subset of a finite-dimensional real inner product space. -/
theorem exists_ray_near_of_convex {C : Set V} (hC : Convex ℝ C) (hCc : IsClosed C) (q : C)
    {η : ℝ} (hη : 0 < η) :
    ∃ r₀ : ℝ, ∀ x : C, r₀ ≤ dist q x → ∃ γ : ℝ≥0 → C, (Isometry γ ∧ γ 0 = q) ∧
      dist x (γ ⟨dist q x, dist_nonneg⟩) ≤ η * dist q x := by
  have : ProperSpace C := ProperSpace.of_isClosed hCc
  exact exists_ray_near (fourPointComparison_zero_subtype C) (segments_of_convex hC) q hη

/-- I6 in a closed subset of a finite-dimensional real inner product space. -/
theorem exists_uniform_rayChord_of_isClosed {C : Set V} (hCc : IsClosed C) (q : C) {η : ℝ}
    (hη : 0 < η) :
    ∃ T : ℝ≥0, 0 < T ∧ ∀ t : ℝ≥0, T ≤ t → ∀ γ σ : ℝ≥0 → C, (Isometry γ ∧ γ 0 = q) →
      (Isometry σ ∧ σ 0 = q) → dist (γ t) (σ t) / (t : ℝ) ≤ rayChordLimit γ σ + η := by
  have : ProperSpace C := ProperSpace.of_isClosed hCc
  exact exists_uniform_rayChord (fourPointComparison_zero_subtype C) q hη

/-- The error budget in a closed subset of a finite-dimensional real inner product space. -/
theorem exists_uniform_dist_le_of_ray_of_isClosed {C : Set V} (hCc : IsClosed C) (q : C)
    {ω : ℝ} (hω : 0 < ω) (S : ℝ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ γ σ : ℝ≥0 → C, (Isometry γ ∧ γ 0 = q) →
      (Isometry σ ∧ σ 0 = q) → ∀ s u : ℝ≥0, (s : ℝ) ≤ S * R → (u : ℝ) ≤ S * R →
        dist (γ s) (σ u) ≤
          Real.sqrt (((s : ℝ) - u) ^ 2 + s * u * rayChordLimit γ σ ^ 2) + ω * R := by
  have : ProperSpace C := ProperSpace.of_isClosed hCc
  exact exists_uniform_dist_le_of_ray (fourPointComparison_zero_subtype C) q hω S

/-- I7 in a closed subset of a finite-dimensional real inner product space. -/
theorem isClosed_rayUnion_of_isClosed {C : Set V} (hCc : IsClosed C) (q : C) :
    IsClosed {x : C | ∃ γ : ℝ≥0 → C, (Isometry γ ∧ γ 0 = q) ∧ x ∈ range γ} := by
  have : ProperSpace C := ProperSpace.of_isClosed hCc
  exact isClosed_rayUnion q

/-- The half-line test space: in `Ici 0 ⊆ ℝ`, far points are relatively close to rays. -/
example (q : Ici (0 : ℝ)) {η : ℝ} (hη : 0 < η) :
    ∃ r₀ : ℝ, ∀ x : Ici (0 : ℝ), r₀ ≤ dist q x → ∃ γ : ℝ≥0 → Ici (0 : ℝ),
      (Isometry γ ∧ γ 0 = q) ∧ dist x (γ ⟨dist q x, dist_nonneg⟩) ≤ η * dist q x :=
  exists_ray_near_of_convex (convex_Ici 0) isClosed_Ici q hη

end GC.MetricGeometry
