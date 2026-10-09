import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeShaveApplications
import DifferentialGeometry.Geometry.Comparison.Nonnegative.BoundaryConcavity

/-!
# REL: concavity of the distance to the relative boundary, in the ambient manifold (CMS3-REL, G2)

Lane CMS3-REL, frozen interfaces §6 of `build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean`
(review `out/review-finite-soul-three.md` item 7, disposition D3, design §11 errata).

* `concaveOn_infDist_relBoundaryOfOrder_of_transverseShift` (REL kernel, `2 ≤ r`, `sec ≥ 0`, any
  dimension). The frozen statement with the errata applied: the tangency clause of the inline transverse
  shift is PREFIX-UNIFORM inside the same `∃ ξ`
  (`∀ T ∈ [0, L], γ [0, T] ⊆ Z → w ∈ T_{γ 0} Z → ∀ t ∈ [0, T], ξ t ∈ T_{γ t} Z`). Proof:
  `concaveOn_of_linear_upper_support`; at a parameter with `γ s ∈ Z` the linear upper support comes from
  the relative orthogonal shift (A1-rel: relative ball, relative foot point, first exit on the shift
  rectangle) and the ambient hinge steps (SL4); otherwise the whole open arc lies in `B` (relative
  open-core propagation, SLICE (7)) and the function vanishes nearby. No intrinsic metric on `Z`.
* `concaveOn_infDist_relBoundaryOfOrder_geodesicFlow` (REL binding, `3 ≤ r`): the kernel fed with
  CMS3-SHIFT's prefix supplier (`relShift_hypothesis_of_sectional_nonneg`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **REL kernel** (`2 ≤ r`, `sec ≥ 0`, any dimension). Concavity of the distance to the relative
boundary along every geodesic arc of `C`, from a transverse shift whose parallel field stays tangent to
the relative interior `Z` along every prefix of the base arc that lies in `Z` (frozen D-CMS3 statement
with the errata of design §11 / disposition D3). -/
theorem concaveOn_infDist_relBoundaryOfOrder_of_transverseShift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C)
    (hshift : ∀ (x : M) (L : ℝ), ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ →
      g.inner p.proj p.snd p.snd = 1 → ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          (∀ t ∈ Icc 0 L, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          (∀ T ∈ Icc 0 L,
            (∀ t ∈ Icc 0 T, (g.geodesicFlow p t).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) →
            w ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) p.proj →
            ∀ t ∈ Icc 0 T,
              ξ t ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) (g.geodesicFlow p t).proj) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤ |t₁ - t₂|)
    (p : TangentBundle I M) (ℓ : ℝ) (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) :
    ConcaveOn ℝ (Icc 0 ℓ)
      (fun t => infDist (g.geodesicFlow p t).proj (relBoundaryOfOrder I (r : ℕ∞ω) C)) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set σ : ℝ := Real.sqrt (g.inner p.proj p.snd p.snd) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hγc : Continuous (fun t : ℝ => (g.geodesicFlow p t).proj) := by
    refine LipschitzWith.continuous (K := ⟨σ, hσ0⟩) (LipschitzWith.of_dist_le_mul fun a b => ?_)
    rw [Real.dist_eq, abs_sub_comm]
    exact g.dist_proj_geodesicFlow_le hr1 hnorm (fun τ _ => by rw [hD]; exact mem_univ _)
  have hshiftZ := fun x (hx : x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) =>
    exists_relative_orthogonal_shift_of_transverseShift g hr hnorm hsec hCcl hconv hshift hx
  refine DifferentialGeometry.Geometry.Topology.concaveOn_of_linear_upper_support (convex_Icc 0 ℓ)
    ((continuous_infDist_pt _).comp hγc).continuousOn ?_
  intro s hs
  rw [interior_Icc] at hs
  by_cases hsZ : (g.geodesicFlow p s).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C
  · exact exists_upper_support_infDist_relBoundaryOfOrder_of_shift g hr hnorm hsec hCcl hconv hshiftZ
      p hmaps hs hsZ
  · have hall : ∀ t ∈ Ioo 0 ℓ, (g.geodesicFlow p t).proj ∈ relBoundaryOfOrder I (r : ℕ∞ω) C := by
      intro t ht
      refine ⟨hmaps t (Ioo_subset_Icc_self ht), fun htZ => hsZ ?_⟩
      exact hconv.proj_geodesicFlow_mem_maxSliceLocusOfOrder hr hnorm p hmaps
        (Ioo_subset_Icc_self ht) htZ s hs
    refine ⟨0, ?_⟩
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with y hy
    rw [infDist_zero_of_mem (hall y hy), infDist_zero_of_mem (hall s hs)]
    simp

/-- **REL binding** (`3 ≤ r`, `sec ≥ 0`, any dimension): the kernel with S3-SHIFT + S3-PT.b + S3-SLICE.
The frozen D-CMS3 statement, verbatim. -/
theorem concaveOn_infDist_relBoundaryOfOrder_geodesicFlow [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M) (ℓ : ℝ)
    (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) :
    ConcaveOn ℝ (Icc 0 ℓ)
      (fun t => infDist (g.geodesicFlow p t).proj (relBoundaryOfOrder I (r : ℕ∞ω) C)) :=
  concaveOn_infDist_relBoundaryOfOrder_of_transverseShift g (le_trans (by norm_num) hr) hnorm hsec hCcl
    hconv (relShift_hypothesis_of_sectional_nonneg g hr hnorm hsec hconv) p ℓ hmaps

end DifferentialGeometry.Geometry.FiniteSoul

end
