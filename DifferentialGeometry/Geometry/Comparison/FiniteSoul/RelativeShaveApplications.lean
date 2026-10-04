import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeShaveTopDimension
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeShaveSteps
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftGeneral

/-!
# Consumers of the CMS3-REL group G1 (theorem A and the REL sub-lemmas)

* CMS-B's two-dimensional B4.5 `concaveOn_infDist_frontier_geodesicFlow` (verbatim signature) is
  re-derived from theorem A (`hdim` only supplies `NeZero`).
* `relShift_hypothesis_of_sectional_nonneg`: CMS3-SHIFT's prefix supplier
  (`exists_transverse_shift_lipschitz_prefix`) with `Z = maxSliceLocusOfOrder I r C` (a totally geodesic
  `C^r` slice by S3-SLICE) is exactly the REL kernel's inline hypothesis (errata D3: prefix-uniform
  tangency inside the same `∃ ξ`).
* `exists_relative_orthogonal_shift_of_sectional_nonneg`: the relative orthogonal boundary shift (A1-rel)
  for `sec ≥ 0`, `3 ≤ r`, any dimension.
* `infDist_relBoundaryOfOrder_step_of_sectional_nonneg`: the relative hinge step (SL4) with the shift
  supplied.
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

/-- CMS-B's B4.5 `concaveOn_infDist_frontier_geodesicFlow` (verbatim signature) from theorem A. -/
example
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCcl : IsClosed C)
    (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M) (ℓ : ℝ)
    (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) :
    ConcaveOn ℝ (Icc 0 ℓ) (fun t => infDist (g.geodesicFlow p t).proj (frontier C)) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  exact concaveOn_infDist_frontier_geodesicFlow_of_parallel g hr hnorm hsec hCcl hconv p ℓ hmaps

/-- **The REL kernel's inline hypothesis from S3-SHIFT** (`3 ≤ r`, `sec ≥ 0`, any dimension): the
parallel transverse shift of `exists_transverse_shift_lipschitz_prefix`, with prefix-uniform tangency
to the relative interior `Z = maxSliceLocusOfOrder I r C` (a totally geodesic `C^r` slice). -/
theorem relShift_hypothesis_of_sectional_nonneg
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hconv : IsTotallyConvexFinite g C) :
    ∀ (x : M) (L : ℝ), ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ →
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
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤
                |t₁ - t₂| := by
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hZ := isEmbeddedSliceOfOrder_maxSliceLocusOfOrder g hr2 hnorm hconv
  have htg := isTotallyGeodesicFinite_maxSliceLocusOfOrder g hr2 hnorm hconv
  intro x L
  obtain ⟨ρ, hρ, hb⟩ := exists_transverse_shift_lipschitz_prefix g hr hnorm hsec x L
  refine ⟨ρ, hρ, fun p hxp hp w hw hwp => ?_⟩
  obtain ⟨ξ, hξ0, -, -, hξu, hξL, hξZ⟩ := hb p hxp hp w hw hwp
  exact ⟨ξ, hξ0, fun t _ => hξu t, fun T hT hγ hwZ => hξZ r hr _ _ hZ htg T hT hγ hwZ, hξL⟩

/-- **A1-rel for `sec ≥ 0`** (`3 ≤ r`, any dimension): the relative orthogonal boundary shift. -/
theorem exists_relative_orthogonal_shift_of_sectional_nonneg [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) :
    ∀ x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, ∃ ρ > 0,
      ∀ y ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, dist x y < ρ → ∀ u w : E,
      g.inner y u u = 1 → g.inner y w w = 1 → g.inner y u w = 0 →
      u ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      w ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      g.expMap (⟨y, infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
        relBoundaryOfOrder I (r : ℕ∞ω) C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M))
          (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤ infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) :=
  fun _ hx => exists_relative_orthogonal_shift_of_transverseShift g (le_trans (by norm_num) hr) hnorm
    hsec hCcl hconv (relShift_hypothesis_of_sectional_nonneg g hr hnorm hsec hconv) hx

/-- **The relative hinge step for `sec ≥ 0`** (`3 ≤ r`, any dimension). -/
theorem infDist_relBoundaryOfOrder_step_of_sectional_nonneg [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) {x : M}
    (hx : x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {u : E} (hu : g.inner x u u = 1)
    (huT : u ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x)
    (hfoot : g.expMap (⟨x, infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
      relBoundaryOfOrder I (r : ℕ∞ω) C)
    {e : E} (he : g.inner x e e = 1) (heT : e ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) x) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M))
        (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤
      infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C) - h * g.inner x u e :=
  infDist_relBoundaryOfOrder_step_of_shift g (le_trans (by norm_num) hr) hnorm hsec hCcl hconv
    (exists_relative_orthogonal_shift_of_sectional_nonneg g hr hnorm hsec hCcl hconv) hx hu huT hfoot
    he heT

end DifferentialGeometry.Geometry.FiniteSoul

end
