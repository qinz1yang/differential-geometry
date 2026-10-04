import DifferentialGeometry.Geometry.Comparison.FiniteSoul.InducedMetric

/-!
# Consumers of EXIT-51 (lane CMS3-CARRIER, group G3)

* the frozen interface `exists_inducedMetric_sectional_eq` VERBATIM (with
  `[NeZero (finrank ℝ E)]`, `[CompactSpace B]`, `[T2Space B]` and `hbinj`, which the proof does not
  use; the unused explicit binder is renamed `_hbinj`, statement text otherwise unchanged), as an
  `example`;
* `exists_inducedMetric_sectional_nonneg`: LFR51's curvature input — for `sec_g ≥ 0` the induced
  metric `b^* g` of order `r − 2` on the carrier of a totally geodesic soul has `K ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
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

/-- The frozen interface EXIT-51, verbatim (`FiniteSoulThreeInterfaces.lean` :649–667). -/
example [NeZero (Module.finrank ℝ E)]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B] [CompactSpace B]
    [T2Space B]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 4 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) (htg : IsTotallyGeodesicFinite g S)
    (b : B → M) (hb : ContMDiff 𝓘(ℝ, EB) I ((r - 1 : ℕ∞) : ℕ∞ω) b) (_hbinj : Injective b)
    (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x) :
    ∃ gS : ContMDiffRiemannianMetric 𝓘(ℝ, EB) ((r - 2 : ℕ∞) : ℕ∞ω) EB
        (TangentSpace 𝓘(ℝ, EB) : B → Type _),
      (∀ (s : B) (v w : TangentSpace 𝓘(ℝ, EB) s), gS.inner s v w =
        g.inner (b s) (mfderiv 𝓘(ℝ, EB) I b s v) (mfderiv 𝓘(ℝ, EB) I b s w)) ∧
      ∀ (s : B) (v w : TangentSpace 𝓘(ℝ, EB) s), gS.sectionalCurvature s v w =
        g.sectionalCurvature (b s) (mfderiv 𝓘(ℝ, EB) I b s v) (mfderiv 𝓘(ℝ, EB) I b s w) :=
  exists_inducedMetric_sectional_eq g hr hnorm hS htg b hb hbS hbinv

/-- **LFR51's curvature input**: the induced metric on the carrier of a totally geodesic soul of a
metric with `sec ≥ 0` has nonnegative sectional curvature. -/
theorem exists_inducedMetric_sectional_nonneg
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 4 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S)
    (htg : IsTotallyGeodesicFinite g S)
    (b : B → M) (hb : ContMDiff 𝓘(ℝ, EB) I ((r - 1 : ℕ∞) : ℕ∞ω) b) (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x) :
    ∃ gS : ContMDiffRiemannianMetric 𝓘(ℝ, EB) ((r - 2 : ℕ∞) : ℕ∞ω) EB
        (TangentSpace 𝓘(ℝ, EB) : B → Type _),
      (∀ (s : B) (v w : TangentSpace 𝓘(ℝ, EB) s), gS.inner s v w =
        g.inner (b s) (mfderiv 𝓘(ℝ, EB) I b s v) (mfderiv 𝓘(ℝ, EB) I b s w)) ∧
      ∀ (s : B) (v w : TangentSpace 𝓘(ℝ, EB) s), 0 ≤ gS.sectionalCurvature s v w := by
  obtain ⟨gS, hin, hsecS⟩ := exists_inducedMetric_sectional_eq g hr hnorm hS htg b hb hbS hbinv
  exact ⟨gS, hin, fun s v w => (hsecS s v w).symm ▸ hsec _ _ _⟩

end DifferentialGeometry.Geometry.FiniteSoul
