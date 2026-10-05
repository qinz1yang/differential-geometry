import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulFlag
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTubeApplications

/-!
# LFR45 assembly: the finite soul and its normal tube for the SAME `S` (lane CMS3-FLOW2, G1)

Design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §4 §8 (frozen
`exists_finite_soul_strict_outward_tube`), errata §11 and disposition D6 (same-witness corollaries).

* `exists_finite_soul_strict_outward_tube`: the frozen statement, verbatim: SOUL3
  (`exists_finite_soul_strict_outward`, CMS3-REL) and S3-TUBE (`exists_normalTube_finite_foot`, CMS3-FLOW)
  for the same `S`.
* `exists_finite_soul_strict_outward_tube_data`: the same witness `S` with ONE tube `(ε, ψ)` and the
  derived interfaces of review §1 / D6: `relBoundary S = ∅`, `d_S` of class `C^(r−1)` on the punctured
  tube, and the `C^(r−1)` foot projection `x ↦ π (ψ x)` into `S` realizing `d_S`. Nothing is chosen twice.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **LFR45, same-witness form** (`3 ≤ r`). One soul `S` (SOUL3) and ONE normal tube `(ε, ψ)` of it
(S3-TUBE, foot form), with the derived interfaces: empty relative boundary, regularity of `d_S` on
the punctured tube, and the foot projection. -/
theorem exists_finite_soul_strict_outward_tube_data [NeZero (Module.finrank ℝ E)]
    [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsConnected S ∧ IsTotallyConvexFinite g S ∧
      IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) S) S ∧
      relBoundaryOfOrder I (r : ℕ∞ω) S = ∅ ∧
      maxSliceDimOfOrder I (r : ℕ∞ω) S < Module.finrank ℝ E ∧ IsTotallyGeodesicFinite g S ∧
      (∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0) ∧
      ∃ ε > 0, ∃ ψ : M → TangentBundle I M,
        ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε} ∧
        (∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
          Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S) ∧
        (∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
          ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd)) ∧
        (∀ s ∈ S, ψ s = (⟨s, 0⟩ : TangentBundle I M)) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
          {x | 0 < infDist x S ∧ infDist x S < ε} ∧
        ContMDiffOn I I ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => (ψ x).proj) {x | infDist x S < ε} ∧
        (∀ x, infDist x S < ε → (ψ x).proj ∈ S ∧ dist x (ψ x).proj = infDist x S) := by
  obtain ⟨S, hSne, hSc, hSconn, hconv, hslice, hrel, hdim, htg, hout⟩ :=
    exists_finite_soul_strict_outward g hr hnorm hsec
  obtain ⟨ε, hε, ψ, hψs, hψ, hψexp, hψS, hdS, hfoot, hfootS⟩ :=
    exists_normalTube_finite_foot g (le_trans (by norm_num) hr) hnorm hSc hSne hslice
  exact ⟨S, hSne, hSc, hSconn, hconv, hslice, hrel, hdim, htg, hout, ε, hε, ψ, hψs, hψ, hψexp,
    hψS, hdS, hfoot, hfootS⟩

/-- **LFR45 (both clauses)** (`3 ≤ r`): SOUL3 + S3-TUBE for the SAME `S`. The frozen D-CMS3
statement, verbatim. -/
theorem exists_finite_soul_strict_outward_tube [NeZero (Module.finrank ℝ E)] [NoncompactSpace M]
    [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsConnected S ∧ IsTotallyConvexFinite g S ∧
      IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) S) S ∧
      maxSliceDimOfOrder I (r : ℕ∞ω) S < Module.finrank ℝ E ∧ IsTotallyGeodesicFinite g S ∧
      (∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0) ∧
      ∃ ε > 0, ∃ ψ : M → TangentBundle I M,
        ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε} ∧
        (∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
          Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S) ∧
        (∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
          ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd)) ∧
        (∀ s ∈ S, ψ s = (⟨s, 0⟩ : TangentBundle I M)) := by
  obtain ⟨S, hSne, hSc, hSconn, hconv, hslice, -, hdim, htg, hout, ε, hε, ψ, hψs, hψ, hψexp,
    hψS, -⟩ := exists_finite_soul_strict_outward_tube_data g hr hnorm hsec
  exact ⟨S, hSne, hSc, hSconn, hconv, hslice, hdim, htg, hout, ε, hε, ψ, hψs, hψ, hψexp, hψS⟩

end DifferentialGeometry.Geometry.FiniteSoul
