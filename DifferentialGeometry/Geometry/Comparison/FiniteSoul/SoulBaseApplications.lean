import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulBaseSurface

/-!
# Consumers of BASE-2 (lane CMS3-FLOW, G3)

* `soulBase_surface_of_isConnected`: the form consumed by the soul (a connected soul is nonempty).
* `soulBase_surface_carrier`: the smooth carrier `Shat` is a compact Hausdorff smooth manifold (the
  instance hypotheses of the normal parametrization `exists_normalParametrization`, design §4 §10), with
  the same base contract.
* `unitNormalCover_wsub_inputs`: the full input list of W-SUB's one-sided kernel, assembled for the
  unit-normal double cover (compactness, Hausdorff, deck involution, equivariance, projection data).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (embeddedSliceChartedSpace)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **BASE-2 for a connected soul** (nonemptiness from connectedness). -/
theorem soulBase_surface_of_isConnected [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 3) {S : Set M} (hSc : IsCompact S) (hconn : IsConnected S)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 2 S) :
    ∃ (Shat : Set M) (hShat : IsEmbeddedSlice I 2 Shat), IsCompact Shat ∧
      let _ := embeddedSliceChartedSpace hShat
      ∃ b : Shat → M, ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I ((r - 1 : ℕ∞) : ℕ∞ω) b ∧ Injective b ∧ range b = S ∧
        ∃ R : M → Shat, (∀ s, R (b s) = s) ∧
          ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, Fin 2 → ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) R x :=
  soulBase_surface g hr hnorm hdim hSc hconn.nonempty hS

/-- **The smooth carrier of a two-dimensional soul is a compact Hausdorff smooth manifold**, with the
base contract of BASE-2. -/
theorem soulBase_surface_carrier [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 3) {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 2 S) :
    ∃ (Shat : Set M) (hShat : IsEmbeddedSlice I 2 Shat),
      let _ := embeddedSliceChartedSpace hShat
      CompactSpace Shat ∧ T2Space Shat ∧ IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ Shat ∧
      ∃ b : Shat → M, ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I ((r - 1 : ℕ∞) : ℕ∞ω) b ∧ Injective b ∧ range b = S ∧
        ∃ R : M → Shat, (∀ s, R (b s) = s) ∧
          ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, Fin 2 → ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) R x := by
  obtain ⟨Shat, hShat, hc, hrest⟩ := soulBase_surface g hr hnorm hdim hSc hSne hS
  refine ⟨Shat, hShat, ?_⟩
  intro _
  exact ⟨isCompact_iff_compactSpace.mp hc, inferInstance,
    DifferentialGeometry.Geometry.Topology.embeddedSlice_isManifold hShat, hrest⟩

/-- **The input list of W-SUB's one-sided kernel for the unit-normal double cover** (codimension one):
compactness, Hausdorff, the antipodal deck involution, equivariance of the tube map, injectivity modulo
the deck map, the local-diffeomorphism properties, and the projection's surjectivity and fibres. -/
theorem unitNormalCover_wsub_inputs [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) {d : ℕ}
    (hcodim : Module.finrank ℝ E = d + 1) (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) :
    CompactSpace (unitNormalCover g S) ∧ T2Space (unitNormalCover g S) ∧
      Continuous (unitNormalCoverNeg g S) ∧
      (∀ v, unitNormalCoverNeg g S (unitNormalCoverNeg g S v) = v) ∧
      (∀ v t, unitNormalTube g S (unitNormalCoverNeg g S v, -t) = unitNormalTube g S (v, t)) ∧
      Surjective (unitNormalCoverProj g S) ∧
      (∀ v w, unitNormalCoverProj g S v = unitNormalCoverProj g S w ↔
        w = v ∨ w = unitNormalCoverNeg g S v) ∧
      ∃ cs : ChartedSpace (Fin d → ℝ) (unitNormalCover g S), ∃ ε > 0,
        (∀ p ∈ (univ : Set (unitNormalCover g S)) ×ˢ Ioo (-ε) ε,
          ∀ q ∈ (univ : Set (unitNormalCover g S)) ×ˢ Ioo (-ε) ε,
            unitNormalTube g S p = unitNormalTube g S q →
              q = p ∨ q = (unitNormalCoverNeg g S p.1, -p.2)) ∧
        let _ := cs
        let _ := embeddedSliceChartedSpaceOfOrder hS
        ∀ n : ℕ, (n : ℕ∞) ≤ r - 1 →
          IsLocalDiffeomorphOn (𝓘(ℝ, Fin d → ℝ).prod 𝓘(ℝ, ℝ)) I n (unitNormalTube g S)
            ((univ : Set (unitNormalCover g S)) ×ˢ Ioo (-ε) ε) ∧
          IsLocalDiffeomorph 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) n (unitNormalCoverProj g S) := by
  obtain ⟨hs, hf⟩ := unitNormalCoverProj_surjective_and_fibres g hr hcodim hS
  exact ⟨isCompact_iff_compactSpace.mp (isCompact_unitNormalSet g hr hnorm hSc hSne hS),
    inferInstance, continuous_unitNormalCoverNeg g S, unitNormalCoverNeg_neg g S,
    unitNormalTube_neg g S, hs, hf, exists_unitNormalCover_tube_data g hr hnorm hSc hSne hcodim hS⟩

end DifferentialGeometry.Geometry.FiniteSoul
