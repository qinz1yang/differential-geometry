import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalParamBundle
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulBaseApplications

/-!
# Consumers of the `Ê` binding (lane CMS3-CARRIER, group G2b)

* `exists_soulNormalBundle_surface`: for a compact nonempty two-dimensional `C^r` soul in dimension
  three, CMS3-FLOW's BASE-2 carrier `Ŝ` (W-SUB) carries the smoothed normal line bundle `Ê` with a map
  `ιE` satisfying exactly the `ι`-hypotheses of LFR46 (`exists_finite_normalFlowMap`) over the base
  map `b : Ŝ → M`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (embeddedSliceChartedSpace)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **The smoothed normal line bundle of a two-dimensional soul**, over W-SUB's smooth carrier,
bound to the LFR46 hypotheses. -/
theorem exists_soulNormalBundle_surface [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 3) {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 2 S) :
    ∃ (Shat : Set M) (hShat : IsEmbeddedSlice I 2 Shat),
      let _ := embeddedSliceChartedSpace hShat
      CompactSpace Shat ∧ T2Space Shat ∧ IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ Shat ∧
      ∃ b : Shat → M, ContMDiff 𝓘(ℝ, Fin 2 → ℝ) I ((r - 1 : ℕ∞) : ℕ∞ω) b ∧ Injective b ∧
        range b = S ∧
        ∃ (V : Shat → Type) (_ : ∀ s, NormedAddCommGroup (V s))
          (_ : ∀ s, InnerProductSpace ℝ (V s))
          (_ : TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))) V))
          (_ : FiberBundle (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))) V)
          (_ : VectorBundle ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))) V)
          (_ : ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))) V
            𝓘(ℝ, Fin 2 → ℝ))
          (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, Fin 2 → ℝ) ∞
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))) V)
          (ιE : TotalSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))) V →
            TangentBundle I M),
          ContMDiff (𝓘(ℝ, Fin 2 → ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))))
            I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ιE ∧
          (∀ z, (ιE z).proj = b z.proj) ∧
          (∀ s : Shat, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ιE ⟨s, w⟩).snd (A w)) ∧
          (∀ z, g.inner (ιE z).proj (ιE z).snd (ιE z).snd = ‖z.2‖ ^ 2) ∧
          (∀ z, ιE z ∈ normalSetFinite g S) ∧
          (∀ v ∈ normalSetFinite g S, ∃ z, ιE z = v) := by
  obtain ⟨Shat, hShat, hrest⟩ := soulBase_surface_carrier g hr hnorm hdim hSc hSne hS
  refine ⟨Shat, hShat, ?_⟩
  intro _
  obtain ⟨hc, ht, hm, b, hb, hbinj, hbS, R, hRb, hR⟩ := hrest
  have := hc
  have := ht
  have := hm
  obtain ⟨V, i1, i2, i3, i4, i5, i6, i7, ιE, h1, h2, h3, h4, h5, h6, -⟩ :=
    exists_soulNormalBundle (EB := Fin 2 → ℝ) g hr hS b hb hbS ⟨R, hRb, hR⟩
  exact ⟨hc, ht, hm, b, hb, hbinj, hbS, V, i1, i2, i3, i4, i5, i6, i7, ιE, h1, h2, h3, h4, h5, h6⟩

end DifferentialGeometry.Geometry.FiniteSoul
