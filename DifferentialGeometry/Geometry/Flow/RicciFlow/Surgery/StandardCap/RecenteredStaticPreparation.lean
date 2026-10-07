import DifferentialGeometry.Geometry.Neck.OrderReduction
import DifferentialGeometry.Geometry.Neck.Recentering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticPinchingInsertion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticCollarAdmitsC11PB

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u v w

theorem exists_uniform_recentered_static_preparation :
    ∃ c : ℝ, 4 ≤ c ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), (2 * A < 1 / 2 ∧ StaticCollarAdmits.{u, v, w} A hA) ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ {E : Type u} {H : Type v} {M : Type w}
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 6)),
        ∀ (σ : ℝ) (hσ : σ ^ 2 = 1),
          ∃ hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹,
          ∃ d' : normalizedDatum g (d.offsetPoint hσ) (c * δ) (m + 4),
            d'.map = d.recenteringMap hσ hfit ∧ d'.retainedSide = true ∧
            |metricScalarAt g (d.offsetPoint hσ) / metricScalarAt g x₀ - 1| ≤ c * δ ∧
            ∃ out : CanonicalStaticInsertionWitness d' A hA D m ε,
              StaticInsertionAdditionalProperties C out := by
  obtain ⟨c, δrec, hc, hδrec, hrec⟩ := exists_fixed_offset_recentering.{u, v, w}
  obtain ⟨C, hC, A, hA, hsmall, hmod⟩ := exists_staticInsertion_with_additional_properties.{u, v, w}
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hcollar : StaticCollarAdmits.{u, v, w} A hA := by
    intro D hD m ε hε
    obtain ⟨δ₀, hδ₀, hhalf, hb⟩ := hmod D hD m ε hε
    refine ⟨δ₀, hδ₀, hhalf, ?_⟩
    intro δ hδ hle E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
    obtain ⟨w, -⟩ := hb δ hδ hle g x₀ d
    exact ⟨w⟩
  refine ⟨c, hc, C, hC, A, hA, ⟨hsmall, hcollar⟩, ?_⟩
  intro D hD m ε hε
  obtain ⟨δi, hδi, _, hinsert⟩ := hmod D hD m ε hε
  let δ₀ := min δrec (min (δi / c) (1 / 8))
  have hδ₀ : 0 < δ₀ := lt_min hδrec (lt_min (div_pos hδi hcpos) (by norm_num))
  refine ⟨δ₀, hδ₀, ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num), ?_⟩
  intro δ hδ hle E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d σ hσ
  have hrecSmall : δ ≤ δrec := hle.trans (min_le_left _ _)
  have hδiSmall : c * δ ≤ δi := by
    have he : δ ≤ δi / c := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
    exact (mul_comm c δ) ▸ (le_div_iff₀ hcpos).mp he
  obtain ⟨hfit, drec, hmap, hside, hratio⟩ :=
    hrec E H I M g x₀ δ (m + 6) d (by omega) hrecSmall σ hσ
  let d' := drec.lowerOrder (show m + 4 ≤ m + 6 by omega)
  obtain ⟨out, hout⟩ := hinsert (c * δ) (mul_pos hcpos hδ) hδiSmall g (d.offsetPoint hσ) d'
  exact ⟨hfit, d', hmap, hside, hratio, out, hout⟩
end DifferentialGeometry.PDE.RicciFlow.StandardCap
