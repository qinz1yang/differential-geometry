import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.RecenteredStaticPreparation

noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
open Surgery.Topology
universe u
private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩
private instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

theorem exists_uniform_marked_recentered_static_preparation :
    ∃ c : ℝ, 4 ≤ c ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric ThreeModel M) {δ : ℝ} {k : ℕ}
        (N : NormalizedNeck g δ k), δ ≤ δ₀ → ∀ hk : m + 6 ≤ k,
        ∀ (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
          (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark) (side : Bool),
        let d₀ := (N.rotatedDatum e he side).lowerOrder hk
        ∀ (σ : ℝ) (hσ : σ ^ 2 = 1),
          ∃ hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹,
          ∃ d : normalizedDatum g (d₀.offsetPoint hσ) (c * δ) (m + 4),
            d.map = d₀.recenteringMap hσ hfit ∧ d.retainedSide = true ∧
            |metricScalarAt g (d₀.offsetPoint hσ) / N.scale - 1| ≤ c * δ ∧
            N.scale / 2 ≤ metricScalarAt g (d₀.offsetPoint hσ) ∧
            metricScalarAt g (d₀.offsetPoint hσ) ≤ (3 / 2 : ℝ) * N.scale ∧
            ∃ out : CanonicalStaticInsertionWitness d A hA D m ε,
              StaticInsertionAdditionalProperties C out := by
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hfactory⟩ := exists_uniform_recentered_static_preparation.{0, 0, u}
  refine ⟨c, hc, C, hC, A, hA, hsmall.1, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₁, hδ₁, hquarter, hprep⟩ := hfactory D hD m ε hε
  refine ⟨min δ₁ (1 / 8646), lt_min hδ₁ (by norm_num), (min_le_left _ _).trans_lt hquarter, ?_⟩
  intro M _ _ _ _ g δ k N hδ hk e he side
  dsimp only
  let d₀ := (N.rotatedDatum e he side).lowerOrder hk
  intro σ hσ
  obtain ⟨hfit, d, hmap, hside, hratio, out, hout⟩ := hprep δ N.delta_pos
    (hδ.trans (min_le_left _ _)) g N.center d₀ σ hσ
  have hbound := N.rotatedDatum_offset_scalar_bounds e he side (by omega)
    (hδ.trans (min_le_right _ _)) hσ
  have hscale : metricScalarAt g N.center = N.scale := N.scale_scalar.symm
  rw [hscale] at hratio
  exact ⟨hfit, d, hmap, hside, hratio, hbound.1, hbound.2, out, hout⟩

end DifferentialGeometry.PDE.RicciFlow.StandardCap
