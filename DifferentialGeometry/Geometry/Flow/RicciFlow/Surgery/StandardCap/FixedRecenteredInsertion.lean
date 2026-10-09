import DifferentialGeometry.Geometry.Neck.Recentering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FixedStaticInsertion

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

theorem exists_fixed_recentered_insertion :
    ∃ c : ℝ, 4 ≤ c ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∃ δBase : ℝ, 0 < δBase ∧ δBase < 1 / 4 ∧
      ∃ δRequest : StaticRequest → ℝ, (∀ P, 0 < δRequest P ∧ δRequest P ≤ δBase) ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δBase → ∀ (k : ℕ) (hk : 8 ≤ k),
      ∀ {E : Type u} {H : Type v} {M : Type w}
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k)
          (σ : ℝ) (hσ : σ ^ 2 = 1),
        ∃ hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹,
        ∃ drec : normalizedDatum g (d.offsetPoint hσ) (c * δ) k,
          drec.map = d.recenteringMap hσ hfit ∧ drec.retainedSide = true ∧
          |metricScalarAt g (d.offsetPoint hσ) / metricScalarAt g x₀ - 1| ≤ c * δ ∧
        ∃ out : CanonicalStaticInsertionWitness (drec.lowerOrder hk) A hA 1 4 1,
          FixedStaticInsertionProperties C out ∧
          ∀ P : StaticRequest, δ ≤ δRequest P → max 8 P.order ≤ k →
            P.IsSatisfied out.data.outMetric (metricScalarAt g (d.offsetPoint hσ)) drec.scalar_pos
              (insertionBall (c * δ)⁻¹) (wideModelMap (inv_pos.mpr drec.precision_pos))
              (wideModelMap_isLocalDiffeomorph (inv_pos.mpr drec.precision_pos))
              (wideModelMap_isSmoothEmbedding (inv_pos.mpr drec.precision_pos)).isEmbedding.injective
              out.data.tip := by
  obtain ⟨c, δrec, hc, hδrec, hrec⟩ := exists_fixed_offset_recentering.{u, v, w}
  obtain ⟨C, hC, A, hA, hsmall, δb, hδb, _, δR, hδR, hb⟩ := exists_fixed_static_insertion.{u, v, w}
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  let δ₀ := min δrec (min (δb / c) (1 / 8))
  have hδ₀ : 0 < δ₀ := lt_min hδrec (lt_min (div_pos hδb hcpos) (by norm_num))
  refine ⟨c, hc, C, hC, A, hA, hsmall, δ₀, hδ₀,
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num),
    fun P => min δ₀ (δR P / c),
    fun P => ⟨lt_min hδ₀ (div_pos (hδR P).1 hcpos), min_le_left _ _⟩, ?_⟩
  intro δ hδ hle k hk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d σ hσ
  have hrecSmall : δ ≤ δrec := hle.trans (min_le_left _ _)
  have hbaseSmall : c * δ ≤ δb := by
    have h : δ ≤ δb / c := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
    exact (mul_comm c δ) ▸ (le_div_iff₀ hcpos).mp h
  obtain ⟨hfit, drec, hmap, hside, hratio⟩ :=
    hrec E H I M g x₀ δ k d (by omega) hrecSmall σ hσ
  obtain ⟨out, hout, hreq⟩ := hb (c * δ) (mul_pos hcpos hδ) hbaseSmall k hk
    g (d.offsetPoint hσ) drec
  refine ⟨hfit, drec, hmap, hside, hratio, out, hout, ?_⟩
  intro P hleP hPk
  apply hreq P _ hPk
  have h : δ ≤ δR P / c := hleP.trans (min_le_right _ _)
  exact (mul_comm c δ) ▸ (le_div_iff₀ hcpos).mp h
end DifferentialGeometry.PDE.RicciFlow.StandardCap
