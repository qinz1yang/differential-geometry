import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.RecenteredStaticPreparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessVolume

noncomputable section
open Set Function TopologicalSpace Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u v w z
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private local instance : MeasurableSpace E3 := borel E3
private local instance : BorelSpace E3 := ⟨rfl⟩
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : SecondCountableTopology (InsertionQuotient hB) :=
  radialCapAttachment_secondCountableTopology transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : LocallyCompactSpace (InsertionQuotient hB) := by
  let : LocallyCompactSpace {x : E3 // ‖x‖ < transitionEnd + B} :=
    (isOpen_lt continuous_norm continuous_const).locallyCompactSpace
  exact (radialCapAttachmentHomeomorph transitionEnd_pos hB :
    InsertionQuotient hB ≃ₜ insertionBall B).isClosedEmbedding.locallyCompactSpace
private local instance {B : ℝ} {hB : 0 < B} : MeasurableSpace (InsertionQuotient hB) :=
  borel (InsertionQuotient hB)
private local instance {B : ℝ} {hB : 0 < B} : BorelSpace (InsertionQuotient hB) := ⟨rfl⟩


theorem exists_uniform_recentered_static_family_volume_bound :
    ∃ c : ℝ, 4 ≤ c ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), (2 * A < 1 / 2 ∧ StaticCollarAdmits.{u, v, w} A hA) ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧
      ∀ {E : Type u} {H : Type v} {M : Type w}
        [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
        [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H]
        {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric I M) {ι : Type z}
        (x₀ : ι → M) (δ : ι → ℝ)
        (d₀ : ∀ i, normalizedDatum g (x₀ i) (δ i) (m + 6)),
        (∀ i, δ i ≤ δ₀) → ∀ (σ : ι → ℝ) (hσ : ∀ i, σ i ^ 2 = 1),
        ∃ hfit : ∀ i, (c * δ i)⁻¹ + 1 ≤ (δ i)⁻¹,
        ∃ d : ∀ i, normalizedDatum g ((d₀ i).offsetPoint (hσ i)) (c * δ i) (m + 4),
        ∃ w : ∀ i, CanonicalStaticInsertionWitness (d i) A hA D m ε,
          (∀ i, (d i).map = (d₀ i).recenteringMap (hσ i) (hfit i)) ∧
          (∀ i, (d i).retainedSide = true) ∧
          (∀ i, |metricScalarAt g ((d₀ i).offsetPoint (hσ i)) / metricScalarAt g (x₀ i) - 1| ≤ c * δ i) ∧
          (∀ i, metricScalarAt g (x₀ i) / 2 ≤ metricScalarAt g ((d₀ i).offsetPoint (hσ i))) ∧
          (∀ i, metricScalarAt g ((d₀ i).offsetPoint (hσ i)) ≤ (3 / 2 : ℝ) * metricScalarAt g (x₀ i)) ∧
          (∀ i, StaticInsertionAdditionalProperties C (w i)) ∧
          (∀ i, riemannianVolumeMeasure (𝓡 3) (InsertionQuotient (inv_pos.mpr (d i).precision_pos))
            (w i).data.outMetric (range (w i).data.capMap) ≤
              ENNReal.ofReal (8 * (metricScalarAt g (x₀ i)) ^ (-3 / 2 : ℝ)) *
                riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}) := by
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hfactory⟩ := exists_uniform_recentered_static_preparation.{u, v, w}
  obtain ⟨δv, hδv, _, hvolume⟩ := exists_canonicalStaticInsertionWitness_cap_volume_bound_of_scalar_lower A hA
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δr, hδr, hquarter, hprep⟩ := hfactory D hD m ε hε
  let δ₀ := min δr (min (δv / c) (1 / 8646))
  refine ⟨δ₀, lt_min hδr (lt_min (div_pos hδv hcpos) (by norm_num)),
    (min_le_left _ _).trans_lt hquarter, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g ι x₀ δ d₀ hδ σ hσ
  have hrec (i : ι) := hprep (δ i) (d₀ i).precision_pos
    ((hδ i).trans (min_le_left _ _)) g (x₀ i) (d₀ i) (σ i) (hσ i)
  choose hfit d hmap hside hratio w hw using hrec
  have hb (i : ι) : metricScalarAt g (x₀ i) / 2 ≤ metricScalarAt g ((d₀ i).offsetPoint (hσ i)) ∧
      metricScalarAt g ((d₀ i).offsetPoint (hσ i)) ≤ (3 / 2 : ℝ) * metricScalarAt g (x₀ i) := by
    have hdsmall : δ i ≤ 1 / 8646 := (hδ i).trans ((min_le_right _ _).trans (min_le_right _ _))
    let q : bufferedCylinder (δ i) := ⟨(spherePoint, σ i), offset_mem_bufferedCylinder (d₀ i).precision_pos (hσ i) spherePoint⟩
    have hq : q ∈ controlledCylinder (δ i) := by
      change -(δ i)⁻¹ ≤ σ i ∧ σ i ≤ (δ i)⁻¹
      have hi := (one_le_inv₀ (d₀ i).precision_pos).mpr (d₀ i).precision_lt_one.le
      rcases sq_eq_one_iff.mp (hσ i) with h | h <;> rw [h] <;> constructor <;> linarith
    have hr := (d₀ i).abs_scalar_ratio_sub_one_le (by omega) (by linarith) q hq
    have hlo : (1 / 2 : ℝ) ≤ metricScalarAt g ((d₀ i).map q) / metricScalarAt g (x₀ i) := by
      have hh := (abs_le.mp hr).1
      linarith
    have hhi : metricScalarAt g ((d₀ i).map q) / metricScalarAt g (x₀ i) ≤ (3 / 2 : ℝ) := by
      have hh := (abs_le.mp hr).2
      linarith
    change metricScalarAt g (x₀ i) / 2 ≤ metricScalarAt g ((d₀ i).map q) ∧
      metricScalarAt g ((d₀ i).map q) ≤ (3 / 2 : ℝ) * metricScalarAt g (x₀ i)
    exact ⟨by linarith [(le_div_iff₀ (d₀ i).scalar_pos).mp hlo],
      (div_le_iff₀ (d₀ i).scalar_pos).mp hhi⟩
  refine ⟨hfit, d, w, hmap, hside, hratio, fun i => (hb i).1, fun i => (hb i).2, hw, ?_⟩
  intro i
  have hvsmall : c * δ i ≤ δv := by
    have h := (hδ i).trans ((min_le_right _ _).trans (min_le_left _ _))
    exact (mul_comm c (δ i)) ▸ (le_div_iff₀ hcpos).mp h
  exact hvolume (c * δ i) (d i).precision_pos hvsmall (m + 4) g ((d₀ i).offsetPoint (hσ i))
    (d i) D m ε (w i) (metricScalarAt g (x₀ i)) (d₀ i).scalar_pos (hb i).1

end DifferentialGeometry.PDE.RicciFlow.StandardCap
