import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.RecenteredStaticPreparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticCollarAdmitsC11PB
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessVolume

/-!
# Recentered static preparation with an explicit recentering constant (C12X)

`exists_uniform_recentered_static_preparation` and
`exists_uniform_recentered_static_family_volume_bound` obtain their recentering constant `c` from
`exists_fixed_offset_recentering` inside the proof, so downstream users cannot recenter a second
(higher-order) datum with the same `c`.  The versions here take `c`, `δrec` and the recentering
property (the body of `exists_fixed_offset_recentering`, valid at every order `k ≥ 2`) as explicit
arguments and additionally record `δ₀ ≤ δrec`.  Step 2 of the S10 window-order parametrization.
-/

set_option autoImplicit false
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

/-- `exists_uniform_recentered_static_preparation` with the recentering constant `c` and the
recentering property supplied explicitly; also `δ₀ ≤ δrec`. -/
theorem exists_uniform_recentered_static_preparation_C12X (c δrec : ℝ) (hc : 4 ≤ c)
    (hδrec : 0 < δrec)
    (hrec : ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        (H : Type v) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type w) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric I M) (x₀ : M) (δ : ℝ) (k : ℕ)
        (d : normalizedDatum g x₀ δ k), 2 ≤ k → δ ≤ δrec →
        ∀ (σ : ℝ) (hσ : σ ^ 2 = 1),
          ∃ hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹,
            ∃ d' : normalizedDatum g (d.offsetPoint hσ) (c * δ) k,
              d'.map = d.recenteringMap hσ hfit ∧ d'.retainedSide = true ∧
              |metricScalarAt g (d.offsetPoint hσ) / metricScalarAt g x₀ - 1| ≤ c * δ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), (2 * A < 1 / 2 ∧ StaticCollarAdmits.{u, v, w} A hA) ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧ δ₀ ≤ δrec ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
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
  obtain ⟨C, hC, A, hA, hsmall, hmod⟩ := exists_staticInsertion_with_additional_properties.{u, v, w}
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hcollar : StaticCollarAdmits.{u, v, w} A hA := by
    intro D hD m ε hε
    obtain ⟨δ₀, hδ₀, hhalf, hb⟩ := hmod D hD m ε hε
    refine ⟨δ₀, hδ₀, hhalf, ?_⟩
    intro δ hδ hle E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
    obtain ⟨w, -⟩ := hb δ hδ hle g x₀ d
    exact ⟨w⟩
  refine ⟨C, hC, A, hA, ⟨hsmall, hcollar⟩, ?_⟩
  intro D hD m ε hε
  obtain ⟨δi, hδi, _, hinsert⟩ := hmod D hD m ε hε
  let δ₀ := min δrec (min (δi / c) (1 / 8))
  have hδ₀ : 0 < δ₀ := lt_min hδrec (lt_min (div_pos hδi hcpos) (by norm_num))
  refine ⟨δ₀, hδ₀, ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num),
    min_le_left _ _, ?_⟩
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

/-- `exists_uniform_recentered_static_family_volume_bound` with the recentering constant `c` and
the recentering property supplied explicitly; also `δ₀ ≤ δrec`. -/
theorem exists_uniform_recentered_static_family_volume_bound_C12X (c δrec : ℝ) (hc : 4 ≤ c)
    (hδrec : 0 < δrec)
    (hrec : ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        (H : Type v) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type w) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric I M) (x₀ : M) (δ : ℝ) (k : ℕ)
        (d : normalizedDatum g x₀ δ k), 2 ≤ k → δ ≤ δrec →
        ∀ (σ : ℝ) (hσ : σ ^ 2 = 1),
          ∃ hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹,
            ∃ d' : normalizedDatum g (d.offsetPoint hσ) (c * δ) k,
              d'.map = d.recenteringMap hσ hfit ∧ d'.retainedSide = true ∧
              |metricScalarAt g (d.offsetPoint hσ) / metricScalarAt g x₀ - 1| ≤ c * δ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), (2 * A < 1 / 2 ∧ StaticCollarAdmits.{u, v, w} A hA) ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 4 ∧ δ₀ ≤ δrec ∧
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
          (∀ i, |metricScalarAt g ((d₀ i).offsetPoint (hσ i)) / metricScalarAt g (x₀ i) - 1| ≤
            c * δ i) ∧
          (∀ i, metricScalarAt g (x₀ i) / 2 ≤ metricScalarAt g ((d₀ i).offsetPoint (hσ i))) ∧
          (∀ i, metricScalarAt g ((d₀ i).offsetPoint (hσ i)) ≤
            (3 / 2 : ℝ) * metricScalarAt g (x₀ i)) ∧
          (∀ i, StaticInsertionAdditionalProperties C (w i)) ∧
          (∀ i, riemannianVolumeMeasure (𝓡 3)
            (InsertionQuotient (inv_pos.mpr (d i).precision_pos))
            (w i).data.outMetric (range (w i).data.capMap) ≤
              ENNReal.ofReal (8 * (metricScalarAt g (x₀ i)) ^ (-3 / 2 : ℝ)) *
                riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}) := by
  obtain ⟨C, hC, A, hA, hsmall, hfactory⟩ :=
    exists_uniform_recentered_static_preparation_C12X.{u, v, w} c δrec hc hδrec hrec
  obtain ⟨δv, hδv, _, hvolume⟩ :=
    exists_canonicalStaticInsertionWitness_cap_volume_bound_of_scalar_lower A hA
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  refine ⟨C, hC, A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δr, hδr, hquarter, hδrrec, hprep⟩ := hfactory D hD m ε hε
  let δ₀ := min δr (min (δv / c) (1 / 8646))
  refine ⟨δ₀, lt_min hδr (lt_min (div_pos hδv hcpos) (by norm_num)),
    (min_le_left _ _).trans_lt hquarter, (min_le_left _ _).trans hδrrec, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g ι x₀ δ d₀ hδ σ hσ
  have hrec (i : ι) := hprep (δ i) (d₀ i).precision_pos
    ((hδ i).trans (min_le_left _ _)) g (x₀ i) (d₀ i) (σ i) (hσ i)
  choose hfit d hmap hside hratio w hw using hrec
  have hb (i : ι) : metricScalarAt g (x₀ i) / 2 ≤ metricScalarAt g ((d₀ i).offsetPoint (hσ i)) ∧
      metricScalarAt g ((d₀ i).offsetPoint (hσ i)) ≤ (3 / 2 : ℝ) * metricScalarAt g (x₀ i) := by
    have hdsmall : δ i ≤ 1 / 8646 := (hδ i).trans ((min_le_right _ _).trans (min_le_right _ _))
    let q : bufferedCylinder (δ i) := ⟨(spherePoint, σ i),
      offset_mem_bufferedCylinder (d₀ i).precision_pos (hσ i) spherePoint⟩
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
