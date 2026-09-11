import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreBoundaryAtlas

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CollarE3 := EuclideanSpace ℝ (Fin 3)
private abbrev CollarE2 := EuclideanSpace ℝ (Fin 2)
private abbrev CollarS2 := Metric.sphere (0 : CollarE3) 1
private abbrev CollarIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev CollarIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev CollarIH := ModelProd CollarE2 (EuclideanHalfSpace 1)
private local instance : Fact (Module.finrank ℝ CollarE3 = 2 + 1) := ⟨by simp⟩

theorem cuttingCollarCylinderMap_contMDiff {δ : ℝ} (hδ : 0 < δ) (b : Bool) :
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth δ)) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
    ContMDiff CollarIR CollarIC ∞ (cuttingCollarCylinderMap hδ b) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth δ)) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
  let : IsManifold (𝓡∂ 1) ∞ (Ico (0 : ℝ) (cuttingCollarWidth δ)) :=
    halfClosedInterval_isManifold (cuttingCollarWidth_pos hδ)
  have ht : ContMDiff CollarIR 𝓘(ℝ) ∞
      (fun q : CollarS2 × Ico (0 : ℝ) (cuttingCollarWidth δ) => q.2.val) :=
    (isSmoothEmbedding_halfClosedInterval_inclusion (cuttingCollarWidth_pos hδ)).contMDiff.comp contMDiff_snd
  have hr : ContMDiff CollarIR CollarIC ∞
      (fun q : CollarS2 × Ico (0 : ℝ) (cuttingCollarWidth δ) =>
        (q.1, cuttingSign b + cuttingSign b * q.2.val)) :=
    contMDiff_fst.prodMk (contMDiff_const.add (contMDiff_const.mul ht))
  dsimp only
  intro q
  exact codRestr_contMDiffAt (I := CollarIR) (J := CollarIC) (V := bufferedCylinder δ)
    (fun p => (cuttingCollarCylinderMap hδ b p).property) hr.contMDiffAt

theorem cutCoreCollarHalfChart_contMDiff_transition
    {ι M : Type*} [TopologicalSpace M] {precision : ι → ℝ}
    (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b c : ι × Bool)
    (q : CollarS2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)))
    (r : CollarS2 × Ico (0 : ℝ) (cuttingCollarWidth (precision c.1))) :
    ContMDiffOn CollarIR CollarIR ∞
      ((cutCoreCollarHalfChart hδ f hf hdisj b q).symm.trans (cutCoreCollarHalfChart hδ f hf hdisj c r))
      ((cutCoreCollarHalfChart hδ f hf hdisj b q).symm.trans (cutCoreCollarHalfChart hδ f hf hdisj c r)).source := by
  by_cases hbc : b = c
  · subst c
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let : IsManifold (𝓡∂ 1) ∞ (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    simp only [cutCoreCollarHalfChart, OpenPartialHomeomorph.lift_openEmbedding_trans]
    exact (contMDiffOn_chart (I := CollarIR) (x := r)).comp' (contMDiffOn_chart_symm (I := CollarIR) (x := q))
  · intro x hx
    have hb := (cutCoreCollarHalfChart hδ f hf hdisj b q).map_target hx.1
    obtain ⟨u, _, hu⟩ := hb
    obtain ⟨v, _, hv⟩ := hx.2
    exact (disjoint_left.mp (pairwise_disjoint_cuttingCollars hδ f (fun i => (hf i).injective) hdisj hbc)
      ⟨u, hu⟩ ⟨v, hv⟩).elim

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type*} {precision : ι → ℝ} (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hi : ∀ i, Injective (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, ContMDiff CollarIC I ∞ (f i))

include hs in
theorem cuttingCollarAmbient_contMDiff (b : ι × Bool) :
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    ContMDiff CollarIR I ∞ (Subtype.val ∘ cuttingCollarMap hδ f hi hdisj b) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  exact (hs b.1).comp (cuttingCollarCylinderMap_contMDiff (hδ b.1) b.2)

include hs in
theorem cutCoreCollarHalfChart_symm_ambient_contMDiffOn
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) (b : ι × Bool)
    (q : CollarS2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    ContMDiffOn CollarIR I ∞
      (fun z : CollarIH => ((cutCoreCollarHalfChart hδ f hf hdisj b q).symm z).val)
      (cutCoreCollarHalfChart hδ f hf hdisj b q).target := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : IsManifold (𝓡∂ 1) ∞ (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  exact (cuttingCollarAmbient_contMDiff I hδ f (fun i => (hf i).injective) hdisj hs b).comp_contMDiffOn
    (contMDiffOn_chart_symm (I := CollarIR) (x := q))
end DifferentialGeometry.Topology.ThreeManifold.Surgery
