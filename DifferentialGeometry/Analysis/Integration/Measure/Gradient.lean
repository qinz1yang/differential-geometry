import DifferentialGeometry.Analysis.Calculus.Derivative.Measurable
import DifferentialGeometry.Geometry.Operator.Gradient.Coordinates
import Mathlib.Topology.Instances.Matrix

noncomputable section

open Bundle Set Filter MeasureTheory
open scoped Manifold ContDiff BigOperators Topology

namespace DifferentialGeometry.Analysis

open Geometry.Operator Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [OpensMeasurableSpace M]

section Static

variable [LindelofSpace M]

theorem measurable_inner_gradFun
    (g : SmoothRiemannianMetric I M) (f h : M → ℝ) :
    Measurable (fun x => g.inner x (gradFun g f x) (gradFun g h x)) := by
  borelize E
  have hlocal (α : M) : Measurable (fun x : (chartAt H α).source =>
      g.inner x (gradFun g f x) (gradFun g h x)) := by
    have hc : Measurable (fun x : (chartAt H α).source => extChartAt I α x) :=
      by
        have hh := continuousOn_extChartAt (I := I) α
        rw [extChartAt_source_eq_chartAt_source] at hh
        exact hh.domRestrict.measurable
    have hp (u : M → ℝ) (i : Fin (Module.finrank ℝ E)) :
        Measurable (fun x : (chartAt H α).source =>
          partialDeriv (E := E) i (scalarOnE (I := I) α u) (extChartAt I α x)) :=
      (measurable_fderiv_apply_const ℝ (scalarOnE (I := I) α u) (chartModelBasis E i)).comp hc
    have hg (i j : Fin (Module.finrank ℝ E)) :
        Measurable (fun x : (chartAt H α).source => chartInvGramMatrix (I := I) g α x i j) := by
      have hh := (chartInvGramMatrix_entry_contMDiffOn g α i j).continuousOn
      rw [trivializationAt_baseSet_eq_chartAt_source] at hh
      exact hh.domRestrict.measurable
    have heq (x : (chartAt H α).source) := inner_gradFun_eq_chartInvGram_sum g α f h
      (by simpa only [trivializationAt_baseSet_eq_chartAt_source] using x.property)
      (by rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
          exact (extChartAt I α).map_source (by simpa only [extChartAt_source_eq_chartAt_source] using x.property))
    simp_rw [heq]
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      ((hg i j).mul (hp f i)).mul (hp h j)
  obtain ⟨s, hs, hcover⟩ := countable_cover_nhds (fun x : M => chart_source_mem_nhds H x)
  let _ := hs.toEncodable
  intro B hB
  have heq : (fun x => g.inner x (gradFun g f x) (gradFun g h x)) ⁻¹' B =
      ⋃ α : s, Subtype.val '' ((fun x : (chartAt H (α : M)).source =>
        g.inner x (gradFun g f x) (gradFun g h x)) ⁻¹' B) := by
    ext x
    constructor
    · intro hx
      have hc : x ∈ ⋃ α ∈ s, (chartAt H α).source := by rw [hcover]; trivial
      obtain ⟨α, hα, hxα⟩ := mem_iUnion₂.mp hc
      exact mem_iUnion.mpr ⟨⟨α, hα⟩, ⟨x, hxα⟩, hx, rfl⟩
    · intro hx
      obtain ⟨α, y, hy, rfl⟩ := mem_iUnion.mp hx
      exact hy
  rw [heq]
  exact MeasurableSet.iUnion fun α : s =>
    ((chartAt H (α : M)).open_source.measurableSet).subtype_image (hlocal α hB)

end Static

section Parameter

variable [SecondCountableTopology M]
  {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]

private theorem measurable_inner_gradFun_with_param_on_chart
    (g : P → SmoothRiemannianMetric I M)
    (hgram : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : P × M => chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (α : M) {f h : P → M → ℝ} (hf : Continuous f.uncurry) (hh : Continuous h.uncurry) :
    Measurable (fun p : P × (chartAt H α).source =>
      (g p.1).inner p.2 (gradFun (g p.1) (f p.1) p.2) (gradFun (g p.1) (h p.1) p.2)) := by
  classical
  borelize E
  have hc : Measurable (fun x : (chartAt H α).source => extChartAt I α x) := by
    have hh := continuousOn_extChartAt (I := I) α
    rw [extChartAt_source_eq_chartAt_source] at hh
    exact hh.domRestrict.measurable
  have htarget (x : (chartAt H α).source) : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by simpa only [extChartAt_source_eq_chartAt_source] using x.property)
  have hp (u : P → M → ℝ) (hu : Continuous u.uncurry) (i : Fin (Module.finrank ℝ E)) :
      Measurable (fun p : P × (chartAt H α).source =>
        partialDeriv (E := E) i (scalarOnE (I := I) α (u p.1)) (extChartAt I α p.2)) := by
    have huc : ContinuousOn (fun p : P × E => scalarOnE (I := I) α (u p.1) p.2)
        (univ ×ˢ (extChartAt I α).target) :=
      hu.comp_continuousOn (continuousOn_fst.prodMk
        ((continuousOn_extChartAt_symm (I := I) α).comp continuousOn_snd fun _ hz => hz.2))
    have hm := measurable_fderiv_with_param_of_continuousOn (f := fun p => scalarOnE (I := I) α (u p)) (isOpen_extChartAt_target (I := I) α) huc
    exact (ContinuousLinearMap.measurable_apply (chartModelBasis E i)).comp
      (hm.comp (measurable_fst.prodMk
        (((hc.subtype_mk (h := htarget)).comp measurable_snd))))
  let A : P × (chartAt H α).source → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun p => chartGramMatrix (I := I) (g p.1) α p.2
  have hA : Continuous A := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (hgram α i j).comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨mem_univ _, by simpa only [trivializationAt_baseSet_eq_chartAt_source, Function.comp_apply] using p.2.property⟩)
  have hdet (p : P × (chartAt H α).source) : (A p).det ≠ 0 :=
    ne_of_gt (chartGramMatrix_det_pos (g p.1) α
      (by simpa only [trivializationAt_baseSet_eq_chartAt_source] using p.2.property))
  have hg (i j : Fin (Module.finrank ℝ E)) :
      Measurable (fun p : P × (chartAt H α).source => chartInvGramMatrix (I := I) (g p.1) α p.2 i j) := by
    have hc : Continuous (fun p => (A p).det⁻¹ * (A p).adjugate i j) :=
      (hA.matrix_det.inv₀ hdet).mul ((continuous_apply j).comp ((continuous_apply i).comp hA.matrix_adjugate))
    simpa only [chartInvGramMatrix, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
      smul_eq_mul, A] using hc.measurable
  have heq (p : P × (chartAt H α).source) := inner_gradFun_eq_chartInvGram_sum (g p.1) α (f p.1) (h p.1)
    (by simpa only [trivializationAt_baseSet_eq_chartAt_source] using p.2.property)
    (by rw [(isOpen_extChartAt_target (I := I) α).interior_eq]; exact htarget p.2)
  simp_rw [heq]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((hg i j).mul (hp f hf i)).mul (hp h hh j)

theorem measurable_inner_gradFun_with_param
    (g : P → SmoothRiemannianMetric I M)
    (hg : Continuous (fun p : P × M =>
      (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))))
    {f h : P → M → ℝ} (hf : Continuous f.uncurry) (hh : Continuous h.uncurry) :
    Measurable (fun p : P × M =>
      (g p.1).inner p.2 (gradFun (g p.1) (f p.1) p.2) (gradFun (g p.1) (h p.1) p.2)) := by
  classical
  borelize E
  have hgram (α : M) (i j : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun p : P × M => chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hsnd : ContinuousOn (Prod.snd : P × M → M)
        (univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := continuousOn_snd
    have hv := (chartBasisVec_contMDiffOn (I := I) α i).continuousOn.comp
      hsnd (fun p hp => hp.2)
    have hw := (chartBasisVec_contMDiffOn (I := I) α j).continuousOn.comp
      hsnd (fun p hp => hp.2)
    have happ := hg.continuousOn.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
      (E₃ := Bundle.Trivial M ℝ) hv hw
    exact (continuous_snd.comp (Bundle.Trivial.homeomorphProd M ℝ).continuous).comp_continuousOn happ
  have hlocal (α : M) := measurable_inner_gradFun_with_param_on_chart g hgram α hf hh
  obtain ⟨s, hs, hcover⟩ := countable_cover_nhds (fun x : M => chart_source_mem_nhds H x)
  let _ := hs.toEncodable
  intro B hB
  let v : P × M → ℝ := fun p =>
    (g p.1).inner p.2 (gradFun (g p.1) (f p.1) p.2) (gradFun (g p.1) (h p.1) p.2)
  have heq : v ⁻¹' B = ⋃ α : s, (univ ×ˢ (chartAt H (α : M)).source) ∩ v ⁻¹' B := by
    rw [← iUnion_inter]
    have hc : (⋃ α : s, (univ : Set P) ×ˢ (chartAt H (α : M)).source) = univ := by
      ext p
      simp only [mem_iUnion, mem_prod, mem_univ, true_and, iff_true]
      have hp : p.2 ∈ ⋃ α ∈ s, (chartAt H α).source := by rw [hcover]; trivial
      obtain ⟨α, hα, hpα⟩ := mem_iUnion₂.mp hp
      exact ⟨⟨α, hα⟩, hpα⟩
    rw [hc, univ_inter]
  change MeasurableSet (v ⁻¹' B)
  rw [heq]
  apply MeasurableSet.iUnion
  intro α
  have hm : Measurable (fun p : (univ : Set P) ×ˢ (chartAt H (α : M)).source => v p) :=
    (hlocal α).comp ((measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk (h := fun p => p.property.2)))
  have hh := (MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (univ : Set P)) (chartAt H (α : M)).open_source.measurableSet).subtype_image (hm hB)
  change MeasurableSet (Subtype.val '' (Subtype.val ⁻¹' (v ⁻¹' B))) at hh
  simpa only [Subtype.image_preimage_coe] using hh

end Parameter

end DifferentialGeometry.Analysis
