import DifferentialGeometry.Topology.Manifold.SmoothCompatibleAtlas.Defs
import DifferentialGeometry.Topology.Manifold.OpenCoverAtlas
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

theorem contDiffAt_symm_trans_of_mem {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (e e' : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ e.source)
    (hx' : x ∈ e'.source) {n : ℕ∞ω}
    (h : ContDiffOn ℝ n (e.symm.trans e') (e.symm.trans e').source) :
    ContDiffAt ℝ n (e.symm.trans e') (e x) := by
  have hmem : e x ∈ (e.symm.trans e').source := by
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e'.source
    rw [e.left_inv hx]
    exact hx'
  exact h.contDiffAt ((e.symm.trans e').open_source.mem_nhds hmem)

def SmoothCarrier {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace X]
    (_A : SmoothCompatibleAtlas E X ι) : Type _ :=
  X

section

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace X]
  (A : SmoothCompatibleAtlas E X ι)

instance : MetricSpace (SmoothCarrier A) :=
  inferInstanceAs (MetricSpace X)

def SmoothCarrier.chart (i : ι) : OpenPartialHomeomorph (SmoothCarrier A) E :=
  A.chart i

instance : ChartedSpace E (SmoothCarrier A) :=
  chartedSpaceOfOpenCover (SmoothCarrier.chart A) A.mem_source

instance : IsManifold 𝓘(ℝ, E) ∞ (SmoothCarrier A) :=
  isManifold_chartedSpaceOfOpenCover (SmoothCarrier.chart A) A.mem_source
    A.contDiffOn_transition

instance [ProperSpace X] : ProperSpace (SmoothCarrier A) :=
  inferInstanceAs (ProperSpace X)

instance [CompleteSpace X] : CompleteSpace (SmoothCarrier A) :=
  inferInstanceAs (CompleteSpace X)

instance [SecondCountableTopology X] : SecondCountableTopology (SmoothCarrier A) :=
  inferInstanceAs (SecondCountableTopology X)

instance [SigmaCompactSpace X] : SigmaCompactSpace (SmoothCarrier A) :=
  inferInstanceAs (SigmaCompactSpace X)

def SmoothCarrier.toBase : SmoothCarrier A → X :=
  id

def SmoothCarrier.ofBase : X → SmoothCarrier A :=
  id

theorem SmoothCarrier.toBase_ofBase (x : X) :
    SmoothCarrier.toBase A (SmoothCarrier.ofBase A x) = x :=
  rfl

theorem SmoothCarrier.ofBase_toBase (y : SmoothCarrier A) :
    SmoothCarrier.ofBase A (SmoothCarrier.toBase A y) = y :=
  rfl

theorem SmoothCarrier.dist_toBase (x y : SmoothCarrier A) :
    dist (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y) = dist x y :=
  rfl

theorem SmoothCarrier.edist_toBase (x y : SmoothCarrier A) :
    edist (SmoothCarrier.toBase A x) (SmoothCarrier.toBase A y) = edist x y :=
  rfl

theorem SmoothCarrier.ofBase_comp_toBase :
    SmoothCarrier.ofBase A ∘ SmoothCarrier.toBase A = id :=
  rfl

theorem SmoothCarrier.toBase_comp_ofBase :
    SmoothCarrier.toBase A ∘ SmoothCarrier.ofBase A = id :=
  rfl

theorem SmoothCarrier.continuous_toBase : Continuous (SmoothCarrier.toBase A) :=
  continuous_id

theorem SmoothCarrier.continuous_ofBase : Continuous (SmoothCarrier.ofBase A) :=
  continuous_id

theorem SmoothCarrier.chart_apply (i : ι) (x : SmoothCarrier A) :
    SmoothCarrier.chart A i x = A.chart i (SmoothCarrier.toBase A x) :=
  rfl

theorem SmoothCarrier.chart_ofBase (i : ι) (y : X) :
    SmoothCarrier.chart A i (SmoothCarrier.ofBase A y) = A.chart i y :=
  rfl

theorem SmoothCarrier.toBase_chart_symm (i : ι) (z : E) :
    SmoothCarrier.toBase A ((SmoothCarrier.chart A i).symm z) = (A.chart i).symm z :=
  rfl

theorem SmoothCarrier.mem_chart_source_iff (i : ι) (x : SmoothCarrier A) :
    x ∈ (SmoothCarrier.chart A i).source ↔ SmoothCarrier.toBase A x ∈ (A.chart i).source :=
  Iff.rfl

theorem SmoothCarrier.ofBase_mem_chart_source_iff (i : ι) (y : X) :
    SmoothCarrier.ofBase A y ∈ (SmoothCarrier.chart A i).source ↔ y ∈ (A.chart i).source :=
  Iff.rfl

theorem SmoothCarrier.chart_symm_trans_chart (i j : ι) :
    (SmoothCarrier.chart A i).symm.trans (SmoothCarrier.chart A j) =
      (A.chart i).symm.trans (A.chart j) :=
  rfl

def SmoothCarrier.equivBase : SmoothCarrier A ≃ X :=
  ⟨SmoothCarrier.toBase A, SmoothCarrier.ofBase A, SmoothCarrier.ofBase_toBase A,
    SmoothCarrier.toBase_ofBase A⟩

theorem SmoothCarrier.coe_equivBase :
    ⇑(SmoothCarrier.equivBase A) = SmoothCarrier.toBase A :=
  rfl

theorem SmoothCarrier.coe_equivBase_symm :
    ⇑(SmoothCarrier.equivBase A).symm = SmoothCarrier.ofBase A :=
  rfl

theorem SmoothCarrier.contMDiff_toBase_of_chartAt {ι' : Type*} [ChartedSpace E X]
    (φ : ι' → OpenPartialHomeomorph X E) (hφ : ∀ y : X, chartAt E y ∈ range φ) {r : ℕ}
    (hA : A.IsCompatible φ r) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r (SmoothCarrier.toBase A) := by
  intro x
  obtain ⟨j, hj⟩ := chart_mem_atlas E x
  obtain ⟨i, hi⟩ := hφ (SmoothCarrier.toBase A x)
  have hxj : x ∈ (SmoothCarrier.chart A j).source := by
    rw [hj]
    exact mem_chart_source E x
  have hxi : SmoothCarrier.toBase A x ∈ (φ i).source := by
    rw [hi]
    exact mem_chart_source E (SmoothCarrier.toBase A x)
  have hxj' : SmoothCarrier.toBase A x ∈ (A.chart j).source :=
    (SmoothCarrier.mem_chart_source_iff A j x).mp hxj
  have key : ContDiffAt ℝ r ((A.chart j).symm.trans (φ i))
      (A.chart j (SmoothCarrier.toBase A x)) :=
    contDiffAt_symm_trans_of_mem (A.chart j) (φ i) hxj' hxi (hA i j).2
  have hfun : ∀ y : E, (extChartAt 𝓘(ℝ, E) (SmoothCarrier.toBase A x) ∘
      SmoothCarrier.toBase A ∘ (extChartAt 𝓘(ℝ, E) x).symm) y =
      ((A.chart j).symm.trans (φ i)) y := by
    intro y
    rw [Function.comp_apply, Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
      Function.comp_apply, Function.comp_apply, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, id_eq, id_eq, ← hi, ← hj,
      SmoothCarrier.toBase_chart_symm, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  have hpt : extChartAt 𝓘(ℝ, E) x x = A.chart j (SmoothCarrier.toBase A x) := by
    rw [extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq, ← hj,
      SmoothCarrier.chart_apply]
  rw [contMDiffAt_iff]
  refine ⟨(SmoothCarrier.continuous_toBase A).continuousAt, ?_⟩
  rw [hpt]
  exact key.contDiffWithinAt.congr (fun y _ => hfun y) (hfun _)

theorem SmoothCarrier.contMDiff_ofBase_of_chartAt {ι' : Type*} [ChartedSpace E X]
    (φ : ι' → OpenPartialHomeomorph X E) (hφ : ∀ y : X, chartAt E y ∈ range φ) {r : ℕ}
    (hA : A.IsCompatible φ r) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r (SmoothCarrier.ofBase A) := by
  intro x
  obtain ⟨i, hi⟩ := hφ x
  obtain ⟨j, hj⟩ := chart_mem_atlas E (SmoothCarrier.ofBase A x)
  have hxi : x ∈ (φ i).source := by
    rw [hi]
    exact mem_chart_source E x
  have hxj : SmoothCarrier.ofBase A x ∈ (SmoothCarrier.chart A j).source := by
    rw [hj]
    exact mem_chart_source E (SmoothCarrier.ofBase A x)
  have hxj' : x ∈ (A.chart j).source :=
    (SmoothCarrier.ofBase_mem_chart_source_iff A j x).mp hxj
  have key : ContDiffAt ℝ r ((φ i).symm.trans (A.chart j)) (φ i x) :=
    contDiffAt_symm_trans_of_mem (φ i) (A.chart j) hxi hxj' (hA i j).1
  have hfun : ∀ y : E, (extChartAt 𝓘(ℝ, E) (SmoothCarrier.ofBase A x) ∘
      SmoothCarrier.ofBase A ∘ (extChartAt 𝓘(ℝ, E) x).symm) y =
      ((φ i).symm.trans (A.chart j)) y := by
    intro y
    rw [Function.comp_apply, Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
      Function.comp_apply, Function.comp_apply, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, id_eq, id_eq, ← hi, ← hj, SmoothCarrier.chart_ofBase,
      OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  have hpt : extChartAt 𝓘(ℝ, E) x x = φ i x := by
    rw [extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq, ← hi]
  rw [contMDiffAt_iff]
  refine ⟨(SmoothCarrier.continuous_ofBase A).continuousAt, ?_⟩
  rw [hpt]
  exact key.contDiffWithinAt.congr (fun y _ => hfun y) (hfun _)

theorem SmoothCarrier.contMDiff_toBase {ι' : Type*} (φ : ι' → OpenPartialHomeomorph X E)
    (hcover : ∀ x, ∃ i, x ∈ (φ i).source) {r : ℕ} (hA : A.IsCompatible φ r) :
    letI := chartedSpaceOfOpenCover φ hcover
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r (SmoothCarrier.toBase A) := by
  let _ : ChartedSpace E X := chartedSpaceOfOpenCover φ hcover
  exact SmoothCarrier.contMDiff_toBase_of_chartAt A φ (fun y => chart_mem_atlas E y) hA

theorem SmoothCarrier.contMDiff_ofBase {ι' : Type*} (φ : ι' → OpenPartialHomeomorph X E)
    (hcover : ∀ x, ∃ i, x ∈ (φ i).source) {r : ℕ} (hA : A.IsCompatible φ r) :
    letI := chartedSpaceOfOpenCover φ hcover
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r (SmoothCarrier.ofBase A) := by
  let _ : ChartedSpace E X := chartedSpaceOfOpenCover φ hcover
  exact SmoothCarrier.contMDiff_ofBase_of_chartAt A φ (fun y => chart_mem_atlas E y) hA

theorem SmoothCarrier.exists_diffeomorph_toBase {ι' : Type*}
    (φ : ι' → OpenPartialHomeomorph X E) (hcover : ∀ x, ∃ i, x ∈ (φ i).source) {r : ℕ}
    (hA : A.IsCompatible φ r) :
    letI := chartedSpaceOfOpenCover φ hcover
    ∃ f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier A) X r,
      ⇑f = SmoothCarrier.toBase A ∧ ⇑f.symm = SmoothCarrier.ofBase A := by
  let _ : ChartedSpace E X := chartedSpaceOfOpenCover φ hcover
  have h1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r ⇑(SmoothCarrier.equivBase A) := by
    rw [SmoothCarrier.coe_equivBase]
    exact SmoothCarrier.contMDiff_toBase A φ hcover hA
  have h2 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r ⇑(SmoothCarrier.equivBase A).symm := by
    rw [SmoothCarrier.coe_equivBase_symm]
    exact SmoothCarrier.contMDiff_ofBase A φ hcover hA
  let f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier A) X r :=
    ⟨SmoothCarrier.equivBase A, h1, h2⟩
  exact ⟨f, (Diffeomorph.coe_toEquiv f).symm.trans (SmoothCarrier.coe_equivBase A),
    (Diffeomorph.toEquiv_coe_symm f).symm.trans (SmoothCarrier.coe_equivBase_symm A)⟩

end

end DifferentialGeometry.Topology.Manifold
