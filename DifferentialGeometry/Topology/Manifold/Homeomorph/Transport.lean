import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

open Set Function Manifold Topology
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.Homeomorph
variable {H M X : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace X]

@[instance_reducible] def pullbackChartedSpace (h : X ≃ₜ M) : ChartedSpace H X where
  atlas := {h.toOpenPartialHomeomorph.trans e | e ∈ atlas H M}
  chartAt x := h.toOpenPartialHomeomorph.trans (chartAt H (h x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt H (h x), chart_mem_atlas H (h x), rfl⟩


@[simp] theorem chartAt_pullback (h : X ≃ₜ M) (x : X) :
    let _ := pullbackChartedSpace (H := H) h
    chartAt H x = h.toOpenPartialHomeomorph.trans (chartAt H (h x)) := rfl

omit [ChartedSpace H M] in
private theorem trans_cancel (h : X ≃ₜ M) (e e' : OpenPartialHomeomorph M H) :
    (h.toOpenPartialHomeomorph.trans e).symm.trans
      (h.toOpenPartialHomeomorph.trans e') = e.symm.trans e' := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc, ← OpenPartialHomeomorph.trans_assoc h.toOpenPartialHomeomorph.symm,
    ← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph,
    Homeomorph.symm_trans_self]
  simp

instance instHasGroupoidPullback (h : X ≃ₜ M) (G : StructureGroupoid H) [HasGroupoid M G] :
    let _ := pullbackChartedSpace (H := H) h
    HasGroupoid X G := by
  let _ := pullbackChartedSpace (H := H) h
  change HasGroupoid X G
  constructor
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  rw [trans_cancel]
  exact G.compatible he he'

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [IsManifold I n M]


instance instIsManifoldPullback (h : X ≃ₜ M) :
    let _ := pullbackChartedSpace (H := H) h
    IsManifold I n X := by
  let _ := pullbackChartedSpace (H := H) h
  exact IsManifold.mk' I n X


theorem contMDiff_pullback (h : X ≃ₜ M) :
    let _ := pullbackChartedSpace (H := H) h
    ContMDiff I I n h := by
  let _ := pullbackChartedSpace (H := H) h
  apply contMDiff_iff.mpr
  refine ⟨h.continuous, ?_⟩
  intro x y
  have hh := (contMDiff_iff.mp (contMDiff_id (I := I) (M := M) (n := n))).2 (h x) y
  convert hh using 1
  · ext z
    simp [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def]
  · ext z
    simp [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def]


theorem contMDiff_symm_pullback (h : X ≃ₜ M) :
    let _ := pullbackChartedSpace (H := H) h
    ContMDiff I I n h.symm := by
  let _ := pullbackChartedSpace (H := H) h
  apply contMDiff_iff.mpr
  refine ⟨h.symm.continuous, ?_⟩
  intro x y
  have hh := (contMDiff_iff.mp (contMDiff_id (I := I) (M := M) (n := n))).2 x (h y)
  convert hh using 1
  · ext z
    simp [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def]
  · ext z
    simp [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def]

def pullbackDiffeomorph (h : X ≃ₜ M) :
    let _ := pullbackChartedSpace (H := H) h
    Diffeomorph I I X M n := by
  let _ := pullbackChartedSpace (H := H) h
  exact ⟨h.toEquiv, contMDiff_pullback h, contMDiff_symm_pullback h⟩

theorem boundaryless_manifold_pullback
    [BoundarylessManifold I M] (h : X ≃ₜ M) (hn : n ≠ 0) :
    let _ := pullbackChartedSpace (H := H) h
    BoundarylessManifold I X := by
  let _ := pullbackChartedSpace (H := H) h
  refine ⟨fun x ↦ ?_⟩
  exact ((pullbackDiffeomorph (I := I) (n := n) h).isLocalDiffeomorph x).isInteriorPoint_iff
    hn |>.mpr BoundarylessManifold.isInteriorPoint

@[simp] theorem pullbackDiffeomorph_apply (h : X ≃ₜ M) (x : X) :
    let _ := pullbackChartedSpace (H := H) h
    pullbackDiffeomorph (I := I) (n := n) h x = h x := rfl

theorem pullbackDiffeomorph_symm_apply (h : X ≃ₜ M) (x : M) :
    let _ := pullbackChartedSpace (H := H) h
    (pullbackDiffeomorph (I := I) (n := n) h).symm x = h.symm x := rfl

end Poincare.Manifold.Homeomorph
