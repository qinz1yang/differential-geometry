import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

section

open Set Function Manifold Topology
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.Homeomorph
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

end DifferentialGeometry.Manifold.Homeomorph

end

end

open scoped Manifold Topology

namespace DifferentialGeometry.Topology.Handle

noncomputable section

universe u v w

@[reducible]
noncomputable def chartedSpaceOfHomeomorph {H : Type u} [TopologicalSpace H]
    {M : Type v} [TopologicalSpace M] {M' : Type w} [TopologicalSpace M']
    (h : M' ≃ₜ M) [ChartedSpace H M] : ChartedSpace H M' where
  atlas := {e : OpenPartialHomeomorph M' H | ∃ e₀ : OpenPartialHomeomorph M H,
    e₀ ∈ ChartedSpace.atlas (H := H) (M := M) ∧ e = h.toOpenPartialHomeomorph ≫ₕ e₀}
  chartAt := fun x : M' => h.toOpenPartialHomeomorph ≫ₕ (chartAt (H := H) (M := M) (h x))
  mem_chart_source := by
    intro x
    have hx : h x ∈ (chartAt (H := H) (M := M) (h x)).source :=
      mem_chart_source (H := H) (M := M) (h x)
    dsimp
    constructor
    · trivial
    · exact hx
  chart_mem_atlas := by
    intro x
    exact ⟨(chartAt (H := H) (M := M) (h x)), chart_mem_atlas (H := H) (M := M) (h x), rfl⟩

private theorem chartedSpaceOfHomeomorph_eq_pullback {H : Type u} [TopologicalSpace H]
    {M : Type v} [TopologicalSpace M] {M' : Type w} [TopologicalSpace M']
    (h : M' ≃ₜ M) [ChartedSpace H M] :
    chartedSpaceOfHomeomorph (H := H) h =
      DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := H) h := by
  apply ChartedSpace.ext
  · ext e
    change (∃ e₀ : OpenPartialHomeomorph M H,
      e₀ ∈ ChartedSpace.atlas (H := H) (M := M) ∧ e = h.toOpenPartialHomeomorph ≫ₕ e₀) ↔
      ∃ e₀ : OpenPartialHomeomorph M H,
        e₀ ∈ ChartedSpace.atlas (H := H) (M := M) ∧ h.toOpenPartialHomeomorph ≫ₕ e₀ = e
    exact ⟨fun ⟨e₀, he₀, he⟩ => ⟨e₀, he₀, he.symm⟩,
      fun ⟨e₀, he₀, he⟩ => ⟨e₀, he₀, he.symm⟩⟩
  · rfl

theorem isManifoldOfHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} {M' : Type*} [TopologicalSpace M'] (h : M' ≃ₜ M)
    [IsManifold I n M] :
    @IsManifold 𝕜 _ E _ _ H _ I n M' _ (chartedSpaceOfHomeomorph h) := by
  rw [chartedSpaceOfHomeomorph_eq_pullback]
  exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := I) (n := n) h

theorem contMDiff_homeomorph_of_chartedSpaceOfHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {X' : Type*} [TopologicalSpace X']
    (h : X' ≃ₜ X) (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) [IsManifold I n X] :
    @ContMDiff 𝕜 _ E _ _ H _ I X' _ (chartedSpaceOfHomeomorph h) E _ _ H _ I X _ _ n h := by
  rw [chartedSpaceOfHomeomorph_eq_pullback]
  exact DifferentialGeometry.Manifold.Homeomorph.contMDiff_pullback (I := I) (n := n) h

theorem contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph {𝕜 : Type*}
    [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {X' : Type*} [TopologicalSpace X']
    (h : X' ≃ₜ X) (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) [IsManifold I n X] :
    @ContMDiff 𝕜 _ E _ _ H _ I X _ _ E _ _ H _ I X' _ (chartedSpaceOfHomeomorph h) n h.symm := by
  rw [chartedSpaceOfHomeomorph_eq_pullback]
  exact DifferentialGeometry.Manifold.Homeomorph.contMDiff_symm_pullback (I := I) (n := n) h

theorem contMDiff_of_contMDiff_comp_homeo {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {X' : Type*} [TopologicalSpace X']
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    (h : X' ≃ₜ X) (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) [IsManifold I n X]
    (f : M → X') (hf : ContMDiff I' I n (fun m : M => h (f m))) :
    @ContMDiff 𝕜 _ E' _ _ H' _ I' M _ _ E _ _ H _ I X' _ (chartedSpaceOfHomeomorph h) n f := by
  classical
  let : ChartedSpace H X' := chartedSpaceOfHomeomorph h
  let : IsManifold I n X' := isManifoldOfHomeomorph I h
  have hsymm : ContMDiff I I n (h.symm) :=
    contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph (𝕜 := 𝕜) h I n
  have hfun : f = fun m : M => h.symm (h (f m)) := by
    funext m
    exact (h.left_inv (f m)).symm
  rw [hfun]
  exact hsymm.comp hf

end

end DifferentialGeometry.Topology.Handle
