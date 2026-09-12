import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open Set Filter
open OpenPartialHomeomorph

namespace DifferentialGeometry.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {n : ℕ∞ω}
variable {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M'] [ChartedSpace H M]

theorem atlas_homeomorphChartedSpace (f : M ≃ₜ M') :
    @atlas H _ M' _ (f.chartedSpace) =
      Set.range (@chartAt H _ M' _ (f.chartedSpace)) := rfl

theorem chartAt_homeomorphChartedSpace (f : M ≃ₜ M') (q : M') :
    @chartAt H _ M' _ (f.chartedSpace) q =
      (f.isLocalHomeomorph.localInverseAt (f.surjective.hasRightInverse.choose q)).trans
        (chartAt H (f.surjective.hasRightInverse.choose q)) := rfl

theorem isManifold_homeomorphChartedSpace (f : M ≃ₜ M') [IsManifold I n M] :
    @IsManifold 𝕜 _ E _ _ H _ I n M' _ (f.chartedSpace) := by
  refine @isManifold_of_contDiffOn 𝕜 _ E _ _ H _ I n M' _ (f.chartedSpace) ?_
  intro e e' he he'
  rw [atlas_homeomorphChartedSpace (H := H) f] at he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  rw [chartAt_homeomorphChartedSpace (H := H) f q, chartAt_homeomorphChartedSpace (H := H) f q']
  set g := f.surjective.hasRightInverse.choose with hgdef
  set A := f.isLocalHomeomorph.localInverseAt (g q) with hA
  set A' := f.isLocalHomeomorph.localInverseAt (g q') with hA'
  set c := chartAt H (g q) with hc
  set c' := chartAt H (g q') with hc'
  have hAs : ⇑(A.symm) = (f : M → M') := by
    rw [hA]; exact IsLocalHomeomorph.localInverseAt_symm f.isLocalHomeomorph (g q)
  have hA's : ⇑(A'.symm) = (f : M → M') := by
    rw [hA']; exact IsLocalHomeomorph.localInverseAt_symm f.isLocalHomeomorph (g q')
  have hB : ∀ y, y ∈ (A.symm ≫ₕ A').source → A' (A.symm y) = y := by
    intro y hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    have hy2 : f y ∈ A'.source := by rw [← hAs]; exact hy.2
    rw [hAs]
    refine f.injective ?_
    have h := A'.left_inv hy2
    rwa [hA's] at h
  have hsrc : ∀ w, w ∈ ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')).source →
      w ∈ c.symm.source ∧ c.symm w ∈ A.symm.source ∧
        A.symm (c.symm w) ∈ A'.source ∧ A' (A.symm (c.symm w)) ∈ c'.source := by
    intro w hw
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] at hw
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hw
    simp only [coe_trans, Function.comp_apply, Set.mem_inter_iff, Set.mem_preimage] at hw
    exact ⟨hw.1.1, hw.1.2, hw.2.1, hw.2.2⟩
  have hsub : ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')).source ⊆ (c.symm ≫ₕ c').source := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hsrc w hw
    have hmem : c.symm w ∈ (A.symm ≫ₕ A').source := by
      rw [OpenPartialHomeomorph.trans_source]; exact ⟨h2, h3⟩
    have hb := hB (c.symm w) hmem
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨h1, by rw [← hb]; exact h4⟩
  have heq : ∀ w ∈ ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')).source,
      ((A ≫ₕ c).symm ≫ₕ (A' ≫ₕ c')) w = (c.symm ≫ₕ c') w := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hsrc w hw
    have hmem : c.symm w ∈ (A.symm ≫ₕ A').source := by
      rw [OpenPartialHomeomorph.trans_source]; exact ⟨h2, h3⟩
    have hb := hB (c.symm w) hmem
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    simp only [OpenPartialHomeomorph.trans_apply]
    rw [hb]
  have hY : (c.symm ≫ₕ c') ∈ contDiffGroupoid n I :=
    StructureGroupoid.compatible (contDiffGroupoid n I)
      (chart_mem_atlas H (g q)) (chart_mem_atlas H (g q'))
  refine (mem_groupoid_of_pregroupoid.mp hY).1.congr_mono (fun z hz => ?_) (fun z hz => ?_)
  · simp only [Function.comp_apply]
    exact congrArg (⇑I) (heq _ hz.1)
  · exact ⟨hsub hz.1, hz.2⟩
section HomeomorphChartedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {M M' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M']
variable {n : ℕ∞ω}

theorem contMDiff_homeomorphChartedSpace (I : ModelWithCorners 𝕜 E H) {n : ℕ∞ω} [IsManifold I n M]
    (f : M ≃ₜ M') :
    let _ := (f.chartedSpace : ChartedSpace H M')
    let _ := isManifold_homeomorphChartedSpace (I := I) (n := n) f
    ContMDiff I I n f := by
  let _ := (f.chartedSpace : ChartedSpace H M')
  let _ := isManifold_homeomorphChartedSpace (I := I) (n := n) f
  dsimp only []
  let g' := f.surjective.hasRightInverse.choose
  have hg' : Function.RightInverse g' f := f.surjective.hasRightInverse.choose_spec
  have hchart : ∀ y, chartAt H y =
      (f.isLocalHomeomorph.localInverseAt (g' y)).trans (chartAt H (g' y)) := fun y => rfl
  rw [contMDiff_iff_target]
  refine ⟨f.continuous, fun y => ?_⟩
  have hinv : ∀ x, f x ∈ (f.isLocalHomeomorph.localInverseAt (g' y)).source →
      (f.isLocalHomeomorph.localInverseAt (g' y)) (f x) = x := fun x hx =>
    f.injective (f.isLocalHomeomorph.apply_localInverseAt_of_mem hx)
  have hsrc : ∀ x, x ∈ f ⁻¹' (extChartAt I y).source →
      f x ∈ (f.isLocalHomeomorph.localInverseAt (g' y)).source ∧
        (f.isLocalHomeomorph.localInverseAt (g' y)) (f x) ∈ (chartAt H (g' y)).source := by
    intro x hx
    rw [mem_preimage, extChartAt_source, hchart y, OpenPartialHomeomorph.trans_source,
      mem_inter_iff, mem_preimage] at hx
    exact hx
  have hsub : f ⁻¹' (extChartAt I y).source ⊆ (chartAt H (g' y)).source := fun x hx => by
    obtain ⟨h1, h2⟩ := hsrc x hx
    rw [← hinv x h1]
    exact h2
  refine (contMDiffOn_extChartAt (I := I) (x := g' y)).mono hsub |>.congr fun x hx => ?_
  rw [Function.comp_apply, extChartAt_coe, extChartAt_coe, Function.comp_apply, hchart y,
    OpenPartialHomeomorph.coe_trans, Function.comp_apply, hinv x (hsrc x hx).1]
  rfl

theorem bijective_mfderiv_homeomorphChartedSpace (I : ModelWithCorners 𝕜 E H)
    [IsManifold I ∞ M] (f : M ≃ₜ M') :
    let _ := (f.chartedSpace : ChartedSpace H M')
    let _ := isManifold_homeomorphChartedSpace (I := I) (n := ∞) f
    ∀ x, Function.Bijective (mfderiv I I f x) := by
  let _ := (f.chartedSpace : ChartedSpace H M')
  let _ := isManifold_homeomorphChartedSpace (I := I) (n := ∞) f
  dsimp only []
  have hf : ContMDiff I I ∞ f := contMDiff_homeomorphChartedSpace I f
  intro x
  let g' := f.surjective.hasRightInverse.choose
  have hg' : Function.RightInverse g' f := f.surjective.hasRightInverse.choose_spec
  have hg'x : g' (f x) = x := f.injective (hg' (f x))
  have hchart : ∀ y, chartAt H y =
      (f.isLocalHomeomorph.localInverseAt (g' y)).trans (chartAt H (g' y)) := fun y => rfl
  have hinv : ∀ y z, f z ∈ (f.isLocalHomeomorph.localInverseAt (g' y)).source →
      (f.isLocalHomeomorph.localInverseAt (g' y)) (f z) = z := fun y z hz =>
    f.injective (f.isLocalHomeomorph.apply_localInverseAt_of_mem hz)
  have heq : (fun z : M => chartAt H (f x) (f z)) =ᶠ[𝓝 x] (fun z : M => chartAt H x z) := by
    have hnb : (chartAt H (f x)).source ∈ 𝓝 (f x) :=
      (chartAt H (f x)).open_source.mem_nhds (mem_chart_source H (f x))
    filter_upwards [f.continuous.continuousAt.preimage_mem_nhds hnb] with z hz
    have hz2 : f z ∈ (f.isLocalHomeomorph.localInverseAt (g' (f x))).source := by
      have h := hz
      rw [hchart (f x), OpenPartialHomeomorph.trans_source] at h
      exact h.1
    rw [hchart (f x), OpenPartialHomeomorph.trans_apply, hinv (f x) z hz2, hg'x]
  have hA : Function.Bijective (mfderiv I I (chartAt H (f x)) (f x)) :=
    ((mdifferentiable_chart (I := I) (x := f x)).mfderiv_bijective (mem_chart_source H (f x)))
  have hB : Function.Bijective (mfderiv I I (chartAt H x) x) :=
    ((mdifferentiable_chart (I := I) (x := x)).mfderiv_bijective (mem_chart_source H x))
  have hchain : mfderiv I I (fun z : M => chartAt H (f x) (f z)) x
      = (mfderiv I I (chartAt H (f x)) (f x)).comp (mfderiv I I f x) := by
    rw [← mfderiv_comp (I := I) (I' := I) (I'' := I) (f := f) (g := chartAt H (f x)) x
      ((mdifferentiable_chart (I := I) (x := f x)).mdifferentiableAt (mem_chart_source H (f x)))
      (hf.mdifferentiableAt (by decide))]
    rfl
  have hkey : mfderiv I I (chartAt H x) x
      = (mfderiv I I (chartAt H (f x)) (f x)).comp (mfderiv I I f x) := by
    rw [← hchain, heq.mfderiv_eq]
  refine ⟨fun v w hvw => ?_, fun w => ?_⟩
  · have hsub : (mfderiv I I f x) (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h0 : mfderiv I I (chartAt H x) x (v - w) = 0 := by
      rw [hkey]
      exact (congrArg (mfderiv I I (chartAt H (f x)) (f x)) hsub).trans (map_zero _)
    exact sub_eq_zero.mp (hB.injective (by rw [h0, map_zero]))
  · obtain ⟨v, hv⟩ := hB.surjective (mfderiv I I (chartAt H (f x)) (f x) w)
    refine ⟨v, ?_⟩
    refine hA.injective ?_
    rw [← ContinuousLinearMap.comp_apply, ← hkey]
    exact hv

end HomeomorphChartedSpace
end DifferentialGeometry.Manifold

end
