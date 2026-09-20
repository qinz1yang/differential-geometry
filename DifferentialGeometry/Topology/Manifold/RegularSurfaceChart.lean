/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import DifferentialGeometry.Topology.Manifold.RegularZero.Coordinates
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! Surface charts whose imaginary coordinate is a prescribed regular function. -/

noncomputable section
open Set Filter Function Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

private def heightPlaneEquiv : (ℝ × (Fin 1 → ℝ)) ≃L[ℝ] ℂ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => ⟨z.2 0, z.1⟩
      invFun := fun z => (z.im, fun _ => z.re)
      left_inv := fun z => Prod.ext rfl (funext fun i => by rw [Subsingleton.elim i 0])
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => by apply Complex.ext <;> simp }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_level_chart_in_coordinates (hdim : Module.finrank ℝ F = 2)
    (c : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hxc : x ∈ c.source)
    (hregular : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {O : Set M} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ (ℓ : F →L[ℝ] ℝ) (r : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, ℂ) F ℂ ∞),
      c x ∈ r.source ∧ r.source ⊆ c.target ∩ c.symm ⁻¹' O ∧
      (∀ z ∈ r.source, (r z).im = f (c.symm z)) ∧
      (∀ z, (r z).re = ℓ (z - c x)) ∧ (r (c x)).re = 0 ∧
      x ∈ (c.trans r).source ∧ (c.trans r).source ⊆ O ∧
      ∀ y ∈ (c.trans r).source, ((c.trans r) y).im = f y := by
  let g : F → ℝ := f ∘ c.symm
  have hg : ContDiffOn ℝ ∞ g c.target :=
    (hf.comp_contMDiffOn c.symm.contMDiffOn).contDiffOn
  have hcx : c x ∈ c.target := c.map_source hxc
  have hgcx := hg.contDiffAt (c.open_target.mem_nhds hcx)
  have hne : fderiv ℝ g (c x) ≠ 0 := by
    intro hz
    have he : g ∘ c =ᶠ[𝓝 x] f := by
      filter_upwards [c.open_source.mem_nhds hxc] with y hy
      exact congrArg f (c.left_inv hy)
    have hcder := mfderiv_comp x (hgcx.contMDiffAt.mdifferentiableAt (by simp))
      (c.mdifferentiableAt (by simp) hxc)
    have hz' : (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) g (c x) : F →L[ℝ] ℝ) = 0 :=
      mfderiv_eq_fderiv.trans hz
    have hcder0 : (mfderiv I 𝓘(ℝ, ℝ) (g ∘ c) x : E →L[ℝ] ℝ) = 0 := by
      calc
        _ = (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) g (c x)).comp
            (mfderiv I 𝓘(ℝ, F) c x) := hcder
        _ = 0 := by rw [hz']; rfl
    exact hregular (he.mfderiv_eq.symm.trans hcder0)
  have hsurj : Surjective (fderiv ℝ g (c x)) := by
    apply LinearMap.surjective
    intro h
    apply hne
    ext z
    exact congrArg (fun L : F →ₗ[ℝ] ℝ => L z) h
  let W := c.target ∩ c.symm ⁻¹' O
  have hW : IsOpen W :=
    c.symm.contMDiffOn.continuousOn.isOpen_inter_preimage c.open_target hO
  have hxW : c x ∈ W := by
    refine ⟨hcx, ?_⟩
    change c.symm (c x) ∈ O
    have hl : c.symm (c x) = x := c.left_inv hxc
    rw [hl]
    exact hxO
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let L := fderiv ℝ g (c x)
  have hker := L.ker_closedComplemented_of_finiteDimensional_range
  let P := Classical.choose hker
  let data := (hgcx.hasStrictFDerivAt (by simp)).implicitFunctionDataOfComplemented g L
    (LinearMap.range_eq_top.mpr hsurj) hker
  have hdata : ContDiffOn ℝ ∞ data.prodFun W :=
    (hg.mono inter_subset_left).prodMk
      ((P.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  obtain ⟨e, hxe, heW, he, hei, heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      hdata hW hxW data.hasStrictFDerivAt.hasFDerivAt
  let e' : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, ℝ × L.ker) F (ℝ × L.ker) ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := he.contMDiffOn
      contMDiffOn_invFun := hei.contMDiffOn }
  have hk : Module.finrank ℝ L.ker = 1 := by
    have hh := L.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, _root_.finrank_top, Module.finrank_self, hdim] at hh
    omega
  let k : L.ker ≃L[ℝ] (Fin 1 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun, hk])
  let Q := ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr k).trans heightPlaneEquiv
  let r := e'.trans Q.toDiffeomorph.toPartialDiffeomorph
  let π : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let ℓ : F →L[ℝ] ℝ := π.comp ((k : L.ker →L[ℝ] (Fin 1 → ℝ)).comp P)
  have hr (z : F) : (r z).im = g z := by
    change (e z).1 = g z
    rw [heq]
    rfl
  have hreal (z : F) : (r z).re = ℓ (z - c x) := by
    change k (e z).2 0 = ℓ (z - c x)
    rw [heq]
    rfl
  have hzr : (r (c x)).re = 0 := by rw [hreal, sub_self, map_zero]
  have hrs : r.source ⊆ W := fun _ hz => heW hz.1
  refine ⟨ℓ, r, ⟨hxe, mem_univ _⟩, hrs, fun z _ => hr z, hreal, hzr,
    ⟨hxc, hxe, mem_univ _⟩, ?_, ?_⟩
  · intro y hy
    have hl : c.symm (c y) = y := c.left_inv hy.1
    have hh : c.symm (c y) ∈ O := (hrs hy.2).2
    exact hl ▸ hh
  · intro y hy
    change (r (c y)).im = f y
    rw [hr]
    exact congrArg f (c.left_inv hy.1)

end DifferentialGeometry.Topology.Manifold
