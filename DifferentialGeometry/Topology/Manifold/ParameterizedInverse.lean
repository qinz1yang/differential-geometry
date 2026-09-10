import DifferentialGeometry.Analysis.Calculus.Inverse.ParameterizedInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_localInverse_preserving_parameter
    {h : M × ℝ → ℝ} {U : Set (M × ℝ)} {p : M × ℝ}
    (hh : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ h U) (hU : IsOpen U) (hp : p ∈ U)
    (hvertical : deriv (fun r ↦ h (p.1, r)) p.2 ≠ 0) :
    ∃ e : OpenPartialHomeomorph (M × ℝ) (M × ℝ),
      p ∈ e.source ∧ e.source ⊆ U ∧
      ContMDiffOn (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞ e e.source ∧
      ContMDiffOn (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞ e.symm e.target ∧
      (∀ z ∈ e.source, e z = (z.1, h z)) ∧
      ∀ z ∈ e.target, (e.symm z).1 = z.1 ∧ h (e.symm z) = z.2 := by
  let c : OpenPartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I p.1
      open_source := isOpen_extChartAt_source p.1
      open_target := isOpen_extChartAt_target p.1
      continuousOn_toFun := continuousOn_extChartAt p.1
      continuousOn_invFun := continuousOn_extChartAt_symm p.1 }
  let C := c.prod (OpenPartialHomeomorph.refl ℝ)
  have hpC : p ∈ C.source := ⟨mem_extChartAt_source p.1, mem_univ _⟩
  have hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source :=
    (contMDiffOn_extChartAt (I := I) (x := p.1)).mono (fun z hz ↦ by
      have hz' : z ∈ (extChartAt I p.1).source := hz
      simpa only [extChartAt_source] using hz')
  have hC : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) ∞ C C.source := by
    have hc' : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ (fun z ↦ c z.1) C.source :=
      hc.comp contMDiffOn_fst (fun z hz ↦ hz.1)
    exact hc'.prodMk_space contMDiffOn_snd
  have hCinv : ContMDiffOn 𝓘(ℝ, E × ℝ) (I.prod 𝓘(ℝ)) ∞ C.symm C.target := by
    have hc' : ContMDiffOn 𝓘(ℝ, E × ℝ) I ∞ (fun z ↦ c.symm z.1) C.target :=
      (contMDiffOn_extChartAt_symm (I := I) p.1).comp contDiff_fst.contMDiff.contMDiffOn
        (fun z hz ↦ hz.1)
    exact hc'.prodMk contDiff_snd.contMDiff.contMDiffOn
  let D : PartialDiffeomorph (I.prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) (M × ℝ) (E × ℝ) ∞ :=
    { toPartialEquiv := C.toPartialEquiv
      open_source := C.open_source
      open_target := C.open_target
      contMDiffOn_toFun := hC
      contMDiffOn_invFun := hCinv }
  let V := C.target ∩ C.symm ⁻¹' U
  have hV : IsOpen V := C.isOpen_inter_preimage_symm hU
  have hpV : C p ∈ V := ⟨C.map_source hpC, by
    change C.symm (C p) ∈ U
    rwa [C.left_inv hpC]⟩
  let f : E × ℝ → ℝ := h ∘ C.symm
  have hf : ContDiffOn ℝ ∞ f V :=
    (hh.comp (hCinv.mono inter_subset_left) (fun z hz ↦ hz.2)).contDiffOn
  have hdf := ((hf.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)).hasFDerivAt
  have hscalar : HasDerivAt (fun r ↦ h (p.1, r)) (fderiv ℝ f (C p) (0, 1)) p.2 := by
    have hd := hdf.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 (c p.1)).prodMk (hasDerivAt_id p.2))
    change HasDerivAt (fun r ↦ h (c.symm (c p.1), r)) _ p.2 at hd
    simpa only [c.left_inv hpC.1] using hd
  have hfv : fderiv ℝ f (C p) (0, 1) ≠ 0 := by
    rwa [← hscalar.deriv]
  obtain ⟨e, hpe, heV, he, heinv, heq, _⟩ :=
    Poincare.Analysis.exists_localInverse_preserving_parameter hf hV hpV hfv
  let A : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := he.contMDiffOn
      contMDiffOn_invFun := heinv.contMDiffOn }
  let Φ := (D.trans A).trans D.symm
  have hΦp : p ∈ Φ.source := by
    refine ⟨⟨hpC, hpe⟩, ?_⟩
    change e (C p) ∈ C.target
    rw [heq]
    exact ⟨c.map_source hpC.1, mem_univ _⟩
  have hΦU : Φ.source ⊆ U := by
    intro z hz
    have hu : C.symm (C z) ∈ U := (heV hz.1.2).2
    rwa [C.left_inv hz.1.1] at hu
  have hΦeq : ∀ z ∈ Φ.source, Φ z = (z.1, h z) := by
    intro z hz
    change C.symm (e (C z)) = (z.1, h z)
    rw [heq]
    change (c.symm (c z.1), h (C.symm (C z))) = (z.1, h z)
    rw [C.left_inv hz.1.1, c.left_inv hz.1.1.1]
  refine ⟨Φ.toOpenPartialHomeomorph, hΦp, hΦU, Φ.contMDiffOn, Φ.symm.contMDiffOn, hΦeq, ?_⟩
  intro z hz
  have h := (hΦeq (Φ.symm z) (Φ.toPartialEquiv.map_target hz)).symm.trans
    (Φ.toPartialEquiv.right_inv hz)
  exact Prod.mk.inj h

end Poincare.Topology.Manifold
