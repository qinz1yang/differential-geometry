import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Implicit

/-!
A continuously differentiable submersion between boundaryless finite-dimensional manifolds
preserves neighborhood filters and is open on every open submersion domain.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

variable {E E' H H' M M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [I.Boundaryless] [I'.Boundaryless]

private def submersionOpenChart (J : ModelWithCorners ℝ E H) [J.Boundaryless] (x : M) :
    OpenPartialHomeomorph M E where
  toPartialEquiv := extChartAt J x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x

theorem map_nhds_eq_of_mfderiv_surjective_at {f : M → M'} {x : M}
    (hf : ContMDiffAt I I' 1 f x) (hd : Surjective (mfderiv I I' f x)) :
    map f (𝓝 x) = 𝓝 (f x) := by
  let cM := submersionOpenChart I x
  let cN := submersionOpenChart I' (f x)
  let g : E → E' := cN ∘ f ∘ cM.symm
  let L : E →L[ℝ] E' := mfderiv I I' f x
  have hstrict : HasStrictFDerivAt g L (cM x) := by
    have hgc : ContDiffAt ℝ 1 g (cM x) := by
      have hh := (contMDiffAt_iff.mp hf).2
      rw [I.range_eq_univ] at hh
      exact hh
    have hgL : HasFDerivAt g L (cM x) := by
      have hh := (hf.mdifferentiableAt (by norm_num)).hasMFDerivAt.2
      exact hh.hasFDerivAt (by rw [I.range_eq_univ]; exact univ_mem)
    exact hgc.hasStrictFDerivAt' hgL (by norm_num)
  have hrange : L.range = ⊤ := LinearMap.range_eq_top.mpr hd
  have hgmap := hstrict.map_nhds_eq_of_surj hrange
  have hxM : x ∈ cM.source := mem_extChartAt_source x
  have hxN : f x ∈ cN.source := mem_extChartAt_source (f x)
  have hfx : ∀ᶠ y in 𝓝 x, f y ∈ cN.source :=
    hf.continuousAt.preimage_mem_nhds (cN.open_source.mem_nhds hxN)
  have heq : f =ᶠ[𝓝 x] cN.symm ∘ cN ∘ f := by
    filter_upwards [hfx] with y hy
    exact (cN.left_inv hy).symm
  have hgm : g (cM x) = cN (f x) := by
    change cN (f (cM.symm (cM x))) = cN (f x)
    rw [cM.left_inv hxM]
  calc
    map f (𝓝 x) = map (cN.symm ∘ cN ∘ f) (𝓝 x) := map_congr heq
    _ = map cN.symm (map (cN ∘ f) (𝓝 x)) := (map_map).symm
    _ = map cN.symm (map g (𝓝 (cM x))) := by
      rw [← cM.symm_map_nhds_eq hxM, map_map]
      rfl
    _ = map cN.symm (𝓝 (cN (f x))) := by rw [hgmap, hgm]
    _ = 𝓝 (f x) := cN.symm_map_nhds_eq hxN

theorem isOpenMap_of_mfderiv_surjective {f : M → M'} {U : Set M}
    (hf : ContMDiffOn I I' 1 f U) (hU : IsOpen U)
    (hd : ∀ x ∈ U, Surjective (mfderiv I I' f x)) :
    IsOpenMap (U.domRestrict f) ∧ ∀ x ∈ U, map f (𝓝 x) = 𝓝 (f x) := by
  have hm : ∀ x ∈ U, map f (𝓝 x) = 𝓝 (f x) := fun x hx =>
    map_nhds_eq_of_mfderiv_surjective_at (hf.contMDiffAt (hU.mem_nhds hx)) (hd x hx)
  refine ⟨isOpenMap_iff_nhds_le.mpr ?_, hm⟩
  intro x
  have hs := map_nhds_subtype_coe_eq_nhds x.property (hU.mem_nhds x.property)
  change 𝓝 (f x.val) ≤ map (f ∘ Subtype.val) (𝓝 x)
  rw [← map_map, hs, hm x.val x.property]

theorem exists_localSection_of_mfderiv_surjective {f : M → M'} {U : Set M}
    (hf : ContMDiffOn I I' 1 f U) (hU : IsOpen U)
    {x : M} (hx : x ∈ U) (hd : Surjective (mfderiv I I' f x)) :
    ∃ (V : TopologicalSpace.Opens M') (hV : f x ∈ V) (s : C(V, M)),
      s ⟨f x, hV⟩ = x ∧ ∀ y : V, s y ∈ U ∧ f (s y) = y.val := by
  let cM := submersionOpenChart I x
  let cN := submersionOpenChart I' (f x)
  let g : E → E' := cN ∘ f ∘ cM.symm
  let L : E →L[ℝ] E' := mfderiv I I' f x
  have hfa := hf.contMDiffAt (hU.mem_nhds hx)
  have hstrict : HasStrictFDerivAt g L (cM x) := by
    have hgc : ContDiffAt ℝ 1 g (cM x) := by
      have hh := (contMDiffAt_iff.mp hfa).2
      rw [I.range_eq_univ] at hh
      exact hh
    have hgL : HasFDerivAt g L (cM x) := by
      have hh := (hfa.mdifferentiableAt (by norm_num)).hasMFDerivAt.2
      exact hh.hasFDerivAt (by rw [I.range_eq_univ]; exact univ_mem)
    exact hgc.hasStrictFDerivAt' hgL (by norm_num)
  have hrange : L.range = ⊤ := LinearMap.range_eq_top.mpr hd
  let e := hstrict.implicitToOpenPartialHomeomorph g L hrange
  have hxM : x ∈ cM.source := mem_extChartAt_source x
  have hxN : f x ∈ cN.source := mem_extChartAt_source (f x)
  have hgx : g (cM x) = cN (f x) := by
    change cN (f (cM.symm (cM x))) = cN (f x)
    rw [cM.left_inv hxM]
  have hea : e (cM x) = (cN (f x), 0) := by
    exact (hstrict.implicitToOpenPartialHomeomorph_self hrange).trans
      (congrArg (fun y => (y, (0 : L.ker))) hgx)
  have hxe : cM x ∈ e.source := hstrict.mem_implicitToOpenPartialHomeomorph_source hrange
  let A := cM.target ∩ cM.symm ⁻¹' (U ∩ f ⁻¹' cN.source)
  have hA : IsOpen A := cM.isOpen_inter_preimage_symm
    (hf.continuousOn.isOpen_inter_preimage hU cN.open_source)
  let B := e.target ∩ e.symm ⁻¹' A
  have hB : IsOpen B := e.isOpen_inter_preimage_symm hA
  let Vset := cN.source ∩ cN ⁻¹' ((fun y : E' => (y, (0 : L.ker))) ⁻¹' B)
  have hVo : IsOpen Vset := cN.isOpen_inter_preimage
    (hB.preimage (continuous_id.prodMk continuous_const))
  let V : TopologicalSpace.Opens M' := ⟨Vset, hVo⟩
  have hV : f x ∈ V := by
    refine ⟨hxN, ?_⟩
    have hpoint : e.symm (cN (f x), 0) = cM x := by
      rw [← hea, e.left_inv hxe]
    refine ⟨?_, ?_⟩
    · change (cN (f x), 0) ∈ e.target
      rw [← hea]
      exact e.map_source hxe
    change e.symm (cN (f x), 0) ∈ cM.target ∩ cM.symm ⁻¹' (U ∩ f ⁻¹' cN.source)
    rw [hpoint]
    refine ⟨cM.map_source hxM, ?_⟩
    change cM.symm (cM x) ∈ U ∩ f ⁻¹' cN.source
    rw [cM.left_inv hxM]
    exact ⟨hx, hxN⟩
  let s0 : M' → M := fun y => cM.symm (e.symm (cN y, 0))
  have hc : ContinuousOn (fun y : M' => (cN y, (0 : L.ker))) Vset :=
    (cN.continuousOn.mono inter_subset_left).prodMk continuousOn_const
  have he : ContinuousOn (fun y : M' => e.symm (cN y, 0)) Vset :=
    e.symm.continuousOn.comp hc (fun y hy => hy.2.1)
  have hsc : ContinuousOn s0 Vset :=
    cM.symm.continuousOn.comp he (fun y hy => hy.2.2.1)
  let s : C(V, M) := ⟨Vset.domRestrict s0, continuousOn_iff_continuous_domRestrict.mp hsc⟩
  refine ⟨V, hV, s, ?_, ?_⟩
  · change cM.symm (e.symm (cN (f x), 0)) = x
    rw [← hea, e.left_inv hxe, cM.left_inv hxM]
  · intro y
    refine ⟨y.property.2.2.2.1, ?_⟩
    have hp := congrArg Prod.fst (e.right_inv y.property.2.1)
    change g (e.symm (cN y.val, 0)) = cN y.val at hp
    have hsrc : f (s y) ∈ cN.source := y.property.2.2.2.2
    calc
      f (s y) = cN.symm (cN (f (s y))) := (cN.left_inv hsrc).symm
      _ = cN.symm (cN y.val) := congrArg cN.symm hp
      _ = y.val := cN.left_inv y.property.1

end DifferentialGeometry.Topology
