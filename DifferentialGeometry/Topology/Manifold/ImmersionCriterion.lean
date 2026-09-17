import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

open Set Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem isImmersionAtOfComplement_of_hasFDerivAt
    {𝕜 : Type*} [RCLike 𝕜]
    {E C F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [CompleteSpace C]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ∞ω} {f : E → F} {U : Set E} {x : E} {L : E →L[𝕜] F}
    (hn : n ≠ 0) (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn 𝕜 n f U)
    (hdf : HasFDerivAt f L x) (A : (E × C) ≃L[𝕜] F)
    (hA : ∀ z, A (z, 0) = L z) :
    IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, F) n f x := by
  let G : E × C → F := fun p => f p.1 + A (0, p.2)
  have hG : ContDiffOn 𝕜 n G (Prod.fst ⁻¹' U) :=
    (hf.comp contDiff_fst.contDiffOn (fun _ h => h)).add
      (A.contDiff.comp (contDiff_const.prodMk contDiff_snd)).contDiffOn
  have hdG : HasFDerivAt G (A : E × C →L[𝕜] F) (x, 0) := by
    let B : E × C →L[𝕜] F := A.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr 𝕜 E C).comp (ContinuousLinearMap.snd 𝕜 E C))
    have h : HasFDerivAt G (L.comp (ContinuousLinearMap.fst 𝕜 E C) + B) (x, 0) :=
      (hdf.comp (x, (0 : C)) hasFDerivAt_fst).add B.hasFDerivAt
    have hL : L.comp (ContinuousLinearMap.fst 𝕜 E C) + B = A := by
      apply ContinuousLinearMap.ext
      intro p
      change L p.1 + A (0, p.2) = A p
      rw [← hA, ← map_add]
      congr 1
      ext <;> simp
    rwa [hL] at h
  obtain ⟨e, hxe, _, he, heinv, heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero
      hn hG (hU.preimage continuous_fst) hx hdG
  let V : Set E := (fun z : E => (z, (0 : C))) ⁻¹' e.source
  have hV : IsOpen V := e.open_source.preimage (continuous_id.prodMk continuous_const)
  let α : OpenPartialHomeomorph E E := (OpenPartialHomeomorph.refl E).restr V
  let β : OpenPartialHomeomorph F F := e.symm.trans A.toHomeomorph.toOpenPartialHomeomorph
  have hαsource : α.source = V := by simp [α, hV.interior_eq]
  have hαtarget : α.target = V := by simp [α, hV.interior_eq]
  have hαmax : α ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n E := by
    apply α.mem_maximalAtlas_of_contMDiffOn
    · exact contMDiff_id.contMDiffOn
    · exact contMDiff_id.contMDiffOn
  have hβmax : β ∈ IsManifold.maximalAtlas 𝓘(𝕜, F) n F := by
    apply β.mem_maximalAtlas_of_contMDiffOn
    · exact (A.contDiff.comp_contDiffOn (heinv.mono inter_subset_left)).contMDiffOn
    · exact (he.comp A.symm.contDiff.contDiffOn (fun _ h => h.2)).contMDiffOn
  have hGzero (z : E) : e (z, (0 : C)) = f z := by
    rw [heq]
    simp [G]
  have hmap (z : E) (hz : z ∈ α.source) : f z ∈ β.source := by
    rw [hαsource] at hz
    exact ⟨hGzero z ▸ e.map_source hz, mem_univ _⟩
  refine IsImmersionAtOfComplement.mk_of_charts A α β
    (hαsource ▸ hxe) (hmap x (hαsource ▸ hxe)) hαmax hβmax hmap ?_
  intro z hz
  have hzV : z ∈ V := by simpa [hαtarget] using hz
  change A (e.symm (f z)) = A (z, 0)
  rw [← hGzero z, e.left_inv hzV]

theorem isImmersionAt_of_injective_hasFDerivAt
    {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {n : ℕ∞ω} {f : E → F} {U : Set E} {x : E} {L : E →L[𝕜] F}
    (hn : n ≠ 0) (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn 𝕜 n f U)
    (hdf : HasFDerivAt f L x) (hinj : Function.Injective L) :
    IsImmersionAt 𝓘(𝕜, E) 𝓘(𝕜, F) n f x := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl L.range
  let : CompleteSpace C := FiniteDimensional.complete 𝕜 C
  let A : (E × C) ≃L[𝕜] F :=
    ((LinearEquiv.prodCongr (LinearEquiv.ofInjective L.toLinearMap hinj)
      (LinearEquiv.refl 𝕜 C)).trans (L.range.prodEquivOfIsCompl C hC)).toContinuousLinearEquiv
  apply (isImmersionAtOfComplement_of_hasFDerivAt hn hU hx hf hdf A ?_).isImmersionAt
  intro z
  change L z + (0 : F) = L z
  exact add_zero _

private noncomputable def modelInverse
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] (n : ℕ∞ω) :
    PartialDiffeomorph 𝓘(𝕜, E) I E H n where
  toPartialEquiv := I.toHomeomorph.symm.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    change ContMDiffOn 𝓘(𝕜, E) I n I.symm univ
    simpa only [I.range_eq_univ] using I.contMDiffOn_symm (n := n)
  contMDiffOn_invFun := I.contMDiff.contMDiffOn

theorem isImmersionAt_of_injective_mfderiv
    {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {H G M N : Type*} [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
    [I.Boundaryless] [J.Boundaryless] {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
    {f : M → N} (hn : n ≠ 0) (hf : ContMDiff I J n f) (x : M)
    (hinj : Function.Injective (mfderiv I J f x)) : IsImmersionAt I J n f x := by
  let c := extChartAtPartialDiffeomorph I n x
  let d := extChartAtPartialDiffeomorph J n (f x)
  let g : E → F := d ∘ f ∘ c.symm
  let U : Set E := c.target ∩ c.symm ⁻¹' (f ⁻¹' d.source)
  have hU : IsOpen U := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm
    (d.open_source.preimage hf.continuous)
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hfd : f x ∈ d.source := mem_extChartAt_source (f x)
  have hcx : c.symm.toPartialEquiv (c.toPartialEquiv x) = x := c.left_inv hxc
  have hxU : c x ∈ U := by
    refine ⟨c.map_source hxc, ?_⟩
    change f (c.symm (c x)) ∈ d.source
    rw [hcx]
    exact hfd
  have hg : ContDiffOn 𝕜 n g U :=
    (d.contMDiffOn.comp
      (hf.comp_contMDiffOn (c.symm.contMDiffOn.mono inter_subset_left))
      (fun _ h => h.2)).contDiffOn
  have hdg : HasFDerivAt g (mfderiv I J f x) (c x) := by
    have h := (hf.mdifferentiableAt hn (x := x)).hasMFDerivAt
    have hw : HasFDerivWithinAt g (mfderiv I J f x) (range I) (c x) := h.2
    exact hw.hasFDerivAt (by rw [I.range_eq_univ]; exact Filter.univ_mem)
  let h := isImmersionAt_of_injective_hasFDerivAt hn hU hxU hg hdg hinj
  let hd : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) E E n :=
    { toPartialEquiv := h.domChart.toPartialEquiv
      open_source := h.domChart.open_source
      open_target := h.domChart.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas }
  let hc : PartialDiffeomorph 𝓘(𝕜, F) 𝓘(𝕜, F) F F n :=
    { toPartialEquiv := h.codChart.toPartialEquiv
      open_source := h.codChart.open_source
      open_target := h.codChart.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas }
  let α := (c.trans hd).trans (modelInverse I n)
  let β := (d.trans hc).trans (modelInverse J n)
  have hgx : g (c x) = d (f x) := by
    change d (f (c.symm (c x))) = d (f x)
    rw [hcx]
  apply IsImmersionAtOfComplement.isImmersionAt (F := h.complement)
  apply IsImmersionAtOfComplement.mk_of_continuousAt hf.continuous.continuousAt h.equiv
    α.toOpenPartialHomeomorph β.toOpenPartialHomeomorph
  · exact ⟨⟨hxc, h.mem_domChart_source⟩, mem_univ _⟩
  · refine ⟨⟨hfd, ?_⟩, mem_univ _⟩
    change d (f x) ∈ h.codChart.source
    rw [← hgx]
    exact h.mem_codChart_source
  · exact α.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      α.contMDiffOn_toFun α.contMDiffOn_invFun
  · exact β.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      β.contMDiffOn_toFun β.contMDiffOn_invFun
  · intro z hz
    have hIz : I (I.symm z) = z := I.toHomeomorph.apply_symm_apply z
    have hzα : I.symm z ∈ α.target := hz.2
    have hzt : z ∈ h.domChart.target := by
      have hmem := hzα.2.1
      change I (I.symm z) ∈ h.domChart.target at hmem
      rwa [hIz] at hmem
    change J (J.symm (h.codChart (g (h.domChart.symm (I (I.symm z)))))) =
      h.equiv (z, 0)
    rw [J.right_inv (by rw [J.range_eq_univ]; exact mem_univ _), hIz]
    exact h.writtenInCharts (by simpa using hzt)

theorem isImmersion_of_isImmersionAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {H G M N : Type*} [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
    {n : ℕ∞ω} {f : M → N} (hf : ∀ x, IsImmersionAt I J n f x) :
    IsImmersion I J n f := by
  let C := Fin (Module.finrank 𝕜 F - Module.finrank 𝕜 E) → 𝕜
  apply IsImmersionOfComplement.isImmersion (F := C)
  intro x
  let h := hf x
  let L₁ := h.equiv.toLinearMap.comp (LinearMap.inl 𝕜 E h.complement)
  let _ : FiniteDimensional 𝕜 E :=
    FiniteDimensional.of_injective L₁ (h.equiv.injective.comp LinearMap.inl_injective)
  let L₂ := h.equiv.toLinearMap.comp (LinearMap.inr 𝕜 E h.complement)
  let _ : FiniteDimensional 𝕜 h.complement :=
    FiniteDimensional.of_injective L₂ (h.equiv.injective.comp LinearMap.inr_injective)
  have hdim : Module.finrank 𝕜 h.complement = Module.finrank 𝕜 C := by
    have hsum := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at hsum
    simp only [C, Module.finrank_fin_fun]
    omega
  exact h.isImmersionAtOfComplement_complement.trans_F (ContinuousLinearEquiv.ofFinrankEq hdim)

theorem isImmersion_of_injective_mfderiv
    {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {H G M N : Type*} [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
    [I.Boundaryless] [J.Boundaryless] {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
    {f : M → N} (hn : n ≠ 0) (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) : IsImmersion I J n f := by
  let C := Fin (Module.finrank 𝕜 F - Module.finrank 𝕜 E) → 𝕜
  apply IsImmersionOfComplement.isImmersion (F := C)
  intro x
  let h := isImmersionAt_of_injective_mfderiv hn hf x (hinj x)
  let L := h.equiv.toLinearMap.comp (LinearMap.inr 𝕜 E h.complement)
  let : FiniteDimensional 𝕜 h.complement :=
    FiniteDimensional.of_injective L (h.equiv.injective.comp LinearMap.inr_injective)
  have hdim : Module.finrank 𝕜 h.complement = Module.finrank 𝕜 C := by
    have hsum := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at hsum
    simp only [C, Module.finrank_fin_fun]
    omega
  exact h.isImmersionAtOfComplement_complement.trans_F (ContinuousLinearEquiv.ofFinrankEq hdim)

end DifferentialGeometry.Topology.Manifold
