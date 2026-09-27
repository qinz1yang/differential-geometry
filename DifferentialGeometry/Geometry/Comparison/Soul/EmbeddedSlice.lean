import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.LocallyClosed

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def IsEmbeddedSlice (I : ModelWithCorners ℝ E H) (d : ℕ) (S : Set M) : Prop :=
  ∀ x ∈ S, ∃ (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (A : AffineSubspace ℝ E),
    FiniteDimensional ℝ A.direction ∧ x ∈ c.source ∧
      Module.finrank ℝ A.direction = d ∧ c.toPartialEquiv.IsImage S (A : Set E)


def sliceDims (I : ModelWithCorners ℝ E H) (C : Set M) : Set ℕ :=
  {d | ∃ S : Set M, S.Nonempty ∧ S ⊆ C ∧ IsEmbeddedSlice I d S}

def maxSliceDim (I : ModelWithCorners ℝ E H) (C : Set M) : ℕ := sSup (sliceDims I C)


def maxSliceLocus (I : ModelWithCorners ℝ E H) (C : Set M) : Set M :=
  {x | ∃ S : Set M, x ∈ S ∧ S ⊆ C ∧ IsEmbeddedSlice I (maxSliceDim I C) S}

private def sliceChart [I.Boundaryless] [IsManifold I ∞ M] (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by simpa only [extChartAt_source] using contMDiffOn_extChartAt (I := I) (x := x)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

private def restrictSliceChart (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (U : Set M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  __ := c.toOpenPartialHomeomorph.restr U
  contMDiffOn_toFun := c.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := c.contMDiffOn_invFun.mono inter_subset_left

namespace IsEmbeddedSlice


theorem of_affineSubspace (A : AffineSubspace ℝ E) [FiniteDimensional ℝ A.direction] :
    IsEmbeddedSlice 𝓘(ℝ, E) (Module.finrank ℝ A.direction) (A : Set E) := by
  intro x hx
  refine ⟨(Diffeomorph.refl 𝓘(ℝ, E) E ∞).toPartialDiffeomorph, A,
    inferInstance, mem_univ x, rfl, ?_⟩
  intro y hy
  exact Iff.rfl


theorem singleton [I.Boundaryless] [IsManifold I ∞ M] (x : M) :
    IsEmbeddedSlice I 0 ({x} : Set M) := by
  intro y hy
  have hyx : y = x := hy
  subst y
  let c := sliceChart (I := I) x
  let A := AffineSubspace.mk' (c x) (⊥ : Submodule ℝ E)
  have hx : x ∈ c.source := mem_extChartAt_source x
  refine ⟨c, A, ?_, hx, ?_, ?_⟩
  · dsimp [A]
    rw [AffineSubspace.direction_mk']
    infer_instance
  · rw [AffineSubspace.direction_mk', finrank_bot]
  · intro y hy
    change c y ∈ AffineSubspace.mk' (c x) (⊥ : Submodule ℝ E) ↔ y ∈ ({x} : Set M)
    rw [AffineSubspace.mem_mk', Submodule.mem_bot, vsub_eq_zero_iff_eq, mem_singleton_iff]
    exact ⟨c.toPartialEquiv.injOn hy hx, congrArg c⟩


theorem dim_le [FiniteDimensional ℝ E] {S : Set M} {d : ℕ}
    (hS : IsEmbeddedSlice I d S) (hne : S.Nonempty) : d ≤ Module.finrank ℝ E := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx
  rw [← hdim]
  exact A.direction.finrank_le


theorem inter_open {S U : Set M} {d : ℕ} (hS : IsEmbeddedSlice I d S) (hU : IsOpen U) :
    IsEmbeddedSlice I d (S ∩ U) := by
  intro x hx
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx.1
  refine ⟨restrictSliceChart c U, A, hA, ⟨hxc, ?_⟩, hdim, ?_⟩
  · rw [hU.interior_eq]
    exact hx.2
  · intro y hy
    change c y ∈ (A : Set E) ↔ y ∈ S ∩ U
    have hyU : y ∈ U := interior_subset hy.2
    simpa only [mem_inter_iff, hyU, and_true] using himage.apply_mem_iff hy.1


theorem image {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSlice I d S)
    (f : PartialDiffeomorph I J M N ∞) (hsub : S ⊆ f.source) :
    IsEmbeddedSlice J d (f '' S) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx
  let e := f.symm.trans c
  refine ⟨e, A, hA, ?_, hdim, ?_⟩
  · refine ⟨f.map_source' (hsub hx), ?_⟩
    change f.toPartialEquiv.symm (f.toPartialEquiv x) ∈ c.source
    rw [f.toPartialEquiv.left_inv (hsub hx)]
    exact hxc
  · intro z hz
    change c (f.symm z) ∈ (A : Set E) ↔ z ∈ f '' S
    have hzc : f.toPartialEquiv.symm z ∈ c.source := hz.2
    constructor
    · intro h
      have hmem : f.toPartialEquiv.symm z ∈ S := (himage.apply_mem_iff hzc).1 h
      exact ⟨f.symm z, hmem, f.toPartialEquiv.right_inv hz.1⟩
    · rintro ⟨w, hw, rfl⟩
      apply (himage.apply_mem_iff hzc).2
      rw [f.toPartialEquiv.left_inv (hsub hw)]
      exact hw


theorem of_isOpen [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    {S : Set M} (hS : IsOpen S) : IsEmbeddedSlice I (Module.finrank ℝ E) S := by
  intro x hx
  let c := sliceChart (I := I) x
  refine ⟨restrictSliceChart c S, ⊤, inferInstance, ⟨mem_extChartAt_source x, ?_⟩, ?_, ?_⟩
  · rwa [hS.interior_eq]
  · rw [AffineSubspace.direction_top, finrank_top]
  · intro y hy
    exact ⟨fun _ => interior_subset hy.2, fun _ => AffineSubspace.mem_top ℝ E _⟩


theorem of_germ {S : Set M} {d : ℕ}
    (h : ∀ x ∈ S, ∃ N U : Set M, IsEmbeddedSlice I d N ∧ IsOpen U ∧
      x ∈ U ∧ x ∈ N ∧ U ∩ S = U ∩ N) : IsEmbeddedSlice I d S := by
  intro x hx
  obtain ⟨N, U, hN, hU, hxU, hxN, heq⟩ := h x hx
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hN x hxN
  refine ⟨restrictSliceChart c U, A, hA, ⟨hxc, ?_⟩, hdim, ?_⟩
  · rwa [hU.interior_eq]
  · intro y hy
    change c y ∈ (A : Set E) ↔ y ∈ S
    have hyU : y ∈ U := interior_subset hy.2
    have he : y ∈ S ↔ y ∈ N := by
      simpa only [mem_inter_iff, hyU, true_and] using Set.ext_iff.1 heq y
    exact (himage.apply_mem_iff hy.1).trans he.symm


theorem isOpen [FiniteDimensional ℝ E] {S : Set M}
    (hS : IsEmbeddedSlice I (Module.finrank ℝ E) S) : IsOpen S := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx
  have hxA : c x ∈ A := (himage.apply_mem_iff hxc).2 hx
  have hdir : A.direction = ⊤ := Submodule.eq_top_of_finrank_eq hdim
  have htop : A = ⊤ := (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨c x, hxA⟩).1 hdir
  apply Filter.mem_of_superset (c.open_source.mem_nhds hxc)
  intro y hy
  apply (himage.apply_mem_iff hy).1
  rw [htop]
  exact AffineSubspace.mem_top ℝ E (c y)


theorem isLocallyClosed {S : Set M} {d : ℕ} (hS : IsEmbeddedSlice I d S) :
    IsLocallyClosed S := by
  apply ((isLocallyClosed_tfae S).out 2 0).mp
  intro x hx
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx
  let : FiniteDimensional ℝ A.direction := hA
  refine ⟨c.source, c.open_source.mem_nhds hxc, ?_⟩
  have heq : (Subtype.val : c.source → M) ⁻¹' S =
      (c.source.domRestrict (c : M → E)) ⁻¹' (A : Set E) := by
    ext y
    exact (himage.apply_mem_iff y.property).symm
  rw [heq]
  exact A.closed_of_finiteDimensional.preimage c.contMDiffOn_toFun.continuousOn.domRestrict

theorem exists_param {S : Set E} {d : ℕ} (hS : IsEmbeddedSlice 𝓘(ℝ, E) d S)
    {x : E} (hx : x ∈ S) :
    ∃ (L : Submodule ℝ E) (U : Set L) (f : L → E) (W : Set E),
      FiniteDimensional ℝ L ∧ Module.finrank ℝ L = d ∧ IsOpen U ∧ (0 : L) ∈ U ∧
        ContDiffOn ℝ ∞ f U ∧ Function.Injective (fderiv ℝ f 0) ∧ f 0 = x ∧
        IsOpen W ∧ x ∈ W ∧ f '' U = W ∩ S := by
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx
  let L : Submodule ℝ E := A.direction
  let : FiniteDimensional ℝ L := hA
  let shift : L → E := fun v => (v : E) + c x
  let U : Set L := shift ⁻¹' c.target
  let f : L → E := fun v => c.symm (shift v)
  have hcx : c x ∈ c.target := c.toPartialEquiv.map_source hxc
  have hcxA : c x ∈ A := (himage.apply_mem_iff hxc).2 hx
  have hshift : ContDiff ℝ ∞ shift := L.subtypeL.contDiff.add contDiff_const
  have hzero : shift 0 = c x := by simp [shift]
  have hU : IsOpen U := c.open_target.preimage hshift.continuous
  have h0U : (0 : L) ∈ U := by change shift 0 ∈ c.target; rwa [hzero]
  have hf : ContDiffOn ℝ ∞ f U :=
    c.symm.contMDiffOn_toFun.contDiffOn.comp hshift.contDiffOn (fun _ hv => hv)
  have hcLocal := c.symm.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hcx
  have hcinj : Function.Injective (fderiv ℝ (c.symm : E → E) (c x)) := by
    rw [← mfderiv_eq_fderiv]
    exact (hcLocal.mfderivToContinuousLinearEquiv (by simp)).injective
  have hcDiff : DifferentiableAt ℝ (c.symm : E → E) (c x) :=
    (hcLocal.mdifferentiableAt (by simp)).differentiableAt
  have hdf : HasFDerivAt f ((fderiv ℝ (c.symm : E → E) (c x)).comp L.subtypeL) 0 := by
    have hdc : HasFDerivAt (c.symm : E → E) (fderiv ℝ (c.symm : E → E) (c x)) (shift 0) := by
      rw [hzero]
      exact hcDiff.hasFDerivAt
    exact hdc.comp 0 (L.subtypeL.hasFDerivAt.add_const (c x))
  have hinj : Function.Injective (fderiv ℝ f 0) := by
    rw [hdf.fderiv]
    exact hcinj.comp L.subtype_injective
  have hfzero : f 0 = x := by
    change c.toPartialEquiv.symm (shift 0) = x
    rw [hzero]
    exact c.toPartialEquiv.left_inv hxc
  have him : f '' U = c.source ∩ S := by
    apply Subset.antisymm
    · rintro _ ⟨v, hv, rfl⟩
      have hfv : f v ∈ c.source := c.toPartialEquiv.map_target hv
      refine ⟨hfv, (himage.apply_mem_iff hfv).1 ?_⟩
      change c.toPartialEquiv (c.toPartialEquiv.symm (shift v)) ∈ A
      rw [c.toPartialEquiv.right_inv hv]
      exact A.vadd_mem_of_mem_direction v.property hcxA
    · rintro y ⟨hyc, hyS⟩
      have hcy : c y ∈ A := (himage.apply_mem_iff hyc).2 hyS
      let v : L := ⟨c y - c x, A.vsub_mem_direction hcy hcxA⟩
      have hshiftv : shift v = c y := sub_add_cancel _ _
      have hv : v ∈ U := by change shift v ∈ c.target; rw [hshiftv]; exact c.toPartialEquiv.map_source hyc
      refine ⟨v, hv, ?_⟩
      change c.toPartialEquiv.symm (shift v) = y
      rw [hshiftv]
      exact c.toPartialEquiv.left_inv hyc
  exact ⟨L, U, f, c.source, inferInstance, hdim, hU, h0U, hf, hinj, hfzero,
    c.open_source, hxc, him⟩

end IsEmbeddedSlice


theorem sliceDims_nonempty [I.Boundaryless] [IsManifold I ∞ M]
    {C : Set M} (hC : C.Nonempty) : (sliceDims I C).Nonempty := by
  obtain ⟨x, hx⟩ := hC
  exact ⟨0, {x}, singleton_nonempty x, singleton_subset_iff.2 hx, IsEmbeddedSlice.singleton x⟩


theorem sliceDims_bddAbove [FiniteDimensional ℝ E] (C : Set M) : BddAbove (sliceDims I C) := by
  refine ⟨Module.finrank ℝ E, ?_⟩
  rintro d ⟨S, hne, hsub, hS⟩
  exact hS.dim_le hne


theorem exists_maxSlice [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    {C : Set M} (hC : C.Nonempty) :
    ∃ S : Set M, S.Nonempty ∧ S ⊆ C ∧ IsEmbeddedSlice I (maxSliceDim I C) S :=
  Nat.sSup_mem (sliceDims_nonempty (I := I) hC) (sliceDims_bddAbove (I := I) C)


theorem le_maxSliceDim [FiniteDimensional ℝ E] {C : Set M} {d : ℕ}
    (hd : d ∈ sliceDims I C) : d ≤ maxSliceDim I C :=
  le_csSup (sliceDims_bddAbove (I := I) C) hd


theorem maxSliceLocus_nonempty [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    {C : Set M} (hC : C.Nonempty) : (maxSliceLocus I C).Nonempty := by
  obtain ⟨S, ⟨x, hx⟩, hsub, hS⟩ := exists_maxSlice (I := I) hC
  exact ⟨x, S, hx, hsub, hS⟩


theorem maxSliceLocus_subset {C : Set M} : maxSliceLocus I C ⊆ C := by
  rintro x ⟨S, hx, hsub, hS⟩
  exact hsub hx


theorem maxSliceDim_mono [FiniteDimensional ℝ E] {C D : Set M} (h : C ⊆ D) :
    maxSliceDim I C ≤ maxSliceDim I D := by
  apply csSup_le' (fun d hd => ?_)
  obtain ⟨S, hne, hSC, hS⟩ := hd
  exact le_maxSliceDim (I := I) ⟨S, hne, hSC.trans h, hS⟩


theorem maxSliceDim_le [FiniteDimensional ℝ E] (C : Set M) :
    maxSliceDim I C ≤ Module.finrank ℝ E := by
  apply csSup_le'
  rintro d ⟨S, hne, hSC, hS⟩
  exact hS.dim_le hne

end DifferentialGeometry.Geometry
