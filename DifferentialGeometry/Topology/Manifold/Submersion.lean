import DifferentialGeometry.Analysis.Calculus.Inverse.LocalSubmersion
import Mathlib.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
noncomputable section

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isSubmersionAt_of_hasFDerivAt_hasRightInverse
    {f : E → F} {U : Set E} {x₀ : E} {f' : E →L[ℝ] F}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hdf : HasFDerivAt f f' x₀) (hsplit : f'.HasRightInverse) :
    Manifold.IsSubmersionAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x₀ := by
  obtain ⟨e, hxe, _, he, heinv, _, hproj⟩ :=
    DifferentialGeometry.Analysis.exists_localProjection_of_hasRightInverse hf hU hx₀ hdf hsplit
  let A := ContinuousLinearEquiv.equivOfRightInverse f' hsplit.rightInverse
    hsplit.rightInverse_rightInverse
  let φ := e.trans A.symm.toHomeomorph.toOpenPartialHomeomorph
  let ψ := OpenPartialHomeomorph.refl F
  apply Manifold.IsSubmersionAtOfComplement.isSubmersionAt (F := f'.ker)
  apply Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt
    (hf.contDiffAt (hU.mem_nhds hx₀)).continuousAt A φ ψ
  · exact ⟨hxe, Set.mem_univ _⟩
  · exact Set.mem_univ _
  · apply φ.mem_maximalAtlas_of_contMDiffOn
    · rw [contMDiffOn_iff_contDiffOn]
      exact A.symm.contDiff.comp_contDiffOn (he.mono (fun _ hx ↦ hx.1))
    · rw [contMDiffOn_iff_contDiffOn]
      exact heinv.comp A.contDiff.contDiffOn (fun _ hx ↦ hx.2)
  · apply ψ.mem_maximalAtlas_of_contMDiffOn
    · exact contMDiffOn_id
    · exact contMDiffOn_id
  · intro z hz
    have hzφ : z ∈ φ.target := by simpa using hz
    exact hproj (A z) hzφ.2

private def openExtChart
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] (x : M) :
    OpenPartialHomeomorph M E where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x

section Manifold

variable {H H' M N : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]

theorem isSubmersionAt_of_mfderiv_hasRightInverse
    (f : M → N) (hf : ContMDiff I J ∞ f) (x₀ : M)
    (hsplit : (mfderiv I J f x₀).HasRightInverse) :
    Manifold.IsSubmersionAt I J ∞ f x₀ := by
  let cM := openExtChart I x₀
  let cN := openExtChart J (f x₀)
  let g : E → F := cN ∘ f ∘ cM.symm
  let U := cM.target ∩ cM.symm ⁻¹' (f ⁻¹' cN.source)
  have hU : IsOpen U := cM.isOpen_inter_preimage_symm
    (cN.open_source.preimage hf.continuous)
  have hxM : x₀ ∈ cM.source := mem_extChartAt_source x₀
  have hxN : f x₀ ∈ cN.source := mem_extChartAt_source (f x₀)
  have hxU : cM x₀ ∈ U := by
    refine ⟨cM.map_source hxM, ?_⟩
    change f (cM.symm (cM x₀)) ∈ cN.source
    rw [cM.left_inv hxM]
    exact hxN
  have hg : ContDiffOn ℝ ∞ g U := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_extChartAt (I := J) (x := f x₀)).comp
      (hf.comp_contMDiffOn ((contMDiffOn_extChartAt_symm x₀).mono Set.inter_subset_left))
      (fun z hz ↦ by
        have hm : f (cM.symm z) ∈ (extChartAt J (f x₀)).source := hz.2
        change f (cM.symm z) ∈ (chartAt H' (f x₀)).source
        simpa only [extChartAt_source] using hm)
  let L : E →L[ℝ] F := mfderiv I J f x₀
  have hL : HasFDerivAt g L (cM x₀) := by
    have hd := ((hf x₀).mdifferentiableAt (by simp)).hasMFDerivAt
    have hw : HasFDerivWithinAt g L (Set.range I) (cM x₀) := hd.2
    exact hw.hasFDerivAt (by rw [I.range_eq_univ]; exact Filter.univ_mem)
  obtain ⟨e, hxe, _, he, heinv, _, hproj⟩ :=
    DifferentialGeometry.Analysis.exists_localProjection_of_hasRightInverse hg hU hxU hL hsplit
  let A := ContinuousLinearEquiv.equivOfRightInverse L hsplit.rightInverse
    hsplit.rightInverse_rightInverse
  let φ := ((cM.trans e).trans A.symm.toHomeomorph.toOpenPartialHomeomorph).trans
    I.toHomeomorph.symm.toOpenPartialHomeomorph
  let ψ := chartAt H' (f x₀)
  have hIsymm : ContMDiff 𝓘(ℝ, E) I ∞ I.symm := by
    rw [← contMDiffOn_univ]
    simpa only [I.range_eq_univ] using (I.contMDiffOn_symm (n := ∞))
  have hφ : ContMDiffOn I I ∞ φ φ.source := by
    have hc : ContMDiffOn I 𝓘(ℝ, E) ∞ cM φ.source :=
      (contMDiffOn_extChartAt (I := I) (x := x₀)).mono
        (fun z hz ↦ by
          have hm : z ∈ (extChartAt I x₀).source := hz.1.1.1
          simpa only [extChartAt_source] using hm)
    exact hIsymm.comp_contMDiffOn
      (A.symm.contDiff.contMDiff.comp_contMDiffOn
        (he.contMDiffOn.comp hc (fun _ hz ↦ hz.1.1.2)))
  have hφinv : ContMDiffOn I I ∞ φ.symm φ.target := by
    have hA : ContMDiff I 𝓘(ℝ, F × L.ker) ∞ (fun z ↦ A (I z)) :=
      A.contDiff.contMDiff.comp (I.contMDiff (n := ∞))
    have heI := heinv.contMDiffOn.comp hA.contMDiffOn (fun z (hz : z ∈ φ.target) ↦ hz.2.2.1)
    exact (contMDiffOn_extChartAt_symm (I := I) x₀).comp heI
      (fun _ hz ↦ hz.2.2.2)
  apply Manifold.IsSubmersionAtOfComplement.isSubmersionAt (F := L.ker)
  apply Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt
    hf.continuous.continuousAt A φ ψ
  · exact ⟨⟨⟨hxM, hxe⟩, Set.mem_univ _⟩, Set.mem_univ _⟩
  · exact mem_chart_source H' (f x₀)
  · exact φ.mem_maximalAtlas_of_contMDiffOn hφ hφinv
  · exact IsManifold.chart_mem_maximalAtlas _
  · intro z hz
    have hIz : I (I.symm z) = z := I.toHomeomorph.apply_symm_apply z
    have hzφ : I.symm z ∈ φ.target := hz.2
    have hze : A z ∈ e.target := by
      have ht := hzφ.2.2.1
      change A (I (I.symm z)) ∈ e.target at ht
      rwa [hIz] at ht
    change g (e.symm (A (I (I.symm z)))) = (A z).1
    rw [hIz]
    exact hproj (A z) hze

theorem isSubmersionAt_of_surjective_mfderiv [FiniteDimensional ℝ F]
    (f : M → N) (hf : ContMDiff I J ∞ f) (x₀ : M)
    (hsurj : Function.Surjective (mfderiv I J f x₀)) :
    Manifold.IsSubmersionAt I J ∞ f x₀ := by
  let L : E →L[ℝ] F := mfderiv I J f x₀
  have hs : Function.Surjective L := hsurj
  have hL : L.HasRightInverse :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional (f := L) hs
  exact isSubmersionAt_of_mfderiv_hasRightInverse f hf x₀ hL

omit [CompleteSpace E] in
theorem isSubmersionAtOfComplement_of_surjective_mfderiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : M → N) (hf : ContMDiff I J ∞ f) (x : M)
    (hsurj : Function.Surjective (mfderiv I J f x)) :
    Manifold.IsSubmersionAtOfComplement
      (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I J ∞ f x := by
  let K₀ := Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
  rcases isSubmersionAt_of_surjective_mfderiv f hf x hsurj with ⟨K, hK, hKmod, h⟩
  let A := h.equiv
  let g : K →L[ℝ] E := A.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ F K)
  have hg : Function.Injective g := by
    intro u v huv
    exact congrArg Prod.snd (A.symm.injective huv)
  let _ : FiniteDimensional ℝ K := FiniteDimensional.of_injective g.toLinearMap hg
  have hdim : Module.finrank ℝ K = Module.finrank ℝ K₀ := by
    have hA := A.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at hA
    change Module.finrank ℝ K = Module.finrank ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
    rw [Module.finrank_fin_fun]
    omega
  exact h.trans_F (ContinuousLinearEquiv.ofFinrankEq hdim)

omit [CompleteSpace E] in
theorem isSubmersion_of_surjective_mfderiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hsurj : ∀ x, Function.Surjective (mfderiv I J f x)) :
    Manifold.IsSubmersion I J ∞ f := by
  exact (show Manifold.IsSubmersionOfComplement
      (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I J ∞ f from
    fun x ↦ isSubmersionAtOfComplement_of_surjective_mfderiv f hf x (hsurj x)).isSubmersion

omit [CompleteSpace E] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem mfderiv_hasRightInverse_of_isSubmersionAt
    {f : M → N} {x₀ : M} (h : Manifold.IsSubmersionAt I J ∞ f x₀) :
    (mfderiv I J f x₀).HasRightInverse := by
  rcases h with ⟨K, hK, hKmod, h⟩
  let φ := h.domChart
  let ψ := h.codChart
  let A := h.equiv
  let ξ := (φ.extend I) x₀
  have hxext : x₀ ∈ (φ.extend I).source := by
    simpa only [OpenPartialHomeomorph.extend_source] using h.mem_domChart_source
  have hξ : ξ ∈ (φ.extend I).target := (φ.extend I).map_source hxext
  have hTopen : IsOpen (φ.extend I).target := by
    rw [OpenPartialHomeomorph.extend_target, I.range_eq_univ, Set.inter_univ]
    exact φ.open_target.preimage I.toHomeomorph.symm.continuous
  have hreturn : (φ.extend I).symm ξ = x₀ := (φ.extend I).left_inv hxext
  have hInvOn : ContMDiffOn 𝓘(ℝ, E) I ∞ (φ.extend I).symm (φ.extend I).target := by
    convert contMDiffOn_extend_symm h.domChart_mem_maximalAtlas using 1
    rw [OpenPartialHomeomorph.extend_target, I.image_eq]
  have hInv := (hInvOn.contMDiffAt (hTopen.mem_nhds hξ)).mdifferentiableAt (by simp)
  have hψOn : ContMDiffOn J J ∞ ψ ψ.source :=
    contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
  have hψInvOn : ContMDiffOn J J ∞ ψ.symm ψ.target :=
    contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
  have hψdiff : ψ.MDifferentiable J J :=
    ⟨hψOn.mdifferentiableOn (by simp), hψInvOn.mdifferentiableOn (by simp)⟩
  have hψat := hψdiff.mdifferentiableAt h.mem_codChart_source
  have hC := J.hasMFDerivAt.comp (f x₀) hψat.hasMFDerivAt
  let C : TangentSpace J (f x₀) →L[ℝ] F :=
    mfderiv J 𝓘(ℝ, F) (ψ.extend J) (f x₀)
  have hCinj : Function.Injective C := by
    change Function.Injective (mfderiv J 𝓘(ℝ, F) (J ∘ ψ) (f x₀))
    rw [hC.mfderiv]
    exact hψdiff.mfderiv_injective h.mem_codChart_source
  let D := mfderiv I J f x₀
  let B : E →L[ℝ] TangentSpace I x₀ := mfderiv 𝓘(ℝ, E) I (φ.extend I).symm ξ
  have hDf := h.contMDiffAt.mdifferentiableAt (by simp)
  have hcod : HasMFDerivAt J 𝓘(ℝ, F) (ψ.extend J) (f x₀) C := by
    exact hC.mdifferentiableAt.hasMFDerivAt
  have hcf : HasMFDerivAt I 𝓘(ℝ, F) ((ψ.extend J) ∘ f)
      ((φ.extend I).symm ξ) (C.comp D) := by
    rw [hreturn]
    exact hcod.comp x₀ hDf.hasMFDerivAt
  have hchain := hcf.comp ξ hInv.hasMFDerivAt
  let P : E →L[ℝ] F := (ContinuousLinearMap.fst ℝ F K).comp A.toContinuousLinearMap
  have hEq : ((ψ.extend J) ∘ f ∘ (φ.extend I).symm) =ᶠ[𝓝 ξ] P :=
    h.writtenInCharts.eventuallyEq_of_mem (hTopen.mem_nhds hξ)
  have hP : HasFDerivAt ((ψ.extend J) ∘ f ∘ (φ.extend I).symm) P ξ :=
    P.hasFDerivAt.congr_of_eventuallyEq hEq
  have hder : (C.comp D).comp B = P :=
    hchain.mfderiv.symm.trans hP.hasMFDerivAt.mfderiv
  let R : TangentSpace J (f x₀) →L[ℝ] TangentSpace I x₀ :=
    B.comp (A.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inl ℝ F K).comp C))
  refine ⟨R, ?_⟩
  intro v
  apply hCinj
  have hv := congrArg (fun L : E →L[ℝ] F ↦ L (A.symm (C v, 0))) hder
  simpa [R, P] using hv

theorem isSubmersionAt_iff_mfderiv_hasRightInverse
    (f : M → N) (hf : ContMDiff I J ∞ f) (x₀ : M) :
    Manifold.IsSubmersionAt I J ∞ f x₀ ↔ (mfderiv I J f x₀).HasRightInverse :=
  ⟨mfderiv_hasRightInverse_of_isSubmersionAt,
    isSubmersionAt_of_mfderiv_hasRightInverse f hf x₀⟩

theorem isSubmersionAt_iff_surjective_mfderiv [FiniteDimensional ℝ F]
    (f : M → N) (hf : ContMDiff I J ∞ f) (x₀ : M) :
    Manifold.IsSubmersionAt I J ∞ f x₀ ↔ Function.Surjective (mfderiv I J f x₀) :=
  ⟨fun h ↦ (mfderiv_hasRightInverse_of_isSubmersionAt h).surjective,
    isSubmersionAt_of_surjective_mfderiv f hf x₀⟩

omit [CompleteSpace E] in
theorem isSubmersion_iff_surjective_mfderiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : M → N) (hf : ContMDiff I J ∞ f) :
    Manifold.IsSubmersion I J ∞ f ↔ ∀ x, Function.Surjective (mfderiv I J f x) :=
  ⟨fun h x ↦ (mfderiv_hasRightInverse_of_isSubmersionAt (h.isSubmersionAt x)).surjective,
    isSubmersion_of_surjective_mfderiv f hf⟩

end Manifold

end DifferentialGeometry.Topology.Manifold
