import DifferentialGeometry.Topology.Manifold.Diffeomorph.OfHomeomorph

/-!
# The inverse of an open `C¹` injective map with invertible differentials is `C¹`

`contMDiffOn_invFunOn_of_isInvertible_mfderiv`: let `f : M → N` be `C¹` on an open set `U`,
injective on `U`, sending open subsets of `U` to open sets, with invertible `mfderiv` at every
point of `U`. Then `invFunOn f U` is `C¹` on the open set `f '' U`. Manifolds with boundary or
corners are allowed: this is the on-a-set form of `contMDiff_symm_of_isInvertible_mfderiv`
(`Diffeomorph/OfHomeomorph.lean`), with the same Euclidean kernel
`contDiffOn_one_of_leftInverse_of_isInvertible` applied in fixed extended charts.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

omit [CompleteSpace E] in
/-- Pointwise form of `isInvertible_fderivWithin_extChartAt_comp`: only differentiability of `f`
at the point is used. -/
theorem isInvertible_fderivWithin_extChartAt_comp_of_mdifferentiableAt {f : M → N} {x₀ : M}
    {y₀ : N} {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hfz : f ((extChartAt I x₀).symm z) ∈ (extChartAt J y₀).source)
    (h2 : MDifferentiableAt I J f ((extChartAt I x₀).symm z))
    (hinv : (mfderiv I J f ((extChartAt I x₀).symm z)).IsInvertible) :
    (fderivWithin ℝ (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) (range I) z).IsInvertible := by
  set x := (extChartAt I x₀).symm z with hx
  have h1 : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) z :=
    mdifferentiableWithinAt_extChartAt_symm hz
  have h3 : MDifferentiableAt J 𝓘(ℝ, E') (extChartAt J y₀) (f x) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hfz)
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, E) (range I) z :=
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt).mpr
      (I.uniqueDiffOn z (extChartAt_target_subset_range x₀ hz))
  have hc : mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E') (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm)
      (range I) z = (mfderiv J 𝓘(ℝ, E') (extChartAt J y₀) (f x)).comp
        ((mfderiv I J f x).comp (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) z)) := by
    have h23 : MDifferentiableAt I 𝓘(ℝ, E') (extChartAt J y₀ ∘ f) x := h3.comp x h2
    rw [show extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm =
      (extChartAt J y₀ ∘ f) ∘ (extChartAt I x₀).symm from rfl,
      mfderiv_comp_mfderivWithin z h23 h1 hu, mfderiv_comp x h3 h2]
    rfl
  have hmi : (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E') (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm)
      (range I) z).IsInvertible := by
    rw [hc]
    exact (isInvertible_mfderiv_extChartAt (by simpa only [extChartAt_source] using hfz)).comp
      (hinv.comp (isInvertible_mfderivWithin_extChartAt_symm hz))
  obtain ⟨e, he⟩ := hmi
  have hm := mfderivWithin_eq_fderivWithin (𝕜 := ℝ)
    (f := extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) (s := range I) (x := z)
  refine ⟨((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.trans e).trans
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) z)), ?_⟩
  ext v
  have h := congrArg (fun L => L ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) (he.trans hm)
  simp only [ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] at h
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply, h]
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) _).apply_symm_apply _

/-- The inverse of a map that is injective on an open set and sends its open subsets to open
sets is continuous on the image. -/
theorem continuousOn_invFunOn_of_isOpenMap_restrict [Nonempty M] {f : M → N} {U : Set M}
    (hinj : InjOn f U) (hopen : ∀ V ⊆ U, IsOpen V → IsOpen (f '' V)) (hU : IsOpen U) :
    ContinuousOn (invFunOn f U) (f '' U) := by
  rw [continuousOn_open_iff (hopen U subset_rfl hU)]
  intro t ht
  have heq : f '' U ∩ invFunOn f U ⁻¹' t = f '' (U ∩ t) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxt⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      rwa [mem_preimage, hinj.leftInvOn_invFunOn hx] at hxt
    · rintro ⟨x, ⟨hx, hxt⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rwa [mem_preimage, hinj.leftInvOn_invFunOn hx]
  rw [heq]
  exact hopen _ inter_subset_left (hU.inter ht)

/-- **The inverse of an open `C¹` injective map with invertible differentials is `C¹`** on the
image (boundary and corners allowed). -/
theorem contMDiffOn_invFunOn_of_isInvertible_mfderiv [Nonempty M] {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I J 1 f U) (hinj : InjOn f U)
    (hopen : ∀ V ⊆ U, IsOpen V → IsOpen (f '' V))
    (hinv : ∀ x ∈ U, (mfderiv I J f x).IsInvertible) :
    ContMDiffOn J I 1 (invFunOn f U) (f '' U) := by
  set g := invFunOn f U with hg
  have hfU : IsOpen (f '' U) := hopen U subset_rfl hU
  have hgcont : ContinuousOn g (f '' U) := continuousOn_invFunOn_of_isOpenMap_restrict hinj hopen hU
  have hgU : MapsTo g (f '' U) U := fun y hy => invFunOn_mem hy
  have hfg : ∀ y ∈ f '' U, f (g y) = y := fun y hy => invFunOn_eq hy
  intro y₀ hy₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  set x₀ := g y₀ with hx₀
  set φ := extChartAt I x₀ with hφ
  set ψ := extChartAt J y₀ with hψ
  rw [contMDiffAt_iff]
  refine ⟨hgcont.continuousAt (hfU.mem_nhds hy₀), ?_⟩
  set S : Set E := φ.target ∩ φ.symm ⁻¹' (U ∩ f ⁻¹' ψ.source) with hSdef
  set T : Set E' := ψ.target ∩ ψ.symm ⁻¹' (f '' U ∩ g ⁻¹' φ.source) with hTdef
  have hDS : IsOpen (U ∩ f ⁻¹' ψ.source) :=
    hf.continuousOn.isOpen_inter_preimage hU (isOpen_extChartAt_source y₀)
  have hDT : IsOpen (f '' U ∩ g ⁻¹' φ.source) :=
    hgcont.isOpen_inter_preimage hfU (isOpen_extChartAt_source x₀)
  obtain ⟨VS, hVS, hVSe⟩ := (continuousOn_iff'.mp (continuousOn_extChartAt_symm (I := I) x₀))
    (U ∩ f ⁻¹' ψ.source) hDS
  have hSV : S = φ.target ∩ VS := by
    rw [hSdef, inter_comm, hVSe, inter_comm]
  obtain ⟨VT, hVT, hVTe⟩ := (continuousOn_iff'.mp (continuousOn_extChartAt_symm (I := J) y₀))
    (f '' U ∩ g ⁻¹' φ.source) hDT
  have hTV : T = ψ.target ∩ VT := by
    rw [hTdef, inter_comm, hVTe, inter_comm]
  have hS : UniqueDiffOn ℝ S := by
    rw [hSV]
    exact (uniqueDiffOn_extChartAt_target x₀).inter hVS
  have hT : UniqueDiffOn ℝ T := by
    rw [hTV]
    exact (uniqueDiffOn_extChartAt_target y₀).inter hVT
  have hRf : ContDiffOn ℝ 1 (ψ ∘ f ∘ φ.symm) S := by
    have h1 : ContMDiffOn 𝓘(ℝ, E) J 1 (f ∘ φ.symm) S :=
      hf.comp ((contMDiffOn_extChartAt_symm x₀).mono inter_subset_left) fun y hy => hy.2.1
    have h : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E') 1 (ψ ∘ (f ∘ φ.symm)) S :=
      (contMDiffOn_extChartAt (n := 1) (x := y₀)).comp h1 (fun y hy => by
        have h' : f (φ.symm y) ∈ ψ.source := hy.2.2
        rw [hψ, extChartAt_source] at h'
        exact h')
    exact contMDiffOn_iff_contDiffOn.mp h
  have hRg : ContinuousOn (φ ∘ g ∘ ψ.symm) T := by
    refine (continuousOn_extChartAt x₀).comp ?_ ?_
    · exact hgcont.comp ((continuousOn_extChartAt_symm y₀).mono inter_subset_left)
        fun y hy => hy.2.1
    · intro y hy
      exact hy.2.2
  have hmaps : MapsTo (φ ∘ g ∘ ψ.symm) T S := by
    intro y hy
    have hsrc : g (ψ.symm y) ∈ φ.source := hy.2.2
    refine ⟨φ.map_source hsrc, ?_⟩
    simp only [mem_preimage, comp_apply, φ.left_inv hsrc]
    refine ⟨hgU hy.2.1, ?_⟩
    rw [mem_preimage, hfg _ hy.2.1]
    exact ψ.map_target hy.1
  have hfgT : ∀ y ∈ T, (ψ ∘ f ∘ φ.symm) ((φ ∘ g ∘ ψ.symm) y) = y := by
    intro y hy
    have hsrc : g (ψ.symm y) ∈ φ.source := hy.2.2
    simp only [comp_apply, φ.left_inv hsrc, hfg _ hy.2.1]
    exact ψ.right_inv hy.1
  have hinv' : ∀ y ∈ T,
      (fderivWithin ℝ (ψ ∘ f ∘ φ.symm) S ((φ ∘ g ∘ ψ.symm) y)).IsInvertible := by
    intro y hy
    have hz := hmaps hy
    have hS' : S = range I ∩ (I.symm ⁻¹' (chartAt H x₀).target ∩ VS) := by
      rw [hSV, hφ, extChartAt_target]
      ext w
      simp only [mem_inter_iff, mem_preimage]
      tauto
    have hO : I.symm ⁻¹' (chartAt H x₀).target ∩ VS ∈ 𝓝 ((φ ∘ g ∘ ψ.symm) y) := by
      refine (((chartAt H x₀).open_target.preimage I.continuous_symm).inter hVS).mem_nhds ?_
      rw [hS'] at hz
      exact hz.2
    rw [hS', fderivWithin_inter hO]
    have hzU : φ.symm ((φ ∘ g ∘ ψ.symm) y) ∈ U := (hmaps hy).2.1
    exact isInvertible_fderivWithin_extChartAt_comp_of_mdifferentiableAt hz.1 hz.2.2
      ((hf.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt one_ne_zero) (hinv _ hzU)
  have hg1 := contDiffOn_one_of_leftInverse_of_isInvertible hS hT hRf hRg hmaps hfgT hinv'
  have hy₀T : ψ y₀ ∈ T := by
    refine ⟨mem_extChartAt_target y₀, ?_⟩
    simp only [mem_preimage, hψ, extChartAt_to_inv]
    exact ⟨hy₀, mem_extChartAt_source _⟩
  have hTnhds : T ∈ 𝓝[range J] (ψ y₀) := by
    refine inter_mem (extChartAt_target_mem_nhdsWithin y₀) ?_
    have hmem : y₀ ∈ f '' U ∩ g ⁻¹' φ.source := ⟨hy₀, mem_extChartAt_source _⟩
    exact mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds (hDT.mem_nhds hmem))
  exact (hg1 _ hy₀T).mono_of_mem_nhdsWithin hTnhds

end DifferentialGeometry.Topology.Manifold
