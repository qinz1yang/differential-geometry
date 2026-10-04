import DifferentialGeometry.Topology.Manifold.Diffeomorph.InvFunOnSmooth

/-!
# The inverse of an open `C²` injective map with invertible differentials is `C²`

The second-order companion of `InvFunOnSmooth.lean`, boundary and corners allowed.

* `contDiffOn_two_of_leftInverse_of_isInvertible` (Euclidean kernel): a continuous right inverse
  `g` on `T` of a map `f` that is `C²` on `S` with invertible derivatives is `C²` on `T`; the
  derivative of `g` is `y ↦ (Df (g y))⁻¹`, which is `C¹` because `g` is `C¹`.
* `contMDiffOn_invFunOn_two_of_isInvertible_mfderiv`: let `f : M → N` be `C²` on an open set `U`,
  injective on `U`, sending open subsets of `U` to open sets, with invertible `mfderiv` at every
  point of `U`. Then `invFunOn f U` is `C²` on `f '' U`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold

section Euclidean

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Euclidean kernel, second order.** A continuous right inverse `g : T → S` of a map `f` that
is `C²` on `S` with invertible derivatives (within `S`) is `C²` on `T`. -/
theorem contDiffOn_two_of_leftInverse_of_isInvertible {S : Set E} {T : Set F}
    (hS : UniqueDiffOn ℝ S) (hT : UniqueDiffOn ℝ T) {f : E → F} {g : F → E}
    (hf : ContDiffOn ℝ 2 f S) (hg : ContinuousOn g T) (hgT : MapsTo g T S)
    (hfg : ∀ y ∈ T, f (g y) = y) (hinv : ∀ y ∈ T, (fderivWithin ℝ f S (g y)).IsInvertible) :
    ContDiffOn ℝ 2 g T := by
  have hg1 : ContDiffOn ℝ 1 g T :=
    contDiffOn_one_of_leftInverse_of_isInvertible hS hT (hf.of_le (by norm_num)) hg hgT hfg hinv
  have hd : ∀ y ∈ T, HasFDerivWithinAt g
      (ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y))) T y := by
    intro y hy
    obtain ⟨e, he⟩ := hinv y hy
    have hf' : HasFDerivWithinAt f (e : E →L[ℝ] F) S (g y) := by
      rw [he]
      exact ((hf.differentiableOn two_ne_zero) (g y) (hgT hy)).hasFDerivWithinAt
    have h := hf'.of_local_left_inverse ((hg y hy).tendsto_nhdsWithin hgT) hy
      (eventually_nhdsWithin_of_forall hfg)
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact h
  have hfd : ∀ y ∈ T, fderivWithin ℝ g T y =
      ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y)) :=
    fun y hy => (hd y hy).fderivWithin (hT y hy)
  have h2 : ContDiffOn ℝ ((1 : ℕ∞ω) + 1) g T := by
    rw [contDiffOn_succ_iff_fderivWithin hT]
    refine ⟨hg1.differentiableOn one_ne_zero, by simp, ?_⟩
    have hcf : ContDiffOn ℝ 1 (fun y => fderivWithin ℝ f S (g y)) T :=
      (hf.fderivWithin hS (by norm_num)).comp hg1 hgT
    have hc : ContDiffOn ℝ 1
        (fun y => ContinuousLinearMap.inverse (fderivWithin ℝ f S (g y))) T := by
      intro y hy
      exact ((hinv y hy).contDiffAt_map_inverse).comp_contDiffWithinAt
        (f := fun y => fderivWithin ℝ f S (g y)) y (hcf y hy)
    exact hc.congr fun y hy => hfd y hy
  exact (show ((1 : ℕ∞ω) + 1) = 2 by norm_num) ▸ h2

end Euclidean

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 2 N]

/-- **The inverse of an open `C²` injective map with invertible differentials is `C²`** on the
image (boundary and corners allowed). -/
theorem contMDiffOn_invFunOn_two_of_isInvertible_mfderiv [Nonempty M] {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I J 2 f U) (hinj : InjOn f U)
    (hopen : ∀ V ⊆ U, IsOpen V → IsOpen (f '' V))
    (hinv : ∀ x ∈ U, (mfderiv I J f x).IsInvertible) :
    ContMDiffOn J I 2 (invFunOn f U) (f '' U) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  let : IsManifold J 1 N := IsManifold.of_le (n := 2) (by norm_num)
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
  have hRf : ContDiffOn ℝ 2 (ψ ∘ f ∘ φ.symm) S := by
    have h1 : ContMDiffOn 𝓘(ℝ, E) J 2 (f ∘ φ.symm) S :=
      hf.comp ((contMDiffOn_extChartAt_symm x₀).mono inter_subset_left) fun y hy => hy.2.1
    have h : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E') 2 (ψ ∘ (f ∘ φ.symm)) S :=
      (contMDiffOn_extChartAt (n := 2) (x := y₀)).comp h1 (fun y hy => by
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
      ((hf.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt two_ne_zero) (hinv _ hzU)
  have hg2 := contDiffOn_two_of_leftInverse_of_isInvertible hS hT hRf hRg hmaps hfgT hinv'
  have hy₀T : ψ y₀ ∈ T := by
    refine ⟨mem_extChartAt_target y₀, ?_⟩
    simp only [mem_preimage, hψ, extChartAt_to_inv]
    exact ⟨hy₀, mem_extChartAt_source _⟩
  have hTnhds : T ∈ 𝓝[range J] (ψ y₀) := by
    refine inter_mem (extChartAt_target_mem_nhdsWithin y₀) ?_
    have hmem : y₀ ∈ f '' U ∩ g ⁻¹' φ.source := ⟨hy₀, mem_extChartAt_source _⟩
    exact mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds (hDT.mem_nhds hmem))
  exact (hg2 _ hy₀T).mono_of_mem_nhdsWithin hTnhds

end Manifold

end DifferentialGeometry.Topology.Manifold
