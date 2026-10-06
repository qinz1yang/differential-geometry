import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentAssembly

/-!
# Local sections of submersions at interior points of a manifold with boundary (lane S-RIM81, G2a)

The coordinate input of external review 81 (b) (`hV`, `hF`): near an INTERIOR point `p` of `W`, a
map `f : W → F` (`F` finite dimensional) with surjective differential at `p` has a continuous local
section `s` over an open neighbourhood `V` of `f p`, with `s y` in any prescribed neighbourhood of
`p` and `f (s y) = y`. (The tree's `exists_localSection_of_mfderiv_surjective` is for boundaryless
models; here the chart `extChartAt` at an interior point and the implicit function theorem are
used.)

* `exists_section_of_surjective_fderiv_RM1`: the Euclidean statement (strict derivative, implicit
  function);
* `exists_section_of_surjective_mvfderiv_RM1`: the manifold statement at an interior point;
* `exists_section_of_ne_zero_mvfderiv_RM1`: a real function with `dt ≠ 0`;
* `exists_section_of_surjective_pair_RM1`: a pair `(u, t)` of real functions with `(du, dt)` onto
  `ℝ²`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- **Euclidean local section** (implicit function theorem): `g` of class `C¹` at `x` with
surjective derivative has a continuous right inverse `s` on an open `V ∋ g x`, with values in any
neighbourhood `N` of `x`. -/
theorem exists_section_of_surjective_fderiv_RM1 {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {g : E → F} {x : E} (hg : ContDiffAt ℝ 1 g x)
    (hs : Surjective (fderiv ℝ g x)) {N : Set E} (hN : N ∈ 𝓝 x) :
    ∃ V : Set F, IsOpen V ∧ g x ∈ V ∧ ∃ s : F → E, ContinuousOn s V ∧
      ∀ y ∈ V, s y ∈ N ∧ g (s y) = y := by
  obtain ⟨O, hON, hOo, hxO⟩ := mem_nhds_iff.mp hN
  have hstrict : HasStrictFDerivAt g (fderiv ℝ g x) x := hg.hasStrictFDerivAt one_ne_zero
  have hrange : (fderiv ℝ g x).range = ⊤ := LinearMap.range_eq_top.mpr hs
  let e := hstrict.implicitToOpenPartialHomeomorph g (fderiv ℝ g x) hrange
  have hxe : x ∈ e.source := hstrict.mem_implicitToOpenPartialHomeomorph_source hrange
  have hea : e x = (g x, 0) := hstrict.implicitToOpenPartialHomeomorph_self hrange
  have hsx : e.symm (g x, 0) = x := by
    rw [← hea]
    exact e.left_inv hxe
  have hxt : (g x, (0 : (fderiv ℝ g x).ker)) ∈ e.target := by
    rw [← hea]
    exact e.map_source hxe
  have hc : Continuous fun y : F => (y, (0 : (fderiv ℝ g x).ker)) :=
    continuous_id.prodMk continuous_const
  refine ⟨(fun y : F => (y, (0 : (fderiv ℝ g x).ker))) ⁻¹' (e.target ∩ e.symm ⁻¹' O),
    (e.isOpen_inter_preimage_symm hOo).preimage hc, ⟨hxt, ?_⟩, fun y => e.symm (y, 0), ?_, ?_⟩
  · change e.symm (g x, 0) ∈ O
    rw [hsx]
    exact hxO
  · exact e.continuousOn_symm.comp hc.continuousOn fun y hy => hy.1
  · intro y hy
    refine ⟨hON hy.2, ?_⟩
    have h1 := congrArg Prod.fst (e.right_inv hy.1)
    rw [hstrict.implicitToOpenPartialHomeomorph_fst hrange] at h1
    exact h1

variable {E F HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- **Local section of a submersion at an interior point of a manifold with boundary.** -/
theorem exists_section_of_surjective_mvfderiv_RM1 {f : M → F} {p : M} (hp : I.IsInteriorPoint p)
    (hf : ContMDiffAt I 𝓘(ℝ, F) 1 f p) (hs : Surjective (mvfderiv I f p)) {N : Set M}
    (hN : N ∈ 𝓝 p) :
    ∃ V : Set F, IsOpen V ∧ f p ∈ V ∧ ∃ s : F → M, ContinuousOn s V ∧
      ∀ y ∈ V, s y ∈ N ∧ f (s y) = y := by
  have hrange : range I ∈ 𝓝 (extChartAt I p p) := range_mem_nhds_isInteriorPoint hp
  have htarget : (extChartAt I p).target ∈ 𝓝 (extChartAt I p p) :=
    mem_of_superset (isOpen_interior.mem_nhds (I.isInteriorPoint_iff.mp hp)) interior_subset
  have hgc : ContDiffAt ℝ 1 (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) := by
    have h := (contMDiffAt_iff.mp hf).2
    exact h.contDiffAt hrange
  have hmd : MDifferentiableAt I 𝓘(ℝ, F) f p := hf.mdifferentiableAt one_ne_zero
  have hsg : Surjective (fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
    have h := hs
    rw [hmd.mvfderiv, fderivWithin_of_mem_nhds hrange] at h
    exact h
  have hN' : (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' N ∈ 𝓝 (extChartAt I p p) := by
    refine inter_mem htarget ?_
    refine (continuousAt_extChartAt_symm p).preimage_mem_nhds ?_
    rw [(extChartAt I p).left_inv (mem_extChartAt_source p)]
    exact hN
  obtain ⟨V, hV, hVp, s, hsc, hspec⟩ := exists_section_of_surjective_fderiv_RM1 hgc hsg hN'
  have hfp : f ((extChartAt I p).symm (extChartAt I p p)) = f p := by
    rw [(extChartAt I p).left_inv (mem_extChartAt_source p)]
  refine ⟨V, hV, hfp ▸ hVp, fun y => (extChartAt I p).symm (s y), ?_, fun y hy => ?_⟩
  · exact (continuousOn_extChartAt_symm p).comp hsc fun y hy => (hspec y hy).1.1
  · exact ⟨(hspec y hy).1.2, (hspec y hy).2⟩

/-- **Local section of a real function with `dt ≠ 0`** at an interior point. -/
theorem exists_section_of_ne_zero_mvfderiv_RM1 {t : M → ℝ} {p : M} (hp : I.IsInteriorPoint p)
    (ht : ContMDiffAt I 𝓘(ℝ, ℝ) 1 t p) (hne : mvfderiv I t p ≠ 0) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ V : Set ℝ, IsOpen V ∧ t p ∈ V ∧ ∃ s : ℝ → M, ContinuousOn s V ∧
      ∀ y ∈ V, s y ∈ N ∧ t (s y) = y := by
  refine exists_section_of_surjective_mvfderiv_RM1 hp ht ?_ hN
  obtain ⟨v, hv⟩ : ∃ v, mvfderiv I t p v ≠ 0 := by
    by_contra h
    exact hne (ContinuousLinearMap.ext fun v => by_contra fun hv => h ⟨v, hv⟩)
  intro y
  refine ⟨(y / mvfderiv I t p v) • v, ?_⟩
  rw [map_smul]
  change y / mvfderiv I t p v * mvfderiv I t p v = y
  field_simp

/-- **Local section of a pair `(u, t)` of real functions** with `(du, dt)` onto `ℝ²` at an
interior point. -/
theorem exists_section_of_surjective_pair_RM1 {u t : M → ℝ} {p : M} (hp : I.IsInteriorPoint p)
    (hu : ContMDiffAt I 𝓘(ℝ, ℝ) 1 u p) (ht : ContMDiffAt I 𝓘(ℝ, ℝ) 1 t p)
    (hs : Surjective fun v : TangentSpace I p => (mvfderiv I u p v, mvfderiv I t p v))
    {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ (u p, t p) ∈ V ∧ ∃ s : ℝ × ℝ → M, ContinuousOn s V ∧
      ∀ y ∈ V, s y ∈ N ∧ u (s y) = y.1 ∧ t (s y) = y.2 := by
  have hf : ContMDiffAt I 𝓘(ℝ, ℝ × ℝ) 1 (fun x => (u x, t x)) p := hu.prodMk_space ht
  have hmu : MDifferentiableAt I 𝓘(ℝ, ℝ) u p := hu.mdifferentiableAt one_ne_zero
  have hmt : MDifferentiableAt I 𝓘(ℝ, ℝ) t p := ht.mdifferentiableAt one_ne_zero
  have hsurj : Surjective (mvfderiv I (fun x => (u x, t x)) p) := by
    intro w
    obtain ⟨v, hv⟩ := hs w
    exact ⟨v, (mvfderiv_pair_BAUGD hmu hmt v).trans hv⟩
  obtain ⟨V, hV, hVp, s, hsc, hspec⟩ := exists_section_of_surjective_mvfderiv_RM1 hp hf hsurj hN
  refine ⟨V, hV, hVp, s, hsc, fun y hy => ⟨(hspec y hy).1, ?_, ?_⟩⟩
  · exact congrArg Prod.fst (hspec y hy).2
  · exact congrArg Prod.snd (hspec y hy).2

end DifferentialGeometry.Geometry.Collapse
