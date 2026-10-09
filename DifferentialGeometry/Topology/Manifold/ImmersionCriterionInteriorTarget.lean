import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.InteriorChart
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Immersion criterion at interior points of a target with boundary

`isImmersionAt_of_injective_mfderiv` (`ImmersionCriterion.lean:103`) needs a boundaryless target
model. Here the target model `J` may have boundary, but the image point is an interior point:

* `modelInverseInterior_GSF J n` — the inverse of `J` on the interior of its range, as a partial
  diffeomorphism `𝓘(𝕜, F) → J`;
* `affinePartialDiffeomorph_GSF B w` — the affine map `z ↦ B (z + w)` of a normed space, as a
  partial diffeomorphism on `univ`;
* `isImmersionAt_of_injective_mfderiv_of_isInteriorPoint_GSF` — a smooth map from a boundaryless
  manifold with injective differential at `x`, with `f x` an interior point, is an immersion at `x`.
  Route: the normal form of `isImmersionAt_of_injective_hasFDerivAt` in the extended chart at `x`
  and the INTERIOR chart at `f x` (`interiorChart`), then a translation of the domain chart and the
  matching translation and a linear change of the codomain chart that move the base point into
  `interior (range J)` (the normal form stays linear), then `J⁻¹` on the interior of its range;
* `isImmersion_of_injective_mfderiv_of_interior_GSF`, `isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF`
  — the global forms.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

/-- The inverse of a model with corners on the interior of its range, as a partial
diffeomorphism. -/
def modelInverseInterior_GSF {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
    (J : ModelWithCorners 𝕜 F G) (n : ℕ∞ω) : PartialDiffeomorph 𝓘(𝕜, F) J F G n where
  toPartialEquiv :=
    { toFun := J.symm
      invFun := J
      source := interior (range J)
      target := J ⁻¹' interior (range J)
      map_source' := fun y hy => by
        change J (J.symm y) ∈ interior (range J)
        rw [J.right_inv (interior_subset hy)]
        exact hy
      map_target' := fun z hz => hz
      left_inv' := fun y hy => J.right_inv (interior_subset hy)
      right_inv' := fun z _ => J.left_inv z }
  open_source := isOpen_interior
  open_target := isOpen_interior.preimage J.continuous
  contMDiffOn_toFun := (J.contMDiffOn_symm (n := n)).mono interior_subset
  contMDiffOn_invFun := J.contMDiff.contMDiffOn

/-- The inverse of a boundaryless model with corners, as a partial diffeomorphism on `univ` (the
private `modelInverse` of `ImmersionCriterion.lean`). -/
def modelInverse_GSF {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] (n : ℕ∞ω) :
    PartialDiffeomorph 𝓘(𝕜, E) I E H n where
  toPartialEquiv := I.toHomeomorph.symm.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    change ContMDiffOn 𝓘(𝕜, E) I n I.symm univ
    simpa only [I.range_eq_univ] using I.contMDiffOn_symm (n := n)
  contMDiffOn_invFun := I.contMDiff.contMDiffOn

/-- The affine map `z ↦ B (z + w)` as a partial diffeomorphism on `univ`. -/
def affinePartialDiffeomorph_GSF {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (B : F ≃L[𝕜] F) (w : F) (n : ℕ∞ω) :
    PartialDiffeomorph 𝓘(𝕜, F) 𝓘(𝕜, F) F F n where
  toPartialEquiv :=
    { toFun := fun z => B (z + w)
      invFun := fun y => B.symm y - w
      source := univ
      target := univ
      map_source' := fun _ _ => mem_univ _
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun z _ => by simp
      right_inv' := fun y _ => by simp }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun :=
    (B.contDiff.comp (contDiff_id.add contDiff_const)).contMDiff.contMDiffOn
  contMDiffOn_invFun :=
    (B.symm.contDiff.sub contDiff_const).contMDiff.contMDiffOn

/-- **Immersion criterion at an interior image point.** -/
theorem isImmersionAt_of_injective_mfderiv_of_isInteriorPoint_GSF
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H G M N : Type*} [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [I.Boundaryless] {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
    {f : M → N} (hn : n ≠ 0) (hf : ContMDiff I J n f) (x : M)
    (hinj : Function.Injective (mfderiv I J f x)) (hx : J.IsInteriorPoint (f x)) :
    IsImmersionAt I J n f x := by
  classical
  let c := extChartAtPartialDiffeomorph I n x
  let d := DifferentialGeometry.Manifold.interiorChart J n (f x)
  let g : E → F := d ∘ f ∘ c.symm
  let U : Set E := c.target ∩ c.symm ⁻¹' (f ⁻¹' d.source)
  have hU : IsOpen U := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm
    (d.open_source.preimage hf.continuous)
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hfd : f x ∈ d.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff J n (f x)).mpr hx
  have hcx : c.symm.toPartialEquiv (c.toPartialEquiv x) = x := c.left_inv hxc
  have hxU : c x ∈ U := by
    refine ⟨c.map_source hxc, ?_⟩
    change f (c.symm (c x)) ∈ d.source
    rw [hcx]
    exact hfd
  have hg : ContDiffOn ℝ n g U :=
    (d.contMDiffOn.comp
      (hf.comp_contMDiffOn (c.symm.contMDiffOn.mono inter_subset_left))
      (fun _ h => h.2)).contDiffOn
  have hdg : HasFDerivAt g (mfderiv I J f x) (c x) := by
    have h := (hf.mdifferentiableAt hn (x := x)).hasMFDerivAt
    have hw : HasFDerivWithinAt g (mfderiv I J f x) (range I) (c x) := h.2
    exact hw.hasFDerivAt (by rw [I.range_eq_univ]; exact Filter.univ_mem)
  let h := isImmersionAt_of_injective_hasFDerivAt hn hU hxU hg hdg hinj
  let hd : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n :=
    { toPartialEquiv := h.domChart.toPartialEquiv
      open_source := h.domChart.open_source
      open_target := h.domChart.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas }
  let hc : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F n :=
    { toPartialEquiv := h.codChart.toPartialEquiv
      open_source := h.codChart.open_source
      open_target := h.codChart.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas }
  -- the normal form, pointwise
  have hnf : ∀ z ∈ h.domChart.target, h.codChart (g (h.domChart.symm z)) = h.equiv (z, 0) := by
    intro z hz
    exact h.writtenInCharts (by simpa using hz)
  have hcxd : c x ∈ h.domChart.source := h.mem_domChart_source
  have hz₁ : h.domChart (c x) ∈ h.domChart.target := h.domChart.map_source hcxd
  have hbase : h.codChart (g (c x)) = h.equiv (h.domChart (c x), 0) := by
    have := hnf _ hz₁
    rwa [h.domChart.left_inv hcxd] at this
  -- a nonzero target vector and a nonzero point of `interior (range J)`
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : E)
  have hAu₀ : h.equiv (u₀, 0) ≠ 0 := by
    intro h0
    have : ((u₀, 0) : E × h.complement) = 0 := h.equiv.injective (h0.trans h.equiv.map_zero.symm)
    exact hu₀ (congrArg Prod.fst this)
  have hq : d (f x) ∈ interior (range J) := by
    have h1 : d (f x) ∈ interior (extChartAt J (f x)).target := d.map_source hfd
    exact interior_mono (extChartAt_target_subset_range (f x)) h1
  obtain ⟨p, hp, hp0⟩ : ∃ p ∈ interior (range J), p ≠ 0 := by
    by_cases hq0 : d (f x) = 0
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hq
      set v : F := h.equiv (u₀, 0)
      have hv : 0 < ‖v‖ := norm_pos_iff.mpr hAu₀
      refine ⟨(ε / (2 * ‖v‖)) • v, hball ?_, ?_⟩
      · rw [Metric.mem_ball, hq0, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        have hεv : ε / (2 * ‖v‖) * ‖v‖ = ε / 2 := by field_simp
        rw [hεv]
        linarith
      · exact smul_ne_zero (by positivity) hAu₀
    · exact ⟨d (f x), hq, hq0⟩
  obtain ⟨B, hB⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := ℝ) hAu₀ hp0
  -- the shifted charts
  set v : E := u₀ - h.domChart (c x) with hv
  let T₁ := affinePartialDiffeomorph_GSF (ContinuousLinearEquiv.refl ℝ E) v n
  let T₂ := affinePartialDiffeomorph_GSF B (h.equiv (v, 0)) n
  let α₀ := (((c.trans hd).trans T₁).trans (modelInverse_GSF I n)).toOpenPartialHomeomorph
  let β := ((d.trans hc).trans T₂).trans (modelInverseInterior_GSF J n)
  have hgx : g (c x) = d (f x) := by
    change d (f (c.symm (c x))) = d (f x)
    rw [hcx]
  have hT₂ : T₂ (hc (d (f x))) = p := by
    change B (h.codChart (d (f x)) + h.equiv (v, 0)) = p
    rw [← hgx, hbase, ← map_add, Prod.mk_add_mk, add_zero, hv, add_sub_cancel, hB]
  have hfxβ : f x ∈ β.source := by
    refine ⟨⟨⟨hfd, ?_⟩, mem_univ _⟩, ?_⟩
    · change d (f x) ∈ h.codChart.source
      rw [← hgx]
      exact h.mem_codChart_source
    · change T₂ (hc (d (f x))) ∈ interior (range J)
      rw [hT₂]
      exact hp
  let s : Set M := f ⁻¹' β.source
  have hs : IsOpen s := β.open_source.preimage hf.continuous
  let α := α₀.restr s
  have hα₀max : α₀ ∈ IsManifold.maximalAtlas I n M :=
    α₀.mem_maximalAtlas_of_contMDiffOn
      (((c.trans hd).trans T₁).trans (modelInverse_GSF I n)).contMDiffOn_toFun
      (((c.trans hd).trans T₁).trans (modelInverse_GSF I n)).contMDiffOn_invFun
  apply IsImmersionAtOfComplement.isImmersionAt (F := h.complement)
  apply IsImmersionAtOfComplement.mk_of_continuousAt hf.continuous.continuousAt
    (h.equiv.trans B) α β.toOpenPartialHomeomorph
  · refine ⟨⟨⟨⟨hxc, hcxd⟩, mem_univ _⟩, mem_univ _⟩, ?_⟩
    rw [hs.interior_eq]
    exact hfxβ
  · exact hfxβ
  · exact restr_mem_maximalAtlas (contDiffGroupoid n I) hα₀max hs
  · exact β.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      β.contMDiffOn_toFun β.contMDiffOn_invFun
  · intro z hz
    have hIz : I (I.symm z) = z := I.toHomeomorph.apply_symm_apply z
    have hz' : I.symm z ∈ α.target := hz.2
    rw [OpenPartialHomeomorph.restr_target, hs.interior_eq] at hz'
    obtain ⟨hz₀, hzs⟩ := hz'
    have hzt : z - v ∈ h.domChart.target := by
      have hmem := hz₀.2.2.1
      change I (I.symm z) - v ∈ h.domChart.target at hmem
      rwa [hIz] at hmem
    have hint : T₂ (hc (d (f (α₀.symm (I.symm z))))) ∈ interior (range J) := hzs.2
    change J (J.symm (T₂ (hc (d (f (α₀.symm (I.symm z))))))) = B (h.equiv (z, 0))
    rw [J.right_inv (interior_subset hint)]
    change B (h.codChart (g (h.domChart.symm (I (I.symm z) - v))) + h.equiv (v, 0)) =
      B (h.equiv (z, 0))
    rw [hIz, hnf _ hzt, ← map_add, Prod.mk_add_mk, add_zero, sub_add_cancel]

/-- **Immersion criterion into the interior**: global form. -/
theorem isImmersion_of_injective_mfderiv_of_interior_GSF
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H G M N : Type*} [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [I.Boundaryless] {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
    {f : M → N} (hn : n ≠ 0) (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hx : ∀ x, J.IsInteriorPoint (f x)) :
    IsImmersion I J n f :=
  isImmersion_of_isImmersionAt fun x =>
    isImmersionAt_of_injective_mfderiv_of_isInteriorPoint_GSF hn hf x (hinj x) (hx x)

/-- **Smooth embeddings into the interior**: a smooth topological embedding of a boundaryless
manifold with injective differential and values in the interior is a smooth embedding. -/
theorem isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H G M N : Type*} [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [I.Boundaryless] {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
    {f : M → N} (hn : n ≠ 0) (hf : ContMDiff I J n f) (hemb : Topology.IsEmbedding f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hx : ∀ x, J.IsInteriorPoint (f x)) :
    IsSmoothEmbedding I J n f :=
  ⟨isImmersion_of_injective_mfderiv_of_interior_GSF hn hf hinj hx, hemb⟩

end DifferentialGeometry.Topology.Manifold
