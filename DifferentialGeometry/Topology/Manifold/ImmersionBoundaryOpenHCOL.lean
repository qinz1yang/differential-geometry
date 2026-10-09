import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionInterior

/-!
# Equal-dimension immersions are open at boundary points that go to boundary points
(lane S-COLLAR, G1, suffix `_HCOL`)

The tree has the boundaryless inverse function theorem (`isOpen_range_of_isImmersion`, …); the
half-collar of a boundary torus needs the boundary version.  The immersion chart data of Mathlib
(`IsImmersionAtOfComplement`) already says that in the extended charts `f` is the LINEAR map
`Lc = h.equiv (·, 0)` on the target of the domain chart.  So openness of `f` at `x` reduces to one
statement about `Lc` and the ranges of the two models:

* `half_space_reflect_HCOL` (pure linear algebra): a linear isomorphism `L` with
  `ℓ₂ (L p) = 0 = ℓ₁ p` that maps the inner cone of `{ℓ₁ ≥ 0}` at `p` into `{ℓ₂ ≥ 0}` satisfies
  `0 ≤ ℓ₂ (L z) → 0 ≤ ℓ₁ z` for ALL `z`;
* `IsImmersionAtOfComplement.nhds_le_map_HCOL` (filter form of the chart argument): if
  `Lc '' range I ∈ 𝓝[range J] (Lc (chart x))` then `𝓝 (f x) ≤ map f (𝓝 x)`;
* **`IsImmersionAt.nhds_le_map_of_halfSpace_HCOL`**: models whose range is `univ` or a closed
  half-space (`𝓡∂ n`, `torusModel.prod (𝓡∂ 1)`, …), equal dimension, and `x` a boundary point only
  if `f x` is one ⟹ `f` is open at `x` (`𝓝 (f x) ≤ map f (𝓝 x)`).

No hypothesis restates the conclusion; every hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace Manifold

universe u

/-- **Linear algebra of half-spaces.**  A linear isomorphism `L : E ≃ F` that sends the inner cone
of `{ℓ₁ ≥ 0}` at a boundary point `p` (with `L p` on `{ℓ₂ = 0}`) into `{ℓ₂ ≥ 0}` reflects the
half-spaces: `0 ≤ ℓ₂ (L z) → 0 ≤ ℓ₁ z`. -/
theorem half_space_reflect_HCOL {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (ℓ₁ : E →ₗ[ℝ] ℝ) (ℓ₂ : F →ₗ[ℝ] ℝ) (L : E ≃ₗ[ℝ] F) (hℓ₁ : ℓ₁ ≠ 0)
    (hℓ₂ : ℓ₂ ≠ 0) (p : E) (hp : ℓ₂ (L p) = 0)
    (hcone : ∀ v, 0 ≤ ℓ₁ v → ∃ ε : ℝ, 0 < ε ∧ 0 ≤ ℓ₂ (L (p + ε • v))) (z : E)
    (hz : 0 ≤ ℓ₂ (L z)) : 0 ≤ ℓ₁ z := by
  set m : E →ₗ[ℝ] ℝ := ℓ₂.comp L.toLinearMap with hm
  have hmv : ∀ v, m v = ℓ₂ (L v) := fun v => rfl
  have hm0 : ∀ v, 0 ≤ ℓ₁ v → 0 ≤ m v := by
    intro v hv
    obtain ⟨ε, hε, h⟩ := hcone v hv
    have h1 : ℓ₂ (L (p + ε • v)) = ε * m v := by
      rw [map_add, map_smul, map_add, map_smul, hp, zero_add, smul_eq_mul]
      rfl
    rw [h1] at h
    exact (mul_nonneg_iff_of_pos_left hε).mp h
  obtain ⟨x, hx⟩ : ∃ x, ℓ₁ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hℓ₁ (LinearMap.ext hcon)
  set e : E := (ℓ₁ x)⁻¹ • x with he_def
  have he : ℓ₁ e = 1 := by
    rw [he_def, map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
  have hker : ∀ v, m v = ℓ₁ v * m e := by
    intro v
    have h0 : ℓ₁ (v - ℓ₁ v • e) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, he, mul_one, sub_self]
    have h1 : 0 ≤ m (v - ℓ₁ v • e) := hm0 _ (by rw [h0])
    have h2 : 0 ≤ m (-(v - ℓ₁ v • e)) := hm0 _ (by rw [map_neg, h0, neg_zero])
    rw [map_neg] at h2
    have h3 : m (v - ℓ₁ v • e) = 0 := le_antisymm (by linarith) h1
    rw [map_sub, map_smul, smul_eq_mul] at h3
    linarith
  have hc : 0 ≤ m e := hm0 e (by rw [he]; exact zero_le_one)
  have hc0 : m e ≠ 0 := by
    intro h
    apply hℓ₂
    ext w
    obtain ⟨v, rfl⟩ := L.surjective w
    have h4 := hker v
    rw [h, mul_zero] at h4
    exact h4
  have hcpos : 0 < m e := lt_of_le_of_ne hc (Ne.symm hc0)
  have h5 : 0 ≤ m z := hz
  rw [hker z] at h5
  exact (mul_nonneg_iff_of_pos_right hcpos).mp h5

section Charts

variable {E : Type*} {E'' : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E'' G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {f : M → N} {x : M}

/-- **Filter form of the chart argument.**  If in the immersion charts at `x` the linear map `Lc`
(equal to `h.equiv (·, 0)`) satisfies `Lc '' range I ∈ 𝓝[range J] (Lc (chart x))`, then `f` is open
at `x`: `𝓝 (f x) ≤ map f (𝓝 x)`. -/
theorem IsImmersionAtOfComplement.nhds_le_map_HCOL {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : IsImmersionAtOfComplement F I J ∞ f x) (Lc : E ≃L[ℝ] E'')
    (hLc : ∀ z, Lc z = h.equiv (z, 0))
    (hR : Lc '' range I ∈ 𝓝[range J] (Lc (h.domChart.extend I x))) :
    𝓝 (f x) ≤ Filter.map f (𝓝 x) := by
  have hxφ : x ∈ h.domChart.source := h.mem_domChart_source
  have hfxψ : f x ∈ h.codChart.source := h.mem_codChart_source
  have hwr : ∀ y ∈ h.domChart.source,
      h.codChart.extend J (f y) = Lc (h.domChart.extend I y) := by
    intro y hy
    have hyT : h.domChart.extend I y ∈ (h.domChart.extend I).target :=
      (h.domChart.extend I).map_source (by rwa [h.domChart.extend_source])
    have h1 := h.writtenInCharts hyT
    simp only [Function.comp_apply] at h1
    rw [(h.domChart.extend I).left_inv (by rwa [h.domChart.extend_source])] at h1
    rw [h1, hLc]
  have h1 : Filter.map (h.codChart.extend J) (𝓝 (f x)) =
      𝓝[range J] (Lc (h.domChart.extend I x)) := by
    rw [h.codChart.map_extend_nhds hfxψ, hwr x hxφ]
  have h2 : Filter.map (h.codChart.extend J) (Filter.map f (𝓝 x)) =
      𝓝[Lc '' range I] (Lc (h.domChart.extend I x)) := by
    have h3 : Filter.map Lc (𝓝[range I] (h.domChart.extend I x)) =
        𝓝[Lc '' range I] (Lc (h.domChart.extend I x)) :=
      Lc.toHomeomorph.isEmbedding.map_nhdsWithin_eq _ _
    rw [← h3, ← h.domChart.map_extend_nhds hxφ, Filter.map_map, Filter.map_map]
    apply Filter.map_congr
    filter_upwards [h.domChart.open_source.mem_nhds hxφ] with y hy
    exact hwr y hy
  have hinj : InjOn (h.codChart.extend J) h.codChart.source := by
    simpa only [h.codChart.extend_source] using (h.codChart.extend J).injOn
  have hs1 : h.codChart.source ∈ 𝓝 (f x) := h.codChart.open_source.mem_nhds hfxψ
  have hs2 : h.codChart.source ∈ Filter.map f (𝓝 x) := by
    rw [Filter.mem_map]
    exact Filter.mem_of_superset (h.domChart.open_source.mem_nhds hxφ)
      h.source_subset_preimage_source
  refine (Filter.map_le_map_iff_of_injOn hs1 hs2 hinj).mp ?_
  rw [h1, h2]
  exact nhdsWithin_le_of_mem hR

/-- The complement of an equal-dimension immersion is trivial: `h.equiv (·, 0)` is a continuous
linear isomorphism `E ≃L E''`. -/
theorem IsImmersionAtOfComplement.exists_linearEquiv_HCOL {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'']
    (h : IsImmersionAtOfComplement F I J ∞ f x) (hdim : Module.finrank ℝ E = Module.finrank ℝ E'') :
    ∃ Lc : E ≃L[ℝ] E'', ∀ z, Lc z = h.equiv (z, 0) := by
  let L₀ : E →ₗ[ℝ] E'' :=
    (h.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E F)).toLinearMap
  have hinj : Function.Injective L₀ := h.equiv.injective.comp (Prod.mk_left_injective 0)
  exact ⟨(L₀.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv, fun z => by
    change (L₀.linearEquivOfInjective hinj hdim) z = _
    rw [LinearMap.linearEquivOfInjective_apply]
    rfl⟩

/-- **Openness at a point, half-space models.**  `I`, `J` are models with corners whose ranges are
`univ` (for `J`) or closed half-spaces `{ℓ ≥ 0}`, of equal finite dimension; `f` is an immersion at
`x`, and `x` is a boundary point only if `f x` is one.  Then `f` is open at `x`. -/
theorem IsImmersionAt.nhds_le_map_of_halfSpace_HCOL [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E''] [IsManifold I ∞ M] [IsManifold J ∞ N]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E'')
    (hI : ∃ ℓ₁ : E →L[ℝ] ℝ, ℓ₁ ≠ 0 ∧ range I = {v | 0 ≤ ℓ₁ v})
    (hJ : range J = univ ∨ ∃ ℓ₂ : E'' →L[ℝ] ℝ, ℓ₂ ≠ 0 ∧ range J = {w | 0 ≤ ℓ₂ w})
    (hf : IsImmersionAt I J ∞ f x) (hbd : I.IsBoundaryPoint x → J.IsBoundaryPoint (f x)) :
    𝓝 (f x) ≤ Filter.map f (𝓝 x) := by
  obtain ⟨F, _, _, h⟩ := hf
  obtain ⟨Lc, hLc⟩ := h.exists_linearEquiv_HCOL hdim
  refine h.nhds_le_map_HCOL Lc hLc ?_
  have hxφ : x ∈ h.domChart.source := h.mem_domChart_source
  have hfxψ : f x ∈ h.codChart.source := h.mem_codChart_source
  set A := h.domChart.extend I with hA
  set B := h.codChart.extend J with hB
  have hz : A x ∈ A.target := A.map_source (by rwa [hA, h.domChart.extend_source])
  have hwr : B (f x) = Lc (A x) := by
    have hT := h.writtenInCharts hz
    simp only [Function.comp_apply] at hT
    rw [A.left_inv (by rwa [hA, h.domChart.extend_source])] at hT
    rw [hT, hLc]
  have hintI : I.IsInteriorPoint x ↔ A x ∈ interior A.target :=
    ModelWithCorners.isInteriorPoint_iff_of_mem_maximalAtlas (I := I) (by simp)
      h.domChart_mem_maximalAtlas hxφ
  have hintJ : J.IsInteriorPoint (f x) ↔ B (f x) ∈ interior B.target :=
    ModelWithCorners.isInteriorPoint_iff_of_mem_maximalAtlas (I := J) (by simp)
      h.codChart_mem_maximalAtlas hfxψ
  by_cases hxI : I.IsInteriorPoint x
  · -- interior point: the image of the interior of the chart target is a neighbourhood
    have hzint := hintI.mp hxI
    have h1 : Lc '' interior A.target ∈ 𝓝 (Lc (A x)) :=
      Lc.toHomeomorph.isOpenMap.image_mem_nhds (isOpen_interior.mem_nhds hzint)
    have h2 : Lc '' range I ∈ 𝓝 (Lc (A x)) :=
      Filter.mem_of_superset h1
        (image_mono (interior_subset.trans h.domChart.extend_target_subset_range))
    exact mem_nhdsWithin_of_mem_nhds h2
  · have hbdI : I.IsBoundaryPoint x := (I.isInteriorPoint_or_isBoundaryPoint x).resolve_left hxI
    have hJb : J.IsBoundaryPoint (f x) := hbd hbdI
    rcases hJ with hJ0 | ⟨ℓ₂, hℓ₂, hJr⟩
    · exfalso
      have hJb' : extChartAt J (f x) (f x) ∈ frontier (range J) := hJb
      rw [hJ0, frontier_univ] at hJb'
      exact notMem_empty _ hJb'
    obtain ⟨ℓ₁, hℓ₁, hIr⟩ := hI
    have hzr : A x ∈ range I := h.domChart.extend_target_subset_range hz
    have hwT : B (f x) ∈ B.target := B.map_source (by rwa [hB, h.codChart.extend_source])
    have hwr' : B (f x) ∈ range J := h.codChart.extend_target_subset_range hwT
    -- the chart coordinates of boundary points lie on the boundary hyperplanes
    have hℓ₁z : ℓ₁ (A x) = 0 := by
      have hge : 0 ≤ ℓ₁ (A x) := by
        have := hzr
        rw [hIr] at this
        exact this
      by_contra hne
      have hpos : 0 < ℓ₁ (A x) := lt_of_le_of_ne hge (Ne.symm hne)
      have hopen : IsOpen ({w | 0 < ℓ₁ w} ∩ I.symm ⁻¹' h.domChart.target) :=
        (isOpen_lt continuous_const ℓ₁.continuous).inter
          (h.domChart.open_target.preimage I.continuous_symm)
      have hsub : {w | 0 < ℓ₁ w} ∩ I.symm ⁻¹' h.domChart.target ⊆ A.target := by
        intro w hw
        rw [hA, h.domChart.extend_target]
        refine ⟨hw.2, ?_⟩
        rw [hIr]
        exact le_of_lt (show 0 < ℓ₁ w from hw.1)
      have hzmem : A x ∈ {w | 0 < ℓ₁ w} ∩ I.symm ⁻¹' h.domChart.target := by
        refine ⟨hpos, ?_⟩
        have := hz
        rw [hA, h.domChart.extend_target] at this
        exact this.1
      exact (I.isInteriorPoint_iff_not_isBoundaryPoint x).mp
        (hintI.mpr (mem_interior.mpr ⟨_, hsub, hopen, hzmem⟩)) hbdI
    have hℓ₂w : ℓ₂ (Lc (A x)) = 0 := by
      rw [← hwr]
      have hge : 0 ≤ ℓ₂ (B (f x)) := by
        have := hwr'
        rw [hJr] at this
        exact this
      by_contra hne
      have hpos : 0 < ℓ₂ (B (f x)) := lt_of_le_of_ne hge (Ne.symm hne)
      have hopen : IsOpen ({w | 0 < ℓ₂ w} ∩ J.symm ⁻¹' h.codChart.target) :=
        (isOpen_lt continuous_const ℓ₂.continuous).inter
          (h.codChart.open_target.preimage J.continuous_symm)
      have hsub : {w | 0 < ℓ₂ w} ∩ J.symm ⁻¹' h.codChart.target ⊆ B.target := by
        intro w hw
        rw [hB, h.codChart.extend_target]
        refine ⟨hw.2, ?_⟩
        rw [hJr]
        exact le_of_lt (show 0 < ℓ₂ w from hw.1)
      have hzmem : B (f x) ∈ {w | 0 < ℓ₂ w} ∩ J.symm ⁻¹' h.codChart.target := by
        refine ⟨hpos, ?_⟩
        have := hwT
        rw [hB, h.codChart.extend_target] at this
        exact this.1
      exact (J.isInteriorPoint_iff_not_isBoundaryPoint (f x)).mp
        (hintJ.mpr (mem_interior.mpr ⟨_, hsub, hopen, hzmem⟩)) hJb
    -- the inner cone at the chart point is mapped into the half-space
    have hcone : ∀ v, 0 ≤ ℓ₁ v → ∃ ε : ℝ, 0 < ε ∧ 0 ≤ ℓ₂ (Lc (A x + ε • v)) := by
      intro v hv
      have hO : IsOpen (I.symm ⁻¹' h.domChart.target) :=
        h.domChart.open_target.preimage I.continuous_symm
      have hzO : A x ∈ I.symm ⁻¹' h.domChart.target := by
        have := hz
        rw [hA, h.domChart.extend_target] at this
        exact this.1
      have hlim : Tendsto (fun ε : ℝ => A x + ε • v) (𝓝[>] 0) (𝓝 (A x)) := by
        have hc : Continuous fun ε : ℝ => A x + ε • v :=
          continuous_const.add (continuous_id.smul continuous_const)
        have := hc.tendsto 0
        simp only [zero_smul, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hε1, hε2⟩ := ((hlim.eventually (hO.mem_nhds hzO)).and
        self_mem_nhdsWithin).exists
      have hε : 0 < ε := hε2
      refine ⟨ε, hε, ?_⟩
      have hmem : A x + ε • v ∈ A.target := by
        rw [hA, h.domChart.extend_target]
        refine ⟨hε1, ?_⟩
        rw [hIr]
        change 0 ≤ ℓ₁ (A x + ε • v)
        rw [map_add, map_smul, hℓ₁z, zero_add, smul_eq_mul]
        exact mul_nonneg hε.le hv
      have hmem' : Lc (A x + ε • v) ∈ B.target := by
        rw [hLc]
        exact h.map_target_subset_target ⟨_, hmem, rfl⟩
      have := h.codChart.extend_target_subset_range hmem'
      rw [hJr] at this
      exact this
    have hrefl := half_space_reflect_HCOL (ℓ₁ : E →ₗ[ℝ] ℝ) (ℓ₂ : E'' →ₗ[ℝ] ℝ)
      Lc.toLinearEquiv (fun h0 => hℓ₁ (ContinuousLinearMap.coe_injective h0))
      (fun h0 => hℓ₂ (ContinuousLinearMap.coe_injective h0)) (A x) hℓ₂w hcone
    have hsub : range J ⊆ Lc '' range I := by
      intro w hw
      refine ⟨Lc.symm w, ?_, Lc.apply_symm_apply w⟩
      rw [hIr]
      change 0 ≤ ℓ₁ (Lc.symm w)
      refine hrefl (Lc.symm w) ?_
      change 0 ≤ ℓ₂ (Lc (Lc.symm w))
      rw [Lc.apply_symm_apply]
      rw [hJr] at hw
      exact hw
    exact Filter.mem_of_superset self_mem_nhdsWithin hsub

end Charts

end Manifold
