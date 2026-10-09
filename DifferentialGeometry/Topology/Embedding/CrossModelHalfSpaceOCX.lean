import DifferentialGeometry.Topology.Embedding.CrossModelLinearOCX
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Cross-model immersions, part 2: codomain charts into the half-space (lane O-CROSS, G1)

Immersions into a manifold `N` modelled on `𝓡∂ n` whose normal form is known only in a
VECTOR chart `β : N ⊇ U ≅ V ⊆ ℝⁿ` (a partial diffeomorphism `(𝓡∂ n) → 𝓘(ℝ, ℝⁿ)`, e.g. a chart of a
boundaryless-modelled manifold transported by a diffeomorphism, or a half-space chart restricted to
the open half-space). Mathlib's normal form `ψ ∘ f ∘ φ⁻¹ = equiv ∘ (·, 0)` needs a half-space chart
`ψ`; when `β ∘ f ∘ φ⁻¹ = equiv (·, 0) + t` we

1. recentre the source chart by a translation `s` of its model that preserves `range I`
   (`modelAffineDiffeomorph_OCX` with `Λ = id`) so that `w = equiv (φ x + s, 0) ≠ 0`, absorbing
   `t` and `equiv (s, 0)` into `β`;
2. compose `β` with the Householder reflection `R` sending `w` to `‖w‖ e₀`
   (`halfSpaceReflection_OCX`, Mathlib's `reflection_sub`) and with the open half-space chart
   `openHalfSpace_OCX` (`{z | 0 < z 0} ≅ {q | 0 < q 0}`), restricted to where `(R β)₀ > 0`.

Main results:
* `isImmersionAtOfComplement_halfSpace_of_vectorChart_OCX` (linear normal form, `w ≠ 0`);
* `isImmersionAtOfComplement_halfSpace_of_affine_OCX` (affine normal form, a nonzero
  range-preserving translation `s₀` of the source model);
* HARD direction `IsImmersion.diffeomorph_comp_toHalfSpace_OCX`: an immersion into an
  `𝓘(ℝ, ℝⁿ)`-manifold followed by a diffeomorphism onto an `𝓡∂ n`-manifold;
* EASY direction `IsImmersion.diffeomorph_comp_fromHalfSpace_OCX`: an immersion into an
  `𝓡∂ n`-manifold followed by a diffeomorphism onto an `𝓘(ℝ, ℝⁿ)`-manifold (the half-space chart
  restricted to the open half-space; every point is interior by Mathlib's invariance of the
  interior under local diffeomorphisms);
* smooth-embedding forms, and the boundary translation `halfSpaceBoundaryShift_OCX` of `𝓡∂ (d+2)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace Manifold

section Affine

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- The affine diffeomorphism `v ↦ L v + t` of normed spaces. -/
def affineDiffeomorph_OCX (L : V ≃L[ℝ] W) (t : W) : Diffeomorph 𝓘(ℝ, V) 𝓘(ℝ, W) V W ∞ where
  toFun v := L v + t
  invFun w := L.symm (w - t)
  left_inv v := by simp
  right_inv w := by simp
  contMDiff_toFun := (L.contDiff.add contDiff_const).contMDiff
  contMDiff_invFun := (L.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff

theorem affineDiffeomorph_OCX_apply (L : V ≃L[ℝ] W) (t : W) (v : V) :
    affineDiffeomorph_OCX L t v = L v + t := rfl

end Affine

section HalfSpace

variable (n : ℕ) [NeZero n]

/-- The open half-space `{z | 0 < z 0}` of `ℝⁿ` as a partial diffeomorphism onto the open part
`{q | 0 < q 0}` of the model half-space. -/
def openHalfSpace_OCX :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n) (EuclideanSpace ℝ (Fin n))
      (EuclideanHalfSpace n) ∞ where
  toFun z := (𝓡∂ n).symm z
  invFun q := q.1
  source := {z | 0 < z 0}
  target := {q | 0 < q.1 0}
  map_source' z hz := by
    change 0 < ((𝓡∂ n).symm z).1 0
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hz)]
    exact hz
  map_target' _ hq := hq
  left_inv' z hz := by
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hz)]
  right_inv' q _ := by
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le q.2]
    rfl
  open_source := isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) 0)
  open_target := isOpen_lt continuous_const
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) 0).comp continuous_subtype_val)
  contMDiffOn_toFun := (𝓡∂ n).contMDiffOn_symm.mono (fun z hz => by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact le_of_lt (show (0 : ℝ) < z 0 from hz))
  contMDiffOn_invFun := (𝓡∂ n).contMDiff.contMDiffOn

/-- The Householder reflection sending `w` to `‖w‖ e₀`. -/
def halfSpaceReflection_OCX (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Submodule.reflection (ℝ ∙ (w - ‖w‖ • EuclideanSpace.single 0 1))ᗮ).toContinuousLinearEquiv

variable {n}

theorem halfSpaceReflection_OCX_self (w : EuclideanSpace ℝ (Fin n)) :
    halfSpaceReflection_OCX n w w = ‖w‖ • EuclideanSpace.single 0 1 := by
  apply Submodule.reflection_sub
  rw [norm_smul, norm_norm]
  simp

theorem halfSpaceReflection_OCX_self_pos {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) :
    0 < halfSpaceReflection_OCX n w w 0 := by
  rw [halfSpaceReflection_OCX_self]
  simpa using norm_pos_iff.mpr hw

/-- An interior point of an `𝓡∂ n`-manifold has positive first coordinate in every chart of
the maximal atlas. -/
theorem chart_pos_of_isInteriorPoint_OCX {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace n) N]
    {B : OpenPartialHomeomorph N (EuclideanHalfSpace n)}
    (hB : B ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ N) {y : N} (hy : y ∈ B.source)
    (hint : (𝓡∂ n).IsInteriorPoint y) : 0 < (B y).1 0 := by
  have hloc : IsLocalDiffeomorphAt (𝓡∂ n) (𝓡∂ n) ∞ B y :=
    PartialDiffeomorph.isLocalDiffeomorphAt (I := 𝓡∂ n) (J := 𝓡∂ n) (n := ∞)
      (chartPartialDiffeomorph_OCX B hB) hy
  have h := (hloc.isInteriorPoint_iff (by simp)).mp hint
  change extChartAt (𝓡∂ n) (B y) (B y) ∈ interior (range (𝓡∂ n)) at h
  rw [extChartAt_self_apply, interior_range_modelWithCornersEuclideanHalfSpace] at h
  exact h

end HalfSpace

section Kernel

variable {n : ℕ} [NeZero n]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N]

/-- **Vector-chart kernel** (linear normal form): if in a source chart `φ` and a vector chart `β`
of `N` the map reads `u ↦ equiv (u, 0)` and `equiv (φ x, 0) ≠ 0`, then `f` is an immersion at `x`
into the half-space-modelled `N`. -/
theorem isImmersionAtOfComplement_halfSpace_of_vectorChart_OCX
    [IsManifold (𝓡∂ n) ∞ N] {f : M → N} {x : M}
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : x ∈ φ.source)
    (β : PartialDiffeomorph (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N
      (EuclideanSpace ℝ (Fin n)) ∞)
    (hsrc : φ.source ⊆ f ⁻¹' β.source) (eq : (E × F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hwr : ∀ u ∈ (φ.extend I).target, β (f ((φ.extend I).symm u)) = eq (u, 0))
    (hne : eq (φ.extend I x, 0) ≠ 0) :
    IsImmersionAtOfComplement F I (𝓡∂ n) ∞ f x := by
  classical
  set w := eq (φ.extend I x, 0) with hw
  let R := halfSpaceReflection_OCX n w
  let ψ : PartialDiffeomorph (𝓡∂ n) (𝓡∂ n) N (EuclideanHalfSpace n) ∞ :=
    β.trans ((affineDiffeomorph_OCX R 0).toPartialDiffeomorph.trans (openHalfSpace_OCX n))
  have hψsrc : ∀ y, y ∈ ψ.source ↔ y ∈ β.source ∧ 0 < R (β y) 0 := by
    intro y
    change y ∈ β.source ∧ (β y ∈ univ ∧ R (β y) + 0 ∈ {z : EuclideanSpace ℝ (Fin n) | 0 < z 0})
      ↔ _
    simp
  have hψapp : ∀ y ∈ ψ.source, (𝓡∂ n) (ψ y) = R (β y) := by
    intro y hy
    have hpos := ((hψsrc y).mp hy).2
    change ((𝓡∂ n).symm (R (β y) + 0)).1 = R (β y)
    rw [add_zero, modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hpos)]
  have hxt : φ.extend I x ∈ (φ.extend I).target :=
    (φ.extend I).map_source (by rwa [φ.extend_source])
  have hfx : β (f x) = w := by
    have h := hwr _ hxt
    rwa [φ.extend_left_inv hx] at h
  have hfxψ : f x ∈ ψ.source := by
    rw [hψsrc, hfx]
    exact ⟨hsrc hx, halfSpaceReflection_OCX_self_pos hne⟩
  -- continuity of `f` on the source chart
  have hβf : ∀ y ∈ φ.source, β (f y) = eq (φ.extend I y, 0) := by
    intro y hy
    have h := hwr _ ((φ.extend I).map_source (by rwa [φ.extend_source]))
    rwa [φ.extend_left_inv hy] at h
  have hcont : ContinuousOn f φ.source := by
    have hin : ContinuousOn (fun y => eq (φ.extend I y, (0 : F))) φ.source :=
      eq.continuous.comp_continuousOn
        ((φ.continuousOn_extend.mono (by rw [φ.extend_source])).prodMk continuousOn_const)
    refine (β.symm.contMDiffOn.continuousOn.comp hin ?_).congr ?_
    · intro y hy
      change eq (φ.extend I y, 0) ∈ β.target
      rw [← hβf y hy]
      exact β.map_source (hsrc hy)
    · intro y hy
      change f y = β.symm (eq (φ.extend I y, 0))
      rw [← hβf y hy]
      exact (β.left_inv (hsrc hy)).symm
  set s₀ : Set M := φ.source ∩ f ⁻¹' ψ.source with hs₀
  have hs₀open : IsOpen s₀ := hcont.isOpen_inter_preimage φ.open_source ψ.open_source
  set φ' : OpenPartialHomeomorph M H := φ.restr s₀ with hφ'
  have hφ'mem : φ' ∈ IsManifold.maximalAtlas I ∞ M :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ I) hφ hs₀open
  have hφ'src : φ'.source = s₀ := by
    rw [hφ', OpenPartialHomeomorph.restr_source' φ s₀ hs₀open, hs₀, Set.inter_eq_right]
    exact fun _ hz => hz.1
  apply IsImmersionAtOfComplement.mk_of_charts (eq.trans R) φ' ψ.toOpenPartialHomeomorph
  · rw [hφ'src]
    exact ⟨hx, hfxψ⟩
  · exact hfxψ
  · exact hφ'mem
  · exact ψ.mem_maximalAtlas_OCX
  · intro y hy
    rw [hφ'src] at hy
    exact hy.2
  · intro u hu
    rw [OpenPartialHomeomorph.extend_target] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hu1' : I.symm u ∈ φ.target := hu1.1
    have hu1s : φ.symm (I.symm u) ∈ s₀ := by
      have h := hu1.2
      rwa [Set.mem_preimage, hs₀open.interior_eq] at h
    have hut : u ∈ (φ.extend I).target := by
      rw [OpenPartialHomeomorph.extend_target]
      exact ⟨hu1', hu2⟩
    change (𝓡∂ n) (ψ (f (φ.symm (I.symm u)))) = R (eq (u, 0))
    rw [hψapp _ hu1s.2]
    exact congrArg R (hwr u hut)

/-- **Recentred vector-chart kernel** (affine normal form, a given range-preserving translation
`s` of the source model with `equiv (φ x + s, 0) ≠ 0`). -/
theorem isImmersionAtOfComplement_halfSpace_of_shift_OCX
    [IsManifold I ∞ M] [IsManifold (𝓡∂ n) ∞ N] (s : E)
    (hsI : ∀ v, (ContinuousLinearEquiv.refl ℝ E) v + s ∈ range I ↔ v ∈ range I)
    {f : M → N} {x : M}
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : x ∈ φ.source)
    (β : PartialDiffeomorph (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N
      (EuclideanSpace ℝ (Fin n)) ∞)
    (hsrc : φ.source ⊆ f ⁻¹' β.source) (eq : (E × F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin n))
    (hwr : ∀ u ∈ (φ.extend I).target, β (f ((φ.extend I).symm u)) = eq (u, 0) + t)
    (hne : eq (φ.extend I x + s, 0) ≠ 0) :
    IsImmersionAtOfComplement F I (𝓡∂ n) ∞ f x := by
  classical
  let Θ := modelAffineDiffeomorph_OCX I I (ContinuousLinearEquiv.refl ℝ E) s hsI
  let φ' : OpenPartialHomeomorph M H := φ.trans Θ.toHomeomorph.toOpenPartialHomeomorph
  have hφ'src : φ'.source = φ.source := by
    simp [φ']
  have hφ'tgt : ∀ h, h ∈ φ'.target ↔ Θ.symm h ∈ φ.target := by
    intro h
    simp [φ']
  have hφ' : φ' ∈ IsManifold.maximalAtlas I ∞ M := by
    apply φ'.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn I I ∞ (Θ ∘ φ) φ'.source
      rw [hφ'src]
      exact Θ.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hφ)
    · change ContMDiffOn I I ∞ (φ.symm ∘ Θ.symm) φ'.target
      exact (contMDiffOn_symm_of_mem_maximalAtlas hφ).comp Θ.symm.contMDiff.contMDiffOn
        (fun h hh => (hφ'tgt h).mp hh)
  have hext : ∀ y, φ'.extend I y = φ.extend I y + s := by
    intro y
    change I (Θ (φ y)) = I (φ y) + s
    rw [modelAffineDiffeomorph_OCX_model]
    rfl
  have hsymm : ∀ u ∈ range I, (φ'.extend I).symm u = (φ.extend I).symm (u - s) := by
    intro u hu
    change φ.symm (Θ.symm (I.symm u)) = φ.symm (I.symm (u - s))
    rw [modelAffineDiffeomorph_OCX_symm_eq hu]
    rfl
  let β' := β.trans (affineDiffeomorph_OCX (ContinuousLinearEquiv.refl ℝ _)
    (eq (s, 0) - t)).toPartialDiffeomorph
  have hβ'src : β'.source = β.source := by
    change β.source ∩ β ⁻¹' univ = β.source
    simp
  have hβ'app : ∀ y, β' y = β y + (eq (s, 0) - t) := fun _ => rfl
  refine isImmersionAtOfComplement_halfSpace_of_vectorChart_OCX φ' hφ' (hφ'src ▸ hx) β' ?_ eq
    ?_ ?_
  · rw [hφ'src, hβ'src]
    exact hsrc
  · intro u hu
    rw [OpenPartialHomeomorph.extend_target] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hus : u - s ∈ (φ.extend I).target := by
      rw [OpenPartialHomeomorph.extend_target]
      refine ⟨?_, ?_⟩
      · have h := (hφ'tgt _).mp hu1
        rw [modelAffineDiffeomorph_OCX_symm_eq hu2] at h
        exact h
      · rw [← hsI (u - s)]
        simpa using hu2
    rw [hβ'app, hsymm u hu2, hwr _ hus]
    have h2 : eq (u - s, 0) + eq (s, 0) = eq (u, 0) := by
      rw [← map_add]
      congr 1
      simp
    rw [← h2]
    abel
  · rw [hext]
    exact hne

/-- **Affine vector-chart kernel**: a nonzero translation `s₀` of the source model preserving
`range I` suffices to recentre; the normal form may carry any translation `t`. -/
theorem isImmersionAtOfComplement_halfSpace_of_affine_OCX
    [IsManifold I ∞ M] [IsManifold (𝓡∂ n) ∞ N] (s₀ : E) (hs₀ : s₀ ≠ 0)
    (hs₀I : ∀ v, v + s₀ ∈ range I ↔ v ∈ range I) {f : M → N} {x : M}
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : x ∈ φ.source)
    (β : PartialDiffeomorph (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N
      (EuclideanSpace ℝ (Fin n)) ∞)
    (hsrc : φ.source ⊆ f ⁻¹' β.source) (eq : (E × F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin n))
    (hwr : ∀ u ∈ (φ.extend I).target, β (f ((φ.extend I).symm u)) = eq (u, 0) + t) :
    IsImmersionAtOfComplement F I (𝓡∂ n) ∞ f x := by
  by_cases h0 : eq (φ.extend I x, 0) = 0
  · refine isImmersionAtOfComplement_halfSpace_of_shift_OCX s₀ (fun v => hs₀I v) φ hφ hx β
      hsrc eq t hwr ?_
    have hadd : eq (φ.extend I x + s₀, 0) = eq (φ.extend I x, 0) + eq (s₀, 0) := by
      rw [← map_add]
      congr 1
      simp
    rw [hadd, h0, zero_add]
    intro h
    apply hs₀
    have h' : ((s₀, 0) : E × F) = 0 := eq.injective (h.trans (map_zero eq).symm)
    exact congrArg Prod.fst h'
  · refine isImmersionAtOfComplement_halfSpace_of_shift_OCX 0 (fun v => by simp) φ hφ hx β
      hsrc eq t hwr ?_
    rw [add_zero]
    exact h0

end Kernel

section Directions

variable {n : ℕ} [NeZero n]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N₀ : Type*} [TopologicalSpace N₀] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₀]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N]

/-- **HARD direction**: an immersion into a manifold modelled on `𝓘(ℝ, ℝⁿ)` followed by a
diffeomorphism onto a manifold modelled on `𝓡∂ n` is an immersion (the source model needs one
nonzero range-preserving translation `s₀`, e.g. a boundary direction of `𝓡∂ (d + 2)`). -/
theorem IsImmersion.diffeomorph_comp_toHalfSpace_OCX [IsManifold I ∞ M]
    [IsManifold (𝓡∂ n) ∞ N]
    (s₀ : E) (hs₀ : s₀ ≠ 0) (hs₀I : ∀ v, v + s₀ ∈ range I ↔ v ∈ range I) {f : M → N₀}
    (hf : IsImmersion I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (e : Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n) N₀ N ∞) :
    IsImmersion I (𝓡∂ n) ∞ (e ∘ f) := by
  obtain ⟨F, hFg, hFs, hF⟩ := hf
  let _ := hFg
  let _ := hFs
  refine IsImmersionOfComplement.isImmersion (F := F) (fun x => ?_)
  let h := hF x
  let β := e.symm.toPartialDiffeomorph.trans
    (chartPartialDiffeomorph_OCX h.codChart h.codChart_mem_maximalAtlas)
  refine isImmersionAtOfComplement_halfSpace_of_affine_OCX s₀ hs₀ hs₀I h.domChart
    h.domChart_mem_maximalAtlas h.mem_domChart_source β ?_ h.equiv 0 ?_
  · intro y hy
    change e (f y) ∈ univ ∧ e.symm (e (f y)) ∈ h.codChart.source
    rw [e.symm_apply_apply]
    exact ⟨mem_univ _, h.source_subset_preimage_source hy⟩
  · intro u hu
    change h.codChart (e.symm (e (f ((h.domChart.extend I).symm u)))) = h.equiv (u, 0) + 0
    rw [e.symm_apply_apply, add_zero]
    exact h.writtenInCharts hu

/-- **EASY direction**: an immersion into a manifold modelled on `𝓡∂ n` followed by a
diffeomorphism onto a manifold modelled on `𝓘(ℝ, ℝⁿ)` is an immersion. -/
theorem IsImmersion.diffeomorph_comp_fromHalfSpace_OCX
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N₀] {f : M → N}
    (hf : IsImmersion I (𝓡∂ n) ∞ f)
    (e : Diffeomorph (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N N₀ ∞) :
    IsImmersion I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (e ∘ f) := by
  obtain ⟨F, hFg, hFs, hF⟩ := hf
  let _ := hFg
  let _ := hFs
  have hbl : BoundarylessManifold (𝓡∂ n) N := e.symm.boundarylessManifold (by simp)
  refine IsImmersionOfComplement.isImmersion (F := F) (fun x => ?_)
  let h := hF x
  let B := h.codChart
  let ψ' := (chartPartialDiffeomorph_OCX B h.codChart_mem_maximalAtlas).trans
    (openHalfSpace_OCX n).symm
  let ψ := e.symm.toPartialDiffeomorph.trans ψ'
  have hψ'src : ∀ y, y ∈ ψ'.source ↔ y ∈ B.source ∧ 0 < (B y).1 0 := fun _ => Iff.rfl
  have hfx : f x ∈ ψ'.source := by
    rw [hψ'src]
    exact ⟨h.mem_codChart_source, chart_pos_of_isInteriorPoint_OCX
      h.codChart_mem_maximalAtlas h.mem_codChart_source BoundarylessManifold.isInteriorPoint⟩
  set s₀ : Set M := h.domChart.source ∩ f ⁻¹' ψ'.source with hs₀
  have hs₀open : IsOpen s₀ :=
    h.continuousOn.isOpen_inter_preimage h.domChart.open_source ψ'.open_source
  set φ' : OpenPartialHomeomorph M H := h.domChart.restr s₀ with hφ'
  have hφ'mem : φ' ∈ IsManifold.maximalAtlas I ∞ M :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ I) h.domChart_mem_maximalAtlas hs₀open
  have hφ'src : φ'.source = s₀ := by
    rw [hφ', OpenPartialHomeomorph.restr_source' _ s₀ hs₀open, hs₀, Set.inter_eq_right]
    exact fun _ hz => hz.1
  have hψsrc : ∀ y, f y ∈ ψ'.source → e (f y) ∈ ψ.source := by
    intro y hy
    change e (f y) ∈ univ ∧ e.symm (e (f y)) ∈ ψ'.source
    rw [e.symm_apply_apply]
    exact ⟨mem_univ _, hy⟩
  apply IsImmersionAtOfComplement.mk_of_charts h.equiv φ' ψ.toOpenPartialHomeomorph
  · rw [hφ'src]
    exact ⟨h.mem_domChart_source, hfx⟩
  · exact hψsrc x hfx
  · exact hφ'mem
  · exact ψ.mem_maximalAtlas_OCX
  · intro y hy
    rw [hφ'src] at hy
    exact hψsrc y hy.2
  · intro u hu
    rw [OpenPartialHomeomorph.extend_target] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hut : u ∈ (h.domChart.extend I).target := by
      rw [OpenPartialHomeomorph.extend_target]
      exact ⟨hu1.1, hu2⟩
    change (B (e.symm (e (f (h.domChart.symm (I.symm u)))))).1 = h.equiv (u, 0)
    rw [e.symm_apply_apply]
    exact h.writtenInCharts hut

/-- Smooth-embedding form of the HARD direction. -/
theorem IsSmoothEmbedding.diffeomorph_comp_toHalfSpace_OCX [IsManifold I ∞ M]
    [IsManifold (𝓡∂ n) ∞ N]
    (s₀ : E) (hs₀ : s₀ ≠ 0) (hs₀I : ∀ v, v + s₀ ∈ range I ↔ v ∈ range I) {f : M → N₀}
    (hf : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (e : Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n) N₀ N ∞) :
    IsSmoothEmbedding I (𝓡∂ n) ∞ (e ∘ f) :=
  ⟨hf.isImmersion.diffeomorph_comp_toHalfSpace_OCX s₀ hs₀ hs₀I e,
    e.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩

/-- Smooth-embedding form of the EASY direction. -/
theorem IsSmoothEmbedding.diffeomorph_comp_fromHalfSpace_OCX
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N₀] {f : M → N}
    (hf : IsSmoothEmbedding I (𝓡∂ n) ∞ f)
    (e : Diffeomorph (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N N₀ ∞) :
    IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (e ∘ f) :=
  ⟨hf.isImmersion.diffeomorph_comp_fromHalfSpace_OCX e,
    e.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩

end Directions

section Shifts

/-- The boundary direction `e₁` of `𝓡∂ (d + 2)`. -/
def halfSpaceBoundaryShift_OCX (d : ℕ) : EuclideanSpace ℝ (Fin (d + 2)) :=
  EuclideanSpace.single 1 1

theorem halfSpaceBoundaryShift_OCX_ne_zero (d : ℕ) : halfSpaceBoundaryShift_OCX d ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 2)) => v 1) h
  simp [halfSpaceBoundaryShift_OCX] at h1

theorem halfSpaceBoundaryShift_OCX_range {d : ℕ} {v : EuclideanSpace ℝ (Fin (d + 2))} :
    v + halfSpaceBoundaryShift_OCX d ∈ range (𝓡∂ (d + 2)) ↔ v ∈ range (𝓡∂ (d + 2)) := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  simp [halfSpaceBoundaryShift_OCX]

/-- Any nonzero translation preserves the range of a boundaryless self model. -/
theorem modelWithCornersSelf_shift_range_OCX {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : E) {v : E} : v + s ∈ range 𝓘(ℝ, E) ↔ v ∈ range 𝓘(ℝ, E) := by
  simp

/-- A range-preserving translation of the first factor of a product model. -/
theorem prod_shift_range_OCX {E H E' H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {s : E}
    (hs : ∀ v, v + s ∈ range I ↔ v ∈ range I) {v : E × E'} :
    v + (s, 0) ∈ range (I.prod I') ↔ v ∈ range (I.prod I') := by
  rw [ModelWithCorners.range_prod]
  simp [hs]

end Shifts

end Manifold
