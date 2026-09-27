import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MiddleSphereSliceEmbedding

set_option autoImplicit false

noncomputable section

open Set Topology Manifold Function Filter
open scoped Manifold ContDiff

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

namespace Manifold

section ModelShear

variable {n : ℕ} [NeZero n]

local notation "𝔼" => EuclideanSpace ℝ (Fin n)
local notation "𝔽" => EuclideanSpace ℝ (Fin 1)

private def modelD : 𝔼 →L[ℝ] 𝔽 :=
  ((PiLp.proj 2 (fun _ : Fin n => ℝ) 0 : 𝔼 →L[ℝ] ℝ)).smulRight
    (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

private def modelV : 𝔼 := EuclideanSpace.single (0 : Fin n) (1 : ℝ)

private lemma modelD_modelV : (modelD (n := n) modelV) 0 = 1 := by
  simp [modelD, modelV, ContinuousLinearMap.smulRight_apply]

private lemma halfSpace_symm_coe (x : 𝔽) (hx : 0 ≤ x 0) : ((𝓡∂ 1).symm x).val = x := by
  rw [modelWithCornersEuclideanHalfSpace_symm_apply]
  simp [max_eq_left hx]

private def shearSrc (v₀ : 𝔼) (s : 𝔽) : Set (𝔼 × EuclideanHalfSpace 1) :=
  {r | 0 < (r.2).val 0 ∧ 0 < ((r.2).val - s + modelD (n := n) (r.1 + v₀)) 0}

private def shearTgt (s : 𝔽) : Set (𝔼 × EuclideanHalfSpace 1) :=
  {w | 0 < (w.2).val 0 ∧ 0 < ((w.2).val + s - modelD (n := n) w.1) 0}

private def shearFun (v₀ : 𝔼) (s : 𝔽)
    (r : 𝔼 × EuclideanHalfSpace 1) : 𝔼 × EuclideanHalfSpace 1 :=
  (r.1 + v₀, (𝓡∂ 1).symm ((r.2).val - s + modelD (n := n) (r.1 + v₀)))

private def shearInv (v₀ : 𝔼) (s : 𝔽)
    (w : 𝔼 × EuclideanHalfSpace 1) : 𝔼 × EuclideanHalfSpace 1 :=
  (w.1 - v₀, (𝓡∂ 1).symm ((w.2).val + s - modelD (n := n) w.1))

private lemma continuous_shearFun (v₀ : 𝔼) (s : 𝔽) : Continuous (shearFun v₀ s) := by
  refine Continuous.prodMk (by fun_prop) ?_
  exact (𝓡∂ 1).continuous_invFun.comp (by fun_prop)

private lemma continuous_shearInv (v₀ : 𝔼) (s : 𝔽) : Continuous (shearInv v₀ s) := by
  refine Continuous.prodMk (by fun_prop) ?_
  exact (𝓡∂ 1).continuous_invFun.comp (by fun_prop)

private lemma isOpen_shearSrc (v₀ : 𝔼) (s : 𝔽) : IsOpen (shearSrc v₀ s) := by
  rw [show shearSrc v₀ s = {r : 𝔼 × EuclideanHalfSpace 1 | 0 < (r.2).val 0} ∩
      {r : 𝔼 × EuclideanHalfSpace 1 | 0 < ((r.2).val - s + modelD (n := n) (r.1 + v₀)) 0}
      from rfl]
  exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))

private lemma isOpen_shearTgt (s : 𝔽) : IsOpen (shearTgt (n := n) s) := by
  rw [show shearTgt (n := n) s = {w : 𝔼 × EuclideanHalfSpace 1 | 0 < (w.2).val 0} ∩
      {w : 𝔼 × EuclideanHalfSpace 1 | 0 < ((w.2).val + s - modelD (n := n) w.1) 0}
      from rfl]
  exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))

private lemma shearInv_shearFun (v₀ : 𝔼) (s : 𝔽) {r : 𝔼 × EuclideanHalfSpace 1}
    (hr : r ∈ shearSrc v₀ s) : shearInv v₀ s (shearFun v₀ s r) = r := by
  have h2 : (shearFun v₀ s r).2.val = (r.2).val - s + modelD (n := n) (r.1 + v₀) :=
    halfSpace_symm_coe _ (le_of_lt hr.2)
  have h1 : (shearFun v₀ s r).1 = r.1 + v₀ := rfl
  ext1
  · change (shearFun v₀ s r).1 - v₀ = r.1
    rw [h1]; abel_nf
  · change (𝓡∂ 1).symm ((shearFun v₀ s r).2.val + s - modelD (n := n) (shearFun v₀ s r).1) = r.2
    rw [h1, h2]
    have hstep : (r.2).val - s + modelD (n := n) (r.1 + v₀) + s
        - modelD (n := n) (r.1 + v₀) = (r.2).val := by abel_nf
    rw [hstep]
    exact (𝓡∂ 1).left_inv r.2

private lemma shearFun_shearInv (v₀ : 𝔼) (s : 𝔽) {w : 𝔼 × EuclideanHalfSpace 1}
    (hw : w ∈ shearTgt (n := n) s) : shearFun v₀ s (shearInv v₀ s w) = w := by
  have h2 : (shearInv v₀ s w).2.val = (w.2).val + s - modelD (n := n) w.1 :=
    halfSpace_symm_coe _ (le_of_lt hw.2)
  have h1 : (shearInv v₀ s w).1 = w.1 - v₀ := rfl
  ext1
  · change (shearInv v₀ s w).1 + v₀ = w.1
    rw [h1]; abel_nf
  · change (𝓡∂ 1).symm ((shearInv v₀ s w).2.val - s + modelD (n := n) ((shearInv v₀ s w).1 + v₀)) = w.2
    rw [h1, h2]
    have hstep : (w.2).val + s - modelD (n := n) w.1 - s
        + modelD (n := n) (w.1 - v₀ + v₀) = (w.2).val := by
      rw [sub_add_cancel]
      abel_nf
    rw [hstep]
    exact (𝓡∂ 1).left_inv w.2

private lemma shearFun_mem_shearTgt (v₀ : 𝔼) (s : 𝔽) {r : 𝔼 × EuclideanHalfSpace 1}
    (hr : r ∈ shearSrc v₀ s) : shearFun v₀ s r ∈ shearTgt (n := n) s := by
  have h2 : (shearFun v₀ s r).2.val = (r.2).val - s + modelD (n := n) (r.1 + v₀) :=
    halfSpace_symm_coe _ (le_of_lt hr.2)
  have h3 : (shearFun v₀ s r).1 = r.1 + v₀ := rfl
  refine ⟨?_, ?_⟩
  · rw [h2]; exact hr.2
  · rw [h2, h3]
    have hstep : (r.2).val - s + modelD (n := n) (r.1 + v₀) + s
        - modelD (n := n) (r.1 + v₀) = (r.2).val := by abel_nf
    rw [hstep]; exact hr.1

private lemma shearInv_mem_shearSrc (v₀ : 𝔼) (s : 𝔽) {w : 𝔼 × EuclideanHalfSpace 1}
    (hw : w ∈ shearTgt (n := n) s) : shearInv v₀ s w ∈ shearSrc v₀ s := by
  have h2 : (shearInv v₀ s w).2.val = (w.2).val + s - modelD (n := n) w.1 :=
    halfSpace_symm_coe _ (le_of_lt hw.2)
  have h3 : (shearInv v₀ s w).1 = w.1 - v₀ := rfl
  refine ⟨?_, ?_⟩
  · rw [h2]; exact hw.2
  · rw [h2, h3]
    have hstep : (w.2).val + s - modelD (n := n) w.1 - s
        + modelD (n := n) (w.1 - v₀ + v₀) = (w.2).val := by
      rw [sub_add_cancel]
      abel_nf
    rw [hstep]; exact hw.1

private def shear (v₀ : 𝔼) (s : 𝔽) :
    OpenPartialHomeomorph (𝔼 × EuclideanHalfSpace 1) (𝔼 × EuclideanHalfSpace 1) where
  toFun := shearFun v₀ s
  invFun := shearInv v₀ s
  source := shearSrc v₀ s
  target := shearTgt s
  map_source' := fun _ hr => shearFun_mem_shearTgt v₀ s hr
  map_target' := fun _ hw => shearInv_mem_shearSrc v₀ s hw
  left_inv' := fun _ hr => shearInv_shearFun v₀ s hr
  right_inv' := fun _ hw => shearFun_shearInv v₀ s hw
  continuousOn_toFun := (continuous_shearFun v₀ s).continuousOn
  continuousOn_invFun := (continuous_shearInv v₀ s).continuousOn
  open_source := isOpen_shearSrc v₀ s
  open_target := isOpen_shearTgt s

private lemma pos_of_symm_pos (x : 𝔽) (hx : 0 < (((𝓡∂ 1).symm x).val) 0) : 0 < x 0 := by
  have hval : (((𝓡∂ 1).symm x).val) 0 = max (x 0) 0 := by
    rw [modelWithCornersEuclideanHalfSpace_symm_apply]
    simp
  rw [hval] at hx
  by_contra hc
  rw [not_lt] at hc
  exact absurd hx (by rw [max_eq_right hc]; exact lt_irrefl 0)

private lemma contDiffOn_shear_comp (v₀ : 𝔼) (s : 𝔽) :
    ContDiffOn ℝ ∞ ((𝓡 n).prod (𝓡∂ 1) ∘ shearFun v₀ s ∘ ((𝓡 n).prod (𝓡∂ 1)).symm)
      (((𝓡 n).prod (𝓡∂ 1)).symm ⁻¹' shearSrc v₀ s ∩ range ((𝓡 n).prod (𝓡∂ 1))) := by
  have hΨ : ContDiff ℝ ∞ (fun p : 𝔼 × 𝔽 => (p.1 + v₀, p.2 - s + modelD (n := n) (p.1 + v₀))) := by
    fun_prop
  refine (hΨ.contDiffOn).congr (fun p hp => ?_)
  rw [mem_inter_iff, mem_preimage] at hp
  have hp1a : 0 < (((𝓡∂ 1).symm p.2).val) 0 := hp.1.1
  have hp1b : 0 < (((𝓡∂ 1).symm p.2).val - s + modelD (n := n) (p.1 + v₀)) 0 := hp.1.2
  have h1 : ((𝓡∂ 1).symm p.2).val = p.2 := halfSpace_symm_coe p.2 (le_of_lt (pos_of_symm_pos p.2 hp1a))
  change (p.1 + v₀, (𝓡∂ 1) ((𝓡∂ 1).symm (((𝓡∂ 1).symm p.2).val - s + modelD (n := n) (p.1 + v₀))))
      = (p.1 + v₀, p.2 - s + modelD (n := n) (p.1 + v₀))
  have hmem : ((𝓡∂ 1).symm p.2).val - s + modelD (n := n) (p.1 + v₀) ∈ range (𝓡∂ 1) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact le_of_lt hp1b
  rw [(𝓡∂ 1).right_inv hmem, h1]

private lemma contDiffOn_shearInv_comp (v₀ : 𝔼) (s : 𝔽) :
    ContDiffOn ℝ ∞ ((𝓡 n).prod (𝓡∂ 1) ∘ shearInv v₀ s ∘ ((𝓡 n).prod (𝓡∂ 1)).symm)
      (((𝓡 n).prod (𝓡∂ 1)).symm ⁻¹' shearTgt s ∩ range ((𝓡 n).prod (𝓡∂ 1))) := by
  have hΨ : ContDiff ℝ ∞ (fun p : 𝔼 × 𝔽 => (p.1 - v₀, p.2 + s - modelD (n := n) p.1)) := by
    fun_prop
  refine (hΨ.contDiffOn).congr (fun p hp => ?_)
  rw [mem_inter_iff, mem_preimage] at hp
  have hp1a : 0 < (((𝓡∂ 1).symm p.2).val) 0 := hp.1.1
  have hp1b : 0 < (((𝓡∂ 1).symm p.2).val + s - modelD (n := n) p.1) 0 := hp.1.2
  have h1 : ((𝓡∂ 1).symm p.2).val = p.2 := halfSpace_symm_coe p.2 (le_of_lt (pos_of_symm_pos p.2 hp1a))
  change (p.1 - v₀, (𝓡∂ 1) ((𝓡∂ 1).symm (((𝓡∂ 1).symm p.2).val + s - modelD (n := n) p.1)))
      = (p.1 - v₀, p.2 + s - modelD (n := n) p.1)
  have hmem : ((𝓡∂ 1).symm p.2).val + s - modelD (n := n) p.1 ∈ range (𝓡∂ 1) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact le_of_lt hp1b
  rw [(𝓡∂ 1).right_inv hmem, h1]

private lemma shear_mem_contDiffGroupoid (v₀ : 𝔼) (s : 𝔽) :
    shear v₀ s ∈ contDiffGroupoid ∞ ((𝓡 n).prod (𝓡∂ 1)) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  exact ⟨contDiffOn_shear_comp v₀ s, contDiffOn_shearInv_comp v₀ s⟩

omit [NeZero n] in
private lemma addRight_mem_contDiffGroupoid (v : 𝔼) :
    (Homeomorph.addRight v).toOpenPartialHomeomorph ∈ contDiffGroupoid ∞ (𝓡 n) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · change ContDiffOn ℝ ∞ ((𝓡 n) ∘ (Homeomorph.addRight v).toOpenPartialHomeomorph
        ∘ (𝓡 n).symm)
      ((𝓡 n).symm ⁻¹' (Homeomorph.addRight v).toOpenPartialHomeomorph.source ∩ range (𝓡 n))
    rw [show ((𝓡 n) ∘ (Homeomorph.addRight v).toOpenPartialHomeomorph ∘ (𝓡 n).symm)
        = fun x : 𝔼 => x + v from by funext x; rfl]
    fun_prop
  · change ContDiffOn ℝ ∞ ((𝓡 n) ∘ (Homeomorph.addRight v).toOpenPartialHomeomorph.symm
        ∘ (𝓡 n).symm)
      ((𝓡 n).symm ⁻¹' (Homeomorph.addRight v).toOpenPartialHomeomorph.target ∩ range (𝓡 n))
    rw [show ((𝓡 n) ∘ (Homeomorph.addRight v).toOpenPartialHomeomorph.symm ∘ (𝓡 n).symm)
        = fun x : 𝔼 => x - v from by funext x; rfl]
    fun_prop

private def shearEquiv : (𝔼 × 𝔽) ≃L[ℝ] (𝔼 × 𝔽) where
  toFun := fun p => (p.1, modelD (n := n) p.1 + p.2)
  invFun := fun p => (p.1, p.2 - modelD (n := n) p.1)
  left_inv := by
    rintro ⟨u, w⟩
    simp
  right_inv := by
    rintro ⟨u, w⟩
    simp
  map_add' := by
    rintro ⟨u₁, w₁⟩ ⟨u₂, w₂⟩
    simp only [Prod.mk_add_mk, map_add]
    ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' := by
    rintro c' ⟨u, w⟩
    simp only [Prod.smul_mk, map_smul, smul_add]
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end ModelShear

end Manifold


namespace Manifold

section MainTheorem

variable {n : ℕ} [NeZero n]

local notation "𝔼" => EuclideanSpace ℝ (Fin n)
local notation "𝔽" => EuclideanSpace ℝ (Fin 1)

theorem isSmoothEmbedding_prodMk_of_isInteriorPoint {M : Type*} [TopologicalSpace M]
    [ChartedSpace 𝔼 M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} [Fact (a < b)] {c : Icc a b} (hc : (𝓡∂ 1).IsInteriorPoint c) :
    IsSmoothEmbedding (𝓡 n) ((𝓡 n).prod (𝓡∂ 1)) ∞ (fun x : M => (x, c)) := by
  have hsc : 0 < ((chartAt (EuclideanHalfSpace 1) c) c).val 0 := by
    have h : ((chartAt (EuclideanHalfSpace 1) c) c).val ∈ interior (range (𝓡∂ 1)) := hc
    rw [interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] at h
    exact h
  refine ⟨?_, isEmbedding_prodMkLeft c⟩
  refine ⟨𝔽, inferInstance, inferInstance, fun x => ?_⟩
  classical
  let χ : OpenPartialHomeomorph M 𝔼 := chartAt 𝔼 x
  let v₀ : 𝔼 := modelV (n := n) - χ x
  let e : OpenPartialHomeomorph (Icc a b) (EuclideanHalfSpace 1) := chartAt (EuclideanHalfSpace 1) c
  let s : 𝔽 := (e c).val
  let χ' : OpenPartialHomeomorph M 𝔼 := χ ≫ₕ (Homeomorph.addRight v₀).toOpenPartialHomeomorph
  let U : Set 𝔼 := {v : 𝔼 | 0 < (modelD (n := n) v) 0}
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hsopen : IsOpen (χ'.source ∩ χ' ⁻¹' U) :=
    χ'.continuousOn.isOpen_inter_preimage χ'.open_source hU
  let domChart : OpenPartialHomeomorph M 𝔼 := χ'.restr (χ'.source ∩ χ' ⁻¹' U)
  let codChart : OpenPartialHomeomorph (M × Icc a b) (𝔼 × EuclideanHalfSpace 1) :=
    (χ.prod e) ≫ₕ shear v₀ s
  have hχ'app : χ x + v₀ = modelV (n := n) := by
    rw [show χ x + v₀ = χ' x from by
      simp only [χ', OpenPartialHomeomorph.trans_apply,
        Homeomorph.toOpenPartialHomeomorph_apply]
      rw [show (Homeomorph.addRight v₀) (χ x) = χ x + v₀ from rfl]]
    simp only [χ', OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply]
    rw [show (Homeomorph.addRight v₀) (χ x) = χ x + v₀ from rfl]
    simp only [v₀]
    abel_nf
  have hxsrc : x ∈ χ'.source := by
    rw [show χ'.source = χ.source ∩ χ ⁻¹'
        (Homeomorph.addRight v₀).toOpenPartialHomeomorph.source from
      OpenPartialHomeomorph.trans_source χ _]
    exact ⟨mem_chart_source 𝔼 x, mem_univ _⟩
  have hχ'x_app : χ' x = χ x + v₀ := by
    simp only [χ', OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply]
    rw [show (Homeomorph.addRight v₀) (χ x) = χ x + v₀ from rfl]
  have hUx : χ' x ∈ U := by
    rw [show U = {v : 𝔼 | 0 < (modelD (n := n) v) 0} from rfl, mem_ofPred_eq, hχ'x_app,
      hχ'app, modelD_modelV]
    norm_num
  have hdomx : x ∈ domChart.source := by
    have hsrc : domChart.source = χ'.source ∩ χ' ⁻¹' U := by
      rw [show domChart = χ'.restr (χ'.source ∩ χ' ⁻¹' U) from rfl,
        OpenPartialHomeomorph.restr_source' χ' _ hsopen, ← Set.inter_assoc, Set.inter_self]
    rw [hsrc]
    exact ⟨hxsrc, hUx⟩
  have hmaxχ : χ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hmaxχ' : χ' ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M :=
    StructureGroupoid.trans_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡 n)) hmaxχ
      (addRight_mem_contDiffGroupoid v₀)
  have hmaxdom : domChart ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡 n)) hmaxχ' hsopen
  have hmaxcod : codChart ∈ IsManifold.maximalAtlas ((𝓡 n).prod (𝓡∂ 1)) ∞ (M × Icc a b) :=
    StructureGroupoid.trans_mem_maximalAtlas (contDiffGroupoid ∞ ((𝓡 n).prod (𝓡∂ 1)))
      (IsManifold.mem_maximalAtlas_prod (IsManifold.chart_mem_maximalAtlas x)
        (IsManifold.chart_mem_maximalAtlas c))
      (shear_mem_contDiffGroupoid v₀ s)
  have hshearx : (χ x, e c) ∈ shearSrc v₀ s := by
    refine ⟨hsc, ?_⟩
    have hsub : (e c).val - (e c).val + modelD (n := n) (χ x + v₀) = modelD (n := n) modelV := by
      rw [hχ'app]; abel_nf
    rw [show s = (e c).val from rfl, hsub, modelD_modelV]
    norm_num
  have hfx : (x, c) ∈ codChart.source := by
    rw [show codChart.source = (χ.prod e).source ∩ (χ.prod e) ⁻¹' (shear v₀ s).source from
      OpenPartialHomeomorph.trans_source _ _]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.prod_source]
      exact ⟨mem_chart_source 𝔼 x, mem_chart_source (EuclideanHalfSpace 1) c⟩
    · rw [mem_preimage, OpenPartialHomeomorph.prod_apply]
      exact hshearx
  have hsource : domChart.source ⊆ (fun x : M => (x, c)) ⁻¹' codChart.source := by
    intro y hy
    have hsrc : domChart.source = χ'.source ∩ χ' ⁻¹' U := by
      rw [show domChart = χ'.restr (χ'.source ∩ χ' ⁻¹' U) from rfl,
        OpenPartialHomeomorph.restr_source' χ' _ hsopen, ← Set.inter_assoc, Set.inter_self]
    rw [hsrc] at hy
    rw [mem_preimage, show codChart.source =
        (χ.prod e).source ∩ (χ.prod e) ⁻¹' (shear v₀ s).source from
      OpenPartialHomeomorph.trans_source _ _]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.prod_source]
      refine ⟨?_, mem_chart_source (EuclideanHalfSpace 1) c⟩
      rw [show χ'.source = χ.source ∩ χ ⁻¹'
          (Homeomorph.addRight v₀).toOpenPartialHomeomorph.source from
        OpenPartialHomeomorph.trans_source χ _] at hy
      exact hy.1.1
    · rw [mem_preimage]
      change (χ y, e c) ∈ shearSrc v₀ s
      simp only [shearSrc, mem_ofPred_eq]
      refine ⟨hsc, ?_⟩
      have hval : χ' y = χ y + v₀ := by
        simp only [χ', OpenPartialHomeomorph.trans_apply,
          Homeomorph.toOpenPartialHomeomorph_apply]
        rw [show (Homeomorph.addRight v₀) (χ y) = χ y + v₀ from rfl]
      have hUy : 0 < (modelD (n := n) (χ' y)) 0 := hy.2
      rw [show s = (e c).val from rfl, ← hval, sub_self, zero_add]
      exact hUy
  refine IsImmersionAtOfComplement.mk_of_charts (shearEquiv (n := n)) domChart codChart
    hdomx hfx hmaxdom hmaxcod hsource ?_
  intro v hv
  have hsrc : domChart.source = χ'.source ∩ χ' ⁻¹' U := by
    rw [show domChart = χ'.restr (χ'.source ∩ χ' ⁻¹' U) from rfl,
      OpenPartialHomeomorph.restr_source' χ' _ hsopen, ← Set.inter_assoc, Set.inter_self]
  set y : M := (domChart.extend (𝓡 n)).symm v with hy
  have hys : y ∈ domChart.source := by
    have h := ((domChart.extend (𝓡 n)).symm).map_source hv
    rwa [PartialEquiv.symm_target, OpenPartialHomeomorph.extend_source] at h
  have hysrc : y ∈ χ'.source ∩ χ' ⁻¹' U := by
    rwa [hsrc] at hys
  have hyv : domChart y = v := by
    have h := (domChart.extend (𝓡 n)).right_inv hv
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply] at h
    simpa [hy] using h
  have hyχ' : χ' y = v := by
    have h := hyv
    rw [OpenPartialHomeomorph.restr_apply] at h
    exact h
  have hχy_app : χ' y = χ y + v₀ := by
    simp only [χ', OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply]
    rw [show (Homeomorph.addRight v₀) (χ y) = χ y + v₀ from rfl]
  have hχy : χ y + v₀ = v := by rw [← hχy_app, hyχ']
  have hUv : 0 < (modelD (n := n) v) 0 := by
    rw [← hχy]
    exact hysrc.2
  have hprod : (χ.prod e) (y, c) = (χ y, e c) := by
    rw [OpenPartialHomeomorph.prod_apply]
  have hcod : codChart (y, c) = (v, (𝓡∂ 1).symm (modelD (n := n) v)) := by
    rw [show codChart = (χ.prod e) ≫ₕ shear v₀ s from rfl,
      OpenPartialHomeomorph.trans_apply, hprod]
    change (χ y + v₀, (𝓡∂ 1).symm ((e c).val - s + modelD (n := n) (χ y + v₀)))
      = (v, (𝓡∂ 1).symm (modelD (n := n) v))
    rw [show s = (e c).val from rfl, hχy, sub_self, zero_add]
  have hmem : modelD (n := n) v ∈ range (𝓡∂ 1) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact le_of_lt hUv
  have hgoal : (codChart.extend ((𝓡 n).prod (𝓡∂ 1))) (y, c)
      = (shearEquiv (n := n)) (v, 0) := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, hcod]
    change (v, (𝓡∂ 1) ((𝓡∂ 1).symm (modelD (n := n) v)))
        = (v, modelD (n := n) v + 0)
    rw [(𝓡∂ 1).right_inv hmem, add_zero]
  simpa only [Function.comp_apply, ← hy] using hgoal

end MainTheorem

end Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem isSmoothEmbedding_middleSphereSlice :
    IsSmoothEmbedding (𝓡 2) ((𝓡 2).prod (𝓡∂ 1)) ∞ middleSphereSlice := by
  exact _root_.Manifold.isSmoothEmbedding_prodMk_of_isInteriorPoint (n := 2) (M := Sphere 2)
    (a := -2) (b := 2) (c := middleLevel)
    (Icc_isInteriorPoint_interior ⟨by norm_num [middleLevel], by norm_num [middleLevel]⟩)

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

variable [ChartedSpace ThreeSpace M]

theorem isSmoothEmbedding_tube_middleSphereSlice_of_isSmoothEmbedding_tube (a : T.Index)
    (hsm : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) :=
  IsSmoothEmbedding.comp (I := 𝓡 2) (J := (𝓡 2).prod (𝓡∂ 1)) (J' := ThreeModel)
    (f := middleSphereSlice) (g := fun z => T.tube a z) hsm isSmoothEmbedding_middleSphereSlice
    (by decide)

end TubeSystem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
