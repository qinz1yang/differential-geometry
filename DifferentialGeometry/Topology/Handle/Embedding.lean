import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Embedding.LinearEquiv
import DifferentialGeometry.Topology.Embedding.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Handle

noncomputable section

variable (k : ℕ) [NeZero k]

attribute [local instance] cellBoundaryChartedSpace cellBoundaryIsManifold

private theorem cellBoundarySphereHomeomorph_contMDiff :
    ContMDiff (𝓡 (k - 1)) (𝓡 (k - 1)) ∞ (cellBoundarySphereHomeomorph k) := by
  exact (cellBoundaryInclusion_contMDiff k).codRestrict_sphere
    (fun x => (cellBoundarySphereHomeomorph k x).property)

private theorem cellBoundarySphereHomeomorph_symm_contMDiff :
    ContMDiff (𝓡 (k - 1)) (𝓡 (k - 1)) ∞ (cellBoundarySphereHomeomorph k).symm := by
  intro x
  let h := cellBoundarySphereHomeomorph k
  let c := chartAt (EuclideanSpace ℝ (Fin (k - 1))) (h.symm x)
  let s := chartAt (EuclideanSpace ℝ (Fin (k - 1))) x
  have hc : c = h.toOpenPartialHomeomorph ≫ₕ s := by
    dsimp [c, s]
    change cellBoundaryChart k (-h.symm x) =
      h.toOpenPartialHomeomorph ≫ₕ stereographic' (k - 1) (-x)
    change h.toOpenPartialHomeomorph ≫ₕ
      stereographic' (k - 1) (h (-h.symm x)) =
      h.toOpenPartialHomeomorph ≫ₕ stereographic' (k - 1) (-x)
    have heq : h (-h.symm x) = -x := Subtype.ext rfl
    rw [heq]
  have hs := contMDiffOn_chart (I := 𝓡 (k - 1)) (n := (∞)) (x := x)
  have hcs := contMDiffOn_chart_symm (I := 𝓡 (k - 1)) (n := (∞)) (x := h.symm x)
  have htarget : c.target = s.target := by rw [hc]; simp
  have hcomp : ContMDiffOn (𝓡 (k - 1)) (𝓡 (k - 1)) ∞
      (fun y => c.symm (s y)) s.source := by
    apply hcs.comp hs
    intro y hy
    rw [htarget]
    exact s.mapsTo hy
  have heq : Set.EqOn h.symm (fun y => c.symm (s y)) s.source := by
    intro y hy
    rw [hc]
    change h.symm y = h.symm (s.symm (s y))
    rw [s.left_inv hy]
  exact (hcomp.congr heq).contMDiffAt (s.open_source.mem_nhds (mem_chart_source _ _))

noncomputable def cellBoundarySphereDiffeomorph :
    Diffeomorph (𝓡 (k - 1)) (𝓡 (k - 1)) (CellBoundary k)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) ∞ where
  toEquiv := (cellBoundarySphereHomeomorph k).toEquiv
  contMDiff_toFun := cellBoundarySphereHomeomorph_contMDiff k
  contMDiff_invFun := cellBoundarySphereHomeomorph_symm_contMDiff k

@[simp] theorem cellBoundarySphereDiffeomorph_apply_val (x : CellBoundary k) :
    (cellBoundarySphereDiffeomorph k x).val = x.val := rfl

@[simp] theorem cellBoundarySphereDiffeomorph_symm_apply_val
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :
    ((cellBoundarySphereDiffeomorph k).symm x).val = x.val := rfl

private def closedCellBoundaryAmbientValue (m : ℕ) (i : Fin (m + 1))
    (x : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin (m + 1)) :=
  closedCellCons m (1 - ‖x‖ ^ 2)
    (closedCellTail m (closedCellPermute (Equiv.swap i 0) x))

private theorem closedCellBoundaryAmbientValue_contDiff (m : ℕ) (i : Fin (m + 1)) :
    ContDiff ℝ ∞ (closedCellBoundaryAmbientValue m i) := by
  exact closedCellCons_contDiff.comp
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).prodMk
      (closedCellTail_contDiff.comp (closedCellPermute_contDiff (Equiv.swap i 0))))

private theorem closedCellPermute_swap_twice (m : ℕ) (i : Fin (m + 1))
    (x : EuclideanSpace ℝ (Fin (m + 1))) :
    closedCellPermute (Equiv.swap i 0) (closedCellPermute (Equiv.swap i 0) x) = x := by
  simpa only [Equiv.symm_swap] using closedCellPermute_left_inv (Equiv.swap i 0) x

private noncomputable def closedCellBoundaryAmbientChart (m : ℕ)
    (i : Fin (m + 1)) (σ : Bool) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1)))
      (EuclideanSpace ℝ (Fin (m + 1))) where
  toFun := closedCellBoundaryAmbientValue m i
  invFun := closedCellBoundaryInvValue m (Equiv.swap i 0) (closedCellSign σ)
  source := {x | 0 < closedCellSign σ * (closedCellPermute (Equiv.swap i 0) x) 0}
  target := {y | 0 < 1 - y 0 - ‖closedCellTail m y‖ ^ 2}
  map_source' := by
    intro x hx
    dsimp [closedCellBoundaryAmbientValue]
    rw [closedCellCons_apply_zero, closedCellCons_tail]
    have he := closedCellSplit_norm_sq m (closedCellPermute (Equiv.swap i 0) x)
    rw [closedCellPermute_norm] at he
    have hn := closedCellPermute_coord_ne_zero (Equiv.swap i 0) hx
    nlinarith [sq_pos_of_ne_zero hn]
  map_target' := by
    intro y hy
    dsimp [closedCellBoundaryInvValue]
    rw [closedCellPermute_swap_twice, closedCellCons_apply_zero, ← mul_assoc,
      closedCellSign_mul_self, one_mul]
    exact Real.sqrt_pos.2 hy
  left_inv' := by
    intro x hx
    dsimp [closedCellBoundaryAmbientValue, closedCellBoundaryInvValue]
    rw [closedCellCons_apply_zero, closedCellCons_tail]
    have he := closedCellSplit_norm_sq m (closedCellPermute (Equiv.swap i 0) x)
    rw [closedCellPermute_norm] at he
    have hv : 1 - (1 - ‖x‖ ^ 2) -
        ‖closedCellTail m (closedCellPermute (Equiv.swap i 0) x)‖ ^ 2 =
        ((closedCellPermute (Equiv.swap i 0) x) 0) ^ 2 := by linarith
    rw [hv, Real.sqrt_sq_eq_abs, closedCellSign_mul_abs hx,
      closedCellCons_split, closedCellPermute_swap_twice]
  right_inv' := by
    intro y hy
    change closedCellCons m
      (1 - ‖closedCellBoundaryInvValue m (Equiv.swap i 0) (closedCellSign σ) y‖ ^ 2)
      (closedCellTail m (closedCellPermute (Equiv.swap i 0)
        (closedCellBoundaryInvValue m (Equiv.swap i 0) (closedCellSign σ) y))) = y
    rw [closedCellBoundaryInvValue_norm_sq (Equiv.swap i 0) (closedCellSign_sq σ) y hy]
    have hv : 1 - (1 - y 0) = y 0 := by ring
    rw [hv]
    dsimp [closedCellBoundaryInvValue]
    rw [closedCellPermute_swap_twice, closedCellCons_tail, closedCellCons_split]
  continuousOn_toFun := (closedCellBoundaryAmbientValue_contDiff m i).continuous.continuousOn
  continuousOn_invFun :=
    (closedCellBoundaryInvValue_contDiffOn (Equiv.swap i 0) (closedCellSign σ)).continuousOn
  open_source := by
    apply isOpen_lt continuous_const
    exact continuous_const.mul
      ((continuous_apply 0).comp
        ((PiLp.continuous_ofLp 2 _).comp (closedCellPermute (Equiv.swap i 0)).continuous))
  open_target := by
    apply isOpen_lt continuous_const
    exact (continuous_const.sub (by fun_prop)).sub
      (continuous_norm.comp closedCellTail_contDiff.continuous |>.pow 2)

private theorem closedCellBoundaryAmbientChart_mem_maximalAtlas (m : ℕ)
    (i : Fin (m + 1)) (σ : Bool) :
    closedCellBoundaryAmbientChart m i σ ∈
      IsManifold.maximalAtlas (𝓡 (m + 1)) ∞ (EuclideanSpace ℝ (Fin (m + 1))) := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (closedCellBoundaryAmbientValue_contDiff m i).contMDiff.contMDiffOn
  · exact (closedCellBoundaryInvValue_contDiffOn (Equiv.swap i 0)
      (closedCellSign σ)).contMDiffOn

private noncomputable def closedCellInteriorAmbientChart (m : ℕ) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1)))
      (EuclideanSpace ℝ (Fin (m + 1))) where
  toFun := closedCellShiftSucc m 1
  invFun := closedCellShiftSucc m (-1)
  source := Set.univ
  target := Set.univ
  map_source' := by intros; trivial
  map_target' := by intros; trivial
  left_inv' := fun x _ => closedCellShiftSucc_neg_left_inv m 1 x
  right_inv' := fun x _ => closedCellShiftSucc_neg_right_inv m 1 x
  continuousOn_toFun := (closedCellShiftSucc_contDiff 1).continuous.continuousOn
  continuousOn_invFun := (closedCellShiftSucc_contDiff (-1)).continuous.continuousOn
  open_source := isOpen_univ
  open_target := isOpen_univ

private theorem closedCellInteriorAmbientChart_mem_maximalAtlas (m : ℕ) :
    closedCellInteriorAmbientChart m ∈
      IsManifold.maximalAtlas (𝓡 (m + 1)) ∞ (EuclideanSpace ℝ (Fin (m + 1))) := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (closedCellShiftSucc_contDiff 1).contMDiff.contMDiffOn
  · exact (closedCellShiftSucc_contDiff (-1)).contMDiff.contMDiffOn

variable (m : ℕ)

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

private theorem closedCellChart_ambient_extension (x : ClosedCell (m + 1)) :
    ∃ c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1)))
        (EuclideanSpace ℝ (Fin (m + 1))),
      c ∈ IsManifold.maximalAtlas (𝓡 (m + 1)) ∞ (EuclideanSpace ℝ (Fin (m + 1))) ∧
      x.val ∈ c.source ∧
      ∀ u : ClosedCell (m + 1), c u.val =
        (chartAt (EuclideanHalfSpace (m + 1)) x u).val := by
  classical
  by_cases hx : ‖x.val‖ < 1
  · refine ⟨closedCellInteriorAmbientChart m,
      closedCellInteriorAmbientChart_mem_maximalAtlas m, Set.mem_univ _, ?_⟩
    intro u
    change closedCellShiftSucc m 1 u.val = (closedCellChartAt x u).val
    rw [closedCellChartAt, dif_pos hx]
    rfl
  · let i : Fin (m + 1) := Classical.choose
      (exists_closedCell_coord_ne_zero x.val (le_of_not_gt hx))
    let σ : Bool := 0 < x.val i
    have hc : chartAt (EuclideanHalfSpace (m + 1)) x =
        closedCellBoundaryChart m i σ := by
      change closedCellChartAt x = closedCellBoundaryChart m i σ
      rw [closedCellChartAt, dif_neg hx]
    refine ⟨closedCellBoundaryAmbientChart m i σ,
      closedCellBoundaryAmbientChart_mem_maximalAtlas m i σ, ?_, ?_⟩
    · have hs := mem_chart_source (EuclideanHalfSpace (m + 1)) x
      rw [hc] at hs
      exact hs
    · intro u
      rw [hc]
      rfl

theorem closedCellInclusion_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace (m + 1))
      (𝓡 (m + 1)) ∞ (Subtype.val : ClosedCell (m + 1) →
        EuclideanSpace ℝ (Fin (m + 1))) := by
  refine ⟨?_, Topology.IsEmbedding.subtypeVal⟩
  apply Manifold.IsImmersionOfComplement.isImmersion (F := PUnit.{1})
  intro x
  obtain ⟨c, hc, hx, hval⟩ := closedCellChart_ambient_extension m x
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt (ContinuousLinearEquiv.prodUnique ℝ _ _)
    (chartAt (EuclideanHalfSpace (m + 1)) x) c (mem_chart_source _ _) hx
    (IsManifold.chart_mem_maximalAtlas x) hc
  intro y hy
  have htarget : (modelWithCornersEuclideanHalfSpace (m + 1)).symm y ∈
      (chartAt (EuclideanHalfSpace (m + 1)) x).target ∧
      y ∈ Set.range (modelWithCornersEuclideanHalfSpace (m + 1)) := by
    simpa only [OpenPartialHomeomorph.extend_target, Set.mem_inter_iff, Set.mem_preimage] using hy
  change c (((chartAt (EuclideanHalfSpace (m + 1)) x).symm
    ((modelWithCornersEuclideanHalfSpace (m + 1)).symm y)).val) = y
  rw [hval]
  rw [(chartAt (EuclideanHalfSpace (m + 1)) x).right_inv htarget.1]
  exact congrArg Subtype.val (modelWithCornersEuclideanHalfSpace_symm_range y htarget.2)

attribute [local instance] closedCellChartedSpace

theorem exists_closedCellChart_extension (l : ℕ) [NeZero l] (x : ClosedCell l) :
    ∃ b : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin l))
        (EuclideanSpace ℝ (Fin ((l - 1) + 1))),
      ContDiffOn ℝ ∞ b b.source ∧ ContDiffOn ℝ ∞ b.symm b.target ∧
      x.val ∈ b.source ∧
      ∀ u : ClosedCell l, b u.val =
        (chartAt (EuclideanHalfSpace ((l - 1) + 1)) x u).val := by
  classical
  let _ : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1))
      (ClosedCell ((l - 1) + 1)) := closedCellChartedSpaceSucc (l - 1)
  let r := closedCellReindexHomeo l
  let e := (closedCellReindex l).toContinuousLinearEquiv
  obtain ⟨c, hc, hx, hval⟩ := closedCellChart_ambient_extension (l - 1) (r x)
  let b := e.toHomeomorph.toOpenPartialHomeomorph.trans c
  have hsource : b.source = e ⁻¹' c.source := by simp [b]
  have htarget : b.target = c.target := by simp [b]
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · change ContDiffOn ℝ ∞ (c ∘ e) b.source
    apply ((contMDiffOn_iff_contDiffOn).1
      (contMDiffOn_of_mem_maximalAtlas hc)).comp e.contDiff.contDiffOn
    intro y hy
    simpa only [hsource, Set.mem_preimage] using hy
  · change ContDiffOn ℝ ∞ (e.symm ∘ c.symm) b.target
    rw [htarget]
    exact e.symm.contDiff.comp_contDiffOn
      ((contMDiffOn_iff_contDiffOn).1 (contMDiffOn_symm_of_mem_maximalAtlas hc))
  · rw [hsource]
    exact hx
  · intro u
    change c (r u).val =
      (chartAt (EuclideanHalfSpace ((l - 1) + 1)) (r x) (r u)).val
    exact hval (r u)

theorem isSmoothEmbedding_coe_cellBoundary (k : ℕ) [NeZero k] :
    Manifold.IsSmoothEmbedding (𝓡 (k - 1)) (𝓡 k) ∞
      (Subtype.val : CellBoundary k → EuclideanSpace ℝ (Fin k)) := by
  exact (isSmoothEmbedding_coe_sphere (E := EuclideanSpace ℝ (Fin k))
    (n := k - 1)).comp_diffeomorph (cellBoundarySphereDiffeomorph k)

theorem isSmoothEmbedding_coe_closedCell (l : ℕ) [NeZero l] :
    Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
      (𝓡 l) ∞ (Subtype.val : ClosedCell l → EuclideanSpace ℝ (Fin l)) := by
  let _ : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1))
      (ClosedCell ((l - 1) + 1)) := closedCellChartedSpaceSucc (l - 1)
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) ∞
      (ClosedCell ((l - 1) + 1)) := closedCellIsManifold (l - 1)
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) ∞
      (ClosedCell l) := isManifoldOfHomeomorph
        (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (closedCellReindexHomeo l)
  let r : Diffeomorph (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
      (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
      (ClosedCell l) (ClosedCell ((l - 1) + 1)) ∞ :=
    { toEquiv := (closedCellReindexHomeo l).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (closedCellReindexHomeo l) _ _
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (closedCellReindexHomeo l) _ _ }
  have h := (closedCellInclusion_isSmoothEmbedding (l - 1)).comp_diffeomorph r
  have h' := h.continuousLinearEquiv_comp (closedCellReindex l).symm.toContinuousLinearEquiv
  refine ⟨h'.isImmersion.congr ?_, .subtypeVal⟩
  funext x
  exact (closedCellReindex l).symm_apply_apply x.val

theorem attachingRegionInclusion_isSmoothEmbedding (k l : ℕ) [NeZero k] [NeZero l] :
    Manifold.IsSmoothEmbedding
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)))
      ((𝓡 k).prod (𝓡 l)) ∞
      (fun p : AttachingRegion k l =>
        ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin l)))) := by
  let _ : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1))
      (ClosedCell ((l - 1) + 1)) := closedCellChartedSpaceSucc (l - 1)
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) ∞
      (ClosedCell ((l - 1) + 1)) := closedCellIsManifold (l - 1)
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) ∞
      (ClosedCell l) := isManifoldOfHomeomorph
        (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (closedCellReindexHomeo l)
  exact (isSmoothEmbedding_coe_cellBoundary k).prodMap
    (isSmoothEmbedding_coe_closedCell l)

end

end DifferentialGeometry.Topology.Handle
