import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusEdgeStageSTR
import DifferentialGeometry.Topology.Embedding.CrossModelPartialOCX
import DifferentialGeometry.Topology.Embedding.CrossModelInstancesOCX
import DifferentialGeometry.Topology.Embedding.Graph
import DifferentialGeometry.Topology.Embedding.LinearEquiv
import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
# S-SOLIDTORUS2 (suffix `_STR`), G2 part 3: the disk slices and the edge handle

The slice `w ↦ chart(w, t)` of the closed unit cell is a smooth embedding into the carrier whose
range is the whole disk over `t` (`‖z₁‖² ≤ 1/16`, edge coordinate `t`); the handle
`(w, t) ↦ chart(w, t)` on `D² × [0, 1]` is an `EdgeHandle Wc` with image the whole component.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_CellSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_CellSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

/-- The point `a e₀ + b e₁` of `ℝ²`. -/
def pair_STR (a b : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  a • EuclideanSpace.single 0 (1 : ℝ) + b • EuclideanSpace.single 1 (1 : ℝ)

@[simp] theorem pair_zero_STR (a b : ℝ) : pair_STR a b 0 = a := by simp [pair_STR]

@[simp] theorem pair_one_STR (a b : ℝ) : pair_STR a b 1 = b := by simp [pair_STR]

theorem norm_sq_fin_two_STR (v : EuclideanSpace ℝ (Fin 2)) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The linear identification `ℝ² × ℝ ≃ ℝ³`. -/
def coords23_STR : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => ofCoords_STI (p.1 0) (p.1 1) p.2
      invFun := fun v => (pair_STR (v 0) (v 1), v 2)
      map_add' := by
        intro p q
        ext i
        fin_cases i <;> simp [ofCoords_STI]
      map_smul' := by
        intro c p
        ext i
        fin_cases i <;> simp [ofCoords_STI]
      left_inv := by
        intro p
        refine Prod.ext ?_ ?_
        · ext i
          fin_cases i <;> simp
        · simp
      right_inv := by
        intro v
        ext i
        fin_cases i <;> simp }

theorem coords23_apply_STR (v : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    coords23_STR (v, t) = ofCoords_STI (v 0) (v 1) t := rfl

/-- The point `(w, t) ∈ D² × ℝ` of `ℝ³` (the chart coordinates `(ζ, t)`). -/
def cellPt_STR (w : ClosedCell 2) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  ofCoords_STI (w.val 0) (w.val 1) t

theorem rho2_cellPt_STR (w : ClosedCell 2) (t : ℝ) :
    rho2_STR (cellPt_STR w t) = ‖w.val‖ ^ 2 := by
  simp [rho2_STR, cellPt_STR, norm_sq_fin_two_STR]

theorem rho2_cellPt_le_STR (w : ClosedCell 2) (t : ℝ) : rho2_STR (cellPt_STR w t) ≤ 1 := by
  rw [rho2_cellPt_STR]
  have := w.2
  nlinarith [norm_nonneg w.val]

theorem rho2_cellPt_lt_STR (w : ClosedCell 2) (t : ℝ) : rho2_STR (cellPt_STR w t) < 4 :=
  lt_of_le_of_lt (rho2_cellPt_le_STR w t) (by norm_num)

theorem cellPt_slice_STR (t : ℝ) :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ (fun w : ClosedCell 2 => cellPt_STR w t) := by
  have h := ((DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).graph
    (V := ℝ) (g := fun _ => t) contDiff_const).continuousLinearEquiv_comp coords23_STR
  exact h


theorem edgeSlice_immersion_STR (t : ℝ) :
    IsImmersion (𝓡∂ 2) (𝓡∂ 3) ∞
      (fun w : ClosedCell 2 => edgeChartW_STR (cellPt_STR w t)) :=
  IsImmersion.partialDiffeomorph_comp_toHalfSpace_OCX (halfSpaceBoundaryShift_OCX 0)
    halfSpaceBoundaryShift_OCX_two.1 halfSpaceBoundaryShift_OCX_two.2
    (cellPt_slice_STR t).isImmersion edgeChartW_STR (fun w => rho2_cellPt_lt_STR w t)

theorem cellPt_injective_STR (t : ℝ) : Injective fun w : ClosedCell 2 => cellPt_STR w t := by
  intro w w' h
  have h0 : w.val 0 = w'.val 0 := by
    simpa [cellPt_STR] using congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) h
  have h1 : w.val 1 = w'.val 1 := by
    simpa [cellPt_STR] using congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 1) h
  apply Subtype.ext
  ext i
  fin_cases i
  exacts [h0, h1]

theorem edgeToW_injOn_STR : InjOn edgeToW_STR {x | rho2_STR x < 4} := by
  intro x hx y hy h
  have h1 := congrArg (fun w : Wc.Carrier => edgeInv_STR w.val) h
  simpa only [edgeToW_STR, edgeInv_edgeMap_STR hx, edgeInv_edgeMap_STR hy] using h1

theorem edgeSlice_injective_STR (t : ℝ) :
    Injective fun w : ClosedCell 2 => edgeToW_STR (cellPt_STR w t) := by
  intro w w' h
  exact cellPt_injective_STR t (edgeToW_injOn_STR (rho2_cellPt_lt_STR w t)
    (rho2_cellPt_lt_STR w' t) h)

theorem edgeSlice_embedding_STR (t : ℝ) :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ (fun w : ClosedCell 2 => edgeToW_STR (cellPt_STR w t)) :=
  ⟨edgeSlice_immersion_STR t,
    (((edgeSlice_immersion_STR t).contMDiff.continuous).isClosedEmbedding
      (edgeSlice_injective_STR t)).isEmbedding⟩


/-! ## The whole disk over `t` and the handle -/

theorem exists_cell_STR {y : Wc.Carrier} (hy : y ∈ edgeParent_STR)
    (h1 : ‖sphereFirst y.val‖ ^ 2 ≤ 1 / 16) :
    ∃ w : ClosedCell 2, edgeToW_STR (cellPt_STR w (tOf_STR (sphereSecond y.val))) = y := by
  have hlt := rho2_lt_of_target_STR hy
  have hρ : rho2_STR (edgeInv_STR y.val) ≤ 1 := by
    rw [rho2_edgeInv_STR]
    linarith
  set x := edgeInv_STR y.val with hx
  have hn : ‖pair_STR (x 0) (x 1)‖ ≤ 1 := by
    have h : ‖pair_STR (x 0) (x 1)‖ ^ 2 ≤ 1 := by
      rw [norm_sq_fin_two_STR]
      simpa [rho2_STR] using hρ
    nlinarith [norm_nonneg (pair_STR (x 0) (x 1))]
  refine ⟨⟨pair_STR (x 0) (x 1), hn⟩, ?_⟩
  have hc : cellPt_STR ⟨pair_STR (x 0) (x 1), hn⟩ (tOf_STR (sphereSecond y.val)) = x := by
    ext i
    fin_cases i
    · simp [cellPt_STR]
    · simp [cellPt_STR]
    · simp [cellPt_STR, hx, edgeInv_two_STR]
  rw [hc]
  exact Subtype.ext (edgeMap_edgeInv_STR hy)

/-- The whole disk over `τ`: `{y ∈ parent | t(y) = τ, ‖z₁‖² ≤ 1/16}`. -/
def fibreSet_STR (τ : ℝ) : Set Wc.Carrier :=
  {y | ∃ _ : y ∈ edgeParent_STR, tOf_STR (sphereSecond y.val) = τ ∧
    ‖sphereFirst y.val‖ ^ 2 ≤ 1 / 16}

theorem range_edgeSlice_STR (τ : ℝ) :
    range (fun w : ClosedCell 2 => edgeToW_STR (cellPt_STR w τ)) = fibreSet_STR τ := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨edgeToW_mem_parent_STR (rho2_cellPt_lt_STR w τ), ?_, ?_⟩
    · rw [tOf_edgeToW_STR (rho2_cellPt_lt_STR w τ)]
      simp [cellPt_STR]
    · rw [sphereFirst_sq_edgeToW_STR (rho2_cellPt_lt_STR w τ), rho2_cellPt_STR]
      have := w.2
      nlinarith [norm_nonneg w.val]
  · rintro ⟨hy, ht, h1⟩
    obtain ⟨w, hw⟩ := exists_cell_STR hy h1
    rw [ht] at hw
    exact ⟨w, hw⟩


/-- The inclusion `D² × [0,1] → ℝ² × ℝ`. -/
def handleIncl_STR : ClosedCell 2 × Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) × ℝ :=
  Prod.map Subtype.val Subtype.val

theorem handleIncl_smooth_STR :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ handleIncl_STR := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).contMDiff
      |>.prodMap (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞))

theorem handleIncl_bijective_STR (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
      handleIncl_STR p) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have hi :=
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).prodMap
      (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))
  exact DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
    ((𝓡∂ 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) handleIncl_STR p
    (hi.isImmersion.isImmersionAt p) (by simp)

/-- The coordinates `(ζ, t) ∈ ℝ³` of a point of `D² × [0,1]`. -/
def handleEuclid_STR : ClosedCell 2 × Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 3) :=
  coords23_STR ∘ handleIncl_STR

theorem handleEuclid_apply_STR (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    handleEuclid_STR p = cellPt_STR p.1 p.2.val := rfl

theorem handleEuclid_smooth_STR :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡 3) ∞ handleEuclid_STR :=
  coords23_STR.contDiff.contMDiff.comp handleIncl_smooth_STR

theorem handleEuclid_bijective_STR (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡 3) handleEuclid_STR p) := by
  unfold handleEuclid_STR
  rw [mfderiv_comp p (coords23_STR.contDiff.contMDiff.mdifferentiableAt
    (show (∞ : ℕ∞ω) ≠ 0 by simp)) (handleIncl_smooth_STR.mdifferentiableAt (by simp))]
  exact (coords23_STR.toDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) (handleIncl_STR p)).bijective.comp (handleIncl_bijective_STR p)

theorem rho2_handleEuclid_lt_STR (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    rho2_STR (handleEuclid_STR p) < 4 :=
  rho2_cellPt_lt_STR p.1 p.2.val

/-- The handle map `(w, t) ↦ chart(w, t)` on `D² × [0, 1]`. -/
def handleMap_STR (p : ClosedCell 2 × Icc (0 : ℝ) 1) : Wc.Carrier :=
  edgeToW_STR (handleEuclid_STR p)

theorem handleMap_smooth_STR :
    ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ handleMap_STR :=
  edgeChartW_STR.contMDiffOn.comp_contMDiff handleEuclid_smooth_STR rho2_handleEuclid_lt_STR

theorem handleMap_bijective_STR (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡∂ 3) handleMap_STR p) :=
  bijective_mfderiv_comp (handleEuclid_smooth_STR.mdifferentiableAt (by simp))
    ((edgeChartW_STR.mdifferentiableAt (by simp) (rho2_handleEuclid_lt_STR p)))
    (handleEuclid_bijective_STR p)
    (bijective_mfderiv_of_mem_source edgeChartW_STR (rho2_handleEuclid_lt_STR p))

theorem handleMap_injective_STR : Injective handleMap_STR := by
  intro p q h
  have h1 := edgeToW_injOn_STR (rho2_handleEuclid_lt_STR p) (rho2_handleEuclid_lt_STR q) h
  have h2 : cellPt_STR p.1 p.2.val = cellPt_STR q.1 q.2.val := h1
  have h3 : p.2.val = q.2.val := by
    simpa [cellPt_STR] using congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 2) h2
  have h4 : p.1 = q.1 := by
    apply cellPt_injective_STR p.2.val
    rw [h3] at h2 ⊢
    exact h2
  exact Prod.ext h4 (Subtype.ext h3)

/-- **The edge handle** `D² × [0, 1] → Wc`. -/
def edgeHandle_STR : EdgeHandle Wc where
  map := handleMap_STR
  smooth := handleMap_smooth_STR
  mfderiv_bijective := handleMap_bijective_STR
  injective := handleMap_injective_STR
  interior := by
    rintro _ ⟨p, rfl⟩
    exact edgeParent_interior_STR (edgeToW_mem_parent_STR (rho2_handleEuclid_lt_STR p))


/-- The whole component over `t ∈ [0, 1]`. -/
def handleSet_STR : Set Wc.Carrier :=
  {y | ∃ _ : y ∈ edgeParent_STR, tOf_STR (sphereSecond y.val) ∈ Icc (0 : ℝ) 1 ∧
    ‖sphereFirst y.val‖ ^ 2 ≤ 1 / 16}

theorem range_handleMap_STR : range handleMap_STR = handleSet_STR := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    have hp := rho2_handleEuclid_lt_STR p
    have hs := sphereFirst_sq_edgeToW_STR hp
    refine ⟨edgeToW_mem_parent_STR hp, ?_, ?_⟩
    · rw [handleMap_STR, tOf_edgeToW_STR hp]
      have h2 : (handleEuclid_STR p) 2 = p.2.val := by
        simp [handleEuclid_apply_STR, cellPt_STR]
      rw [h2]
      exact p.2.2
    · change ‖sphereFirst (edgeToW_STR (handleEuclid_STR p)).val‖ ^ 2 ≤ 1 / 16
      rw [hs, handleEuclid_apply_STR, rho2_cellPt_STR]
      have := p.1.2
      nlinarith [norm_nonneg p.1.val]
  · rintro ⟨hy, ht, h1⟩
    obtain ⟨w, hw⟩ := exists_cell_STR hy h1
    exact ⟨(w, ⟨_, ht⟩), hw⟩

theorem handleMap_slice_STR (t : Icc (0 : ℝ) 1) :
    (fun w : ClosedCell 2 => handleMap_STR (w, t)) =
      fun w => edgeToW_STR (cellPt_STR w t.val) := rfl

/-- The rim over `τ`: `‖z₁‖² = 1/16` exactly. -/
def rimSet_STR (τ : ℝ) : Set Wc.Carrier :=
  {y | ∃ _ : y ∈ edgeParent_STR, tOf_STR (sphereSecond y.val) = τ ∧
    ‖sphereFirst y.val‖ ^ 2 = 1 / 16}

theorem isBoundaryPoint_cell_STR {w : ClosedCell 2} :
    w ∈ diskRim ↔ ‖w.val‖ = 1 := by
  change w ∈ (𝓡∂ 2).boundary (ClosedCell 2) ↔ _
  rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 1]
  rfl

theorem slice_rim_STR (τ : ℝ) :
    (fun w : ClosedCell 2 => edgeToW_STR (cellPt_STR w τ)) '' diskRim = rimSet_STR τ := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 := isBoundaryPoint_cell_STR.1 hw
    refine ⟨edgeToW_mem_parent_STR (rho2_cellPt_lt_STR w τ), ?_, ?_⟩
    · rw [tOf_edgeToW_STR (rho2_cellPt_lt_STR w τ)]
      simp [cellPt_STR]
    · rw [sphereFirst_sq_edgeToW_STR (rho2_cellPt_lt_STR w τ), rho2_cellPt_STR, h1]
      norm_num
  · rintro ⟨hy, ht, h1⟩
    obtain ⟨w, hw⟩ := exists_cell_STR hy h1.le
    rw [ht] at hw
    refine ⟨w, isBoundaryPoint_cell_STR.2 ?_, hw⟩
    have h2 := sphereFirst_sq_edgeToW_STR (rho2_cellPt_lt_STR w τ)
    rw [hw, h1, rho2_cellPt_STR] at h2
    have h3 : ‖w.val‖ ^ 2 = 1 := by linarith
    nlinarith [norm_nonneg w.val, w.2]

theorem edgeProj_eq_single_STR {y : Wc.Carrier} (hy : y ∈ edgeParent_STR) :
    edgeProj_STR ⟨y, hy⟩ = EuclideanSpace.single (0 : Fin 1) (tOf_STR (sphereSecond y.val)) := by
  ext i
  fin_cases i
  simpa using edgeProj_val_STR ⟨y, hy⟩

theorem continuousOn_edgeToW_STR : ContinuousOn edgeToW_STR {x | rho2_STR x < 4} :=
  edgeChartW_STR.contMDiffOn.continuousOn

theorem continuous_cellPt_STR : Continuous fun p : ClosedCell 2 × ℝ => cellPt_STR p.1 p.2 := by
  have hf : Continuous fun p : ClosedCell 2 × ℝ => ((p.1.val 0, p.1.val 1, p.2) : ℝ × ℝ × ℝ) :=
    ((EuclideanSpace.proj (0 : Fin 2)).continuous.comp
        (continuous_subtype_val.comp continuous_fst)).prodMk
      (((EuclideanSpace.proj (1 : Fin 2)).continuous.comp
        (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  exact contDiff_ofCoords_STI.continuous.comp hf

/-- **EDP04 properness over a compact base**. -/
theorem edgeProper_STR (K : Set (EuclideanSpace ℝ (Fin 1))) (hK : IsCompact K) :
    IsCompact {y : Wc.Carrier | ∃ hy : y ∈ edgeParent_STR, edgeProj_STR ⟨y, hy⟩ ∈ K ∧
      edgeHeight_STR ⟨y, hy⟩ ≤ edgeLevel_STR} := by
  have hK' : IsCompact ((fun v : EuclideanSpace ℝ (Fin 1) => v 0) '' K) :=
    hK.image (EuclideanSpace.proj (0 : Fin 1)).continuous
  have hcomp : IsCompact ((fun p : ClosedCell 2 × ℝ => edgeToW_STR (cellPt_STR p.1 p.2)) ''
      (univ ×ˢ ((fun v : EuclideanSpace ℝ (Fin 1) => v 0) '' K))) :=
    (isCompact_univ.prod hK').image
      (continuousOn_edgeToW_STR.comp_continuous continuous_cellPt_STR
        (fun p => rho2_cellPt_lt_STR p.1 p.2))
  convert hcomp using 1
  ext y
  constructor
  · rintro ⟨hy, hk, hh⟩
    have h1 : ‖sphereFirst y.val‖ ^ 2 ≤ 1 / 16 := hh
    obtain ⟨w, hw⟩ := exists_cell_STR hy h1
    refine ⟨(w, tOf_STR (sphereSecond y.val)), ⟨mem_univ _, ?_⟩, hw⟩
    rw [edgeProj_eq_single_STR] at hk
    exact ⟨_, hk, by simp⟩
  · rintro ⟨⟨w, τ⟩, ⟨-, v, hv, rfl⟩, rfl⟩
    have hp := rho2_cellPt_lt_STR w (v 0)
    refine ⟨edgeToW_mem_parent_STR hp, ?_, ?_⟩
    · rw [edgeProj_eq_single_STR, tOf_edgeToW_STR hp]
      convert hv using 1
      ext i
      fin_cases i
      simp [cellPt_STR]
    · change ‖sphereFirst (edgeToW_STR (cellPt_STR w (v 0))).val‖ ^ 2 ≤ 1 / 16
      rw [sphereFirst_sq_edgeToW_STR hp, rho2_cellPt_STR]
      have := w.2
      nlinarith [norm_nonneg w.val]

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
