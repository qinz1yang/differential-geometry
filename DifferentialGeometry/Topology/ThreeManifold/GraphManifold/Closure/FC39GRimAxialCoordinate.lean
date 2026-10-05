import DifferentialGeometry.Topology.Manifold.DiskModelChartExtension
import DifferentialGeometry.Topology.Manifold.ClosedBall
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# FC39 GROUP G, RIMBOX route B (sheet §3 K3, step B1): the axial coordinate of an interval component

Lane FC39-G-RIMBOX. The flow handle (`FC39GRimFlowHandle.lean`) needs a smooth axial coordinate
`P = φ ∘ proj` along an interval component of the edge base with `φ ∘ intervalBase = id` on `[0, 1]`,
regular, injective, with a margin `(-ε, 1 + ε)` and proper. For an arbitrary smooth embedding
`β : [0, 1] → N` into a boundaryless 1-manifold this file builds `φ` on an open `V ⊇ β [0, 1]`:

* `cellOneIccDiffeo_GRIM : ClosedCell 1 ≃ₘ [0, 1]` (affine; smoothness through
  `contMDiff_iff_comp_subtypeVal_Icc` and the closed-cell inclusion immersion);
* `exists_axialCoordinate_GRIM`: the chart `j` extending `β ∘ cellOneIccDiffeo_GRIM` across the ends
  (`exists_partialDiffeomorph_extend_diskModel`, `m = 0`), `φ = affine ∘ j⁻¹` on
  `V = j (ball 0 (1 + δ))`: smooth, `φ ∘ β = id`, injective, submersive, `φ V = (-ε, 1 + ε)`,
  `V ∩ φ⁻¹ K` compact for compact `K ⊆ (-ε, 1 + ε)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local instance cellOneCharts_GRIM : ChartedSpace (EuclideanHalfSpace 1) (ClosedCell 1) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 0

local instance cellOneSmooth_GRIM : IsManifold (𝓡∂ 1) ∞ (ClosedCell 1) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 0

local instance cellOneCharts'_GRIM :
    ChartedSpace (EuclideanHalfSpace (0 + 1)) (ClosedCell (0 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 0

local instance cellOneSmooth'_GRIM : IsManifold (𝓡∂ (0 + 1)) ∞ (ClosedCell (0 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 0

theorem isImmersion_cellOne_val_GRIM :
    Manifold.IsImmersion (𝓡∂ 1) (𝓡 1) ∞ (Subtype.val : ClosedCell 1 → EuclideanSpace ℝ (Fin 1)) :=
  (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 0).isImmersion

theorem abs_apply_le_one_GRIM (z : ClosedCell 1) : |(z : EuclideanSpace ℝ (Fin 1)) 0| ≤ 1 :=
  (PiLp.norm_apply_le (z : EuclideanSpace ℝ (Fin 1)) 0).trans z.2

theorem single_apply_zero_GRIM (a : ℝ) : (EuclideanSpace.single (0 : Fin 1) a) 0 = a := by
  simp

theorem eq_single_GRIM (x : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace.single (0 : Fin 1) (x 0) = x := by
  ext i
  fin_cases i
  simp

/-- The affine map `[-1, 1] → [0, 1]`. -/
def cellOneToIcc_GRIM (z : ClosedCell 1) : Icc (0 : ℝ) 1 :=
  ⟨((z : EuclideanSpace ℝ (Fin 1)) 0 + 1) / 2, by
    have h := abs_le.mp (abs_apply_le_one_GRIM z)
    constructor <;> linarith [h.1, h.2]⟩

/-- The affine map `[0, 1] → [-1, 1]`. -/
def iccToCellOne_GRIM (t : Icc (0 : ℝ) 1) : ClosedCell 1 :=
  ⟨EuclideanSpace.single 0 (2 * (t : ℝ) - 1), by
    have : ‖EuclideanSpace.single (0 : Fin 1) (2 * (t : ℝ) - 1)‖ = |2 * (t : ℝ) - 1| := by
      simp
    rw [this, abs_le]
    constructor <;> linarith [t.2.1, t.2.2]⟩

theorem contMDiff_cellOneToIcc_GRIM : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ cellOneToIcc_GRIM := by
  rw [contMDiff_iff_comp_subtypeVal_Icc]
  have hval : ContMDiff (𝓡∂ 1) (𝓡 1) ∞ (Subtype.val : ClosedCell 1 → EuclideanSpace ℝ (Fin 1)) :=
    isImmersion_cellOne_val_GRIM.contMDiff
  have hc : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 1) => x 0) :=
    (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff
  have haff : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 1) => (x 0 + 1) / 2) :=
    (hc.add contDiff_const).div_const 2
  refine ⟨?_, haff.contMDiff.comp hval⟩
  exact ((hc.continuous.comp continuous_subtype_val).add continuous_const |>.div_const 2).subtype_mk _

theorem contMDiff_iccToCellOne_GRIM : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ iccToCellOne_GRIM := by
  rw [ContMDiff.iff_comp_isImmersion isImmersion_cellOne_val_GRIM]
  have hlin : ContDiff ℝ ∞ (fun s : ℝ => EuclideanSpace.single (0 : Fin 1) (2 * s - 1)) := by
    refine contDiff_euclidean.2 fun i => ?_
    fin_cases i
    simp
    fun_prop
  refine ⟨?_, hlin.contMDiff.comp contMDiff_subtypeVal_Icc⟩
  exact (hlin.continuous.comp continuous_subtype_val).subtype_mk _

/-- **The closed 1-cell and the unit interval are diffeomorphic** (affine). -/
def cellOneIccDiffeo_GRIM : ClosedCell 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1 where
  toFun := cellOneToIcc_GRIM
  invFun := iccToCellOne_GRIM
  left_inv z := by
    apply Subtype.ext
    change EuclideanSpace.single 0 (2 * (((z : EuclideanSpace ℝ (Fin 1)) 0 + 1) / 2) - 1) = _
    rw [show 2 * (((z : EuclideanSpace ℝ (Fin 1)) 0 + 1) / 2) - 1 = (z : EuclideanSpace ℝ (Fin 1)) 0
      by ring]
    exact eq_single_GRIM _
  right_inv t := by
    apply Subtype.ext
    change ((EuclideanSpace.single (0 : Fin 1) (2 * (t : ℝ) - 1)) 0 + 1) / 2 = t
    rw [single_apply_zero_GRIM]
    ring
  contMDiff_toFun := contMDiff_cellOneToIcc_GRIM
  contMDiff_invFun := contMDiff_iccToCellOne_GRIM

/-- The affine coordinate `x ↦ (x 0 + 1) / 2` of `ℝ¹`. -/
def cellAffine_GRIM (x : EuclideanSpace ℝ (Fin 1)) : ℝ := (x 0 + 1) / 2

theorem contDiff_cellAffine_GRIM : ContDiff ℝ ∞ cellAffine_GRIM :=
  (((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff).add
    contDiff_const).div_const 2

theorem norm_eq_abs_GRIM (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

/-- **The axial coordinate of an embedded arc in a 1-manifold**: a regular injective smooth
function `φ` on an open neighbourhood `V` of the arc with `φ ∘ β = id`, image `(-ε, 1 + ε)` and
compact preimages of compact subsets of `(-ε, 1 + ε)`. -/
theorem exists_axialCoordinate_GRIM {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) N] [IsManifold (𝓡 1) ∞ N] [T2Space N]
    (β : Icc (0 : ℝ) 1 → N) (hβ : ContMDiff (𝓡∂ 1) (𝓡 1) ∞ β) (hβinj : Injective β)
    (hβimm : ∀ t, Injective (mfderiv (𝓡∂ 1) (𝓡 1) β t)) :
    ∃ (V : Set N) (φ : N → ℝ) (ε : ℝ), IsOpen V ∧ 0 < ε ∧ range β ⊆ V ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ V ∧ (∀ t, φ (β t) = t) ∧ InjOn φ V ∧
      (∀ c ∈ V, Surjective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c)) ∧
      φ '' V = Ioo (-ε) (1 + ε) ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-ε) (1 + ε) → IsCompact (V ∩ φ ⁻¹' K) := by
  let _ : ChartedSpace (EuclideanHalfSpace (0 + 1)) (Icc (0 : ℝ) 1) :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1))
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (0 + 1))) N :=
    inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 1)) N)
  have _ : IsManifold (𝓡 (0 + 1)) ∞ N := inferInstanceAs (IsManifold (𝓡 1) ∞ N)
  obtain ⟨j, hjs, hjD⟩ := DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_extend_diskModel (m := 0) (N := N)
    cellOneIccDiffeo_GRIM β hβ hβinj hβimm
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨δ, hδ, hsub⟩ : ∃ δ > 0,
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) (δ + 1) ⊆ j.source := by
    obtain ⟨δ, hδ, h⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1).exists_cthickening_subset_open
      j.open_source hjs
    refine ⟨δ, hδ, ?_⟩
    rwa [cthickening_closedBall hδ.le zero_le_one] at h
  have hleft : ∀ y ∈ j.source, j.symm (j y) = y := fun y hy => j.toPartialEquiv.left_inv hy
  have hright : ∀ c ∈ j.target, j (j.symm c) = c := fun c hc => j.toPartialEquiv.right_inv hc
  have hmapt : ∀ c ∈ j.target, j.symm c ∈ j.source := fun c hc => j.toPartialEquiv.map_target hc
  let φ : N → ℝ := fun c => cellAffine_GRIM (j.symm c)
  let V : Set N := j.target ∩ j.symm ⁻¹' Metric.ball 0 (δ + 1)
  have hballsrc : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) (δ + 1), x ∈ j.source :=
    fun x hx => hsub (Metric.ball_subset_closedBall hx)
  have hjV : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) (δ + 1), j x ∈ V ∧ φ (j x) =
      cellAffine_GRIM x := by
    intro x hx
    have hl : j.symm (j x) = x := hleft x (hballsrc x hx)
    refine ⟨⟨j.map_source (hballsrc x hx), ?_⟩, ?_⟩
    · rw [mem_preimage, hl]
      exact hx
    · change cellAffine_GRIM (j.symm (j x)) = _
      rw [hl]
  have hβj : ∀ t, β t = j (iccToCellOne_GRIM t : EuclideanSpace ℝ (Fin 1)) := by
    intro t
    rw [hjD]
    exact congrArg β (cellOneIccDiffeo_GRIM.apply_symm_apply t).symm
  have hzball : ∀ t, (iccToCellOne_GRIM t : EuclideanSpace ℝ (Fin 1)) ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) (δ + 1) := fun t => by
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt (iccToCellOne_GRIM t).2 (by linarith)
  have haffz : ∀ t, cellAffine_GRIM (iccToCellOne_GRIM t : EuclideanSpace ℝ (Fin 1)) = t := by
    intro t
    change ((EuclideanSpace.single (0 : Fin 1) (2 * (t : ℝ) - 1)) 0 + 1) / 2 = t
    rw [single_apply_zero_GRIM]
    ring
  have hVopen : IsOpen V :=
    j.symm.contMDiffOn.continuousOn.isOpen_inter_preimage j.open_target Metric.isOpen_ball
  refine ⟨V, φ, δ / 2, hVopen, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    rw [hβj]
    exact (hjV _ (hzball t)).1
  · exact contDiff_cellAffine_GRIM.contMDiff.comp_contMDiffOn
      (j.symm.contMDiffOn.mono inter_subset_left)
  · intro t
    rw [hβj, (hjV _ (hzball t)).2, haffz]
  · intro c hc c' hc' hcc
    have h0 : (j.symm c) 0 = (j.symm c') 0 := by
      have := hcc
      change ((j.symm c) 0 + 1) / 2 = ((j.symm c') 0 + 1) / 2 at this
      linarith
    have h1 : j.symm c = j.symm c' := by rw [← eq_single_GRIM (j.symm c), h0, eq_single_GRIM]
    rw [← hright c hc.1, ← hright c' hc'.1]
    exact congrArg j h1
  · intro c hc
    set x := j.symm c with hx
    have hxs : x ∈ j.source := hmapt c hc.1
    have hcx : j x = c := hright c hc.1
    have hev : φ ∘ j =ᶠ[𝓝 x] cellAffine_GRIM := by
      filter_upwards [j.open_source.mem_nhds hxs] with y hy
      change cellAffine_GRIM (j.symm (j y)) = cellAffine_GRIM y
      rw [hleft y hy]
    have hlin : HasFDerivAt cellAffine_GRIM
        ((1 / 2 : ℝ) • (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) x := by
      have h := ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).hasFDerivAt
        (x := x)).add_const (1 : ℝ)
      have h2 := h.const_mul (1 / 2 : ℝ)
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [cellAffine_GRIM]
      ring
    have hφd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) φ c :=
      ((contDiff_cellAffine_GRIM.contMDiff.comp_contMDiffOn
        (j.symm.contMDiffOn.mono inter_subset_left)).contMDiffAt
        (hVopen.mem_nhds hc)).mdifferentiableAt hn
    have hjd : MDifferentiableAt (𝓡 1) (𝓡 1) j x :=
      (j.contMDiffOn.contMDiffAt (j.open_source.mem_nhds hxs)).mdifferentiableAt hn
    have hcomp : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (φ ∘ j) x =
        (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c).comp (mfderiv (𝓡 1) (𝓡 1) j x) := by
      rw [← hcx] at hφd
      rw [mfderiv_comp x hφd hjd, hcx]
    have hsurj : Surjective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (φ ∘ j) x) := by
      rw [hev.mfderiv_eq, mfderiv_eq_fderiv, hlin.fderiv]
      intro r
      let r' : ℝ := r
      refine ⟨EuclideanSpace.single 0 (2 * r'), ?_⟩
      change (1 / 2 : ℝ) • ((EuclideanSpace.single (0 : Fin 1) (2 * r')) 0) = r'
      rw [single_apply_zero_GRIM, smul_eq_mul]
      ring
    rw [hcomp] at hsurj
    exact Surjective.of_comp hsurj
  · ext s
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hb := hc.2
      change j.symm c ∈ Metric.ball 0 (δ + 1) at hb
      rw [mem_ball_zero_iff, norm_eq_abs_GRIM, abs_lt] at hb
      change ((j.symm c) 0 + 1) / 2 ∈ Ioo (-(δ / 2)) (1 + δ / 2)
      constructor <;> linarith [hb.1, hb.2]
    · intro hs
      have hxb : EuclideanSpace.single (0 : Fin 1) (2 * s - 1) ∈
          Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) (δ + 1) := by
        rw [mem_ball_zero_iff, norm_eq_abs_GRIM, single_apply_zero_GRIM, abs_lt]
        constructor <;> linarith [hs.1, hs.2]
      refine ⟨_, (hjV _ hxb).1, ?_⟩
      rw [(hjV _ hxb).2]
      change ((EuclideanSpace.single (0 : Fin 1) (2 * s - 1)) 0 + 1) / 2 = s
      rw [single_apply_zero_GRIM]
      ring
  · intro K hK hKsub
    have hAball : cellAffine_GRIM ⁻¹' K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) (δ + 1) := by
      intro x hx
      have h := hKsub hx
      change (x 0 + 1) / 2 ∈ Ioo (-(δ / 2)) (1 + δ / 2) at h
      rw [mem_ball_zero_iff, norm_eq_abs_GRIM, abs_lt]
      constructor <;> linarith [h.1, h.2]
    have hAc : IsCompact (cellAffine_GRIM ⁻¹' K) :=
      Metric.isCompact_of_isClosed_isBounded (hK.isClosed.preimage contDiff_cellAffine_GRIM.continuous)
        (Metric.isBounded_ball.subset hAball)
    have heq : V ∩ φ ⁻¹' K = j '' (cellAffine_GRIM ⁻¹' K) := by
      ext c
      constructor
      · rintro ⟨hc, hcK⟩
        exact ⟨j.symm c, hcK, hright c hc.1⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨(hjV x (hAball hx)).1, ?_⟩
        change φ (j x) ∈ K
        rw [(hjV x (hAball hx)).2]
        exact hx
    rw [heq]
    exact hAc.image_of_continuousOn (j.contMDiffOn.continuousOn.mono
      (fun x hx => hballsrc x (hAball hx)))


end GC.GraphManifold.Assembly.FC39P0
