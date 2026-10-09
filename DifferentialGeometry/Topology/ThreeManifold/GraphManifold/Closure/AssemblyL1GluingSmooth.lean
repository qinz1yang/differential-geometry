import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1GluingApplications
import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Immersion

/-!
# Chapter-14 assembly, item L1, group G3c: the glued map is a smooth injective immersion

For the model normal form `N₀` of the solid torus (`ModelCycleNormalForm`) and a cycle normal form
`N` with union `U` in a manifold `X`, the glued map `gluedMap N N₀ : solidTorusSet → X`
(the transfer of `AssemblyL1Gluing.lean`) is smooth with injective differential everywhere
(`exists_map_of_cycleNormalForms`, the frozen G3c statement):

* near a point of a model neck target the map is `N.neck ∘ N₀.neck⁻¹` (case A);
* off the neck targets, a point lies in exactly one model ball or handle, and near it the solid
  torus lies in that piece (`CycleNormalForm.exists_nhds_mem_pieces`: the other pieces are closed
  and the fillets lie in the compact neck images of `filletBox`); there the map is
  `N.ball k ∘ N₀.ball k⁻¹` or `N.handle k ∘ N₀.handle k⁻¹`, and the local inverses are smooth by
  the immersion criterion for the inclusions of the closed cells and of `[0, 1]` (cases B, C);
* the differential is injective in case A as a composite of bijections, and at a ball or handle
  point because `gluedMap ∘ N₀.ball k = N.ball k` (resp. handle) has bijective differential, so
  the differential of `gluedMap` is onto, hence injective (equal dimensions).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1d : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1d : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskCharts_ASML1d : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1d : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- The charts of the closed 3-cell, indexed as `ClosedCell (2 + 1)` (the form of
`isSmoothEmbedding_closedCell_inclusion 2`). -/
local instance ballChartsSucc_ASML1d :
    ChartedSpace (EuclideanHalfSpace (2 + 1)) (ClosedCell (2 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

/-- The charts of the closed 2-cell, indexed as `ClosedCell (1 + 1)`. -/
local instance diskChartsSucc_ASML1d :
    ChartedSpace (EuclideanHalfSpace (1 + 1)) (ClosedCell (1 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-! ## The fillet box -/

/-- A compact box of neck coordinates containing every fillet point (`ψ ≤ 0` off the ball and
handle sides). -/
def filletBox (ε : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {q | 1 ≤ ‖q.1‖ ∧ 0 ≤ q.2 ∧ ‖q.1‖ - 1 + q.2 ≤ 3 / 4 * ε}

theorem isCompact_filletBox (ε : ℝ) : IsCompact (filletBox ε) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have hc : Continuous fun q : EuclideanSpace ℝ (Fin 2) × ℝ => ‖q.1‖ := continuous_fst.norm
    have hs : Continuous fun q : EuclideanSpace ℝ (Fin 2) × ℝ => ‖q.1‖ - 1 + q.2 :=
      (hc.sub continuous_const).add continuous_snd
    exact (isClosed_le
      (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin 2) × ℝ => (1 : ℝ)) hc).inter
      ((isClosed_le (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin 2) × ℝ => (0 : ℝ))
        continuous_snd).inter (isClosed_le hs
          (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin 2) × ℝ => 3 / 4 * ε)))
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨1 + |ε|, fun q hq => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hq
    have hε : 3 / 4 * ε ≤ |ε| := by
      have := le_abs_self ε
      have := abs_nonneg ε
      linarith
    rw [Prod.norm_def, max_le_iff]
    constructor
    · linarith
    · rw [Real.norm_eq_abs, abs_of_nonneg h2]
      linarith

theorem filletBox_subset_neckDomain {ε : ℝ} (hε : 0 < ε) : filletBox ε ⊆ neckDomain ε := by
  rintro q ⟨h1, h2, h3⟩
  refine ⟨by linarith, ?_⟩
  rw [abs_of_nonneg h2]
  linarith

/-- A fillet point lies in the fillet box. -/
theorem mem_filletBox_of_neckRounding_nonpos {ε : ℝ} (hε : 0 < ε)
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (h1 : 1 < ‖q.1‖) (h2 : 0 < q.2)
    (hψ : neckRounding ε q ≤ 0) : q ∈ filletBox ε := by
  have hx : 0 < (‖q.1‖ - 1) / ε := div_pos (by linarith) hε
  have hy : 0 < q.2 / ε := div_pos h2 hε
  have hb := band_of_standardRimRounding_nonpos ((‖q.1‖ - 1) / ε, q.2 / ε) hx hy hψ
  simp only at hb
  rw [← add_div, div_lt_iff₀ hε] at hb
  exact ⟨h1.le, h2.le, by linarith⟩

/-! ## Closedness of the pieces and the local piece lemma -/

namespace CycleNormalForm

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {len : ℕ} {ε : ℝ} {U : Set X}
  (N : CycleNormalForm I X len ε U)

theorem isCompact_range_ball (k : Fin len) : IsCompact (range (N.ball k)) :=
  isCompact_range (N.ball_smooth k).continuous

theorem isCompact_range_handle (k : Fin len) : IsCompact (range (N.handle k)) :=
  isCompact_range (N.handle_smooth k).continuous

theorem isCompact_neck_image_filletBox (k : Fin len) (b : Bool) :
    IsCompact (N.neck k b '' filletBox ε) :=
  (isCompact_filletBox ε).image_of_continuousOn
    ((N.neck k b).contMDiffOn.continuousOn.mono
      (by rw [N.neck_source]; exact filletBox_subset_neckDomain N.ε_pos))

theorem neck_image_filletBox_subset_target (k : Fin len) (b : Bool) :
    N.neck k b '' filletBox ε ⊆ (N.neck k b).target := by
  rintro _ ⟨q, hq, rfl⟩
  exact N.neck_mem_target (filletBox_subset_neckDomain N.ε_pos hq)

/-- A handle point on a ball lies in a neck target. -/
theorem exists_target_of_handle_mem_ball {k j : Fin len} {q : ClosedCell 2 × Icc (0 : ℝ) 1}
    (h : N.handle k q ∈ range (N.ball j)) : ∃ b, N.handle k q ∈ (N.neck k b).target := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨b, -, hb, -, -⟩ := (N.ball_eq_handle_iff).mp hx
  have hend : |(q.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε := by
    rw [hb, sub_self, abs_zero]
    linarith [N.ε_pos]
  refine ⟨b, ?_⟩
  rw [N.handle_end k b q hend]
  exact N.neck_mem_target (handleEnd_mem_neckDomain b hend).1

/-- **Local piece lemma.** Off the neck images of the fillet box, every point `p` has a
neighbourhood whose points of `U` lie in the balls and handles containing `p`. -/
theorem exists_nhds_mem_pieces [T2Space X] {p : X}
    (hp : ∀ k b, p ∉ N.neck k b '' filletBox ε) :
    ∃ V ∈ 𝓝 p, ∀ p' ∈ V, p' ∈ U →
      (∃ j x, N.ball j x = p' ∧ p ∈ range (N.ball j)) ∨
        ∃ j q, N.handle j q = p' ∧ p ∈ range (N.handle j) := by
  classical
  let Z : Set X := ((⋃ j ∈ {j | p ∉ range (N.ball j)}, range (N.ball j)) ∪
      ⋃ j ∈ {j | p ∉ range (N.handle j)}, range (N.handle j)) ∪
    ⋃ k, ⋃ b, N.neck k b '' filletBox ε
  have hZ : IsClosed Z := by
    refine (((Set.toFinite _).isClosed_biUnion
      (fun j _ => (N.isCompact_range_ball j).isClosed)).union
      ((Set.toFinite _).isClosed_biUnion
        (fun j _ => (N.isCompact_range_handle j).isClosed))).union ?_
    exact isClosed_iUnion_of_finite (fun k => isClosed_iUnion_of_finite
      (fun b => (N.isCompact_neck_image_filletBox k b).isClosed))
  have hpZ : p ∉ Z := by
    rintro ((h | h) | h)
    · obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.mp h
      exact hj hpj
    · obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.mp h
      exact hj hpj
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hk
      exact hp k b hb
  refine ⟨Zᶜ, hZ.isOpen_compl.mem_nhds hpZ, fun p' hp'Z hp'U => ?_⟩
  have hball : ∀ j x, N.ball j x = p' → p ∈ range (N.ball j) := by
    intro j x hx
    by_contra hj
    exact hp'Z (Or.inl (Or.inl (Set.mem_iUnion₂.mpr ⟨j, hj, x, hx⟩)))
  have hhandle : ∀ j q, N.handle j q = p' → p ∈ range (N.handle j) := by
    intro j q hq
    by_contra hj
    exact hp'Z (Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hj, q, hq⟩)))
  rcases N.mem_union_cases hp'U with ⟨j, x, hx⟩ | ⟨j, q, hq⟩ | ⟨k, b, q, ⟨hqD, hψ⟩, hq⟩
  · exact Or.inl ⟨j, x, hx, hball j x hx⟩
  · exact Or.inr ⟨j, q, hq, hhandle j q hq⟩
  · by_cases h2 : q.2 ≤ 0
    · obtain ⟨x, hx⟩ := (N.neck_ball k b hqD).mpr h2
      rw [hq] at hx
      exact Or.inl ⟨_, x, hx, hball _ x hx⟩
    · by_cases h1 : ‖q.1‖ ≤ 1
      · obtain ⟨q', hq'⟩ := (N.neck_handle k b hqD).mpr ⟨(not_le.mp h2).le, h1⟩
        rw [hq] at hq'
        exact Or.inr ⟨_, q', hq', hhandle _ q' hq'⟩
      · exfalso
        exact hp'Z (Or.inr (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨b, q,
          mem_filletBox_of_neckRounding_nonpos N.ε_pos (not_le.mp h1) (not_le.mp h2) hψ, hq⟩⟩))

end CycleNormalForm

/-! ## Transfer along an equation -/

section TransferEq

variable {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H₀}
  {X₀ : Type*} [TopologicalSpace X₀] [ChartedSpace H₀ X₀]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {len : ℕ} {ε : ℝ} {U₀ : Set X₀} {U : Set X}
  (N₀ : CycleNormalForm I₀ X₀ len ε U₀) (N : CycleNormalForm I X len ε U)

theorem transfer_eq_ball {k : Fin len} {x : ClosedCell 3} {p : X₀} (hp : p ∈ U₀)
    (h : N₀.ball k x = p) : transfer N₀ N p hp = N.ball k x := by
  subst h
  exact transfer_ball N₀ N k x hp

theorem transfer_eq_handle {k : Fin len} {q : ClosedCell 2 × Icc (0 : ℝ) 1} {p : X₀}
    (hp : p ∈ U₀) (h : N₀.handle k q = p) : transfer N₀ N p hp = N.handle k q := by
  subst h
  exact transfer_handle N₀ N k q hp

theorem transfer_eq_neck {k : Fin len} {b : Bool} {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ neckDomain ε) {p : X₀} (hp : p ∈ U₀) (h : N₀.neck k b q = p) :
    transfer N₀ N p hp = N.neck k b q := by
  subst h
  exact transfer_neck N₀ N k b hq hp

end TransferEq

/-! ## The glued map -/

section Glued

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {len : ℕ} {ε : ℝ} {U : Set X}

/-- The glued map: the transfer from the model solid torus. -/
def gluedMap (N : CycleNormalForm I X len ε U) (N₀ : ModelCycleNormalForm.{u} len ε)
    (p : solidTorusSet.{u}) : X :=
  transfer N₀.toCycleNormalForm N p.1 p.2

/-- The local inverse of the model ball `k` (any value off the ball). -/
def ModelCycleNormalForm.ballInv {len : ℕ} {ε : ℝ} (N₀ : ModelCycleNormalForm.{u} len ε)
    (k : Fin len) (p : solidTorusSet.{u}) : ClosedCell 3 :=
  if h : ‖(N₀.ballChart k).symm p.1‖ ≤ 1 then ⟨(N₀.ballChart k).symm p.1, h⟩ else ⟨0, by simp⟩

/-- The local inverse of the model handle `k` (any value off the handle). -/
def ModelCycleNormalForm.handleInv {len : ℕ} {ε : ℝ} (N₀ : ModelCycleNormalForm.{u} len ε)
    (k : Fin len) (p : solidTorusSet.{u}) : ClosedCell 2 × Icc (0 : ℝ) 1 :=
  (if h : ‖((N₀.handleChart k).symm p.1).1‖ ≤ 1 then ⟨((N₀.handleChart k).symm p.1).1, h⟩
    else ⟨0, by simp⟩, projIcc 0 1 zero_le_one ((N₀.handleChart k).symm p.1).2)

variable (N : CycleNormalForm I X len ε U) (N₀ : ModelCycleNormalForm.{u} len ε)

theorem ModelCycleNormalForm.ballChart_symm_ball (k : Fin len) (x : ClosedCell 3) :
    (N₀.ballChart k).symm (N₀.ball k x) = x.1 := by
  rw [N₀.ballChart_eq]
  exact (N₀.ballChart k).left_inv (N₀.ballChart_source k (mem_closedBall_zero_iff.mpr x.2))

theorem ModelCycleNormalForm.handleChart_symm_handle (k : Fin len)
    (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    (N₀.handleChart k).symm (N₀.handle k q) =
      ((q.1 : EuclideanSpace ℝ (Fin 2)), (q.2 : ℝ)) := by
  rw [N₀.handleChart_eq]
  exact (N₀.handleChart k).left_inv (N₀.handleChart_source k ⟨q.1.2, q.2.2⟩)

theorem ModelCycleNormalForm.ballInv_eq {k : Fin len} {x : ClosedCell 3}
    {p : solidTorusSet.{u}} (h : N₀.ball k x = p.1) : N₀.ballInv k p = x := by
  have hs : (N₀.ballChart k).symm p.1 = x.1 := by rw [← h, N₀.ballChart_symm_ball]
  have hx : ‖(N₀.ballChart k).symm p.1‖ ≤ 1 := by rw [hs]; exact x.2
  rw [ModelCycleNormalForm.ballInv, dite_eq_left hx]
  exact Subtype.ext hs

theorem ModelCycleNormalForm.handleInv_eq {k : Fin len} {q : ClosedCell 2 × Icc (0 : ℝ) 1}
    {p : solidTorusSet.{u}} (h : N₀.handle k q = p.1) : N₀.handleInv k p = q := by
  have hs : (N₀.handleChart k).symm p.1 = ((q.1 : EuclideanSpace ℝ (Fin 2)), (q.2 : ℝ)) := by
    rw [← h, N₀.handleChart_symm_handle]
  have hx : ‖((N₀.handleChart k).symm p.1).1‖ ≤ 1 := by rw [hs]; exact q.1.2
  rw [ModelCycleNormalForm.handleInv, dite_eq_left hx]
  refine Prod.ext (Subtype.ext ?_) ?_
  · change ((N₀.handleChart k).symm p.1).1 = (q.1 : EuclideanSpace ℝ (Fin 2))
    rw [hs]
  · change projIcc 0 1 zero_le_one ((N₀.handleChart k).symm p.1).2 = q.2
    rw [hs]
    exact projIcc_val zero_le_one q.2

/-- Case A: near a point of a model neck target the glued map is `N.neck ∘ N₀.neck⁻¹`. -/
theorem gluedMap_eq_neck {k : Fin len} {b : Bool} {p : solidTorusSet.{u}}
    (hp : p.1 ∈ (N₀.neck k b).target) :
    gluedMap N N₀ p = N.neck k b ((N₀.neck k b).symm p.1) := by
  have hq : (N₀.neck k b).symm p.1 ∈ neckDomain ε := by
    rw [← N₀.neck_source k b]
    exact (N₀.neck k b).map_target hp
  exact transfer_eq_neck N₀.toCycleNormalForm N hq p.2 ((N₀.neck k b).right_inv hp)

theorem contMDiffAt_gluedMap_of_mem_target {k : Fin len} {b : Bool} {p : solidTorusSet.{u}}
    (hp : p.1 ∈ (N₀.neck k b).target) :
    ContMDiffAt (𝓡∂ 3) I ∞ (gluedMap N N₀) p ∧
      Injective (mfderiv (𝓡∂ 3) I (gluedMap N N₀) p) := by
  have hev : gluedMap N N₀ =ᶠ[𝓝 p]
      (N.neck k b ∘
        ((N₀.neck k b).symm ∘ (Subtype.val : solidTorusSet.{u} → SphereCarrier.{u}))) := by
    filter_upwards [((N₀.neck k b).open_target.preimage continuous_subtype_val).mem_nhds hp]
      with p' hp'
    exact gluedMap_eq_neck N N₀ hp'
  have hsrc : (N₀.neck k b).symm p.1 ∈ (N.neck k b).source := by
    rw [N.neck_source, ← N₀.neck_source k b]
    exact (N₀.neck k b).map_target hp
  have hsymm : ContMDiffAt (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ (N₀.neck k b).symm p.1 :=
    (N₀.neck k b).symm.contMDiffOn.contMDiffAt ((N₀.neck k b).open_target.mem_nhds hp)
  have hψ : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
      ((N₀.neck k b).symm ∘ (Subtype.val : solidTorusSet.{u} → SphereCarrier.{u})) p :=
    hsymm.comp p (contMDiff_solidTorus_val p)
  have hΨ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) I ∞ (N.neck k b)
      ((N₀.neck k b).symm p.1) :=
    (N.neck k b).contMDiffOn.contMDiffAt ((N.neck k b).open_source.mem_nhds hsrc)
  refine ⟨(hΨ.comp p hψ).congr_of_eventuallyEq hev, ?_⟩
  rw [hev.mfderiv_eq, mfderiv_comp p (hΨ.mdifferentiableAt (by simp))
    (hψ.mdifferentiableAt (by simp)), mfderiv_comp p (hsymm.mdifferentiableAt (by simp))
    ((contMDiff_solidTorus_val p).mdifferentiableAt (by simp))]
  have h1 := (((N.neck k b).isLocalDiffeomorphAt _ _ _ hsrc).isInvertible_mfderiv
    (by simp)).bijective.1
  have h2 := (((N₀.neck k b).symm.isLocalDiffeomorphAt _ _ _ hp).isInvertible_mfderiv
    (by simp)).bijective.1
  have h3 := (solidTorusAtlas.{u}.mfderiv_subtypeVal_bijective p).1
  simp only [ContinuousLinearMap.coe_comp]
  exact h1.comp (h2.comp h3)


/-- Case B: the local inverse of a model ball is smooth where the solid torus lies in the ball. -/
theorem ModelCycleNormalForm.contMDiffAt_ballInv {k : Fin len} {p : solidTorusSet.{u}}
    (hp : ∀ᶠ p' in 𝓝 p, (p' : solidTorusSet.{u}).1 ∈ range (N₀.ball k)) :
    ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (N₀.ballInv k) p := by
  have hev : (Subtype.val ∘ N₀.ballInv k) =ᶠ[𝓝 p]
      ((N₀.ballChart k).symm ∘ (Subtype.val : solidTorusSet.{u} → SphereCarrier.{u})) := by
    filter_upwards [hp] with p' hp'
    obtain ⟨x, hx⟩ := hp'
    simp only [Function.comp_apply]
    rw [N₀.ballInv_eq hx, ← hx, N₀.ballChart_symm_ball]
  obtain ⟨x₀, hx₀⟩ := hp.self_of_nhds
  have htgt : p.1 ∈ (N₀.ballChart k).target := by
    rw [← hx₀, N₀.ballChart_eq]
    exact (N₀.ballChart k).map_source (N₀.ballChart_source k (mem_closedBall_zero_iff.mpr x₀.2))
  have hsm : ContMDiffAt (𝓡∂ 3) (𝓡 3) ∞
      ((N₀.ballChart k).symm ∘ (Subtype.val : solidTorusSet.{u} → SphereCarrier.{u})) p :=
    ((N₀.ballChart k).symm.contMDiffOn.contMDiffAt
      ((N₀.ballChart k).open_target.mem_nhds htgt)).comp p (contMDiff_solidTorus_val p)
  have himm := (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion
    2).isImmersion.isImmersionAt (N₀.ballInv k p)
  refine (ContMDiffAt.iff_comp_isImmersionAt himm).mpr ⟨?_, hsm.congr_of_eventuallyEq hev⟩
  exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (hsm.continuousAt.congr hev.symm)

/-- Case C: the local inverse of a model handle is smooth where the solid torus lies in the
handle. -/
theorem ModelCycleNormalForm.contMDiffAt_handleInv {k : Fin len} {p : solidTorusSet.{u}}
    (hp : ∀ᶠ p' in 𝓝 p, (p' : solidTorusSet.{u}).1 ∈ range (N₀.handle k)) :
    ContMDiffAt (𝓡∂ 3) ((𝓡∂ 2).prod (𝓡∂ 1)) ∞ (N₀.handleInv k) p := by
  have hsymm : ∀ᶠ p' in 𝓝 p, (N₀.handleChart k).symm p'.1 =
      (((N₀.handleInv k p').1 : EuclideanSpace ℝ (Fin 2)), ((N₀.handleInv k p').2 : ℝ)) := by
    filter_upwards [hp] with p' hp'
    obtain ⟨q, hq⟩ := hp'
    rw [N₀.handleInv_eq hq, ← hq, N₀.handleChart_symm_handle]
  obtain ⟨q₀, hq₀⟩ := hp.self_of_nhds
  have htgt : p.1 ∈ (N₀.handleChart k).target := by
    rw [← hq₀, N₀.handleChart_eq]
    exact (N₀.handleChart k).map_source (N₀.handleChart_source k ⟨q₀.1.2, q₀.2.2⟩)
  have hsm : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
      ((N₀.handleChart k).symm ∘ (Subtype.val : solidTorusSet.{u} → SphereCarrier.{u})) p :=
    ((N₀.handleChart k).symm.contMDiffOn.contMDiffAt
      ((N₀.handleChart k).open_target.mem_nhds htgt)).comp p (contMDiff_solidTorus_val p)
  have h1 : ContMDiffAt (𝓡∂ 3) (𝓡 2) ∞
      (fun p' : solidTorusSet.{u} => ((N₀.handleChart k).symm p'.1).1) p :=
    contDiff_fst.contMDiff.contMDiffAt.comp p hsm
  have h2 : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞
      (fun p' : solidTorusSet.{u} => ((N₀.handleChart k).symm p'.1).2) p :=
    contDiff_snd.contMDiff.contMDiffAt.comp p hsm
  refine ContMDiffAt.prodMk ?_ ?_
  · have hev : (Subtype.val ∘ fun p' => (N₀.handleInv k p').1) =ᶠ[𝓝 p]
        fun p' : solidTorusSet.{u} => ((N₀.handleChart k).symm p'.1).1 := by
      filter_upwards [hsymm] with p' hp'
      simp only [Function.comp_apply]
      rw [hp']
    have himm := (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion
      1).isImmersion.isImmersionAt (N₀.handleInv k p).1
    refine (ContMDiffAt.iff_comp_isImmersionAt (f := fun p' => (N₀.handleInv k p').1) (x := p)
      himm).mpr ⟨?_, h1.congr_of_eventuallyEq hev⟩
    exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (h1.continuousAt.congr hev.symm)
  · have hev : (Subtype.val ∘ fun p' => (N₀.handleInv k p').2) =ᶠ[𝓝 p]
        fun p' : solidTorusSet.{u} => ((N₀.handleChart k).symm p'.1).2 := by
      filter_upwards [hsymm] with p' hp'
      simp only [Function.comp_apply]
      rw [hp']
    have himm := (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)
      (n := ∞)).isImmersion.isImmersionAt (N₀.handleInv k p).2
    refine (ContMDiffAt.iff_comp_isImmersionAt (f := fun p' => (N₀.handleInv k p').2) (x := p)
      himm).mpr ⟨?_, h2.congr_of_eventuallyEq hev⟩
    exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (h2.continuousAt.congr hev.symm)

/-- **Smoothness of the glued map.** -/
theorem contMDiffAt_gluedMap (p : solidTorusSet.{u}) :
    ContMDiffAt (𝓡∂ 3) I ∞ (gluedMap N N₀) p := by
  by_cases hT : ∃ k b, p.1 ∈ (N₀.neck k b).target
  · obtain ⟨k, b, hkb⟩ := hT
    exact (contMDiffAt_gluedMap_of_mem_target N N₀ hkb).1
  push Not at hT
  have hpfil : ∀ k b, p.1 ∉ N₀.neck k b '' filletBox ε := fun k b h =>
    hT k b (N₀.neck_image_filletBox_subset_target k b h)
  obtain ⟨V, hV, hVp⟩ := N₀.exists_nhds_mem_pieces hpfil
  have hV' : ∀ᶠ p' in 𝓝 p, (p' : solidTorusSet.{u}).1 ∈ V :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hV
  rcases N₀.mem_union_cases p.2 with ⟨k, x, hx⟩ | ⟨k, q, hq⟩ | ⟨k, b, q, ⟨hqD, -⟩, hq⟩
  · have hloc : ∀ᶠ p' in 𝓝 p, (p' : solidTorusSet.{u}).1 ∈ range (N₀.ball k) := by
      filter_upwards [hV'] with p' hp'
      rcases hVp p'.1 hp' p'.2 with ⟨j, y, hy, hpj⟩ | ⟨j, q', -, hpj⟩
      · obtain ⟨z, hz⟩ := hpj
        have hj : j = k := ((N₀.ball_eq_ball_iff).mp (hz.trans hx.symm)).1
        subst hj
        exact ⟨y, hy⟩
      · exfalso
        obtain ⟨q'', hq''⟩ := hpj
        obtain ⟨b, hb⟩ := N₀.exists_target_of_handle_mem_ball (j := k) ⟨x, hx.trans hq''.symm⟩
        rw [hq''] at hb
        exact hT j b hb
    have hev : gluedMap N N₀ =ᶠ[𝓝 p] N.ball k ∘ N₀.ballInv k := by
      filter_upwards [hloc] with p' hp'
      obtain ⟨y, hy⟩ := hp'
      simp only [Function.comp_apply]
      rw [N₀.ballInv_eq hy]
      exact transfer_eq_ball N₀.toCycleNormalForm N p'.2 hy
    exact ((N.ball_smooth k).contMDiffAt.comp p (N₀.contMDiffAt_ballInv hloc)).congr_of_eventuallyEq
      hev
  · have hloc : ∀ᶠ p' in 𝓝 p, (p' : solidTorusSet.{u}).1 ∈ range (N₀.handle k) := by
      filter_upwards [hV'] with p' hp'
      rcases hVp p'.1 hp' p'.2 with ⟨j, y, -, hpj⟩ | ⟨j, q', hq', hpj⟩
      · exfalso
        obtain ⟨z, hz⟩ := hpj
        obtain ⟨b, hb⟩ := N₀.exists_target_of_handle_mem_ball (j := j) ⟨z, hz.trans hq.symm⟩
        rw [hq] at hb
        exact hT k b hb
      · obtain ⟨z, hz⟩ := hpj
        have hj : j = k := ((N₀.handle_eq_handle_iff).mp (hz.trans hq.symm)).1
        subst hj
        exact ⟨q', hq'⟩
    have hev : gluedMap N N₀ =ᶠ[𝓝 p] N.handle k ∘ N₀.handleInv k := by
      filter_upwards [hloc] with p' hp'
      obtain ⟨y, hy⟩ := hp'
      simp only [Function.comp_apply]
      rw [N₀.handleInv_eq hy]
      exact transfer_eq_handle N₀.toCycleNormalForm N p'.2 hy
    exact ((N.handle_smooth k).contMDiffAt.comp p
      (N₀.contMDiffAt_handleInv hloc)).congr_of_eventuallyEq hev
  · exact absurd (hq ▸ N₀.neck_mem_target hqD) (hT k b)

theorem contMDiff_gluedMap : ContMDiff (𝓡∂ 3) I ∞ (gluedMap N N₀) :=
  contMDiffAt_gluedMap N N₀

/-- At a model ball point the differential of the glued map is injective: it is onto, since
`gluedMap ∘ N₀.ball k = N.ball k` has bijective differential. -/
theorem injective_mfderiv_gluedMap_ball (k : Fin len) (x : ClosedCell 3) :
    Injective (mfderiv (𝓡∂ 3) I (gluedMap N N₀) ⟨N₀.ball k x, N₀.ball_mem k x⟩) := by
  let β : ClosedCell 3 → solidTorusSet.{u} := fun y => ⟨N₀.ball k y, N₀.ball_mem k y⟩
  have hβ : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ β := (contMDiff_solidTorus_iff β).mpr (N₀.ball_smooth k)
  have hFβ : gluedMap N N₀ ∘ β = N.ball k :=
    funext fun y => transfer_ball N₀.toCycleNormalForm N k y (N₀.ball_mem k y)
  have hcomp := mfderiv_comp x ((contMDiffAt_gluedMap N N₀ (β x)).mdifferentiableAt (by simp))
    ((hβ x).mdifferentiableAt (by simp))
  rw [hFβ] at hcomp
  have hsurj : Surjective (mfderiv (𝓡∂ 3) I (gluedMap N N₀) (β x)) := by
    intro v
    obtain ⟨w, hw⟩ := (N.ball_mfderiv k x).2 v
    rw [hcomp] at hw
    exact ⟨_, hw⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv (𝓡∂ 3) I (gluedMap N N₀) (β x)).toLinearMap) rfl).mpr hsurj

/-- At a model handle point the differential of the glued map is injective. -/
theorem injective_mfderiv_gluedMap_handle (k : Fin len) (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    Injective (mfderiv (𝓡∂ 3) I (gluedMap N N₀) ⟨N₀.handle k q, N₀.handle_mem k q⟩) := by
  let β : ClosedCell 2 × Icc (0 : ℝ) 1 → solidTorusSet.{u} :=
    fun y => ⟨N₀.handle k y, N₀.handle_mem k y⟩
  have hβ : ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ β :=
    (contMDiff_solidTorus_iff β).mpr (N₀.handle_smooth k)
  have hFβ : gluedMap N N₀ ∘ β = N.handle k :=
    funext fun y => transfer_handle N₀.toCycleNormalForm N k y (N₀.handle_mem k y)
  have hcomp := mfderiv_comp q ((contMDiffAt_gluedMap N N₀ (β q)).mdifferentiableAt (by simp))
    ((hβ q).mdifferentiableAt (by simp))
  rw [hFβ] at hcomp
  have hsurj : Surjective (mfderiv (𝓡∂ 3) I (gluedMap N N₀) (β q)) := by
    intro v
    obtain ⟨w, hw⟩ := (N.handle_mfderiv k q).2 v
    rw [hcomp] at hw
    exact ⟨_, hw⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv (𝓡∂ 3) I (gluedMap N N₀) (β q)).toLinearMap) rfl).mpr hsurj

/-- **Full rank of the glued map.** -/
theorem injective_mfderiv_gluedMap (p : solidTorusSet.{u}) :
    Injective (mfderiv (𝓡∂ 3) I (gluedMap N N₀) p) := by
  by_cases hT : ∃ k b, p.1 ∈ (N₀.neck k b).target
  · obtain ⟨k, b, hkb⟩ := hT
    exact (contMDiffAt_gluedMap_of_mem_target N N₀ hkb).2
  push Not at hT
  obtain ⟨p, hpU⟩ := p
  rcases N₀.mem_union_cases hpU with ⟨k, x, rfl⟩ | ⟨k, q, rfl⟩ | ⟨k, b, q, ⟨hqD, -⟩, rfl⟩
  · exact injective_mfderiv_gluedMap_ball N N₀ k x
  · exact injective_mfderiv_gluedMap_handle N N₀ k q
  · exact absurd (N₀.neck_mem_target hqD) (hT k b)

theorem injective_gluedMap : Injective (gluedMap N N₀) := fun p p' h =>
  Subtype.ext (transfer_injective N₀.toCycleNormalForm N p.2 p'.2 h)

theorem range_gluedMap : range (gluedMap N N₀) = U := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact transfer_mem N₀.toCycleNormalForm N p.1 p.2
  · intro hy
    obtain ⟨p, hp, hpy⟩ := exists_transfer_eq N₀.toCycleNormalForm N hy
    exact ⟨⟨p, hp⟩, hpy⟩

end Glued

end GC.GraphManifold.Assembly

namespace GC.GraphManifold.Assembly

/-- **G3c, gluing** (the frozen statement without its two unused instance hypotheses
`[IsManifold I ∞ X]`, `[T2Space X]`; the verbatim form is the `example` below). A cycle normal form
with union `U` in `X` and the model one at the same combinatorics and scale give a smooth injective
immersion of the solid torus onto `U`. -/
theorem exists_map_of_cycleNormalForms {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {len : ℕ} {ε : ℝ} {U : Set X} (N : CycleNormalForm I X len ε U)
    (N₀ : ModelCycleNormalForm.{u} len ε) :
    ∃ F : solidTorusSet.{u} → X, ContMDiff (𝓡∂ 3) I ∞ F ∧ Injective F ∧
      (∀ p, Injective (mfderiv (𝓡∂ 3) I F p)) ∧ range F = U :=
  ⟨gluedMap N N₀, contMDiff_gluedMap N N₀, injective_gluedMap N N₀,
    injective_mfderiv_gluedMap N N₀, range_gluedMap N N₀⟩

/-- The frozen G3c statement, verbatim. -/
example {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    {len : ℕ} {ε : ℝ} {U : Set X} (N : CycleNormalForm I X len ε U)
    (N₀ : ModelCycleNormalForm.{u} len ε) :
    ∃ F : solidTorusSet.{u} → X, ContMDiff (𝓡∂ 3) I ∞ F ∧ Injective F ∧
      (∀ p, Injective (mfderiv (𝓡∂ 3) I F p)) ∧ range F = U :=
  exists_map_of_cycleNormalForms N N₀

end GC.GraphManifold.Assembly
