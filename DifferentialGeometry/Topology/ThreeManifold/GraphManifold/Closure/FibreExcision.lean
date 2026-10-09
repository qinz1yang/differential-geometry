import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RegularFibreTube
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

/-!
# Actual excision of a regular circle fibre
-/

set_option autoImplicit false

noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.CircleFibration

def fibreExcisionPolar :
    PartialDiffeomorph (torusModel.prod 𝓘(ℝ)) (𝓘(ℝ, ℂ).prod (𝓡 1))
      (Torus × ℝ) (PlaneLift.{u} × Circle) ∞ where
  toFun p := (ULift.up ((1 + p.2 / 2) • (p.1.1 : ℂ)), p.1.2)
  invFun p := ((unitOf p.1.down, p.2), 2 * (‖p.1.down‖ - 1))
  source := {p | -2 < p.2}
  target := {p | p.1.down ≠ 0}
  map_source' p hp := by
    change -2 < p.2 at hp
    change (1 + p.2 / 2) • (p.1.1 : ℂ) ≠ 0
    exact smul_ne_zero (by linarith : (1 + p.2 / 2 : ℝ) ≠ 0) (Circle.coe_ne_zero p.1.1)
  map_target' p hp := by
    change -2 < 2 * (‖p.1.down‖ - 1)
    have hn := norm_pos_iff.mpr hp
    linarith
  left_inv' p hp := by
    change -2 < p.2 at hp
    have hr : 0 < 1 + p.2 / 2 := by linarith
    apply Prod.ext
    · exact Prod.ext (unitOf_smul hr p.1.1) rfl
    · change 2 * (‖(1 + p.2 / 2) • (p.1.1 : ℂ)‖ - 1) = p.2
      rw [norm_smul, Real.norm_of_nonneg hr.le, Circle.norm_coe, mul_one]
      ring
  right_inv' p hp := by
    apply Prod.ext
    · apply ULift.ext
      change (1 + (2 * (‖p.1.down‖ - 1)) / 2) • (unitOf p.1.down : ℂ) = p.1.down
      rw [show 1 + (2 * (‖p.1.down‖ - 1)) / 2 = ‖p.1.down‖ by ring]
      exact norm_smul_unitOf p.1.down
    · rfl
  open_source := isOpen_lt continuous_const continuous_snd
  open_target := isOpen_compl_singleton.preimage
    (continuous_uliftDown.comp continuous_fst)
  contMDiffOn_toFun := by
    have ha : ContMDiff (torusModel.prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞
        (fun p : Torus × ℝ => (1 + p.2 / 2) • (p.1.1 : ℂ)) :=
      (contMDiff_const.add (contMDiff_snd.div_const 2)).smul
        (contMDiff_circle_coe.comp (contMDiff_fst.comp contMDiff_fst))
    exact ((contMDiff_planeLift_up.comp ha).prodMk
      (contMDiff_snd.comp contMDiff_fst)).contMDiffOn
  contMDiffOn_invFun := by
    have hd : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
        (fun p : PlaneLift.{u} × Circle => p.1.down) :=
      contMDiff_planeLift_down.comp contMDiff_fst
    have hu : ContMDiffOn (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 1) ∞
        (fun p : PlaneLift.{u} × Circle => unitOf p.1.down) {p | p.1.down ≠ 0} :=
      contMDiffOn_unitOf.comp hd.contMDiffOn (fun p hp => hp)
    have hn : ContMDiffOn (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ) ∞
        (fun p : PlaneLift.{u} × Circle => 2 * (‖p.1.down‖ - 1))
        {p | p.1.down ≠ 0} := by
      intro p hp
      have hnorm := (contDiffAt_norm ℝ hp).contMDiffAt.comp p (hd p)
      exact (contMDiffAt_const.mul (hnorm.sub contMDiffAt_const)).contMDiffWithinAt
    exact (hu.prodMk contMDiff_snd.contMDiffOn).prodMk hn

def fibreExcisionClosedDisc : Set (PlaneLift.{u} × Circle) :=
  {p | ‖p.1.down‖ ≤ 1}

def fibreExcisionOpenDisc : Set (PlaneLift.{u} × Circle) :=
  {p | ‖p.1.down‖ < 1}

private theorem fibreExcisionClosedDisc_compact : IsCompact fibreExcisionClosedDisc.{u} := by
  have hc : IsCompact {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} := by
    have he : {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} =
        (Homeomorph.ulift.symm : ℂ ≃ₜ PlaneLift.{u}) '' Metric.closedBall 0 1 := by
      ext z
      rcases z with ⟨z⟩
      simp [Metric.mem_closedBall, dist_zero_right, Homeomorph.ulift]
    rw [he]
    exact (isCompact_closedBall (0 : ℂ) 1).image Homeomorph.ulift.symm.continuous
  have he : fibreExcisionClosedDisc.{u} = {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} ×ˢ univ := by
    ext p
    simp [fibreExcisionClosedDisc]
  rw [he]
  exact hc.prod isCompact_univ

private theorem fibreExcisionClosedDisc_interior :
    interior fibreExcisionClosedDisc.{u} = fibreExcisionOpenDisc.{u} := by
  have heq : fibreExcisionClosedDisc.{u} =
      ((Homeomorph.ulift.symm : ℂ ≃ₜ PlaneLift.{u}) '' Metric.closedBall 0 1) ×ˢ univ := by
    ext p
    rcases p with ⟨⟨z⟩, t⟩
    simp [fibreExcisionClosedDisc, Metric.mem_closedBall, dist_zero_right, Homeomorph.ulift]
  rw [heq, interior_prod_eq, interior_univ, ← Homeomorph.image_interior,
    interior_closedBall (0 : ℂ) one_ne_zero]
  ext p
  rcases p with ⟨⟨z⟩, t⟩
  simp [fibreExcisionOpenDisc, Metric.mem_ball, dist_zero_right, Homeomorph.ulift]

private theorem fibreExcisionClosedDisc_regular :
    closure (interior fibreExcisionClosedDisc.{u}) = fibreExcisionClosedDisc.{u} := by
  rw [fibreExcisionClosedDisc_interior]
  have he : fibreExcisionOpenDisc.{u} =
      ((Homeomorph.ulift.symm : ℂ ≃ₜ PlaneLift.{u}) '' Metric.ball 0 1) ×ˢ univ := by
    ext p
    rcases p with ⟨⟨z⟩, t⟩
    simp [fibreExcisionOpenDisc, Metric.mem_ball, dist_zero_right, Homeomorph.ulift]
  rw [he]
  rw [closure_prod_eq, closure_univ, ← Homeomorph.image_closure, closure_ball (0 : ℂ) one_ne_zero]
  ext p
  rcases p with ⟨⟨z⟩, t⟩
  simp [fibreExcisionClosedDisc, Metric.mem_closedBall, dist_zero_right, Homeomorph.ulift]

section Excision

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] [CompactSpace M]

variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
  (PlaneLift.{u} × Circle) M ∞)
  (hφ : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)

def fibreExcisionSet : Set M := (φ '' fibreExcisionOpenDisc)ᶜ

include hφ

omit [T2Space M] [CompactSpace M] in
private theorem fibreExcision_disc_source : fibreExcisionClosedDisc.{u} ⊆ φ.source := by
  intro p hp
  exact hφ (by change ‖p.1.down‖ ≤ 3; change ‖p.1.down‖ ≤ 1 at hp; linarith)

omit [T2Space M] [CompactSpace M] in
private theorem fibreExcision_image_compact : IsCompact (φ '' fibreExcisionClosedDisc) :=
  fibreExcisionClosedDisc_compact.image_of_continuousOn
    (φ.contMDiffOn.continuousOn.mono (fibreExcision_disc_source φ hφ))

omit [T2Space M] [CompactSpace M] in
private theorem fibreExcision_image_interior :
    interior (φ '' fibreExcisionClosedDisc) = φ '' fibreExcisionOpenDisc := by
  have h := φ.toOpenPartialHomeomorph.image_interior_of_subset_source
    (fibreExcision_disc_source φ hφ)
  change φ '' interior fibreExcisionClosedDisc = interior (φ '' fibreExcisionClosedDisc) at h
  rw [fibreExcisionClosedDisc_interior] at h
  exact h.symm

omit [T2Space M] [CompactSpace M] in
private theorem fibreExcisionSet_closed : IsClosed (fibreExcisionSet φ) := by
  apply IsOpen.isClosed_compl
  exact φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_lt ((continuous_uliftDown.comp continuous_fst).norm) continuous_const)
    (fun p hp => hφ (by change ‖p.1.down‖ ≤ 3; change ‖p.1.down‖ < 1 at hp; linarith))

omit [CompactSpace M] in
private theorem fibreExcision_image_regular :
    closure (interior (φ '' fibreExcisionClosedDisc)) = φ '' fibreExcisionClosedDisc :=
  φ.toOpenPartialHomeomorph.closure_interior_image_of_subset_source
    (fibreExcision_disc_source φ hφ) fibreExcisionClosedDisc_regular
    (fibreExcision_image_compact φ hφ).isClosed

omit [CompactSpace M] in
private theorem fibreExcisionSet_interior :
    interior (fibreExcisionSet φ) = (φ '' fibreExcisionClosedDisc)ᶜ := by
  rw [fibreExcisionSet, interior_compl, ← fibreExcision_image_interior φ hφ,
    fibreExcision_image_regular φ hφ]

omit hφ [T2Space M] [CompactSpace M] in
private theorem fibreExcisionClosedDisc_frontier :
    frontier fibreExcisionClosedDisc.{u} = {p | ‖p.1.down‖ = 1} := by
  rw [frontier, fibreExcisionClosedDisc_compact.isClosed.closure_eq,
    fibreExcisionClosedDisc_interior]
  ext p
  simp only [fibreExcisionClosedDisc, fibreExcisionOpenDisc, mem_sdiff, mem_ofPred_eq, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

omit [CompactSpace M] in
private theorem fibreExcision_frontier :
    frontier (fibreExcisionSet φ) = φ '' {p | ‖p.1.down‖ = 1} := by
  have hi := φ.toOpenPartialHomeomorph.image_frontier_of_subset_source
    (fibreExcision_disc_source φ hφ) fibreExcisionClosedDisc_compact.isClosed
    (fibreExcision_image_compact φ hφ).isClosed
  rw [fibreExcisionClosedDisc_frontier] at hi
  rw [fibreExcisionSet, ← fibreExcision_image_interior φ hφ, frontier_compl]
  rw [frontier, interior_interior, fibreExcision_image_regular φ hφ]
  change φ '' {p | ‖p.1.down‖ = 1} = frontier (φ '' fibreExcisionClosedDisc) at hi
  rw [frontier, (fibreExcision_image_compact φ hφ).isClosed.closure_eq] at hi
  exact hi.symm

def fibreExcisionSigned :
    PartialDiffeomorph (torusModel.prod 𝓘(ℝ)) (𝓡 3) (Torus × ℝ) M ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    (fibreExcisionPolar.trans φ) {p | -1 < p.2 ∧ p.2 < 2}
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const))

omit [T2Space M] [CompactSpace M] in
private theorem fibreExcisionSigned_source {p : Torus × ℝ}
    (hp : -1 < p.2 ∧ p.2 < 2) : p ∈ (fibreExcisionSigned φ).source := by
  refine ⟨⟨by change -2 < p.2; linarith [hp.1], ?_⟩, hp⟩
  apply hφ
  change ‖(1 + p.2 / 2) • (p.1.1 : ℂ)‖ ≤ 3
  rw [norm_smul, Real.norm_of_nonneg (by linarith [hp.1]), Circle.norm_coe, mul_one]
  linarith [hp.2]

omit [T2Space M] [CompactSpace M] in
private theorem fibreExcisionSigned_mem_iff {p : Torus × ℝ}
    (hp : p ∈ (fibreExcisionSigned φ).source) :
    fibreExcisionSigned φ p ∈ fibreExcisionSet φ ↔ 0 ≤ p.2 := by
  have hr : 0 < 1 + p.2 / 2 := by have ht := hp.2.1; linarith
  have hn : ‖(fibreExcisionPolar p).1.down‖ = 1 + p.2 / 2 := by
    change ‖(1 + p.2 / 2) • (p.1.1 : ℂ)‖ = 1 + p.2 / 2
    rw [norm_smul, Real.norm_of_nonneg hr.le, Circle.norm_coe, mul_one]
  change φ (fibreExcisionPolar p) ∉ φ '' fibreExcisionOpenDisc ↔ 0 ≤ p.2
  constructor
  · intro h
    by_contra! ht
    apply h
    exact ⟨fibreExcisionPolar p, by change ‖(fibreExcisionPolar p).1.down‖ < 1; linarith, rfl⟩
  · intro ht h
    obtain ⟨q, hq, heq⟩ := h
    have hqs := hφ (by change ‖q.1.down‖ ≤ 3; change ‖q.1.down‖ < 1 at hq; linarith)
    have he := φ.injOn hqs hp.1.2 heq
    have hqn : ‖q.1.down‖ < 1 := hq
    have he' : q = fibreExcisionPolar p := he
    rw [he', hn] at hqn
    linarith

omit [CompactSpace M] in
private theorem fibreExcision_boundary_param {x : M}
    (hx : x ∈ frontier (fibreExcisionSet φ)) :
    ∃ t : Torus, fibreExcisionSigned φ (t, 0) = x := by
  rw [fibreExcision_frontier φ hφ] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨(unitOf p.1.down, p.2), ?_⟩
  change φ (ULift.up ((1 + (0 : ℝ) / 2) • (unitOf p.1.down : ℂ)), p.2) = φ p
  congr 1
  apply Prod.ext
  · apply ULift.ext
    change (1 + (0 : ℝ) / 2) • (unitOf p.1.down : ℂ) = p.1.down
    change ‖p.1.down‖ = 1 at hp
    rw [zero_div, add_zero, ← hp]
    exact norm_smul_unitOf p.1.down
  · rfl

private def fibreExcisionNormalFirst :
    ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ)
      ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((ContinuousLinearEquiv.prodComm ℝ
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ℝ).trans
      ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
        (ContinuousLinearEquiv.ofFinrankEq (by simp)))).trans
          (SmoothBoundaryAtlas.firstCoordinateEquiv 2)

private def fibreExcisionNormalFirstDiffeomorph :
    ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ)
      ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)).prod
        𝓘(ℝ), 𝓡 3⟯ EuclideanSpace ℝ (Fin 3) where
  toEquiv := fibreExcisionNormalFirst.toEquiv
  contMDiff_toFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact fibreExcisionNormalFirst.contDiff.contMDiff
  contMDiff_invFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact fibreExcisionNormalFirst.symm.contDiff.contMDiff

private def fibreExcisionBoundaryChart (t : Torus) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) M (EuclideanSpace ℝ (Fin 3)) ∞ :=
  ((fibreExcisionSigned φ).symm.trans
    ((DifferentialGeometry.Topology.PartialDiffeomorph.extendedChart (I := torusModel) t).prod
      (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).toPartialDiffeomorph)).trans
        fibreExcisionNormalFirstDiffeomorph.toPartialDiffeomorph

omit hφ [T2Space M] [CompactSpace M] in
private theorem fibreExcisionBoundaryChart_zero (t : Torus) (x : M) :
    fibreExcisionBoundaryChart φ t x 0 = ((fibreExcisionSigned φ).symm x).2 := rfl

omit [T2Space M] [CompactSpace M] in
private theorem fibreExcisionBoundaryChart_source (t : Torus) :
    fibreExcisionSigned φ (t, 0) ∈ (fibreExcisionBoundaryChart φ t).source := by
  have hs : (t, (0 : ℝ)) ∈ (fibreExcisionSigned φ).source :=
    fibreExcisionSigned_source φ hφ (by constructor <;> norm_num)
  refine ⟨⟨(fibreExcisionSigned φ).map_source hs, ?_, trivial⟩, trivial⟩
  change ((fibreExcisionSigned φ).symm (fibreExcisionSigned φ (t, 0))).1 ∈
    (extChartAt torusModel t).source
  have he : ((fibreExcisionSigned φ).symm (fibreExcisionSigned φ (t, 0))).1 = t :=
    congrArg Prod.fst ((fibreExcisionSigned φ).left_inv hs)
  exact he.symm ▸ mem_extChartAt_source t

omit [T2Space M] [CompactSpace M] in
private theorem fibreExcisionBoundaryChart_mem_iff (t : Torus) {x : M}
    (hx : x ∈ (fibreExcisionBoundaryChart φ t).source) :
    x ∈ fibreExcisionSet φ ↔ 0 ≤ fibreExcisionBoundaryChart φ t x 0 := by
  rw [fibreExcisionBoundaryChart_zero]
  have h := fibreExcisionSigned_mem_iff φ hφ
    ((fibreExcisionSigned φ).map_target hx.1.1)
  have he := (fibreExcisionSigned φ).right_inv' hx.1.1
  change fibreExcisionSigned φ ((fibreExcisionSigned φ).symm.toPartialEquiv x) = x at he
  change fibreExcisionSigned φ ((fibreExcisionSigned φ).symm.toPartialEquiv x) ∈
    fibreExcisionSet φ ↔ 0 ≤ ((fibreExcisionSigned φ).symm.toPartialEquiv x).2 at h
  rw [he] at h
  exact h

variable [IsManifold (𝓡 3) ∞ M]

omit [CompactSpace M] in
private theorem fibreExcision_exists_atlas :
    ∃ A : SmoothBoundaryAtlas (𝓡 3) 3 (fibreExcisionSet φ),
      ∀ x, A.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier (fibreExcisionSet φ) := by
  have hc : ∀ x : fibreExcisionSet φ,
      ∃ a : PartialDiffeomorph (𝓡 3) (𝓡 3) M (EuclideanSpace ℝ (Fin 3)) ∞,
        x.val ∈ a.source ∧ (∀ y ∈ a.source, y ∈ fibreExcisionSet φ ↔ 0 ≤ a y 0) ∧
          (a x.val 0 = 0 ↔ x.val ∈ frontier (fibreExcisionSet φ)) := by
    intro x
    by_cases hx : x.val ∈ interior (fibreExcisionSet φ)
    · obtain ⟨a, ha, hsub, hpos⟩ :=
        SmoothBoundaryAtlas.exists_partialDiffeomorph_coord_pos (𝓡 3)
          (n := 2) (by simp) isOpen_interior hx
      refine ⟨a, ha, fun y hy => iff_of_true (interior_subset (hsub hy)) (hpos y hy).le, ?_⟩
      exact iff_of_false (hpos x.val ha).ne' (fun hf => hf.2 hx)
    · have hf : x.val ∈ frontier (fibreExcisionSet φ) := ⟨subset_closure x.2, hx⟩
      obtain ⟨t, ht⟩ := fibreExcision_boundary_param φ hφ hf
      refine ⟨fibreExcisionBoundaryChart φ t, ht ▸ fibreExcisionBoundaryChart_source φ hφ t,
        fun y hy => fibreExcisionBoundaryChart_mem_iff φ hφ t hy, ?_⟩
      apply iff_of_true ?_ hf
      rw [← ht, fibreExcisionBoundaryChart_zero]
      have hs := fibreExcisionSigned_source φ hφ
        (p := (t, 0)) (by constructor <;> norm_num)
      exact congrArg Prod.snd ((fibreExcisionSigned φ).left_inv' hs)
  choose a ha hmem hz using hc
  exact ⟨⟨a, ha, hmem⟩, hz⟩

private def fibreExcisionAtlas : SmoothBoundaryAtlas (𝓡 3) 3 (fibreExcisionSet φ) :=
  Classical.choose (fibreExcision_exists_atlas φ hφ)

omit [CompactSpace M] in
private theorem fibreExcisionAtlas_boundary (x : fibreExcisionSet φ) :
    letI := (fibreExcisionAtlas φ hφ).toChartedSpace
    (𝓡∂ 3).IsBoundaryPoint x ↔ x.val ∈ frontier (fibreExcisionSet φ) := by
  rw [(fibreExcisionAtlas φ hφ).isBoundaryPoint_iff]
  exact Classical.choose_spec (fibreExcision_exists_atlas φ hφ) x

private def fibreExcisionCollarMap (p : Torus × EuclideanHalfSpace 1) : fibreExcisionSet φ :=
  ⟨fibreExcisionSigned φ (p.1, min (p.2.val 0) 1),
    (fibreExcisionSigned_mem_iff φ hφ
      (fibreExcisionSigned_source φ hφ (by
        constructor
        · have hs := p.2.2
          have hm : 0 ≤ min (p.2.val 0) 1 := le_min hs zero_le_one
          linarith
        · exact lt_of_le_of_lt (min_le_right (p.2.val 0) 1) (by norm_num)))).mpr
      (le_min p.2.2 zero_le_one)⟩

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] in
private theorem fibreExcisionCollarMap_val {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    (fibreExcisionCollarMap φ hφ p).val = fibreExcisionSigned φ (p.1, p.2.val 0) := by
  change fibreExcisionSigned φ (p.1, min (p.2.val 0) 1) = _
  rw [min_eq_left (show p.2.val 0 < 1 from hp).le]

private def fibreExcisionCollarTarget : Set (fibreExcisionSet φ) :=
  {x | x.val ∈ (fibreExcisionSigned φ).target ∧ ((fibreExcisionSigned φ).symm x.val).2 < 1}

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] in
private theorem fibreExcisionCollarTarget_nonneg {x : fibreExcisionSet φ}
    (hx : x ∈ fibreExcisionCollarTarget φ) : 0 ≤ ((fibreExcisionSigned φ).symm x.val).2 := by
  apply (fibreExcisionSigned_mem_iff φ hφ
    ((fibreExcisionSigned φ).map_target hx.1)).mp
  have he : fibreExcisionSigned φ ((fibreExcisionSigned φ).symm x.val) = x.val :=
    (fibreExcisionSigned φ).right_inv hx.1
  exact he.symm ▸ x.2

private def fibreExcisionCollarInv (x : fibreExcisionSet φ) : Torus × EuclideanHalfSpace 1 :=
  (((fibreExcisionSigned φ).symm x.val).1,
    Manifold.halfSpaceOneLift (((fibreExcisionSigned φ).symm x.val).2))

private def fibreExcisionCollar :
    letI := (fibreExcisionAtlas φ hφ).toChartedSpace
    PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) (fibreExcisionSet φ) ∞ := by
  letI := (fibreExcisionAtlas φ hφ).toChartedSpace
  refine
    { toFun := fibreExcisionCollarMap φ hφ
      invFun := fibreExcisionCollarInv φ
      source := halfCollarSource
      target := fibreExcisionCollarTarget φ
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := ?_
      open_target := ?_
      contMDiffOn_toFun := ?_
      contMDiffOn_invFun := ?_ }
  · intro p hp
    have hs := fibreExcisionSigned_source φ hφ
      (p := (p.1, p.2.val 0)) (by
        have ht : p.2.val 0 < 1 := hp
        constructor <;> linarith [p.2.2])
    change (fibreExcisionCollarMap φ hφ p).val ∈ (fibreExcisionSigned φ).target ∧
      ((fibreExcisionSigned φ).symm (fibreExcisionCollarMap φ hφ p).val).2 < 1
    rw [fibreExcisionCollarMap_val φ hφ hp]
    have he : (fibreExcisionSigned φ).symm.toPartialEquiv
        (fibreExcisionSigned φ (p.1, p.2.val 0)) = (p.1, p.2.val 0) :=
      (fibreExcisionSigned φ).left_inv hs
    rw [he]
    exact ⟨(fibreExcisionSigned φ).map_source hs, hp⟩
  · intro x hx
    change max (((fibreExcisionSigned φ).symm x.val).2) 0 < 1
    exact max_lt hx.2 one_pos
  · intro p hp
    have hs := fibreExcisionSigned_source φ hφ
      (p := (p.1, p.2.val 0)) (by
        have ht : p.2.val 0 < 1 := hp
        constructor <;> linarith [p.2.2])
    change fibreExcisionCollarInv φ (fibreExcisionCollarMap φ hφ p) = p
    unfold fibreExcisionCollarInv
    rw [fibreExcisionCollarMap_val φ hφ hp]
    have he : (fibreExcisionSigned φ).symm.toPartialEquiv
        (fibreExcisionSigned φ (p.1, p.2.val 0)) = (p.1, p.2.val 0) :=
      (fibreExcisionSigned φ).left_inv hs
    rw [he, halfSpaceOneLift_coord]
  · intro x hx
    have hn := fibreExcisionCollarTarget_nonneg φ hφ hx
    have hs : fibreExcisionCollarInv φ x ∈ halfCollarSource := by
      change max (((fibreExcisionSigned φ).symm x.val).2) 0 < 1
      exact max_lt hx.2 one_pos
    apply Subtype.ext
    rw [fibreExcisionCollarMap_val φ hφ hs]
    change fibreExcisionSigned φ
      (((fibreExcisionSigned φ).symm x.val).1,
        max (((fibreExcisionSigned φ).symm x.val).2) 0) = x.val
    rw [max_eq_left hn]
    exact (fibreExcisionSigned φ).right_inv hx.1
  · exact isOpen_lt
      ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
      continuous_const
  · exact ((fibreExcisionSigned φ).symm.contMDiffOn.continuousOn.isOpen_inter_preimage
      (fibreExcisionSigned φ).open_target
      (isOpen_lt continuous_snd continuous_const)).preimage continuous_subtype_val
  · apply ((fibreExcisionAtlas φ hφ).contMDiffOn_iff_subtype_val
      (fibreExcisionCollarMap φ hφ) halfCollarSource).mpr
    have hg : ContMDiff halfCollarModel (torusModel.prod 𝓘(ℝ)) ∞
        (fun p : Torus × EuclideanHalfSpace 1 => (p.1, p.2.val 0)) :=
      contMDiff_fst.prodMk (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
    have hc := (fibreExcisionSigned φ).contMDiffOn.comp hg.contMDiffOn
      (fun p hp => fibreExcisionSigned_source φ hφ (by
        have ht : p.2.val 0 < 1 := hp
        constructor <;> linarith [p.2.2]))
    exact hc.congr (fun p hp => fibreExcisionCollarMap_val φ hφ hp)
  · have hv := (fibreExcisionAtlas φ hφ).contMDiff_subtype_val
    have hc : ContMDiffOn (𝓡∂ 3) (torusModel.prod 𝓘(ℝ)) ∞
        (fun x : fibreExcisionSet φ => (fibreExcisionSigned φ).symm x.val)
        (fibreExcisionCollarTarget φ) :=
      (fibreExcisionSigned φ).symm.contMDiffOn.comp hv.contMDiffOn
        (fun x hx => hx.1)
    have hfirst := contMDiff_fst.comp_contMDiffOn hc
    have hsecond := contMDiff_snd.comp_contMDiffOn hc
    exact hfirst.prodMk (Manifold.contMDiffOn_halfSpaceOneLift.comp hsecond
      (fun x hx => fibreExcisionCollarTarget_nonneg φ hφ hx))

variable [SecondCountableTopology M]

private def fibreExcisionCarrier (O : ManifoldOrientation (𝓡 3) M 3) : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := fibreExcisionSet φ
  charts := (fibreExcisionAtlas φ hφ).toChartedSpace
  smooth := (fibreExcisionAtlas φ hφ).isManifold
  compact := isCompact_iff_compactSpace.mp (fibreExcisionSet_closed φ hφ).isCompact
  orientation := (fibreExcisionAtlas φ hφ).orientation O

private def fibreExcisionBoundary (O : ManifoldOrientation (𝓡 3) M 3) :
    BoundaryTori (fibreExcisionCarrier φ hφ O) 1 := by
  let : ChartedSpace (EuclideanHalfSpace 3) (fibreExcisionSet φ) :=
    (fibreExcisionAtlas φ hφ).toChartedSpace
  exact {
  collar i := fibreExcisionCollar φ hφ
  source_eq i := rfl
  boundary_zero i t := by
    apply (fibreExcisionAtlas_boundary φ hφ
      (fibreExcisionCollar φ hφ (t, halfZero))).mpr
    rw [fibreExcision_frontier φ hφ]
    refine ⟨(ULift.up (t.1 : ℂ), t.2), Circle.norm_coe t.1, ?_⟩
    change φ (ULift.up (t.1 : ℂ), t.2) =
      fibreExcisionSigned φ (t, min (halfZero.val 0) 1)
    change φ (ULift.up (t.1 : ℂ), t.2) =
      φ (ULift.up ((1 + min (0 : ℝ) 1 / 2) • (t.1 : ℂ)), t.2)
    norm_num
  disjoint i j hij := (hij (Subsingleton.elim i j)).elim }

private theorem fibreExcisionBoundary_exhausted (O : ManifoldOrientation (𝓡 3) M 3) :
    (fibreExcisionCarrier φ hφ O).model.boundary (fibreExcisionCarrier φ hφ O).Carrier =
      (fibreExcisionBoundary φ hφ O).image := by
  let : ChartedSpace (EuclideanHalfSpace 3) (fibreExcisionSet φ) :=
    (fibreExcisionAtlas φ hφ).toChartedSpace
  change (𝓡∂ 3).boundary (fibreExcisionSet φ) = (fibreExcisionBoundary φ hφ O).image
  ext x
  change (𝓡∂ 3).IsBoundaryPoint x ↔ x ∈ (fibreExcisionBoundary φ hφ O).image
  rw [fibreExcisionAtlas_boundary φ hφ]
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := fibreExcision_boundary_param φ hφ hx
    apply mem_iUnion.mpr
    refine ⟨0, t, ?_⟩
    apply Subtype.ext
    change fibreExcisionSigned φ (t, min (halfZero.val 0) 1) = x.val
    change fibreExcisionSigned φ (t, min (0 : ℝ) 1) = x.val
    simpa only [min_eq_left zero_le_one] using ht
  · intro hx
    obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hx
    exact (fibreExcisionAtlas_boundary φ hφ
      ((fibreExcisionBoundary φ hφ O).torusMap i t)).mp
      ((fibreExcisionBoundary φ hφ O).boundary_zero i t)

end Excision

theorem exists_regularFibreExcision
    (C : ConnectedClosedOrientedManifold.{u} 3)
    (F : CircleFibration (NoCuts.carrier C) ⊤) :
    ∃ β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
        PlaneLift.{u} F.base.Carrier ∞,
    ∃ φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
        (PlaneLift.{u} × Circle) C.Carrier ∞,
      {z | ‖z.down‖ ≤ 3} ⊆ β.source ∧
      φ.source = β.source ×ˢ Set.univ ∧
      (∀ z t, z ∈ β.source → F.projection ⟨φ (z, t), trivial⟩ = β z) ∧
      ∃ K : CompactCarrier.{u}, ∃ ι : K.Carrier → C.Carrier,
      ∃ E : BoundaryTori K 1,
        K.kind = .withBoundary ∧
        IsSmoothEmbedding K.model (𝓡 3) ∞ ι ∧
        Set.range ι = (φ '' {p | ‖p.1.down‖ < 1})ᶜ ∧
        K.model.boundary K.Carrier = E.image ∧
        (∀ x, Function.Bijective (mfderiv K.model (𝓡 3) ι x)) ∧
        (∀ x, ∃ D : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
          D.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
          Orientation.map (Fin 3) D.toLinearEquiv (K.orientation.orientation x) =
            C.orientation.orientation (ι x)) ∧
        ∀ (t : Torus) (s : EuclideanHalfSpace 1), s.val 0 < 1 →
          ι (E.collar 0 (t, s)) =
            φ (ULift.up ((1 + s.val 0 / 2) • (t.1 : ℂ)), t.2) := by
  obtain ⟨β, φ, hβ, hsource, htarget, hbase, hprojection⟩ := F.exists_regularFibreTube
  let : SecondCountableTopology C.Carrier := (NoCuts.carrier C).secondCountable
  have hφ : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source := by
    intro p hp
    rw [hsource]
    exact ⟨hβ hp, mem_univ p.2⟩
  let K := fibreExcisionCarrier φ hφ C.orientation
  let ι : K.Carrier → C.Carrier := Subtype.val
  let E := fibreExcisionBoundary φ hφ C.orientation
  refine ⟨β, φ, hβ, hsource, ?_, K, ι, E, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z t hz
    obtain ⟨hu, he⟩ := hprojection z t hz
    exact he
  · exact (fibreExcisionAtlas φ hφ).isSmoothEmbedding_subtype_val
  · exact Subtype.range_coe
  · exact fibreExcisionBoundary_exhausted φ hφ C.orientation
  · exact (fibreExcisionAtlas φ hφ).mfderiv_subtypeVal_bijective
  · intro x
    refine ⟨(fibreExcisionAtlas φ hφ).inclusionDifferentialEquiv x, rfl, ?_⟩
    exact (fibreExcisionAtlas φ hφ).orientation_map_inclusion C.orientation x
  · intro t s hs
    change (fibreExcisionCollarMap φ hφ (t, s)).val = _
    rw [fibreExcisionCollarMap_val φ hφ hs]
    rfl

theorem exists_fibreExcision_of_tube
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) M ∞)
    (hφ : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (O : ManifoldOrientation (𝓡 3) M 3) :
    ∃ K : CompactCarrier.{u}, ∃ ι : K.Carrier → M, ∃ E : BoundaryTori K 1,
      K.kind = .withBoundary ∧
      IsSmoothEmbedding K.model (𝓡 3) ∞ ι ∧
      Set.range ι = (φ '' {p | ‖p.1.down‖ < 1})ᶜ ∧
      K.model.boundary K.Carrier = E.image ∧
      (∀ x, Function.Bijective (mfderiv K.model (𝓡 3) ι x)) ∧
      (∀ x, ∃ D : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
        D.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
        Orientation.map (Fin 3) D.toLinearEquiv (K.orientation.orientation x) =
          O.orientation (ι x)) ∧
      ∀ (t : Torus) (s : EuclideanHalfSpace 1), s.val 0 < 1 →
        ι (E.collar 0 (t, s)) =
          φ (ULift.up ((1 + s.val 0 / 2) • (t.1 : ℂ)), t.2) := by
  let K := fibreExcisionCarrier φ hφ O
  let ι : K.Carrier → M := Subtype.val
  let E := fibreExcisionBoundary φ hφ O
  refine ⟨K, ι, E, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fibreExcisionAtlas φ hφ).isSmoothEmbedding_subtype_val
  · exact Subtype.range_coe
  · exact fibreExcisionBoundary_exhausted φ hφ O
  · exact (fibreExcisionAtlas φ hφ).mfderiv_subtypeVal_bijective
  · intro x
    refine ⟨(fibreExcisionAtlas φ hφ).inclusionDifferentialEquiv x, rfl, ?_⟩
    exact (fibreExcisionAtlas φ hφ).orientation_map_inclusion O x
  · intro t s hs
    change (fibreExcisionCollarMap φ hφ (t, s)).val = _
    rw [fibreExcisionCollarMap_val φ hφ hs]
    rfl

end GC.GraphManifold.CircleFibration
