import DifferentialGeometry.Topology.Manifold.ClosedBall.BallChart
import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.Manifold.ClosedBall.Coordinates
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs

noncomputable section

open Manifold Module
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
local instance : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem cap_mfderiv_orientation (b : T.Boundary) (x : ClosedCell 3) (hx : ‖x.val‖ < 1) :
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (C.cap b) x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) (C.cap b) x).toLinearMap hj)
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation =
          (if b.2 then (1 : ℝˣ) else -1) • N.orientation.orientation (C.cap b x) := by
  have hint : (𝓡∂ 3).IsInteriorPoint x := by
    rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
    change x ∉ (𝓡∂ 3).boundary (ClosedCell 3)
    rw [Manifold.closedCell_boundary_eq_sphere 2]
    exact ne_of_lt hx
  obtain ⟨hi, hj, h⟩ := C.cap_positive b x hint
  refine ⟨hj, ?_⟩
  have heq : (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → E3) x).toLinearMap hi).symm.trans
      (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) (C.cap b) x).toLinearMap hj) =
      LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) (C.cap b) x).toLinearMap hj := by
    have hinc : LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ClosedCell 3 → E3) x).toLinearMap hi = LinearEquiv.refl ℝ E3 := by
      ext v
      exact congrArg (fun L : E3 →L[ℝ] E3 => L v)
        (Manifold.mfderiv_closedCell_inclusion_of_norm_lt_one hx)
    rw [hinc]
    rfl
  rwa [heq] at h

private theorem cap_mfderiv_signed_scale_orientation (b : T.Boundary)
    (x : ClosedCell 3) (hx : ‖x.val‖ < 1) (r : ℝ) (hr : 0 < r) :
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (C.cap b) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.smulOfNeZero ℝ E3 (if b.2 then r else -r)
          (by cases b.2 <;> simp [ne_of_gt hr])).trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) (C.cap b) x).toLinearMap hj))
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation =
          N.orientation.orientation (C.cap b x) := by
  obtain ⟨hj, h⟩ := C.cap_mfderiv_orientation b x hx
  refine ⟨hj, ?_⟩
  erw [Topology.orientation_map_trans]
  cases hb : b.2 with
  | true =>
    simp only [hb, ite_true, one_smul] at h ⊢
    rw [Topology.orientation_map_smulOfNeZero_pos r hr]
    exact h
  | false =>
    simp only [hb, Bool.false_eq_true, ite_false] at h ⊢
    erw [Module.Ray.neg_units_smul, one_smul] at h
    have hs : Orientation.map (Fin 3)
        (LinearEquiv.smulOfNeZero ℝ E3 (-r) (neg_ne_zero.mpr (ne_of_gt hr)))
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation =
        -(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation := by
      apply (Orientation.map_eq_neg_iff_det_neg _ _ (by simp)).mpr
      change LinearMap.det ((-r) • (LinearMap.id : E3 →ₗ[ℝ] E3)) < 0
      rw [LinearMap.det_smul, LinearMap.det_id]
      norm_num
      rw [show (-r : ℝ) ^ 3 = -(r ^ 3) by ring]
      exact neg_lt_zero.mpr (pow_pos hr 3)
    rw [hs]
    erw [Orientation.map_neg, h, neg_neg]

theorem exists_orientedBallChart_cap (b : T.Boundary) :
    ∃ c : OrientedBallChart N,
      c.chart.source = Metric.ball 0 4 ∧
      c.chart.target = C.cap b '' {x : ClosedCell 3 | ‖x.val‖ < 1} ∧
      ∀ (x : E3) (hx : ‖(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • x‖ < 1),
        c.chart x = C.cap b ⟨(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • x, hx.le⟩ := by
  obtain ⟨φ, hsource, htarget, hφ⟩ :=
    Manifold.exists_partialDiffeomorph_of_closedCell_embedding (C.cap b) (C.cap_embedding b)
  let r : ℝ := if b.2 then 1 / 4 else -(1 / 4)
  have hr : r ≠ 0 := by dsimp only [r]; cases b.2 <;> norm_num
  let A : E3 ≃L[ℝ] E3 := (LinearEquiv.smulOfNeZero ℝ E3 r hr).toContinuousLinearEquiv
  let ψ := A.toDiffeomorph.toPartialDiffeomorph.trans φ
  have hs : ψ.source = Metric.ball 0 4 := by
    change Set.univ ∩ A ⁻¹' φ.source = _
    rw [hsource, Set.univ_inter]
    ext x
    change r • x ∈ Metric.ball (0 : E3) 1 ↔ x ∈ Metric.ball 0 4
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs]
    have habs : |r| = 1 / 4 := by dsimp only [r]; cases b.2 <;> norm_num
    rw [habs]
    constructor <;> intro h <;> linarith
  have ht : ψ.target = C.cap b '' {x : ClosedCell 3 | ‖x.val‖ < 1} := by
    change φ.target ∩ φ.symm ⁻¹' Set.univ = _
    rw [Set.preimage_univ, Set.inter_univ, htarget]
  have hψ (x : E3) (hx : ‖r • x‖ < 1) : ψ x = C.cap b ⟨r • x, hx.le⟩ :=
    hφ (r • x) hx
  let c : BallChart 3 (𝓡 3) N.Carrier :=
    ⟨ψ, by rw [hs]; exact Metric.closedBall_subset_ball (by norm_num)⟩
  have hor : ∀ x, ∀ hx : x ∈ ψ.source,
      Orientation.map (Fin 3)
        (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
          (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ ψ hx) (by simp)).toLinearEquiv
        (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
          (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation) =
        N.orientation.orientation (ψ x) := by
    intro x hx
    have hx' : ‖r • x‖ < 1 := by
      have hnorm : ‖x‖ < 4 := by rwa [hs, mem_ball_zero_iff] at hx
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |r| = 1 / 4 := by dsimp only [r]; cases b.2 <;> norm_num
      rw [habs]
      linarith
    let y : ClosedCell 3 := ⟨r • x, hx'.le⟩
    obtain ⟨hj, hp⟩ := C.cap_mfderiv_signed_scale_orientation b y hx' (1 / 4) (by norm_num)
    have hder (v : E3) : mfderiv (𝓡 3) (𝓡 3) ψ x v =
        mfderiv (𝓡∂ 3) (𝓡 3) (C.cap b) y (r • v) :=
      Manifold.mfderiv_eq_of_eq_closedCell_smul hx'
        ((C.cap_embedding b).contMDiff.mdifferentiableAt (by simp)) hψ v
    have heq : (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
        (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ ψ hx) (by simp)).toLinearEquiv =
        (LinearEquiv.smulOfNeZero ℝ E3 r hr).trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) (C.cap b) y).toLinearMap hj) := by
      ext v
      exact hder v
    change Orientation.map (Fin 3) _ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation = _
    erw [heq]
    rw [hψ x hx']
    exact hp
  exact ⟨⟨c, hor⟩, hs, ht, hψ⟩

def capBallChart (b : T.Boundary) : OrientedBallChart N :=
  (C.exists_orientedBallChart_cap b).choose

@[simp] theorem capBallChart_source (b : T.Boundary) :
    (C.capBallChart b).chart.source = Metric.ball 0 4 :=
  (C.exists_orientedBallChart_cap b).choose_spec.1

@[simp] theorem capBallChart_target (b : T.Boundary) :
    (C.capBallChart b).chart.target = C.cap b '' {x : ClosedCell 3 | ‖x.val‖ < 1} :=
  (C.exists_orientedBallChart_cap b).choose_spec.2.1

theorem capBallChart_apply (b : T.Boundary) (x : E3)
    (hx : ‖(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • x‖ < 1) :
    (C.capBallChart b).chart x =
      C.cap b ⟨(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • x, hx.le⟩ :=
  (C.exists_orientedBallChart_cap b).choose_spec.2.2 x hx

private theorem norm_cap_scale_lt_one (b : T.Boundary) (x : E3)
    (hx : x ∈ Metric.closedBall (0 : E3) 2) :
    ‖(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • x‖ < 1 := by
  have hn : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  rw [norm_smul, Real.norm_eq_abs]
  have ha : |if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)| = 1 / 4 := by
    cases b.2 <;> norm_num
  rw [ha]
  linarith

theorem capBallChart_closedBall_subset_range_cap (b : T.Boundary) :
    (C.capBallChart b).chart '' Metric.closedBall (0 : E3) 2 ⊆ Set.range (C.cap b) := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨⟨(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • x,
    (norm_cap_scale_lt_one b x hx).le⟩, (C.capBallChart_apply b x (norm_cap_scale_lt_one b x hx)).symm⟩

theorem pairwise_disjoint_capBallChart_closedBall :
    Pairwise fun b b' : T.Boundary => Disjoint
      ((C.capBallChart b).chart '' Metric.closedBall (0 : E3) 2)
      ((C.capBallChart b').chart '' Metric.closedBall (0 : E3) 2) :=
  fun _ _ hne => (C.cap_disjoint hne).mono
    (C.capBallChart_closedBall_subset_range_cap _) (C.capBallChart_closedBall_subset_range_cap _)

theorem disjoint_capBallChart_closedBall_core (b : T.Boundary) :
    Disjoint ((C.capBallChart b).chart '' Metric.closedBall (0 : E3) 2)
      (Set.range C.coreInclusion) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ hy
  let p : ClosedCell 3 := ⟨(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • x,
    (norm_cap_scale_lt_one b x hx).le⟩
  have hp : (C.capBallChart b).chart x = C.cap b p :=
    C.capBallChart_apply b x (norm_cap_scale_lt_one b x hx)
  rw [hp] at hy
  have hboth : C.cap b p ∈ Set.range C.coreInclusion ∩ Set.range (C.cap b) :=
    ⟨hy, ⟨p, rfl⟩⟩
  rw [C.core_cap_intersection b] at hboth
  obtain ⟨z, hz⟩ := hboth
  have hcap : C.cap b (sphereToClosedCell ((C.attaching b).symm z)) = C.cap b p := by
    rw [C.boundary_eq b ((C.attaching b).symm z), Diffeomorph.apply_symm_apply]
    exact hz
  have heq := congrArg (fun q : ClosedCell 3 => ‖q.val‖) ((C.cap_embedding b).isEmbedding.injective hcap)
  have hz1 : ‖(sphereToClosedCell ((C.attaching b).symm z)).val‖ = 1 := by
    exact mem_sphere_zero_iff_norm.mp ((C.attaching b).symm z).property
  rw [hz1] at heq
  have hlt : ‖p.val‖ < 1 := norm_cap_scale_lt_one b x hx
  linarith

end DifferentialGeometry.Topology.SphericalCapping
