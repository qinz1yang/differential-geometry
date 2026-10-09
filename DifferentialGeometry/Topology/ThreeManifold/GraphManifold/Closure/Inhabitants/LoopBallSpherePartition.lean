import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallRimInverse
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleRimInverse
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallLatitude
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideBall

/-!
The entire original ball sphere is partitioned by the two whole original handle end disks
and the genuine full-circle latitude annulus of the same nonempty ball-handle cycle.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology InnerProductSpace
namespace GC.GraphManifold.Assembly

private local instance spherePartitionRank2 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩

private local instance spherePartitionRank3 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩

private local instance spherePartitionCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

private local instance spherePartitionSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

theorem loopBallWholeFace_chart : loopBallWholeFace = loopActualBallChart ''
    {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ = 1} := by
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    change x ∈ (𝓡∂ 3).boundary (ClosedCell 3) at hx
    rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2] at hx
    refine ⟨x.val,hx,?_⟩
    exact loopActualBallChart_ball x
  · rintro ⟨x,hx,rfl⟩
    let xb : ClosedCell 3 := ⟨x,hx.le⟩
    refine ⟨xb,?_,?_⟩
    · change xb ∈ (𝓡∂ 3).boundary (ClosedCell 3)
      rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2]
      exact hx
    · exact (loopActualBallChart_ball xb).symm

private theorem spherePartition_capNorm (b : Bool) (x : ClosedCell 3) (hx : ‖x.val‖ = 1)
    (hs : if b then 3 / 5 ≤ (ballCoord x.val).2 else (ballCoord x.val).2 ≤ -3 / 5) :
    ‖(capMap b x.val).1‖ ≤ 1 := by
  have hfalse : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ = 1 →
      (ballCoord y).2 ≤ -3/5 → ‖(capMap false y).1‖ ≤ 1 := by
    intro y hy hh
    have hy0 : y ≠ 0 := by intro he; rw [he,norm_zero] at hy; norm_num at hy
    have hp : 0 < ‖y‖-(ballCoord y).2 := by rw [hy]; linarith
    have he := capMap_false_eq hy0 (by rw [← ballCoord_snd]; exact hp.ne')
    rw [he,norm_smul,Real.norm_of_nonneg (by positivity),hy]
    have hsq := norm_sq_ballCoord y
    rw [hy] at hsq
    have hd : 0 < 1-(ballCoord y).2 := by linarith
    rw [div_mul_eq_mul_div,div_le_iff₀ hd]
    have hmul : 0 ≤ (1-(ballCoord y).2)*(-5*(ballCoord y).2-3) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [norm_nonneg (ballCoord y).1]
  cases b
  · exact hfalse x.val hx hs
  · change 3/5 ≤ (ballCoord x.val).2 at hs
    change ‖(capMap false (reflectThree x.val)).1‖ ≤ 1
    apply hfalse (reflectThree x.val)
    · rw [norm_reflectThree,hx]
    · rw [ballCoord_reflectThree]
      change -(ballCoord x.val).2 ≤ -3/5
      linarith

private theorem spherePartition_capRegion (b : Bool) (x : ClosedCell 3) (hx : ‖x.val‖ = 1)
    (hs : if b then 3 / 5 ≤ (ballCoord x.val).2 else (ballCoord x.val).2 ≤ -3 / 5) :
    x ∈ neckCapRegion (1/16) b := by
  have hnorm := spherePartition_capNorm b x hx hs
  refine ⟨?_,?_,?_⟩
  · rw [hx]
    norm_num
  · cases b
    · change (ballCoord x.val).2 ≤ -3/5 at hs
      change 0 < ⟪x.val, (-northVec)⟫_ℝ
      rw [inner_neg_right,real_inner_comm,← ballCoord_snd]
      linarith
    · change 3/5 ≤ (ballCoord x.val).2 at hs
      change 0 < ⟪x.val, northVec⟫_ℝ
      rw [real_inner_comm,← ballCoord_snd]
      linarith
  · linarith

private theorem spherePartition_capEnd (b : Bool) (x : ClosedCell 3) (hx : ‖x.val‖ = 1)
    (hs : if b then 3 / 5 ≤ (ballCoord x.val).2 else (ballCoord x.val).2 ≤ -3 / 5) :
    (standardLoopBallHandleCycle.ball ⟨0,standardLoopBallHandleCycle.len_pos⟩).map x ∈
    (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).endDisk b := by
  let w : ClosedCell 2 := ⟨(capMap b x.val).1,spherePartition_capNorm b x hx hs⟩
  let yh := (w,iccEnd b)
  have he : handleEnd b yh = capMap b x.val := by
    apply Prod.ext
    · rfl
    · change endCoord b (iccEnd b).val = (capMap b x.val).2
      rw [capMap_snd,hx]
      cases b <;> norm_num [endCoord,iccEnd]
  have hcap := modelBall_cap (by norm_num : 0 < (1 : ℕ))
    (by norm_num : (0 : ℝ) < 1/16) (by norm_num : (1/16 : ℝ) ≤ 1/8)
    (0 : Fin 1) b x (spherePartition_capRegion b x hx hs)
  have hk : rimBall 1 (0 : Fin 1) b = 0 := Subsingleton.elim _ _
  rw [hk] at hcap
  have hH := modelHandle_end (by norm_num : 0 < (1 : ℕ))
    (by norm_num : (0 : ℝ) < 1/16) (by norm_num : (1/16 : ℝ) ≤ 1/8) (0 : Fin 1) b yh
  rw [he] at hH
  have hp : (standardLoopBallHandleCycle.ball ⟨0,standardLoopBallHandleCycle.len_pos⟩).map x =
      (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map yh :=
    hcap.trans hH.symm
  exact ⟨w,hp.symm⟩

theorem loopBallSphere_middle (x : ClosedCell 3) (hx : ‖x.val‖ = 1)
    (hm : -3 / 5 ≤ (ballCoord x.val).2 ∧ (ballCoord x.val).2 ≤ 3 / 5) :
    ∃ (θ : Circle) (t : Set.Icc (0 : ℝ) 1), loopBallLatitudePoint θ t = x := by
  let h := (ballCoord x.val).2
  let ξ := (ballCoord x.val).1
  let t : Set.Icc (0 : ℝ) 1 := ⟨(5/6)*(h+3/5),by constructor <;> dsimp [h] <;> linarith [hm.1,hm.2]⟩
  let θ := unitOf (modelPlaneComplex ξ)
  refine ⟨θ,t,?_⟩
  apply Subtype.ext
  apply ballCoord_injective
  have hco := loopBallLatitudePoint_coordinates θ t
  change ballCoord (loopBallLatitudePoint θ t).val =
    (Real.sqrt (1-(-3/5+(6/5)*t.val)^2) • planeOfCircle θ,-3/5+(6/5)*t.val) at hco
  have ht : -3/5+(6/5)*t.val = h := by dsimp only [t]; ring
  rw [ht] at hco
  rw [hco]
  have hsq := norm_sq_ballCoord x.val
  rw [hx] at hsq
  have hr : Real.sqrt (1-h^2) = ‖ξ‖ := by
    have he : 1-h^2 = ‖ξ‖^2 := by dsimp [h,ξ]; nlinarith [hsq]
    rw [he,Real.sqrt_sq (norm_nonneg ξ)]
  rw [hr]
  apply Prod.ext
  · change ‖ξ‖ • planeOfCircle θ = ξ
    apply modelPlaneComplex.injective
    rw [map_smul,modelPlaneComplex,planeOfCircle,LinearIsometryEquiv.symm_apply_apply]
    rw [← modelPlaneComplex.norm_map]
    exact norm_smul_unitOf (modelPlaneComplex ξ)
  · rfl

theorem loopBallWholeFace_partition : loopBallWholeFace =
    (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).endDisk false ∪
    (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).endDisk true ∪
    Set.range loopBallAnnulus := by
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hn : ‖(x : ClosedCell 3).val‖ = 1 := by
      change x ∈ (𝓡∂ 3).boundary (ClosedCell 3) at hx
      rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2] at hx
      exact hx
    by_cases hs : (ballCoord (x : ClosedCell 3).val).2 ≤ -3/5
    · exact Or.inl (Or.inl (spherePartition_capEnd false x hn hs))
    by_cases hnorth : 3/5 ≤ (ballCoord (x : ClosedCell 3).val).2
    · exact Or.inl (Or.inr (spherePartition_capEnd true x hn hnorth))
    · obtain ⟨θ,t,he⟩ := loopBallSphere_middle x hn
        ⟨le_of_lt (lt_of_not_ge hs),le_of_lt (lt_of_not_ge hnorth)⟩
      right
      refine ⟨(θ,t),?_⟩
      change (standardLoopBallHandleCycle.ball ⟨0,standardLoopBallHandleCycle.len_pos⟩).map
        ((standardLoopBallHandleCycle.ballModel ⟨0,standardLoopBallHandleCycle.len_pos⟩).symm
          (loopBallLatitudePoint θ t)) = _
      rw [he]
      rfl
  · intro hp
    rcases hp with (hs | he) | ha
    · exact standardLoopBallHandleCycle.start_face ⟨0,standardLoopBallHandleCycle.len_pos⟩ hs
    · have ht := standardLoopBallHandleCycle.end_face ⟨0,standardLoopBallHandleCycle.len_pos⟩ he
      have hrot : finRotate standardLoopBallHandleCycle.len
          ⟨0,standardLoopBallHandleCycle.len_pos⟩ = ⟨0,standardLoopBallHandleCycle.len_pos⟩ := by
        apply Fin.ext
        have hlt := (finRotate standardLoopBallHandleCycle.len
          ⟨0,standardLoopBallHandleCycle.len_pos⟩).isLt
        have hbound : standardLoopBallHandleCycle.len ≤ 1 := by
          rw [standardLoopBallHandleCycle_len]
        have hlt1 := lt_of_lt_of_le hlt hbound
        change _ = 0
        omega
      rwa [hrot] at ht
    · exact loopBallAnnulus_face ha

end GC.GraphManifold.Assembly
