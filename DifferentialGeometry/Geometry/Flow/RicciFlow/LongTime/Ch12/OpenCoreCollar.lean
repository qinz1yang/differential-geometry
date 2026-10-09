import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Topology.Manifold.HalfCollarExtension
import DifferentialGeometry.Topology.Manifold.HalfLine

set_option autoImplicit false

noncomputable section

open Set Function Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- The canonical half-interval coordinate, with its boundary manifold structure. -/
def halfIntervalLift_CX1 : Ico (0 : ℝ) 1 → EuclideanHalfSpace 1 :=
  fun t => halfSpaceOneLift t.val

theorem halfIntervalLift_height_CX1 (t : Ico (0 : ℝ) 1) :
    (halfIntervalLift_CX1 t).val 0 = t.val := by
  change max t.val 0 = t.val
  exact max_eq_left t.property.1

theorem halfIntervalLift_smooth_CX1 :
    let := halfClosedIntervalChartedSpace (show (0 : ℝ) < 1 by norm_num)
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ halfIntervalLift_CX1 := by
  let := halfClosedIntervalChartedSpace (show (0 : ℝ) < 1 by norm_num)
  exact contMDiffOn_halfSpaceOneLift.comp_contMDiff
    (isSmoothEmbedding_halfClosedInterval_inclusion (show (0 : ℝ) < 1 by norm_num)).contMDiff
    (fun t => t.property.1)

theorem halfIntervalLift_injective_mfderiv_CX1 (t : Ico (0 : ℝ) 1) :
    let := halfClosedIntervalChartedSpace (show (0 : ℝ) < 1 by norm_num)
    Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) halfIntervalLift_CX1 t) := by
  let := halfClosedIntervalChartedSpace (show (0 : ℝ) < 1 by norm_num)
  have h := ((isSmoothEmbedding_halfClosedInterval_inclusion
    (show (0 : ℝ) < 1 by norm_num)).isImmersion.isImmersionAt t).mfderiv_injective (by simp)
  have heq : (fun q : EuclideanHalfSpace 1 => q.val 0) ∘ halfIntervalLift_CX1 =
      (Subtype.val : Ico (0 : ℝ) 1 → ℝ) := funext halfIntervalLift_height_CX1
  rw [← heq, mfderiv_comp t
    (contMDiff_halfSpaceOneCoordinate.mdifferentiableAt (by simp))
    (halfIntervalLift_smooth_CX1.mdifferentiableAt (by simp))] at h
  exact fun v w hvw => h (congrArg
    (mfderiv (𝓡∂ 1) 𝓘(ℝ) (fun q : EuclideanHalfSpace 1 => q.val 0)
      (halfIntervalLift_CX1 t)) hvw)

/-- Smooth extension across the zero torus of an actual cusp embedding.
The positive side retains the original cusp parametrization. -/
theorem exists_cusp_bicollar_CX1 {H : FiniteVolumeHyperbolicModel.{u}}
    (T : HyperbolicTruncation H) (i : Fin T.count) :
    ∃ d : SmoothTwoSidedCollar torusModel (𝓡 3)
        (fun x => T.cuspMap i (x, halfZero)),
      d.radius ≤ 1 ∧ ∀ p (_hp : 0 ≤ p.2.val),
        d.toFun p = T.cuspMap i (p.1, halfSpaceOneLift p.2.val) := by
  let := halfClosedIntervalChartedSpace (show (0 : ℝ) < 1 by norm_num)
  let c : Torus × Ico (0 : ℝ) 1 → H.Carrier :=
    fun p => T.cuspMap i (p.1, halfIntervalLift_CX1 p.2)
  have hz : halfIntervalLift_CX1 ⟨0, le_rfl, by norm_num⟩ = halfZero := by
    apply Subtype.ext
    ext j
    rw [Subsingleton.elim j 0]
    exact halfIntervalLift_height_CX1 _
  have hc : ContMDiff halfCollarModel (𝓡 3) ∞ c :=
    (T.cuspEmbedding i).contMDiff.comp
      (contMDiff_id.prodMap halfIntervalLift_smooth_CX1)
  have hinj : Injective (fun s => c (s, ⟨0, le_rfl, by norm_num⟩)) := by
    intro x y h
    exact congrArg Prod.fst ((T.cuspEmbedding i).isEmbedding.injective h)
  have hd : ∀ s, Bijective (mfderiv halfCollarModel (𝓡 3) c
      (s, ⟨0, le_rfl, by norm_num⟩)) := by
    intro s
    let p : Torus × Ico (0 : ℝ) 1 := (s, ⟨0, le_rfl, by norm_num⟩)
    have hD : Injective (mfderiv halfCollarModel (𝓡 3) c p) := by
      change Injective (mfderiv halfCollarModel (𝓡 3)
        (T.cuspMap i ∘ Prod.map id halfIntervalLift_CX1) p)
      rw [mfderiv_comp p ((T.cuspEmbedding i).contMDiff.mdifferentiableAt (by simp))
        ((contMDiff_id.prodMap halfIntervalLift_smooth_CX1).mdifferentiableAt (by simp)),
        mfderiv_prodMap mdifferentiableAt_id
          (halfIntervalLift_smooth_CX1.mdifferentiableAt (by simp)), mfderiv_id]
      exact ((T.cuspEmbedding i).isImmersion.isImmersionAt _).mfderiv_injective
        (by simp) |>.comp (injective_id.prodMap (halfIntervalLift_injective_mfderiv_CX1 p.2))
    exact (mfderiv halfCollarModel (𝓡 3) c p).toLinearMap.linearEquivOfInjective
      hD (by
        change Module.finrank ℝ ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
          EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
        simp [Module.finrank_prod]) |>.bijective
  obtain ⟨d, hw, heq⟩ := exists_smoothTwoSidedCollar_of_halfClosedInterval
    (show (0 : ℝ) < 1 by norm_num) c hc hinj hd
  have hc0 : (fun s => c (s, ⟨0, le_rfl, by norm_num⟩)) =
      (fun s => T.cuspMap i (s, halfZero)) := by
    funext s
    exact congrArg (fun q => T.cuspMap i (s, q)) hz
  let d' : SmoothTwoSidedCollar torusModel (𝓡 3)
      (fun x => T.cuspMap i (x, halfZero)) :=
    { d with zero_eq := fun x => (d.zero_eq x).trans (congrFun hc0 x) }
  refine ⟨d', hw, ?_⟩
  intro p hp
  exact heq p hp

end GC.LongTime.Ch12
