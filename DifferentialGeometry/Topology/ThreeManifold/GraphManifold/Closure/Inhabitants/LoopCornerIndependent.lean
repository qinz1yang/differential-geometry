import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCommonCorners

/-!
The two active actual ball and handle defining functions have independent native differentials.
Their genuine common center charts pull the pair back to the actual coordinate negation map.
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private def cornerPairNegation : Diffeomorph 𝓘(ℝ, ℝ × ℝ)
    (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toEquiv :=
    { toFun := fun v => (-v.1, -v.2)
      invFun := fun v => (-v.1, -v.2)
      left_inv := by rintro ⟨x, y⟩; simp
      right_inv := by rintro ⟨x, y⟩; simp }
  contMDiff_toFun :=
    (contDiff_fst.neg.contMDiff).prodMk (contDiff_snd.neg.contMDiff)
  contMDiff_invFun := contMDiff_fst.neg.prodMk_space contMDiff_snd.neg

private theorem cornerPairNegation_apply (v : ℝ × ℝ) :
    cornerPairNegation v = (-v.1, -v.2) := rfl

theorem loopHandleBall_independent (z : loopCircleBase)
    (hh : loopHandleDefining z = 0) (hb : loopBallDefining z = 0) :
    Function.Surjective fun w : TangentSpace (𝓡 2) z =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopHandleDefining z w,
       mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopBallDefining z w) := by
  obtain ⟨b, rfl⟩ := loopHandleBall_common_center z hh hb
  let φ := loopBaseCorner b
  let F : loopCircleBase → ℝ × ℝ := fun z => (loopHandleDefining z, loopBallDefining z)
  have h0 : (0, 0) ∈ φ.source := by
    rw [loopBaseCorner_source]
    constructor <;> norm_num
  have hφ := (φ.contMDiffOn_toFun.contMDiffAt (φ.open_source.mem_nhds h0))
    |>.mdifferentiableAt (by simp)
  have hH := loopHandleDefining_smooth.mdifferentiableAt (x := φ (0, 0)) (by simp)
  have hB := loopBallDefining_smooth.mdifferentiableAt (x := φ (0, 0)) (by simp)
  have hF : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) F (φ (0, 0)) :=
    hH.prodMk hB
  have he : (F ∘ φ) =ᶠ[𝓝 (0, 0)] (cornerPairNegation : ℝ × ℝ → ℝ × ℝ) := by
    filter_upwards [φ.open_source.mem_nhds h0] with v hv
    have hvr : v ∈ rimBox 2 := by rwa [loopBaseCorner_source] at hv
    rw [cornerPairNegation_apply]
    change (loopHandleDefining (loopBaseCorner b v), loopBallDefining (loopBaseCorner b v)) = _
    rw [loopHandleDefining_rim b hvr, loopBallDefining_rim b hvr]
  have hder := he.mfderiv_eq (I := 𝓘(ℝ, ℝ × ℝ)) (I' := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
  have hcomp := mfderiv_comp (0, 0) hF hφ
  let hneg := (cornerPairNegation.isLocalDiffeomorph (0, 0)).mfderivToContinuousLinearEquiv
    (by simp)
  let tc := tangentSpaceCast (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
    (cornerPairNegation (0, 0)) ((F ∘ φ) (0, 0))
  intro v
  obtain ⟨u, hu⟩ := tc.surjective v
  obtain ⟨w, hw⟩ := hneg.surjective u
  refine ⟨mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) φ (0, 0) w , ?_⟩
  have hd : mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) F (φ (0, 0))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) φ (0, 0) w) = v := by
    rw [← ContinuousLinearMap.comp_apply,← hcomp, hder, ContinuousLinearMap.comp_apply]
    have hnc : hneg.toContinuousLinearMap =
        mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
          (cornerPairNegation : ℝ × ℝ → ℝ × ℝ) (0, 0) := by
      dsimp only [hneg]
      rfl
    have hww := hw
    change hneg.toContinuousLinearMap w = u at hww
    rw [hnc] at hww
    exact (congrArg tc hww).trans hu
  have hp := mfderiv_prodMk hH hB
  change mfderiv (𝓡 2) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) F (φ (0, 0)) = _ at hp
  rw [hp] at hd
  exact hd

theorem loopBallHandle_independent (z : loopCircleBase)
    (hb : loopBallDefining z = 0) (hh : loopHandleDefining z = 0) :
    Function.Surjective fun w : TangentSpace (𝓡 2) z =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopBallDefining z w,
       mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopHandleDefining z w) := by
  intro v
  obtain ⟨w, hw⟩ := loopHandleBall_independent z hh hb (v.2, v.1)
  refine ⟨w , ?_⟩
  exact Prod.ext (congrArg Prod.snd hw) (congrArg Prod.fst hw)

end GC.GraphManifold.Assembly
