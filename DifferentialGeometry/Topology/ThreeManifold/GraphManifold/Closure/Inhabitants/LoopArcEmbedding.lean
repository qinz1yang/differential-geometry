import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcSmooth
import DifferentialGeometry.Topology.Manifold.Interval.Immersion
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding

/-!
The actual original ball base arc is a genuine smooth embedding through both endpoints.
Phase recovery gives injective native differentials for the interval boundary model.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private def arcRecover (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (3 / 5 - Complex.arg (modelPlaneComplex z) / modelAngleScale 1) / (6 / 5)

private theorem arcRecover_left (t : Set.Icc (0 : ℝ) 1) :
    arcRecover (loopBallArcBase t).val = t.val := by
  unfold arcRecover
  rw [loopBallArcBase_arg]
  have hk := modelAngleScale_pos (by norm_num : 0 < 1)
  have hd : (-modelAngleScale 1 * loopBallArcHeight t) / modelAngleScale 1 =
      -loopBallArcHeight t := by field_simp [hk.ne']
  rw [hd]
  unfold loopBallArcHeight
  ring

private theorem arcRecover_smooth (t : Set.Icc (0 : ℝ) 1) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ arcRecover (loopBallArcBase t).val := by
  have hlog : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 2) =>
      Complex.log (modelPlaneComplex z)) (loopBallArcBase t).val :=
    ((Complex.contDiffAt_log (loopBallArcBase_slit t)).restrict_scalars ℝ).comp _
      modelPlaneComplex.toContinuousLinearEquiv.contDiff.contDiffAt
  have harg : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 2) =>
      Complex.arg (modelPlaneComplex z)) (loopBallArcBase t).val := by
    have he : (fun z : EuclideanSpace ℝ (Fin 2) => Complex.arg (modelPlaneComplex z)) =
        fun z => (Complex.log (modelPlaneComplex z)).im := by
      funext z
      rw [Complex.log_im]
    rw [he]
    exact Complex.imCLM.contDiff.contDiffAt.comp _ hlog
  have hd : ContDiffAt ℝ ∞ arcRecover (loopBallArcBase t).val :=
    (contDiffAt_const.sub (harg.div_const _)).div_const _
  exact hd.contMDiffAt

private theorem arcAmbient_smooth : ContMDiff (𝓡∂ 1) (𝓡 2) ∞
    (fun t : Set.Icc (0 : ℝ) 1 => (loopBallArcBase t).val) :=
  (ContMDiff.subtypeVal_comp_iff loopCircleBase _).mpr loopBallArcBase_smooth

private theorem arcAmbient_embedding : IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞
    (fun t : Set.Icc (0 : ℝ) 1 => (loopBallArcBase t).val) := by
  have hinj : Injective (fun t : Set.Icc (0 : ℝ) 1 => (loopBallArcBase t).val) := by
    intro t s he
    exact loopBallArcBase_injective (Subtype.ext he)
  refine ⟨isImmersion_Icc_of_injective_mfderiv arcAmbient_smooth ?_,
    arcAmbient_smooth.continuous.isClosedEmbedding hinj |>.isEmbedding⟩
  intro t
  have hleft : arcRecover ∘ (fun t : Set.Icc (0 : ℝ) 1 => (loopBallArcBase t).val) =
      (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) := funext arcRecover_left
  have hc := mfderiv_comp t ((arcRecover_smooth t).mdifferentiableAt (by simp))
    (arcAmbient_smooth.mdifferentiableAt (by simp))
  rw [hleft] at hc
  have hv : Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ)
      (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) t) :=
    by
      have hi := (isImmersionOfComplement_subtypeVal_Icc
        (x := (0 : ℝ)) (y := 1) (n := ∞)).isImmersion
      exact (hi.isImmersionAt t).mfderiv_injective (by simp)
  rw [hc] at hv
  exact Function.Injective.of_comp hv

private def arcRetarget : PartialDiffeomorph (𝓡 2) (𝓡 2)
    (EuclideanSpace ℝ (Fin 2)) loopCircleBase ∞ :=
  (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    loopCircleBase loopCircleBase_nonempty).symm

private theorem arcRetarget_source : arcRetarget.source = loopCircleBase :=
  TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target
    loopCircleBase loopCircleBase_nonempty

private theorem arcRetarget_apply (z : loopCircleBase) : arcRetarget z.val = z := by
  let φ : PartialDiffeomorph (𝓡 2) (𝓡 2) loopCircleBase
      (EuclideanSpace ℝ (Fin 2)) ∞ :=
    DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
      loopCircleBase loopCircleBase_nonempty
  have he : φ.source = Set.univ :=
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source
      loopCircleBase loopCircleBase_nonempty
  have hs : z ∈ φ.source := by rw [he]; trivial
  exact φ.left_inv hs

theorem loopBallArcBase_embedding : IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ loopBallArcBase := by
  have hs : range (fun t : Set.Icc (0 : ℝ) 1 => (loopBallArcBase t).val) ⊆
      arcRetarget.source := by
    rintro z ⟨t, rfl⟩
    rw [arcRetarget_source]
    exact (loopBallArcBase t).property
  have he := DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph
    arcRetarget arcAmbient_embedding hs
  have hf : arcRetarget ∘ (fun t : Set.Icc (0 : ℝ) 1 => (loopBallArcBase t).val) =
      loopBallArcBase := funext fun t => arcRetarget_apply (loopBallArcBase t)
  rw [hf] at he
  exact he

end GC.GraphManifold.Assembly
