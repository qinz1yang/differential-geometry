import DifferentialGeometry.Geometry.Comparison.CGTHomotopyLift
import DifferentialGeometry.Geometry.Comparison.HalfSqDistGrad

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential NormalCoordinates Variation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private noncomputable def flatTime (t : Real) : Real :=
  Real.smoothTransition (3 * t - 1)

private theorem flatTime_zero : flatTime 0 = 0 := by
  rw [flatTime, Real.smoothTransition.zero_of_nonpos (by norm_num)]

private theorem flatTime_one : flatTime 1 = 1 := by
  rw [flatTime, Real.smoothTransition.one_of_one_le (by norm_num)]

private theorem flatTime_nonneg (t : Real) : 0 ≤ flatTime t :=
  Real.smoothTransition.nonneg _

private theorem flatTime_le_one (t : Real) : flatTime t ≤ 1 :=
  Real.smoothTransition.le_one _

private theorem flatTime_mono : Monotone flatTime := by
  apply Real.smoothTransition.monotone.comp
  intro a b hab
  dsimp only [flatTime]
  linarith

private theorem flatTime_cd : ContDiff Real ∞ flatTime := by
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.mul contDiff_id |>.sub contDiff_const)

private theorem flatTime_zero_nhds :
    flatTime =ᶠ[𝓝 (0 : Real)] (fun _ => 0) := by
  filter_upwards [eventually_lt_nhds (show (0 : Real) < 1 / 3 by norm_num)]
    with t ht
  rw [flatTime, Real.smoothTransition.zero_of_nonpos]
  linarith

private theorem flatTime_one_nhds :
    flatTime =ᶠ[𝓝 (1 : Real)] (fun _ => 1) := by
  filter_upwards [eventually_gt_nhds (show (2 / 3 : Real) < 1 by norm_num)]
    with t ht
  rw [flatTime, Real.smoothTransition.one_of_one_le]
  linarith

noncomputable def radialFlat
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    Path p (intrinsicFramedExp (I := I) g hEnorm p u) where
  toFun t :=
    intrinsicFramedExp (I := I) g hEnorm p (flatTime t • u)
  continuous_toFun :=
    (intrFrame_smooth (I := I) g hEnorm p).continuous.comp
      (by
        exact
          (flatTime_cd.continuous.comp continuous_subtype_val).smul
            continuous_const)
  source' := by
    change intrinsicFramedExp (I := I) g hEnorm p (flatTime (0 : Real) • u) = p
    rw [flatTime_zero, zero_smul, intrFrame_zero]
  target' := by
    change
      intrinsicFramedExp (I := I) g hEnorm p (flatTime (1 : Real) • u) =
        intrinsicFramedExp (I := I) g hEnorm p u
    rw [flatTime_one, one_smul]

theorem radialFlat_extend
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    (radialFlat (I := I) g hEnorm p u).extend =
      fun t : Real =>
        intrinsicFramedExp (I := I) g hEnorm p (flatTime t • u) := by
  funext t
  by_cases ht0 : t ≤ 0
  · rw [(radialFlat (I := I) g hEnorm p u).extend_of_le_zero ht0,
      flatTime, Real.smoothTransition.zero_of_nonpos]
    · simpa only [zero_smul] using
        (intrFrame_zero (I := I) g hEnorm p).symm
    · linarith
  · have h0t : 0 ≤ t := (not_le.mp ht0).le
    by_cases ht1 : t ≤ 1
    · have ht : t ∈ Set.Icc (0 : Real) 1 := ⟨h0t, ht1⟩
      rw [(radialFlat (I := I) g hEnorm p u).extend_apply ht]
      rfl
    · have h1t : 1 ≤ t := (not_le.mp ht1).le
      rw [(radialFlat (I := I) g hEnorm p u).extend_of_one_le h1t,
        flatTime, Real.smoothTransition.one_of_one_le]
      · simp only [one_smul]
      · linarith

theorem radialFlat_flat
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    IsFlatC1Path (I := I) (radialFlat (I := I) g hEnorm p u) where
  c1 := by
    rw [radialFlat_extend]
    apply (intrFrame_smooth (I := I) g hEnorm p).of_le (by norm_num) |>.comp
    rw [contMDiff_iff_contDiff]
    exact (flatTime_cd.of_le (by norm_num)).smul contDiff_const
  flat_zero := by
    rw [radialFlat_extend]
    filter_upwards [flatTime_zero_nhds] with t ht
    rw [ht, zero_smul, intrFrame_zero]
  flat_one := by
    rw [radialFlat_extend]
    filter_upwards [flatTime_one_nhds] with t ht
    rw [ht, one_smul]

theorem radialFlat_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    pathLen (I := I) (radialFlat (I := I) g hEnorm p u) =
      ENNReal.ofReal ‖u‖ := by
  let v : TangentSpace I p := normalFrame (I := I) g p u
  let γ : Real → M :=
    fun t => intrinsicFramedExp (I := I) g hEnorm p (t • u)
  have hγ :
      γ = intrinsicGeodesic (I := I) g hEnorm p v := by
    funext t
    dsimp only [γ, v]
    rw [intrFrame_apply, map_smul, expMapIntrinsic_def,
      intrinsicGeodesic_smul]
  have hγC1 :
      ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc 0 1) := by
    rw [hγ]
    exact
      (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v).mono
        (Set.subset_univ _)
  have hbase :
      Manifold.pathELength I γ 0 1 = ENNReal.ofReal ‖u‖ := by
    have hv :
        Real.sqrt (g.inner p v v) = ‖u‖ := by
      dsimp only [v]
      exact normalFrame_sqrt (I := I) g p u
    rw [Geodesic.pathELength_eq_arcLength_riemannianBundle (I := I) g zero_le_one
      (Geodesic.speedSqrt_integrableOn_Icc_of_C1
        (I := I) g zero_le_one hγC1)
      (fun t _ => hEnorm (γ t)
        (mfderiv 𝓘(Real, Real) I γ t (1 : Real))),
      hγ, arcLength_radial (I := I) g hEnorm p v 0 1, hv]
    norm_num
  rw [pathLen, radialFlat_extend]
  change
    Manifold.pathELength I (γ ∘ flatTime) 0 1 =
      ENNReal.ofReal ‖u‖
  rw [Manifold.pathELength_comp_of_monotoneOn
    (I := I) (γ := γ) (f := flatTime) (a := 0) (b := 1)
    zero_le_one (flatTime_mono.monotoneOn (s := Set.Icc 0 1))
    (flatTime_cd.differentiable (by norm_num)).differentiableOn
    (by
      simpa only [flatTime_zero, flatTime_one] using
        hγC1.mdifferentiableOn one_ne_zero)]
  simpa only [flatTime_zero, flatTime_one] using hbase

noncomputable def radialFlatLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    IntrFrameLift (I := I) g hEnorm p
      (radialFlat (I := I) g hEnorm p u).extend 0 1 where
  toFun t := flatTime t • u
  contDiff := by
    apply ContDiff.contDiffOn
    exact (flatTime_cd.of_le (by norm_num)).smul contDiff_const
  start := by rw [flatTime_zero, zero_smul]
  lifts := by
    intro t _
    rw [radialFlat_extend]
    rfl

@[simp] theorem radialLift_one
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    (radialFlatLift (I := I) g hEnorm p u).toFun 1 = u := by
  change flatTime (1 : Real) • u = u
  rw [flatTime_one, one_smul]

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
