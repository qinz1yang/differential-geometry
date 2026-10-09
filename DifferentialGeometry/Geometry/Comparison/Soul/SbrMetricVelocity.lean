import DifferentialGeometry.Geometry.Comparison.Soul.SbrGradient
import DifferentialGeometry.Geometry.Comparison.Soul.SbrGradientVelocity
import DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.IntrinsicDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem tendsto_normalized_gradient_of_eventual_support
    {ι : Type*} {l : Filter ι} {D : V → ℝ} {G : V} {W : ι → V}
    (hsmul : ∀ (a : ℝ), 0 ≤ a → ∀ v : V, D (a • v) = a * D v)
    (hsupport : ∀ v : V, D v ≤ inner ℝ G v) (hcal : D G = ‖G‖ ^ 2)
    (hG : G ≠ 0) (hvalue : ∀ᶠ i in l, 1 ≤ D (W i))
    (hspeed : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ‖W i‖ ≤ ‖G‖⁻¹ + ε) :
    Tendsto W l (𝓝 ((‖G‖ ^ 2)⁻¹ • G)) := by
  let U : V := (‖G‖ ^ 2)⁻¹ • G
  have hpos : 0 < ‖G‖ := norm_pos_iff.mpr hG
  have hUnorm : ‖U‖ = ‖G‖⁻¹ :=
    (superadditive_normalized_gradient_spec hsmul hcal hG).2
  have hinner : ∀ᶠ i in l, 1 ≤ inner ℝ G (W i) := by
    filter_upwards [hvalue] with i hi
    exact hi.trans (hsupport (W i))
  have hlower : ∀ᶠ i in l, ‖G‖⁻¹ ≤ ‖W i‖ := by
    filter_upwards [hinner] with i hi
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    simpa only [mul_comm] using hi.trans (real_inner_le_norm G (W i))
  have hnorm : Tendsto (fun i => ‖W i‖) l (𝓝 ‖G‖⁻¹) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [hlower] with i hi
      exact ha.trans_le hi
    · intro b hb
      have hε : 0 < (b - ‖G‖⁻¹) / 2 := by linarith
      filter_upwards [hspeed _ hε] with i hi
      linarith
  have hsqbound : ∀ᶠ i in l, ‖W i - U‖ ^ 2 ≤ ‖W i‖ ^ 2 - (‖G‖⁻¹) ^ 2 := by
    filter_upwards [hinner] with i hi
    have hcoeff : (‖G‖ ^ 2)⁻¹ = (‖G‖⁻¹) ^ 2 := (inv_pow _ _).symm
    have hcross : (‖G‖ ^ 2)⁻¹ ≤ (‖G‖ ^ 2)⁻¹ * inner ℝ G (W i) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (sq_nonneg ‖G‖))
    have hWU : inner ℝ (W i) U = (‖G‖ ^ 2)⁻¹ * inner ℝ G (W i) := by
      dsimp only [U]
      rw [real_inner_smul_right, real_inner_comm (W i) G]
    rw [norm_sub_sq_real, hUnorm, hWU]
    nlinarith [hcoeff, hcross]
  have hupper : Tendsto (fun i => ‖W i‖ ^ 2 - (‖G‖⁻¹) ^ 2) l (𝓝 0) := by
    convert! (hnorm.pow 2).sub_const ((‖G‖⁻¹) ^ 2) using 1
    simp only [sub_self]
  have hsquared : Tendsto (fun i => ‖W i - U‖ ^ 2) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i => sq_nonneg ‖W i - U‖) hsqbound hupper
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsquared
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

end InnerProduct

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_minimizing_exp_velocity_of_metric_speed
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (η : ℝ → M) (G : TangentSpace I (η 0))
    (hsupport : ∀ v : TangentSpace I (η 0),
      intrinsicRightDerivative g hEnorm F (η 0) v ≤ g.inner (η 0) G v)
    (hcal : intrinsicRightDerivative g hEnorm F (η 0) G = g.inner (η 0) G G)
    (hG : G ≠ 0)
    (hlevel : ∀ᶠ h in 𝓝[>] (0 : ℝ), F (η h) = F (η 0) + h)
    (hspeed : ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝[>] (0 : ℝ),
      dist (η 0) (η h) / h ≤ (Real.sqrt (g.inner (η 0) G G))⁻¹ + ε) :
    ∃ ξ : ℝ → TangentSpace I (η 0), ξ 0 = 0 ∧
      (∀ h : ℝ, expMapIntrinsic g hEnorm (η 0) (ξ h) = η h ∧
        Real.sqrt (g.inner (η 0) (ξ h) (ξ h)) = dist (η 0) (η h)) ∧
      Tendsto (fun h => h⁻¹ • ξ h) (𝓝[>] (0 : ℝ))
        (𝓝 ((g.inner (η 0) G G)⁻¹ • G)) := by
  classical
  let p : M := η 0
  let D : TangentSpace I p → ℝ := intrinsicRightDerivative g hEnorm F p
  have hm : ∀ h : ℝ, ∃ v : TangentSpace I p,
      expMapIntrinsic g hEnorm p v = η h ∧
      Real.sqrt (g.inner p v v) = dist p (η h) := by
    intro h
    obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top g hEnorm p (η h) (by
      rw [← IsRiemannianManifold.out (I := I)]
      exact edist_ne_top p (η h))
    rw [← IsRiemannianManifold.out (I := I), edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] at hlen
    exact ⟨v, hv, hlen⟩
  choose ξ hξexp hξlen using hm
  have hξ0 : ξ 0 = 0 := by
    by_contra hne
    have hpos := Real.sqrt_pos.mpr (g.pos p (ξ 0) hne)
    have hz : Real.sqrt (g.inner p (ξ 0) (ξ 0)) = 0 := by
      simpa only [p, dist_self] using hξlen 0
    exact hpos.ne' hz
  let W : ℝ → TangentSpace I p := fun h => h⁻¹ • ξ h
  have hscale (h : ℝ) (hh : 0 < h) : h • W h = ξ h := by
    simp only [W, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
  have hvalue : ∀ᶠ h in 𝓝[>] (0 : ℝ), 1 ≤ D (W h) := by
    filter_upwards [hlevel, self_mem_nhdsWithin] with h hlev hh
    change 0 < h at hh
    have hexp : intrinsicGeodesic g hEnorm p (W h) h = η h := by
      rw [← intrinsicGeodesic_smul, ← expMapIntrinsic_def, hscale h hh, hξexp h]
    have hsec := slope_le_intrinsicRightDerivative g hEnorm F p (W h) (hconc p _) hh
    simpa only [hexp, hlev, p, add_sub_cancel_left, div_self hh.ne'] using hsec
  have hWspeed : ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Real.sqrt (g.inner p (W h) (W h)) ≤ (Real.sqrt (g.inner p G G))⁻¹ + ε := by
    intro ε hε
    filter_upwards [hspeed ε hε, self_mem_nhdsWithin] with h hs hh
    change 0 < h at hh
    calc
      Real.sqrt (g.inner p (W h) (W h)) = h⁻¹ * dist p (η h) := by
        dsimp only [W]
        rw [sqrt_gInner_smul_self g p (inv_nonneg.mpr hh.le), hξlen h]
      _ = dist p (η h) / h := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ (Real.sqrt (g.inner p G G))⁻¹ + ε := hs
  have hsmul : ∀ (a : ℝ), 0 ≤ a → ∀ v : TangentSpace I p, D (a • v) = a * D v := by
    intro a ha v
    exact intrinsicRightDerivative_smul g hEnorm F p v (hconc p v) ha
  refine ⟨ξ, hξ0, fun h => ⟨hξexp h, hξlen h⟩, ?_⟩
  let K : InnerProductSpace.Core ℝ (TangentSpace I p) := g.toRiemannianMetric.toCore p
  have hKcont : ContinuousAt (fun v : TangentSpace I p => K.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt p
  have hKbounded : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I p | RCLike.re (K.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded p
  let : NormedAddCommGroup (TangentSpace I p) :=
    K.toNormedAddCommGroupOfTopology hKcont hKbounded
  let : InnerProductSpace ℝ (TangentSpace I p) :=
    InnerProductSpace.ofCoreOfTopology K hKcont hKbounded
  have hnorm (v : TangentSpace I p) : ‖v‖ = Real.sqrt (g.inner p v v) :=
    norm_eq_sqrt_real_inner v
  have hsq : ‖G‖ ^ 2 = g.inner p G G := (real_inner_self_eq_norm_sq G).symm
  have hs : ∀ v : TangentSpace I p, D v ≤ inner ℝ G v := hsupport
  have hc : D G = ‖G‖ ^ 2 := hcal.trans (real_inner_self_eq_norm_sq G)
  have hspeed' : ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ‖W h‖ ≤ ‖G‖⁻¹ + ε := by
    simpa only [hnorm] using hWspeed
  simpa only [hsq] using
    tendsto_normalized_gradient_of_eventual_support hsmul hs hc hG hvalue hspeed'

set_option backward.isDefEq.respectTransparency false in
theorem hasMFDerivWithinAt_of_calibration_and_metric_speed
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (η : ℝ → M) (G : TangentSpace I (η 0))
    (hsupport : ∀ v : TangentSpace I (η 0),
      intrinsicRightDerivative g hEnorm F (η 0) v ≤ g.inner (η 0) G v)
    (hcal : intrinsicRightDerivative g hEnorm F (η 0) G = g.inner (η 0) G G)
    (hG : G ≠ 0)
    (hlevel : ∀ᶠ h in 𝓝[>] (0 : ℝ), F (η h) = F (η 0) + h)
    (hspeed : ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝[>] (0 : ℝ),
      dist (η 0) (η h) / h ≤ (Real.sqrt (g.inner (η 0) G G))⁻¹ + ε) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I η (Ici 0) 0
      (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (η 0) G G)⁻¹ • G)) := by
  obtain ⟨ξ, hξ0, hξ, hscaled⟩ :=
    exists_minimizing_exp_velocity_of_metric_speed g hEnorm F hconc η G
      hsupport hcal hG hlevel hspeed
  let V : TangentSpace I (η 0) := (g.inner (η 0) G G)⁻¹ • G
  have hξder : HasDerivWithinAt (fun h => (ξ h : E)) (V : E) (Ioi 0) 0 := by
    apply (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mpr
    change Tendsto (fun h => slope (fun s => (ξ s : E)) 0 h) (𝓝[>] (0 : ℝ)) (𝓝 (V : E))
    simpa only [slope_def_module, hξ0, sub_zero] using hscaled
  let e : E → M := fun v => expMapIntrinsic g hEnorm (η 0)
    (show TangentSpace I (η 0) from v)
  have he : HasMFDerivAt 𝓘(ℝ, E) I e (0 : E) (ContinuousLinearMap.id ℝ E) := by
    have hd : HasMFDerivAt 𝓘(ℝ, E) I e (0 : E) (mfderiv 𝓘(ℝ, E) I e (0 : E)) :=
      ((intrinsicFiber_smooth g hEnorm (η 0)).mdifferentiableAt (by simp)).hasMFDerivAt
    rwa [mfderiv_expMapIntrinsic_at_zero g hEnorm (η 0)] at hd
  have he' : HasMFDerivAt 𝓘(ℝ, E) I e (ξ 0 : E) (ContinuousLinearMap.id ℝ E) := by
    rw [hξ0]
    exact he
  have hξMF : HasMFDerivWithinAt (M := ℝ) (M' := E) 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun h => (ξ h : E)) (Ici 0) 0
      (ContinuousLinearMap.toSpanSingleton ℝ (V : E)) :=
    (hξder.Ici_of_Ioi.hasFDerivWithinAt (F := E)).hasMFDerivWithinAt (E := ℝ) (E' := E)
  have hcomp := he'.comp_hasMFDerivWithinAt 0 hξMF
  have hcomp' : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun h => e (ξ h)) (Ici 0) 0 (ContinuousLinearMap.toSpanSingleton ℝ V) := by
    convert! hcomp using 1
  apply hcomp'.congr_of_eventuallyEq
  · exact Eventually.of_forall fun h => (hξ h).1.symm
  · exact (hξ 0).1.symm

theorem hasMFDerivWithinAt_normalized_intrinsicGeneralizedGradient
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (η : ℝ → M)
    (hG : intrinsicGeneralizedGradient g hEnorm hF hconc (η 0) ≠ 0)
    (hlevel : ∀ᶠ h in 𝓝[>] (0 : ℝ), F (η h) = F (η 0) + h)
    (hspeed : let G := intrinsicGeneralizedGradient g hEnorm hF hconc (η 0)
      ∀ ε : ℝ, 0 < ε → ∀ᶠ h in 𝓝[>] (0 : ℝ),
        dist (η 0) (η h) / h ≤ (Real.sqrt (g.inner (η 0) G G))⁻¹ + ε) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc (η 0)
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I η (Ici 0) 0
      (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (η 0) G G)⁻¹ • G)) := by
  have hspec := intrinsicGeneralizedGradient_spec g hEnorm hF hconc (η 0)
  exact hasMFDerivWithinAt_of_calibration_and_metric_speed g hEnorm F hconc η _
    hspec.1 hspec.2 hG hlevel hspeed

end DifferentialGeometry.Geometry.Topology
