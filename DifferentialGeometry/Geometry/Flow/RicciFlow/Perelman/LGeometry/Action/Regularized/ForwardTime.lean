import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.VelocityComposition
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

section ForwardTime

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedLagrangian_forwardTime
    (S : SolutionOn (I := I) (M := M) D) (T u : ℝ) (gamma : ℝ → M)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma (T - u ^ 2)) :
    lRegularizedLagrangian S T (fun r => gamma (T - r ^ 2)) u =
      2 * u ^ 2 * (S.scalar (T - u ^ 2) (gamma (T - u ^ 2)) +
        (S.base.metric (T - u ^ 2)).inner (gamma (T - u ^ 2))
          (lVelocity gamma (T - u ^ 2)) (lVelocity gamma (T - u ^ 2))) := by
  have hclock : HasDerivAt (fun r : ℝ => T - r ^ 2) (-2 * u) u := by
    simpa [neg_mul] using (hasDerivAt_pow 2 u).const_sub T
  have hvel := lVelocity_comp_of_hasDerivAt (r := fun r : ℝ => T - r ^ 2) (u := u) hgamma hclock
  unfold lRegularizedLagrangian
  simp only [Function.comp_def] at hvel
  rw [hvel]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem lRegularizedAction_eq_integral_forwardTime
    (S : SolutionOn (I := I) (M := M) D) {T a b : ℝ} (hab : a ≤ b) (hbT : b ≤ T)
    (gamma : ℝ → M)
    (hgamma : ∀ t ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t) :
    lRegularizedAction S T (fun u => gamma (T - u ^ 2))
        (Real.sqrt (T - b)) (Real.sqrt (T - a)) =
      ∫ t in a..b, Real.sqrt (T - t) *
        (S.scalar t (gamma t) + (S.base.metric t).inner (gamma t)
          (lVelocity gamma t) (lVelocity gamma t)) := by
  have haT := hab.trans hbT
  have horder : Real.sqrt (T - b) ≤ Real.sqrt (T - a) := Real.sqrt_le_sqrt (by linarith)
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (f := fun u : ℝ => T - u ^ 2) (f' := fun u : ℝ => -2 * u)
    (g := fun t => Real.sqrt (T - t) *
      (S.scalar t (gamma t) + (S.base.metric t).inner (gamma t)
        (lVelocity gamma t) (lVelocity gamma t)))
    (a := Real.sqrt (T - b)) (b := Real.sqrt (T - a))
    (by fun_prop)
    (by intro u _; simpa [neg_mul] using (hasDerivAt_pow 2 u).const_sub T)
    (by
      intro u hu
      have hu0 : 0 ≤ u := (Real.sqrt_nonneg _).trans (by simpa [horder] using hu.1.le)
      nlinarith)
  have hupper : T - Real.sqrt (T - b) ^ 2 = b := by rw [Real.sq_sqrt (by linarith)]; ring
  have hlower : T - Real.sqrt (T - a) ^ 2 = a := by rw [Real.sq_sqrt (by linarith)]; ring
  rw [hupper, hlower, intervalIntegral.integral_symm a b] at hchange
  have hcongr : (∫ u in Real.sqrt (T - b)..Real.sqrt (T - a),
      (fun t => Real.sqrt (T - t) *
        (S.scalar t (gamma t) + (S.base.metric t).inner (gamma t)
          (lVelocity gamma t) (lVelocity gamma t))) (T - u ^ 2) * (-2 * u)) =
      -lRegularizedAction S T (fun u => gamma (T - u ^ 2))
        (Real.sqrt (T - b)) (Real.sqrt (T - a)) := by
    rw [lRegularizedAction, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    have hu' : u ∈ Ioo (Real.sqrt (T - b)) (Real.sqrt (T - a)) := by
      simpa [uIoo, min_eq_left horder, max_eq_right horder] using hu
    have hu0 : 0 ≤ u := (Real.sqrt_nonneg _).trans hu'.1.le
    have htime : T - u ^ 2 ∈ Ioo a b := by
      have hl : Real.sqrt (T - b) ^ 2 < u ^ 2 :=
        (sq_lt_sq₀ (Real.sqrt_nonneg _) hu0).mpr hu'.1
      have hr : u ^ 2 < Real.sqrt (T - a) ^ 2 :=
        (sq_lt_sq₀ hu0 (Real.sqrt_nonneg _)).mpr hu'.2
      rw [Real.sq_sqrt (by linarith : 0 ≤ T - b)] at hl
      rw [Real.sq_sqrt (by linarith : 0 ≤ T - a)] at hr
      constructor <;> linarith
    dsimp only
    rw [lRegularizedLagrangian_forwardTime S T u gamma (hgamma _ htime)]
    simp only [sub_sub_cancel, Real.sqrt_sq hu0]
    ring
  exact neg_injective (hcongr.symm.trans hchange)

end ForwardTime

section LocalPullback

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  {D D' : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem scalar_kinetic_eq_of_parabolic_localPullMetric
    (S : SolutionOn (I := I) (M := M) D)
    (gflow : ℝ → SmoothRiemannianMetric J N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi) {birth q t : ℝ} (hq : 0 < q)
    (hmetric : S.base.metric t =
      localPullMetric (scaleMetric q hq (gflow (birth + t / q))) Phi hPhi)
    (beta : ℝ → M) (hbeta : MDifferentiableAt 𝓘(ℝ, ℝ) I beta t) :
    metricScalarAt (gflow (birth + t / q)) (Phi (beta t)) +
        (gflow (birth + t / q)).inner (Phi (beta t))
          (lVelocity (I := J) (fun s => Phi (beta (q * (s - birth)))) (birth + t / q))
          (lVelocity (I := J) (fun s => Phi (beta (q * (s - birth)))) (birth + t / q)) =
      q * (S.scalar t (beta t) + (S.base.metric t).inner (beta t)
        (lVelocity (I := I) beta t) (lVelocity (I := I) beta t)) := by
  have hclock : q * (birth + t / q - birth) = t := by field_simp; ring
  have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) J (Phi ∘ beta) t :=
    ((hPhi (beta t)).mdifferentiableAt (by simp)).comp t hbeta
  have htime : HasDerivAt (fun s : ℝ => q * (s - birth)) q (birth + t / q) := by
    simpa using ((hasDerivAt_id (birth + t / q)).sub_const birth).const_mul q
  have hcomp' : MDifferentiableAt 𝓘(ℝ, ℝ) J (Phi ∘ beta)
      (q * (birth + t / q - birth)) := by rw [hclock]; exact hcomp
  have hvel := lVelocity_comp_of_hasDerivAt
    (r := fun s : ℝ => q * (s - birth)) (u := birth + t / q) hcomp' htime
  dsimp only [Function.comp_def] at hvel
  rw [hclock] at hvel
  have hpush : lVelocity (I := J) (Phi ∘ beta) t =
      mfderiv I J Phi (beta t) (lVelocity (I := I) beta t) := by
    unfold lVelocity
    rw [mfderiv_comp t ((hPhi (beta t)).mdifferentiableAt (by simp)) hbeta]
    rfl
  have hscalar : S.scalar t (beta t) =
      q⁻¹ * metricScalarAt (gflow (birth + t / q)) (Phi (beta t)) := by
    change metricScalarAt (S.base.metric t) (beta t) = _
    rw [hmetric, metricScalarAt_localPull, metricScalarAt_scaleMetric]
  rw [hvel]
  change metricScalarAt (gflow (birth + t / q)) (Phi (beta t)) +
      (gflow (birth + t / q)).inner (Phi (beta t))
        (q • lVelocity (I := J) (Phi ∘ beta) t) (q • lVelocity (I := J) (Phi ∘ beta) t) = _
  rw [hpush, hscalar, hmetric]
  simp only [localPullMetric_inner, scaleMetric_inner, map_smul, smul_apply, smul_eq_mul]
  field_simp

theorem lRegularizedAction_eq_integral_of_parabolic_localPullMetric
    (S : SolutionOn (I := I) (M := M) D) (U : SolutionOn (I := J) (M := N) D')
    (Phi : M → N) (hPhi : IsLocalDiffeomorph I J ∞ Phi)
    {birth q T a b : ℝ} (hq : 0 < q) (hab : a ≤ b) (hbT : birth + b / q ≤ T)
    (hmetric : ∀ t ∈ Ioo a b, S.base.metric t =
      localPullMetric (scaleMetric q hq (U.base.metric (birth + t / q))) Phi hPhi)
    (beta : ℝ → M) (hbeta : ∀ t ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I beta t) :
    lRegularizedAction U T (fun u => Phi (beta (q * (T - u ^ 2 - birth))))
        (Real.sqrt (T - birth - b / q)) (Real.sqrt (T - birth - a / q)) =
      ∫ t in a..b, Real.sqrt (T - birth - t / q) *
        (S.scalar t (beta t) + (S.base.metric t).inner (beta t)
          (lVelocity (I := I) beta t) (lVelocity (I := I) beta t)) := by
  let gamma : ℝ → N := fun s => Phi (beta (q * (s - birth)))
  have hphysical : birth + a / q ≤ birth + b / q := by gcongr
  have hgamma : ∀ s ∈ Ioo (birth + a / q) (birth + b / q),
      MDifferentiableAt 𝓘(ℝ, ℝ) J gamma s := by
    intro s hs
    have htime : q * (s - birth) ∈ Ioo a b := by
      constructor
      · have hh := (div_lt_iff₀ hq).mp (show a / q < s - birth by linarith [hs.1])
        nlinarith
      · have hh := (lt_div_iff₀ hq).mp (show s - birth < b / q by linarith [hs.2])
        nlinarith
    have ht : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => q * (s - birth)) s :=
      mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
    exact ((hPhi _).mdifferentiableAt (by simp)).comp s ((hbeta _ htime).comp s ht)
  have hforward := lRegularizedAction_eq_integral_forwardTime U hphysical hbT gamma hgamma
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun t : ℝ => birth + t / q) (f' := fun _ : ℝ => q⁻¹)
    (g := fun s => Real.sqrt (T - s) *
      (U.scalar s (gamma s) + (U.base.metric s).inner (gamma s)
        (lVelocity (I := J) gamma s) (lVelocity (I := J) gamma s)))
    (a := a) (b := b) (by fun_prop)
    (by
      intro t _
      simpa [one_div] using ((hasDerivAt_id t).div_const q).const_add birth)
    (by intro _ _; positivity)
  have hcongr : (∫ t in a..b,
      (fun s => Real.sqrt (T - s) *
        (U.scalar s (gamma s) + (U.base.metric s).inner (gamma s)
          (lVelocity (I := J) gamma s) (lVelocity (I := J) gamma s))) (birth + t / q) * q⁻¹) =
      ∫ t in a..b, Real.sqrt (T - birth - t / q) *
        (S.scalar t (beta t) + (S.base.metric t).inner (beta t)
          (lVelocity (I := I) beta t) (lVelocity (I := I) beta t)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo a b := by simpa [uIoo, min_eq_left hab, max_eq_right hab] using ht
    have hh := scalar_kinetic_eq_of_parabolic_localPullMetric S U.base.metric Phi hPhi hq
      (hmetric t ht') beta (hbeta t ht')
    have hclock : q * (birth + t / q - birth) = t := by field_simp; ring
    dsimp only
    change Real.sqrt (T - (birth + t / q)) *
      (metricScalarAt (U.base.metric (birth + t / q)) (gamma (birth + t / q)) +
        (U.base.metric (birth + t / q)).inner (gamma (birth + t / q))
          (lVelocity (I := J) gamma (birth + t / q)) (lVelocity (I := J) gamma (birth + t / q))) * q⁻¹ = _
    have hpoint : gamma (birth + t / q) = Phi (beta t) := by simp only [gamma, hclock]
    rw [hpoint, hh]
    rw [show T - (birth + t / q) = T - birth - t / q by ring]
    field_simp
  have hclocka : T - (birth + a / q) = T - birth - a / q := by ring
  have hclockb : T - (birth + b / q) = T - birth - b / q := by ring
  simpa only [gamma, hclocka, hclockb] using hforward.trans (hchange.symm.trans hcongr)

end LocalPullback

end DifferentialGeometry.PDE.RicciFlow.Perelman
