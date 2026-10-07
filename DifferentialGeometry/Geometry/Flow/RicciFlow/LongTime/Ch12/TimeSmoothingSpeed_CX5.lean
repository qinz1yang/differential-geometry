import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingGlue_CX5
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

/-! # H2: physical velocity of the explicit interpolation

The map `f` is static in the chosen unscathed carrier. The chain rule therefore
has only the isotopy term. The operator estimate is `4*t` in the physical
metric, obtained from the constant `4` in `t⁻¹*g`. No normalized velocity is
silently inserted into `PersistentModelPatch.speed`.
-/

noncomputable section
open Set Filter Topology DifferentialGeometry
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {V W HM HN M N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace HM] [TopologicalSpace HN]
  {I : ModelWithCorners ℝ V HM} {J : ModelWithCorners ℝ W HN}
  [TopologicalSpace M] [ChartedSpace HM M] [TopologicalSpace N] [ChartedSpace HN N]

/-- The canonical unit time vector; this avoids relying on reducibility of
Mathlib's tangent-space type synonym during derivative calculations. -/
def timeVector_CX5 (t : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t :=
  (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm (1 : ℝ)

/-- Relate the physical time derivative to the `(1,0)` vector used by the field. -/
theorem time_mfderiv_CX5 {G : ℝ × M → N} {t : ℝ} {p : M}
    (hG : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) J G (t, p)) :
    mfderiv (𝓘(ℝ, ℝ).prod I) J G (t, p) (1, 0) =
      mfderiv 𝓘(ℝ, ℝ) J (fun r : ℝ => G (r, p)) t (timeVector_CX5 t) := by
  have hline : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I)
      (fun r : ℝ => (r, p)) t := mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have h := mfderiv_comp t hG hline
  rw [mfderiv_prod_left] at h
  exact (congrArg (fun L => L (timeVector_CX5 t)) h).symm

theorem mfderiv_curve_comp_scalar_CX5 {u : ℝ → N} {φ : ℝ → ℝ} {t c : ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ) J u (φ t)) (hφ : HasDerivAt φ c t) :
    mfderiv 𝓘(ℝ, ℝ) J (fun r => u (φ r)) t (timeVector_CX5 t) =
      c • mfderiv 𝓘(ℝ, ℝ) J u (φ t) (timeVector_CX5 (φ t)) := by
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t (timeVector_CX5 t) =
      c • timeVector_CX5 (φ t) := by
    rw [mfderiv_eq_fderiv]
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (φ t)).symm
      (fderiv ℝ φ t ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t)
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, HasFDerivAt.fderiv (HasDerivAt.hasFDerivAt hφ)]
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (φ t)).symm (1 * c) = _
    rw [one_mul]
    simpa only [smul_eq_mul, mul_one, timeVector_CX5] using
      map_smul (NormedSpace.fromTangentSpace (𝕜 := ℝ) (φ t)).symm c (1 : ℝ)
  calc
    _ = mfderiv 𝓘(ℝ, ℝ) J u (φ t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t (timeVector_CX5 t)) :=
      congrArg (fun L => L (timeVector_CX5 t))
        (mfderiv_comp t hu hφ.differentiableAt.mdifferentiableAt)
    _ = c • mfderiv 𝓘(ℝ, ℝ) J u (φ t) (timeVector_CX5 (φ t)) := by
      rw [hd, map_smul]

/-- The exact velocity formula, in the product-source convention of the patch
field. The factor is `θ'(t/a)/a`, where `a` is the dyadic left endpoint. -/
theorem smoothingPiece_velocity_CX5 {θ : ℝ → ℝ} {a t : ℝ} {p : M}
    {f : M → N} {E : ℝ × M → M}
    (hθ : DifferentiableAt ℝ θ (t / a))
    (hE : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I E (θ (t / a), p))
    (hf : MDifferentiableAt I J f (E (θ (t / a), p))) :
    mfderiv (𝓘(ℝ, ℝ).prod I) J (smoothingPiece_CX5 θ a f E) (t, p) (1, 0) =
      (deriv θ (t / a) / a) •
        mfderiv I J f (E (θ (t / a), p))
          (mfderiv 𝓘(ℝ, ℝ) I (fun s => E (s, p)) (θ (t / a)) (timeVector_CX5 (θ (t / a)))) := by
  have hc : HasDerivAt (fun r : ℝ => θ (r / a)) (deriv θ (t / a) / a) t := by
    convert! hθ.hasDerivAt.comp t ((hasDerivAt_id t).div_const a) using 1
    simp only [div_eq_mul_inv, one_mul]
  have hEc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s => E (s, p)) (θ (t / a)) :=
    hE.comp (θ (t / a))
      (show MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I)
        (fun r : ℝ => (r, p)) (θ (t / a)) from
          mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hp : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun q : ℝ × M => θ (q.1 / a)) (t, p) :=
    (show MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) θ (t / a) from
      hθ.mdifferentiableAt).comp (t, p)
        (show MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
          (fun q : ℝ × M => q.1 / a) (t, p) from
            (((contDiff_id.div_const a : ContDiff ℝ ∞ (fun r : ℝ => r / a)).contMDiff).comp
              contMDiff_fst).mdifferentiableAt (by simp))
  have hEP : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I
      (fun q : ℝ × M => E (θ (q.1 / a), q.2)) (t, p) :=
    hE.comp (t, p) (hp.prodMk mdifferentiableAt_snd)
  have hG : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) J
      (smoothingPiece_CX5 θ a f E) (t, p) := hf.comp (t, p) hEP
  rw [time_mfderiv_CX5 hG]
  change mfderiv 𝓘(ℝ, ℝ) J (fun r => f (E (θ (r / a), p))) t (timeVector_CX5 t) = _
  have hfe : MDifferentiableAt 𝓘(ℝ, ℝ) J (fun s => f (E (s, p))) (θ (t / a)) :=
    hf.comp (θ (t / a)) hEc
  have hs := mfderiv_curve_comp_scalar_CX5 (u := fun s => f (E (s, p)))
    (φ := fun r : ℝ => θ (r / a)) hfe hc
  refine hs.trans ?_
  exact congrArg (fun w => (deriv θ (t / a) / a) • w)
    (congrArg (fun L => L (timeVector_CX5 (θ (t / a))))
      (mfderiv_comp (θ (t / a)) hf hEc))

section Metric
variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- Convert the normalized operator bound to the physical one explicitly. -/
theorem physical_bound_of_normalized_CX5 (h : SmoothRiemannianMetric I M)
    (g : SmoothRiemannianMetric J N) {t : ℝ} (ht : 0 < t)
    {p : M} {q : N} (L : TangentSpace I p →L[ℝ] TangentSpace J q)
    (hL : ∀ v, (scaleMetric t⁻¹ (inv_pos.mpr ht) g).inner q (L v) (L v) ≤
      4 * h.inner p v v) :
    ∀ v, g.inner q (L v) (L v) ≤ 4 * t * h.inner p v v := by
  intro v
  have hb := mul_le_mul_of_nonneg_left (hL v) ht.le
  rw [scaleMetric_inner, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at hb
  nlinarith

/-- The HPS04 estimate in the exact squared, physical form of the consumer.
For isotopy speed `η = 1/m`, the bound is `(4*B/m)^2/t`; a strict margin
`4*B*η < α` gives the required strict inequality. -/
theorem smoothingPiece_physical_speed_CX5 (h : SmoothRiemannianMetric I M)
    (g : SmoothRiemannianMetric J N) {θ : ℝ → ℝ} {a t B η α : ℝ} {p : M}
    {f : M → N} {E : ℝ × M → M}
    (ha : 0 < a) (ht : t ∈ Icc a (2 * a)) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hmargin : 4 * B * η < α) (hderiv : |deriv θ (t / a)| ≤ B)
    (hθ : DifferentiableAt ℝ θ (t / a))
    (hE : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I E (θ (t / a), p))
    (hf : MDifferentiableAt I J f (E (θ (t / a), p)))
    (hmetric : ∀ w : TangentSpace I (E (θ (t / a), p)),
      g.inner (f (E (θ (t / a), p))) (mfderiv I J f (E (θ (t / a), p)) w)
        (mfderiv I J f (E (θ (t / a), p)) w) ≤ 4 * t * h.inner _ w w)
    (hispeed :
      let u := mfderiv 𝓘(ℝ, ℝ) I (fun s => E (s, p)) (θ (t / a)) (timeVector_CX5 (θ (t / a)));
      h.inner (E (θ (t / a), p)) u u ≤ η ^ 2) :
    let v := mfderiv (𝓘(ℝ, ℝ).prod I) J (smoothingPiece_CX5 θ a f E) (t, p) (1, 0);
    g.inner (smoothingPiece_CX5 θ a f E (t, p)) v v < α ^ 2 / t := by
  have htpos : 0 < t := ha.trans_le ht.1
  let c := deriv θ (t / a) / a
  let u := mfderiv 𝓘(ℝ, ℝ) I (fun s => E (s, p)) (θ (t / a)) (timeVector_CX5 (θ (t / a)))
  have hc : |c| ≤ 2 * B / t := calc
    |c| = |deriv θ (t / a)| / a := by simp only [c, abs_div, abs_of_pos ha]
    _ ≤ B / a := div_le_div_of_nonneg_right hderiv ha.le
    _ ≤ 2 * B / t := (div_le_div_iff₀ ha htpos).mpr (by nlinarith [ht.2])
  have hc2 : c ^ 2 ≤ (2 * B / t) ^ 2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg (show 0 ≤ 2 * B / t by positivity)] using hc
  have hu : g.inner (f (E (θ (t / a), p)))
      (mfderiv I J f (E (θ (t / a), p)) u)
      (mfderiv I J f (E (θ (t / a), p)) u) ≤ 4 * t * η ^ 2 :=
    (hmetric u).trans (mul_le_mul_of_nonneg_left hispeed (by positivity))
  have hsq : (4 * B * η) ^ 2 < α ^ 2 := by
    have hnonneg : 0 ≤ 4 * B * η := by positivity
    nlinarith [mul_pos (sub_pos.mpr hmargin) (show 0 < α + 4 * B * η by linarith)]
  dsimp only
  have hvel := smoothingPiece_velocity_CX5 hθ hE hf
  dsimp only [smoothingPiece_CX5] at hvel ⊢
  rw [hvel]
  change g.inner _ (c • _) (c • _) < _
  simp only [map_smul, smul_apply, smul_eq_mul]
  calc
    _ = c ^ 2 * g.inner (f (E (θ (t / a), p)))
        (mfderiv I J f (E (θ (t / a), p)) u)
        (mfderiv I J f (E (θ (t / a), p)) u) := by ring
    _ ≤ c ^ 2 * (4 * t * η ^ 2) := mul_le_mul_of_nonneg_left hu (sq_nonneg c)
    _ ≤ (2 * B / t) ^ 2 * (4 * t * η ^ 2) :=
      mul_le_mul_of_nonneg_right hc2 (by positivity)
    _ = (4 * B * η) ^ 2 / t := by field_simp; ring
    _ < α ^ 2 / t := div_lt_div_of_pos_right hsq htpos


omit [IsManifold I ∞ M] in
/-- Transport energy through equality of map germs. The point equality also
identifies the target tangent spaces; this is not a comparison of nearby maps. -/
theorem energy_eq_of_eventuallyEq_CX5 (g : SmoothRiemannianMetric J N)
    {G G' : ℝ × M → N} {q : ℝ × M}
    (heq : G =ᶠ[𝓝 q] G') (v : TangentSpace (𝓘(ℝ, ℝ).prod I) q) :
    g.inner (G q) (mfderiv (𝓘(ℝ, ℝ).prod I) J G q v)
      (mfderiv (𝓘(ℝ, ℝ).prod I) J G q v) =
    g.inner (G' q) (mfderiv (𝓘(ℝ, ℝ).prod I) J G' q v)
      (mfderiv (𝓘(ℝ, ℝ).prod I) J G' q v) := by
  have hd := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ).prod I) (I' := J) heq
  have hv := congrArg (fun L => (L v : W)) hd
  change (mfderiv (𝓘(ℝ, ℝ).prod I) J G q v : W) =
    (mfderiv (𝓘(ℝ, ℝ).prod I) J G' q v : W) at hv
  exact congrArg₂ (fun (y : N) (w : W) => g.inner y w w) heq.eq_of_nhds hv

end Metric
end GC.LongTime.Ch12
