import DifferentialGeometry.Geometry.Metric.ConeRadius
import DifferentialGeometry.Geometry.Comparison.HopfRinow.GeodesicSpeedBound
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

section

noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {Y : Type*} [PseudoMetricSpace Y]

private theorem angular_eq_of_dist_eq_zero
    {M : Type*} [TopologicalSpace M] [T0Space M]
    (e : OpenPartialHomeomorph M (ℝ × Y))
    {z : ℝ × Y} (hz : z ∈ e.target) {y : Y} (h : dist z.2 y = 0) : z.2 = y := by
  have hi : Inseparable z (z.1, y) :=
    Inseparable.prod Inseparable.rfl (Metric.inseparable_iff.mpr h)
  have hy : (z.1, y) ∈ e.target := (hi.mem_open_iff e.open_target).mp hz
  have heq : e.symm z = e.symm (z.1, y) :=
    (hi.map_of_continuousAt
      (e.continuousAt_symm hz) (e.continuousAt_symm hy)).eq
  have hpair : z = (z.1, y) := by
    simpa only [e.right_inv hz, e.right_inv hy] using congrArg e heq
  exact congrArg Prod.snd hpair

open DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem radial_image_of_unit_gradient_curve_of_riemannianEDistOf_cone
    (g : SmoothRiemannianMetric I M)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpos : ∀ x ∈ e.source, 0 < (e x).1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      (riemannianEDistOf g x y).toReal = Metric.coneDistance (e x) (e y))
    {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hconn : IsPreconnected J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ J)
    (hstay : ∀ τ ∈ J, γ τ ∈ e.source)
    (hr : ∀ τ ∈ J, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => (e x).1) (γ τ))
    (hvel : ∀ τ ∈ J,
      mfderiv 𝓘(ℝ, ℝ) I γ τ 1 = gradientFun g (fun x => (e x).1) (γ τ))
    (hunit : ∀ τ ∈ J,
      g.inner (γ τ) (gradientFun g (fun x => (e x).1) (γ τ))
        (gradientFun g (fun x => (e x).1) (γ τ)) = 1)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    e (γ t) = ((e (γ s)).1 + (t - s), (e (γ s)).2) := by
  let : T1Space M := I.t1Space M
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let r : M → ℝ := fun x => (e x).1
  have hγmd : ∀ τ ∈ J, MDifferentiableAt 𝓘(ℝ, ℝ) I γ τ := by
    intro τ hτ
    exact ((hγ τ hτ).contMDiffAt (hJ.mem_nhds hτ)).mdifferentiableAt (by norm_num)
  have hder : ∀ τ ∈ J, HasDerivAt (fun u => r (γ u)) 1 τ := by
    intro τ hτ
    have hc := ((hr τ hτ).comp τ (hγmd τ hτ)).differentiableAt.hasDerivAt
    have hd := _root_.mvfderiv_comp_apply τ (hr τ hτ) (hγmd τ hτ) (1 : ℝ)
    erw [DifferentialGeometry.mvfderiv_real_model_eq_fderiv (r ∘ γ) τ
      (1 : TangentSpace 𝓘(ℝ, ℝ) τ)] at hd
    change fderiv ℝ (r ∘ γ) τ 1 = mvfderiv I r (γ τ)
      (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) at hd
    rw [fderiv_apply_one_eq_deriv, hvel τ hτ, ← inner_gradientFun g, hunit τ hτ] at hd
    exact hc.congr_deriv hd
  have hder_sub : ∀ τ ∈ J, HasDerivAt (fun u => r (γ u) - u) 0 τ := by
    intro τ hτ
    convert! (hder τ hτ).fun_sub (hasDerivAt_id τ) using 1
    simp only [sub_self]
  have hrad (a b : ℝ) (ha : a ∈ J) (hb : b ∈ J) :
      r (γ b) = r (γ a) + (b - a) := by
    have hconst := hJ.is_const_of_deriv_eq_zero hconn
      (fun τ hτ => (hder_sub τ hτ).differentiableAt.differentiableWithinAt)
      (fun τ hτ => (hder_sub τ hτ).deriv) ha hb
    linarith
  have hang (a b : ℝ) (ha : a ∈ J) (hb : b ∈ J) (hab : a ≤ b) :
      (e (γ a)).2 = (e (γ b)).2 := by
    have hsub : Icc a b ⊆ J := hconn.ordConnected.out ha hb
    have hspeed : ∀ τ ∈ Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ τ 1‖ₑ ≤ ENNReal.ofReal (1 : ℝ) := by
      intro τ hτ
      have hn : ‖mfderiv 𝓘(ℝ, ℝ) I γ τ 1‖ₑ = ENNReal.ofReal
          (Real.sqrt (g.inner (γ τ) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1)
            (mfderiv 𝓘(ℝ, ℝ) I γ τ 1))) :=
        tensor0SBundle_enorm_eq_riemannianBundle_enorm g (γ τ) _
      rw [hn, hvel τ (hsub hτ), hunit τ (hsub hτ), Real.sqrt_one]
    have hlen := HopfRinow.curve_edist_le_speed_mul_time
      (I := I) (γ := γ) (by norm_num : (0 : ℝ) ≤ 1) hab (hγ.mono hsub) hspeed
    change riemannianEDistOf g (γ a) (γ b) ≤ ENNReal.ofReal (1 * (b - a)) at hlen
    rw [one_mul] at hlen
    have hdist_le : (riemannianEDistOf g (γ a) (γ b)).toReal ≤ b - a := by
      simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlen
    apply angular_eq_of_dist_eq_zero e (e.map_source (hstay a ha))
    apply Metric.dist_snd_eq_zero_of_coneDistance_le_radius_sub
      (hpos (γ a) (hstay a ha)) (hpos (γ b) (hstay b hb))
    rw [← hdist (γ a) (hstay a ha) (γ b) (hstay b hb)]
    change (riemannianEDistOf g (γ a) (γ b)).toReal ≤ r (γ b) - r (γ a)
    rw [hrad a b ha hb]
    linarith
  apply Prod.ext
  · exact hrad s t hs ht
  · rcases le_total s t with hst | hts
    · exact (hang s t hs ht hst).symm
    · exact hang t s ht hs hts

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem radial_image_of_gradient_curve_of_riemannianEDistOf_cone
    (g : SmoothRiemannianMetric I M) (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpos : ∀ x ∈ e.source, 0 < (e x).1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      (riemannianEDistOf g x y).toReal = Metric.coneDistance (e x) (e y))
    {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hconn : IsPreconnected J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ J)
    (hstay : ∀ τ ∈ J, γ τ ∈ e.source)
    (hvel : ∀ τ ∈ J,
      mfderiv 𝓘(ℝ, ℝ) I γ τ 1 = gradientFun g (fun x => (e x).1) (γ τ))
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    e (γ t) = ((e (γ s)).1 + (t - s), (e (γ s)).2) := by
  apply radial_image_of_unit_gradient_curve_of_riemannianEDistOf_cone
    g e hpos hdist hJ hconn hγ hstay ?_ hvel ?_ hs ht
  · intro τ hτ
    exact ((contMDiffOn_radius_of_riemannianEDistOf_cone g e hpos hdist
      (γ τ) (hstay τ hτ)).contMDiffAt
        (e.open_source.mem_nhds (hstay τ hτ))).mdifferentiableAt (by simp)
  · intro τ hτ
    exact gradient_radius_normSq_eq_one_of_riemannianEDistOf_cone g e hpos hdist (hstay τ hτ)

end DifferentialGeometry.Geometry.Riemannian

end

end
