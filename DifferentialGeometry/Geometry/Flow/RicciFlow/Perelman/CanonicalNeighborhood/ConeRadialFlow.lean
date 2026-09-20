import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeDistance
import DifferentialGeometry.Geometry.Comparison.Distance.LocalSmoothness
import DifferentialGeometry.Geometry.Comparison.Distance.Eikonal
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Order.Real
import DifferentialGeometry.Geometry.Comparison.HopfRinow.GeodesicSpeedBound
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private theorem exists_radial_anchor
    {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph M (ℝ × Y)) {x : M} (hx : x ∈ e.source)
    {V : Set M} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ b : ℝ, (e x).1 < b ∧
      ∃ p : M, p ∈ V ∩ e.source ∧ e p = (b, (e x).2) := by
  have hmem : e '' (V ∩ e.source) ∈ 𝓝 (e x) :=
    e.image_mem_nhds hx ((hV.inter e.open_source).mem_nhds ⟨hxV, hx⟩)
  have hline : ContinuousAt (fun b : ℝ => (b, (e x).2)) (e x).1 :=
    continuousAt_id.prodMk continuousAt_const
  have hpre : (fun b : ℝ => (b, (e x).2)) ⁻¹' (e '' (V ∩ e.source)) ∈
      𝓝 (e x).1 := hline.preimage_mem_nhds hmem
  obtain ⟨c, hrc, hc⟩ := exists_Ico_subset_of_mem_nhds hpre (exists_gt (e x).1)
  obtain ⟨b, hrb, hbc⟩ := exists_between hrc
  obtain ⟨p, hp, hep⟩ := hc ⟨hrb.le, hbc⟩
  exact ⟨b, hrb, p, hp, hep⟩

variable {E H M Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [MetricSpace Y]

theorem contMDiffOn_radial_of_local_riemannian_distance_cone
    (g : SmoothRiemannianMetric I M) (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpos : ∀ x ∈ e.source, 0 < (e x).1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      (riemannianEDistOf g x y).toReal = openConeDistance (e x) (e y)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => (e x).1) e.source := by
  intro p hp
  obtain ⟨U, hU, hpU, hsmooth⟩ :=
    Geometry.Riemannian.exists_open_contMDiff_riemannianEDistOf_sq g p
  obtain ⟨b, hab, p1, hp1, hep1⟩ := exists_radial_anchor e hp hU hpU
  have hsq (z : M) (hz : z ∈ U) :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => (riemannianEDistOf g y z).toReal ^ 2) p := by
    exact (hsmooth.contMDiffAt ((hU.prod hU).mem_nhds ⟨hpU, hz⟩)).comp p
      (contMDiffAt_id.prodMk contMDiffAt_const)
  have hrad : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => (e y).1 ^ 2) p := by
    have hc : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y => (b * (riemannianEDistOf g y p).toReal ^ 2 -
          (e p).1 * (riemannianEDistOf g y p1).toReal ^ 2) / (b - (e p).1) + (e p).1 * b) p :=
      ((contMDiffAt_const.mul (hsq p hpU)).sub
        (contMDiffAt_const.mul (hsq p1 hp1.1))).div_const (b - (e p).1)
          |>.add contMDiffAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hp] with y hy
    rw [hdist y hy p hp, hdist y hy p1 hp1.2, hep1]
    exact radial_sq_eq_of_openConeDistance (hpos y hy).le (hpos p hp).le
      ((hpos p hp).trans hab).le hab.ne (e p).2
  have hroot := (Real.contDiffAt_sqrt (sq_pos_of_pos (hpos p hp)).ne').contMDiffAt.comp p hrad
  apply (hroot.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [e.open_source.mem_nhds hp] with y hy
  exact (Real.sqrt_sq (hpos y hy).le).symm


theorem inner_gradient_radial_self_of_local_riemannian_distance_cone
    (g : SmoothRiemannianMetric I M) (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpos : ∀ x ∈ e.source, 0 < (e x).1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      (riemannianEDistOf g x y).toReal = openConeDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    g.inner p (Geometry.Operator.gradientFun g (fun y => (e y).1) p)
      (Geometry.Operator.gradientFun g (fun y => (e y).1) p) = 1 := by
  let r : M → ℝ := fun y => (e y).1
  have hr : MDifferentiableAt I 𝓘(ℝ, ℝ) r p :=
    ((contMDiffOn_radial_of_local_riemannian_distance_cone g e hpos hdist p hp).contMDiffAt
      (e.open_source.mem_nhds hp)).mdifferentiableAt (by simp)
  obtain ⟨U, hU, hpU, hsquared⟩ :=
    Geometry.Riemannian.exists_open_contMDiff_riemannianEDistOf_sq g p
  obtain ⟨V, hV, hpV, heikonal⟩ :=
    Geometry.Riemannian.exists_open_gradient_riemannianEDistOf_normSq_eq_one g p
  obtain ⟨b, hab, p1, hp1, hep1⟩ := exists_radial_anchor e hp (hU.inter hV) ⟨hpU, hpV⟩
  have hb : 0 < b := (hpos p hp).trans hab
  have hne : p ≠ p1 := by
    intro heq
    have hf := congrArg Prod.fst hep1
    rw [← heq] at hf
    exact hab.ne hf
  have hbase : (riemannianEDistOf g p p1).toReal = b - (e p).1 := by
    rw [hdist p hp p1 hp1.2, hep1, openConeDistance]
    simp only [dist_self, min_eq_right Real.pi_pos.le, Real.cos_zero, mul_one]
    rw [show (e p).1 ^ 2 + b ^ 2 - 2 * (e p).1 * b = (b - (e p).1) ^ 2 by ring,
      Real.sqrt_sq (sub_pos.mpr hab).le]
  have hdSq : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => (riemannianEDistOf g y p1).toReal ^ 2) p :=
    (hsquared.contMDiffAt ((hU.prod hU).mem_nhds ⟨hpU, hp1.1.1⟩)).comp p
      (contMDiffAt_id.prodMk contMDiffAt_const)
  have hd : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => (riemannianEDistOf g y p1).toReal) p := by
    have hpositive : 0 < (riemannianEDistOf g p p1).toReal := hbase ▸ sub_pos.mpr hab
    have h := (Real.contDiffAt_sqrt (sq_pos_of_pos hpositive).ne').contMDiffAt.comp p hdSq
    exact (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y =>
      (Real.sqrt_sq ENNReal.toReal_nonneg).symm)).mdifferentiableAt (by simp)
  have hsupport : ∀ᶠ y in 𝓝 p, b - (riemannianEDistOf g y p1).toReal ≤ r y := by
    filter_upwards [e.open_source.mem_nhds hp] with y hy
    have h := sub_radial_le_openConeDistance (hpos y hy).le hb.le
      (z := e y) (w := (b, (e p).2))
    rw [← hep1, ← hdist y hy p1 hp1.2, hep1] at h
    change b - (riemannianEDistOf g y p1).toReal ≤ (e y).1
    linarith
  have hgrad := Geometry.Topology.gradientFun_eq_of_differentiable_lower_support
    g hr (mdifferentiableAt_const.sub hd)
    (show b - (riemannianEDistOf g p p1).toReal = r p by rw [hbase]; dsimp [r]; ring) hsupport
  rw [hgrad]
  change g.inner p (Geometry.Operator.gradientFun g
    (fun y => b - (riemannianEDistOf g y p1).toReal) p)
    (Geometry.Operator.gradientFun g (fun y => b - (riemannianEDistOf g y p1).toReal) p) = 1
  rw [Geometry.Operator.gradientFun_sub g (f := fun _ => b) mdifferentiableAt_const hd,
    Geometry.Operator.gradientFun_const, zero_sub]
  simp only [map_neg, neg_apply, neg_neg]
  have h := heikonal p1 hp1.1.2 p hpV hne.symm
    (by simpa only [riemannianEDistOf_comm g p1] using hd)
  simpa only [riemannianEDistOf_comm g p1] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {Y : Type*} [MetricSpace Y]

theorem snd_eq_of_openConeDistance_le_radial_sub
    {z w : ℝ × Y} (hz : 0 < z.1) (hw : 0 < w.1)
    (hd : openConeDistance z w ≤ w.1 - z.1) :
    z.2 = w.2 := by
  have heq : openConeDistance z w = w.1 - z.1 :=
    le_antisymm hd (sub_radial_le_openConeDistance hz.le hw.le)
  have hs := openConeDistance_sq hz.le hw.le
  rw [heq] at hs
  have hprod : (2 * z.1 * w.1) *
      (1 - Real.cos (min Real.pi (dist z.2 w.2))) = 0 := by
    nlinarith [hs]
  have hcoef : 2 * z.1 * w.1 ≠ 0 := ne_of_gt (by positivity)
  have hcos : Real.cos (min Real.pi (dist z.2 w.2)) = 1 := by
    have h := (mul_eq_zero.mp hprod).resolve_left hcoef
    linarith
  have htheta : min Real.pi (dist z.2 w.2) = 0 := by
    apply (Real.cos_eq_one_iff_of_lt_of_lt ?_ ?_).mp hcos
    · exact lt_of_lt_of_le (by linarith [Real.pi_pos])
        (le_min Real.pi_pos.le dist_nonneg)
    · exact (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  by_contra hne
  have hpositive : 0 < min Real.pi (dist z.2 w.2) :=
    lt_min Real.pi_pos (dist_pos.mpr hne)
  rw [htheta] at hpositive
  exact (lt_irrefl 0) hpositive

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem radial_image_of_unit_gradient_curve_of_local_riemannian_distance_cone
    (g : SmoothRiemannianMetric I M)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpos : ∀ x ∈ e.source, 0 < (e x).1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      (riemannianEDistOf g x y).toReal = openConeDistance (e x) (e y))
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
    apply snd_eq_of_openConeDistance_le_radial_sub
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

theorem radial_image_of_gradient_curve_of_local_riemannian_distance_cone
    (g : SmoothRiemannianMetric I M) (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpos : ∀ x ∈ e.source, 0 < (e x).1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      (riemannianEDistOf g x y).toReal = openConeDistance (e x) (e y))
    {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hconn : IsPreconnected J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ J)
    (hstay : ∀ τ ∈ J, γ τ ∈ e.source)
    (hvel : ∀ τ ∈ J,
      mfderiv 𝓘(ℝ, ℝ) I γ τ 1 = gradientFun g (fun x => (e x).1) (γ τ))
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    e (γ t) = ((e (γ s)).1 + (t - s), (e (γ s)).2) := by
  apply radial_image_of_unit_gradient_curve_of_local_riemannian_distance_cone
    g e hpos hdist hJ hconn hγ hstay ?_ hvel ?_ hs ht
  · intro τ hτ
    exact ((contMDiffOn_radial_of_local_riemannian_distance_cone g e hpos hdist
      (γ τ) (hstay τ hτ)).contMDiffAt
        (e.open_source.mem_nhds (hstay τ hτ))).mdifferentiableAt (by simp)
  · intro τ hτ
    exact inner_gradient_radial_self_of_local_riemannian_distance_cone g e hpos hdist (hstay τ hτ)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
