import DifferentialGeometry.Geometry.Metric.ConeRadius
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  {Y : Type*} [PseudoMetricSpace Y]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
section Complete
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem radial_translation_smooth_of_complete
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ e.source ∧
      MapsTo (fun z : ℝ × M => ((e z.2).1 + z.1, (e z.2).2))
        (Ioo (-δ) δ ×ˢ U) e.target ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun z : ℝ × M => e.symm ((e z.2).1 + z.1, (e z.2).2)) (Ioo (-δ) δ ×ˢ U) := by
  have hmetric (x y : M) : edist x y = riemannianEDistOf g x y := by
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm]
    exact IsRiemannianManifold.out x y
  let ρ : M → ℝ := fun x => (e x).1
  let G := gradientFun g ρ
  let J : ℝ × M → ℝ × Y := fun z => ((e z.2).1 + z.1, (e z.2).2)
  have hJ : ContinuousAt J (0, p) := by
    have he : ContinuousAt (fun z : ℝ × M => e z.2) (0, p) :=
      (e.continuousAt hp).comp continuousAt_snd
    exact (he.fst.add continuousAt_fst).prodMk he.snd
  have hJ0 : J (0, p) = e p := by simp [J]
  have htarget : J ⁻¹' e.target ∈ 𝓝 (0, p) :=
    hJ (by simpa only [hJ0] using e.open_target.mem_nhds (e.map_source hp))
  obtain ⟨A, hA, W, hW, hAW⟩ := mem_nhds_prod_iff.mp htarget
  obtain ⟨R, hR, hRA⟩ := Metric.mem_nhds_iff.mp hA
  let δ := R / 2
  have hδ : 0 < δ := half_pos hR
  have hradial (x : M) (hx : x ∈ W) (s : ℝ) (hs : s ∈ Icc (-δ) δ) :
      ((e x).1 + s, (e x).2) ∈ e.target := by
    apply hAW (show (s, x) ∈ A ×ˢ W from ⟨hRA ?_, hx⟩)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact (abs_le.mpr hs).trans_lt (half_lt_self hR)
  let U := interior W ∩ e.source
  have hU : IsOpen U := isOpen_interior.inter e.open_source
  have hpU : p ∈ U := ⟨mem_interior_iff_mem_nhds.mpr hW, hp⟩
  have heq : EqOn (fun z : ℝ × M => e.symm (J z))
      (fun z => expMapIntrinsic g hEnorm z.2 (z.1 • G z.2)) (Ioo (-δ) δ ×ˢ U) := by
    intro z hz
    have hxW : z.2 ∈ W := interior_subset hz.2.1
    let f : ℝ → M := fun s => e.symm ((e z.2).1 + s, (e z.2).2)
    have hf0 : f 0 = z.2 := by simpa only [f, add_zero] using e.left_inv hz.2.2
    have hfeq (s : ℝ) (hs : s ∈ Icc (-δ) δ) : e (f s) = ((e z.2).1 + s, (e z.2).2) :=
      e.right_inv (hradial z.2 hxW s hs)
    have hfdist (s : ℝ) (hs : s ∈ Icc (-δ) δ) (v : ℝ) (hv : v ∈ Icc (-δ) δ) :
        dist (f s) (f v) = |s - v| := by
      rw [hdist (f s) (e.map_target (hradial z.2 hxW s hs))
        (f v) (e.map_target (hradial z.2 hxW v hv)), hfeq s hs, hfeq v hv,
        Metric.coneDistance_same_direction]
      congr 1
      ring
    have hsegment := eqOn_intrinsicGeodesic_of_metric_segment g hEnorm f hδ hfdist hz.1
    have hgradient := gradient_radius_eq_radial_velocity_of_coneDistance
      g hmetric e hpositive hdist hz.2.2
    change (G z.2 : E) = (mfderiv 𝓘(ℝ, ℝ) I f 0 1 : E) at hgradient
    change f z.1 = expMapIntrinsic g hEnorm z.2 (z.1 • G z.2)
    rw [expMapIntrinsic_def, intrinsicGeodesic_smul, hsegment]
    congr 1
    exact hgradient.symm
  refine ⟨δ, hδ, U, hU, hpU, inter_subset_right, ?_, ?_⟩
  · intro z hz
    exact hradial z.2 (interior_subset hz.2.1) z.1 ⟨hz.1.1.le, hz.1.2.le⟩
  intro z hz
  have hG : ContMDiffAt I I.tangent ∞ (T% G) z.2 :=
    gradientFun_contMDiffAt g ((contMDiffOn_radius_of_coneDistance g hmetric e hpositive hdist).contMDiffAt (e.open_source.mem_nhds hz.2.2))
  have hsection : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun z : ℝ × M => (⟨z.2, z.1 • G z.2⟩ : TangentBundle I M)) z :=
    contMDiffAt_fst.smul_bundle (hG.comp z contMDiffAt_snd)
  have h := (intrinsicExp_smooth g hEnorm).contMDiffAt.comp z hsection
  exact h.contMDiffWithinAt.congr (fun y hy => heq hy) (heq hz)

end Complete

theorem exists_contMDiffOn_radial_translation_of_coneDistance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ e.source ∧
      MapsTo (fun z : ℝ × M => ((e z.2).1 + z.1, (e z.2).2))
        (Ioo (-δ) δ ×ˢ U) e.target ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun z : ℝ × M => e.symm ((e z.2).1 + z.1, (e z.2).2)) (Ioo (-δ) δ ×ˢ U) := by
  classical
  let d : M → M → ℝ := dist
  have hd_nonneg (x y : M) : 0 ≤ d x y := dist_nonneg
  let : PathConnectedSpace M := by
    refine ⟨⟨p⟩, fun x y => ?_⟩
    by_contra h
    have hp : IsEmpty (Path x y) := not_nonempty_iff.mp h
    have hinf : riemannianEDistOf g x y = ⊤ := by
      rw [edistOf_iInf]
      exact le_antisymm le_top (le_iInf fun γ => (hp.false γ).elim)
    rw [← hmetric] at hinf
    exact edist_ne_top x y hinf
  obtain ⟨g', r, V, hr, hcomplete, _, _, _, _, hlocal⟩ :=
    exists_riemannianMetricComplete_eqOn_ball g hmetric p
  let B : Set M := Metric.ball p r
  let e' := e.restrOpen B Metric.isOpen_ball
  have hp' : p ∈ e'.source := ⟨hp, Metric.mem_ball_self hr⟩
  have hpos' : ∀ z ∈ e'.target, 0 < z.1 := fun z hz => hpositive z hz.1
  let : IsManifold I 1 M := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g'.inner, g'.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let em : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : MetricSpace M := @EMetricSpace.toMetricSpace M em
    (fun x y => (Manifold.riemannianEDist_lt_top (I := I) x y).ne)
  let : CompleteSpace M := hcomplete.complete
  let : IsRiemannianManifold I M := ⟨fun x y => rfl⟩
  have hEnorm : IsMetricNorm (I := I) g' :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g' x v
  have hd (x y : M) (hx : x ∈ B) (hy : y ∈ B) : dist x y = d x y := by
    change (riemannianEDistOf g' x y).toReal = d x y
    rw [hlocal x hx y hy, ENNReal.toReal_ofReal (hd_nonneg x y)]
  have hdist' : ∀ x ∈ e'.source, ∀ y ∈ e'.source,
      dist x y = Metric.coneDistance (e' x) (e' y) := by
    intro x hx y hy
    exact (hd x y hx.2 hy.2).trans (hdist x hx.1 y hy.1)
  obtain ⟨δ, hδ, U, hU, hpU, hsub, hmaps, hsmooth⟩ :=
    radial_translation_smooth_of_complete g' hEnorm e' hpos' hdist' hp'
  exact ⟨δ, hδ, U, hU, hpU, fun x hx => (hsub hx).1, fun z hz => (hmaps hz).1, hsmooth⟩

private theorem dilation_smooth_near_one
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    ∃ Ω : Set (ℝ × M), IsOpen Ω ∧ (1, p) ∈ Ω ∧
      Ω ⊆ Ioi 0 ×ˢ e.source ∧
      MapsTo (fun z : ℝ × M => (z.1 * (e z.2).1, (e z.2).2)) Ω e.target ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun z : ℝ × M => e.symm (z.1 * (e z.2).1, (e z.2).2)) Ω := by
  obtain ⟨δ, hδ, U, hU, hpU, hsub, hmaps, htranslation⟩ :=
    exists_contMDiffOn_radial_translation_of_coneDistance g hmetric e hpositive hdist hp
  let F : ℝ × M → ℝ × M := fun z => ((z.1 - 1) * (e z.2).1, z.2)
  have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ F (Ioi 0 ×ˢ U) := by
    have hr : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : ℝ × M => (e z.2).1) (Ioi 0 ×ˢ U) := (contMDiffOn_radius_of_coneDistance g hmetric e hpositive hdist).comp
      contMDiff_snd.contMDiffOn (fun z hz => hsub hz.2)
    exact ((contMDiff_fst.contMDiffOn.sub contMDiff_const.contMDiffOn).mul hr).prodMk contMDiff_snd.contMDiffOn
  let Ω := (Ioi 0 ×ˢ U) ∩ F ⁻¹' (Ioo (-δ) δ ×ˢ U)
  have hΩ : IsOpen Ω := hF.continuousOn.isOpen_inter_preimage (isOpen_Ioi.prod hU)
    (isOpen_Ioo.prod hU)
  have hpΩ : (1, p) ∈ Ω := by
    refine ⟨⟨by norm_num, hpU⟩, ?_⟩
    change ((1 - 1) * (e p).1, p) ∈ Ioo (-δ) δ ×ˢ U
    simpa only [sub_self, zero_mul, mem_prod, mem_Ioo, neg_lt_zero] using ⟨⟨hδ, hδ⟩, hpU⟩
  have hformula (z : ℝ × M) : (e (F z).2).1 + (F z).1 = z.1 * (e z.2).1 := by
    dsimp only [F]
    ring
  refine ⟨Ω, hΩ, hpΩ, fun z hz => ⟨hz.1.1, hsub hz.1.2⟩, ?_, ?_⟩
  · intro z hz
    have h := hmaps hz.2
    change ((e (F z).2).1 + (F z).1, (e (F z).2).2) ∈ e.target at h
    rwa [hformula] at h
  · have h := htranslation.comp (hF.mono inter_subset_left) (fun z hz => hz.2)
    apply h.congr
    intro z hz
    change e.symm (z.1 * (e z.2).1, (e z.2).2) =
      e.symm ((e (F z).2).1 + (F z).1, (e (F z).2).2)
    rw [hformula]

theorem exists_smooth_dilation_of_coneDistance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    ∃ Ω : Set (ℝ × M), IsOpen Ω ∧ (1, p) ∈ Ω ∧
      Ω ⊆ Ioi 0 ×ˢ e.source ∧
      MapsTo (fun z : ℝ × M => (z.1 * (e z.2).1, (e z.2).2)) Ω e.target ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun z : ℝ × M => e.symm (z.1 * (e z.2).1, (e z.2).2)) Ω ∧
      ∀ z ∈ Ω, ∀ v w : TangentSpace I z.2,
        g.inner (e.symm (z.1 * (e z.2).1, (e z.2).2))
          (mfderiv I I (fun x => e.symm (z.1 * (e x).1, (e x).2)) z.2 v)
          (mfderiv I I (fun x => e.symm (z.1 * (e x).1, (e x).2)) z.2 w) =
            z.1 ^ 2 * g.inner z.2 v w := by
  obtain ⟨Ω, hΩ, hpΩ, hsub, hmaps, hsmooth⟩ :=
    dilation_smooth_near_one g hmetric e hpositive hdist hp
  refine ⟨Ω, hΩ, hpΩ, hsub, hmaps, hsmooth, ?_⟩
  intro z hz v w
  let D : M → M := fun x => e.symm (z.1 * (e x).1, (e x).2)
  have hD : MDifferentiableAt I I D z.2 :=
    ((hsmooth.contMDiffAt (hΩ.mem_nhds hz)).comp z.2
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by decide)
  apply inner_mfderiv_eq_mul_of_eventually_riemannian_distance_eq g g D z.2 z.1 hD ?_ v w
  have hev : ∀ᶠ x in 𝓝 z.2, (z.1, x) ∈ Ω :=
    (continuousAt_const.prodMk continuousAt_id) (hΩ.mem_nhds hz)
  filter_upwards [hev] with x hx
  rw [← hmetric, ← hmetric, edist_dist, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_ofReal dist_nonneg]
  rw [hdist (D x) (e.map_target (hmaps hx)) (D z.2) (e.map_target (hmaps hz))]
  change Metric.coneDistance (e (e.symm (z.1 * (e x).1, (e x).2)))
      (e (e.symm (z.1 * (e z.2).1, (e z.2).2))) = z.1 * dist x z.2
  rw [e.right_inv (hmaps hx), e.right_inv (hmaps hz), Metric.coneDistance_radial_mul,
    abs_of_pos (hsub hz).1, hdist x (hsub hx).2 z.2 (hsub hz).2]

end DifferentialGeometry.Geometry.Riemannian
