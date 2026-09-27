import DifferentialGeometry.Geometry.Exponential.PathLifting
import DifferentialGeometry.Geometry.Exponential.RadialPath
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import Mathlib.Topology.Homotopy.Lifting

noncomputable section

open Bundle Function Manifold Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private def loopRadialPath
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.ball (0 : E) R) (expDomain g p))
    (c : Path p p) (z : Metric.ball (0 : E) R) :
    Path p (framedExpMap g p (z : E)) :=
  c.trans (radialPath g p (normalFrame g p (z : E)) (hdom z.property)).withSittingInstants

private theorem exists_loopRadialPath_lift
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.ball (0 : E) R) (expDomain g p))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1)
    (z : Metric.ball (0 : E) R)
    (hbudget : let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      c.riemannianELength (I := I) + ENNReal.ofReal ‖(z : E)‖ < ENNReal.ofReal R) :
    ∃ η : ℝ → E, isLiftOn (framedExpMap g p)
      (loopRadialPath g p hdom c z).extend (Metric.ball (0 : E) R) 0 0 1 η := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hEnorm : IsMetricNorm g := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  let ray := radialPath g p (normalFrame g p (z : E)) (hdom z.property)
  have hRay : Path.IsContMDiffWithSittingInstants (I := I) ∞ ray.withSittingInstants := by
    exact ray.isContMDiffWithSittingInstants_withSittingInstants
      (contMDiffOn_extend_radialPath g p _ _)
  have hregular : (loopRadialPath g p hdom c z).IsContMDiffWithSittingInstants (I := I) 1 :=
    hc.trans (hRay.of_le (by norm_num))
  have hlen : (loopRadialPath g p hdom c z).riemannianELength (I := I) <
      ENNReal.ofReal R := by
    change (c.trans ray.withSittingInstants).riemannianELength (I := I) < _
    rw [Path.riemannianELength_trans
      (hc.contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero)
      (hRay.contMDiff.contMDiffOn.mdifferentiableOn (by decide)),
      Path.riemannianELength_withSittingInstants ray
        ((contMDiffOn_extend_radialPath g p _ _).mdifferentiableOn (by decide)),
      riemannianELength_radialPath g hEnorm, normalFrame_sqrt]
    exact hbudget
  exact exists_isLiftOn_framedExpMap g hEnorm p zero_le_one
    hregular.contMDiff.contMDiffOn (Path.extend_zero _) hlen hdom hloc

def loopTransport
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.ball (0 : E) R) (expDomain g p))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1)
    (z : Metric.ball (0 : E) R)
    (hbudget : let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      c.riemannianELength (I := I) + ENNReal.ofReal ‖(z : E)‖ < ENNReal.ofReal R) :
    Metric.ball (0 : E) R :=
  ⟨Classical.choose (exists_loopRadialPath_lift g p hdom hloc c hc z hbudget) 1,
    (Classical.choose_spec (exists_loopRadialPath_lift g p hdom hloc c hc z hbudget)).mapsTo
      ⟨zero_le_one, le_rfl⟩⟩

theorem framedExpMap_loopTransport
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.ball (0 : E) R) (expDomain g p))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1)
    (z : Metric.ball (0 : E) R)
    (hbudget : let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      c.riemannianELength (I := I) + ENNReal.ofReal ‖(z : E)‖ < ENNReal.ofReal R) :
    framedExpMap g p (loopTransport g p hdom hloc c hc z hbudget : E) =
      framedExpMap g p (z : E) := by
  have h := Classical.choose_spec (exists_loopRadialPath_lift g p hdom hloc c hc z hbudget)
  exact (h.2.2 1 ⟨zero_le_one, le_rfl⟩).2.trans (Path.extend_one _)

theorem continuous_loopTransport
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.ball (0 : E) R) (expDomain g p))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1)
    (S : Set (Metric.ball (0 : E) R))
    (hbudget : ∀ z ∈ S, let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      c.riemannianELength (I := I) + ENNReal.ofReal ‖(z : E)‖ < ENNReal.ofReal R) :
    Continuous (fun z : S => loopTransport g p hdom hloc c hc z.1 (hbudget z.1 z.2)) := by
  let U : Opens E := ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
  let fU : U → M := fun z => framedExpMap g p z
  let lift : unitInterval × S → U := fun tz =>
    ⟨Classical.choose (exists_loopRadialPath_lift g p hdom hloc c hc
        tz.2.1 (hbudget tz.2.1 tz.2.2)) tz.1,
      (Classical.choose_spec (exists_loopRadialPath_lift g p hdom hloc c hc
        tz.2.1 (hbudget tz.2.1 tz.2.2))).mapsTo tz.1.property⟩
  let base : unitInterval × S → M := fun tz =>
    loopRadialPath g p hdom c tz.2.1 tz.1
  have hrad : Continuous (fun zt : S × unitInterval =>
      (radialPath g p (normalFrame g p (zt.1.1 : E))
        (hdom zt.1.1.property)).withSittingInstants zt.2) := by
    have hformula (zt : S × unitInterval) :
        (radialPath g p (normalFrame g p (zt.1.1 : E))
          (hdom zt.1.1.property)).withSittingInstants zt.2 =
        framedExpMap g p (Real.smoothTransition (3 * (zt.2 : ℝ) - 1) • (zt.1.1 : E)) := by
      rw [← Path.extend_apply _ zt.2.property, extend_radialPath_withSittingInstants]
      simp only [framedExpMap_apply, map_smul]
    have ht : Continuous (fun zt : S × unitInterval =>
        Real.smoothTransition (3 * (zt.2 : ℝ) - 1)) :=
      Real.smoothTransition.continuous.comp
        ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const)
    have hz : Continuous (fun zt : S × unitInterval => (zt.1.1 : E)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
    have harg : Continuous (fun zt : S × unitInterval =>
        Real.smoothTransition (3 * (zt.2 : ℝ) - 1) • (zt.1.1 : E)) :=
      (ht.smul hz).congr (fun _ => rfl)
    have hmem (zt : S × unitInterval) :
        Real.smoothTransition (3 * (zt.2 : ℝ) - 1) • (zt.1.1 : E) ∈
          Metric.ball (0 : E) R := by
      have hznorm : ‖(zt.1.1 : E)‖ < R := by
        simpa only [Metric.mem_ball, dist_zero_right] using zt.1.1.property
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)).trans_lt hznorm
    exact (hloc.contMDiffOn.continuousOn.comp_continuous harg hmem).congr
      (fun zt => (hformula zt).symm)
  have hfamily : Continuous (fun zt : S × unitInterval =>
      loopRadialPath g p hdom c zt.1.1 zt.2) := by
    exact Path.trans_continuous_family (fun _ : S => c)
      (c.continuous.comp continuous_snd)
      (fun z : S => (radialPath g p (normalFrame g p (z.1 : E))
        (hdom z.1.property)).withSittingInstants) hrad
  have hbase : Continuous base := by
    exact (hfamily.comp (continuous_snd.prodMk continuous_fst)).congr (fun _ => rfl)
  let f : C(unitInterval × S, M) := ⟨base, hbase⟩
  have hlifts : fU ∘ lift = f := by
    funext tz
    have h := (Classical.choose_spec (exists_loopRadialPath_lift g p hdom hloc c hc
      tz.2.1 (hbudget tz.2.1 tz.2.2))).2.2 tz.1 tz.1.property
    rw [Path.extend_apply _ tz.1.property] at h
    exact h.2
  have hstart : Continuous (fun z : S => lift (0, z)) := by
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    change Continuous (fun z : S => (lift (0, z) : E))
    apply (continuous_const : Continuous (fun _ : S => (0 : E))).congr
    intro z
    exact (Classical.choose_spec (exists_loopRadialPath_lift g p hdom hloc c hc
      z.1 (hbudget z.1 z.2))).2.1.symm
  have hpaths : ∀ z : S, Continuous (fun t : unitInterval => lift (t, z)) := by
    intro z
    have h := Classical.choose_spec (exists_loopRadialPath_lift g p hdom hloc c hc
      z.1 (hbudget z.1 z.2))
    exact (continuousOn_iff_continuous_domRestrict.mp h.continuousOn).codRestrict
      (fun t => h.mapsTo t.property)
  have hjoint : Continuous lift :=
    (isLocalDiffeomorph_restrict_open U hloc).isLocalHomeomorph.continuous_lift
      (T2Space.isSeparatedMap fU) f hlifts hstart hpaths
  exact (hjoint.comp
    ((continuous_const : Continuous (fun _ : S => (1 : unitInterval))).prodMk continuous_id)).congr
      (fun _ => rfl)

theorem contMDiffOn_loopTransport_comp
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.ball (0 : E) R) (expDomain g p))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1)
    {γ : ℝ → (⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩ : Opens E)} {s t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc s t))
    (hbudget : ∀ u : ℝ, let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      c.riemannianELength (I := I) + ENNReal.ofReal ‖(γ u : E)‖ < ENNReal.ofReal R) :
    let U : Opens E := ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
    let η : ℝ → U := fun u => loopTransport g p hdom hloc c hc (γ u) (hbudget u)
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc s t) := by
  let U : Opens E := ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
  let S : Set U := {z | let : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    c.riemannianELength (I := I) + ENNReal.ofReal ‖(z : E)‖ < ENNReal.ofReal R}
  let η : ℝ → U := fun u => loopTransport g p hdom hloc c hc (γ u) (hbudget u)
  let ηE : ℝ → E := fun u => (η u : E)
  let γE : ℝ → E := fun u => (γ u : E)
  let F : E → M := framedExpMap g p
  let β : ℝ → M := F ∘ γE
  have hγS : ContinuousOn (fun u => (⟨γ u, hbudget u⟩ : S)) (Icc s t) :=
    Topology.IsInducing.subtypeVal.continuousOn_iff.mpr (by
      simpa only [Function.comp_def] using hγ.continuousOn)
  have hT : Continuous (fun z : S =>
      (loopTransport g p hdom hloc c hc z.1 z.2 : E)) :=
    continuous_subtype_val.comp (continuous_loopTransport g p hdom hloc c hc S (fun _ hz => hz))
  have hηcont : ContinuousOn ηE (Icc s t) := by
    exact (hT.comp_continuousOn' hγS).congr (fun _ _ => rfl)
  have hγE : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γE (Icc s t) :=
    (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := 1)).comp_contMDiffOn hγ
  have hβ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 β (Icc s t) :=
    (hloc.contMDiffOn.of_le (by norm_num)).comp hγE (fun u _ => (γ u).property)
  have hηLift : isLiftOn F β (Metric.ball (0 : E) R) (ηE s) s t ηE := by
    refine ⟨hηcont, rfl, ?_⟩
    intro u _
    exact ⟨(η u).property, framedExpMap_loopTransport g p hdom hloc c hc (γ u) (hbudget u)⟩
  have hηEm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 ηE (Icc s t) :=
    (hηLift.contDiffOn hloc hβ).contMDiffOn
  change ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc s t)
  intro u hu
  have hamb := hηEm u hu
  rw [contMDiffWithinAt_iff] at hamb ⊢
  obtain ⟨hcont, hdiff⟩ := hamb
  refine ⟨Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr ?_, ?_⟩
  · simpa only [ηE, η, Function.comp_def] using hcont
  · convert hdiff using 2
    rfl

theorem pathELength_loopTransport_comp
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.ball (0 : E) R) (expDomain g p))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1)
    {γ : ℝ → (⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩ : Opens E)} {s t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc s t))
    (hbudget : ∀ u : ℝ, let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      c.riemannianELength (I := I) + ENNReal.ofReal ‖(γ u : E)‖ < ENNReal.ofReal R) :
    let U : Opens E := ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
    let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
      (isLocalDiffeomorph_restrict_open U hloc)
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) :=
      ⟨gPull.toRiemannianMetric⟩
    let η : ℝ → U := fun u => loopTransport g p hdom hloc c hc (γ u) (hbudget u)
    Manifold.pathELength 𝓘(ℝ, E) η s t =
      Manifold.pathELength 𝓘(ℝ, E) γ s t := by
  let U : Opens E := ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
  let f : U → M := fun z => framedExpMap g p z
  let hf := isLocalDiffeomorph_restrict_open U hloc
  let gPull := localPullMetric g f hf
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) := ⟨gPull.toRiemannianMetric⟩
  have hEnorm : IsMetricNorm g := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  let η : ℝ → U := fun u => loopTransport g p hdom hloc c hc (γ u) (hbudget u)
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc s t) :=
    contMDiffOn_loopTransport_comp g p hdom hloc c hc hγ hbudget
  have hproj : EqOn (f ∘ η) (f ∘ γ) (Icc s t) := by
    intro u _
    exact framedExpMap_loopTransport g p hdom hloc c hc (γ u) (hbudget u)
  calc
    Manifold.pathELength 𝓘(ℝ, E) η s t =
        Manifold.pathELength I (f ∘ η) s t := (localPull_pathLen g hEnorm f hf hη).symm
    _ = Manifold.pathELength I (f ∘ γ) s t := Manifold.pathELength_congr hproj
    _ = Manifold.pathELength 𝓘(ℝ, E) γ s t := localPull_pathLen g hEnorm f hf hγ

theorem riemannianEDistOf_loopTransport_le_of_path
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.ball (0 : E) R) (expDomain g p))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1)
    {x y : (⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩ : Opens E)}
    (j : Path x y) (hj : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 j.extend (Icc (0 : ℝ) 1))
    (hbudget : ∀ u : ℝ, let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      c.riemannianELength (I := I) + ENNReal.ofReal ‖(j.extend u : E)‖ < ENNReal.ofReal R)
    (hjlen : let U : Opens E := ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
      let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
        (isLocalDiffeomorph_restrict_open U hloc)
      let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) := ⟨gPull.toRiemannianMetric⟩
      j.riemannianELength (I := 𝓘(ℝ, E)) = riemannianEDistOf gPull x y) :
    let U : Opens E := ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
    let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
      (isLocalDiffeomorph_restrict_open U hloc)
    riemannianEDistOf gPull
      (loopTransport g p hdom hloc c hc x (by simpa only [Path.extend_zero] using hbudget 0))
      (loopTransport g p hdom hloc c hc y (by simpa only [Path.extend_one] using hbudget 1)) ≤
      riemannianEDistOf gPull x y := by
  let U : Opens E := ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩
  let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
    (isLocalDiffeomorph_restrict_open U hloc)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) := ⟨gPull.toRiemannianMetric⟩
  let η : ℝ → U := fun u => loopTransport g p hdom hloc c hc (j.extend u) (hbudget u)
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc (0 : ℝ) 1) :=
    contMDiffOn_loopTransport_comp g p hdom hloc c hc hj hbudget
  have hlen : Manifold.pathELength 𝓘(ℝ, E) η 0 1 =
      Manifold.pathELength 𝓘(ℝ, E) j.extend 0 1 :=
    pathELength_loopTransport_comp g p hdom hloc c hc hj hbudget
  have hd : riemannianEDistOf gPull (η 0) (η 1) ≤ riemannianEDistOf gPull x y := by
    calc
      riemannianEDistOf gPull (η 0) (η 1) ≤ Manifold.pathELength 𝓘(ℝ, E) η 0 1 :=
        Manifold.riemannianEDist_le_pathELength hη rfl rfl zero_le_one
      _ = j.riemannianELength (I := 𝓘(ℝ, E)) := hlen
      _ = riemannianEDistOf gPull x y := hjlen
  simpa only [η, Path.extend_zero, Path.extend_one] using hd

theorem loopTransport_ne_of_lift_end_ne
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hdom : MapsTo (normalFrame g p) (Metric.ball (0 : E) R) (expDomain g p))
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1)
    (z : Metric.ball (0 : E) R)
    (hbudget : let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      c.riemannianELength (I := I) + ENNReal.ofReal ‖(z : E)‖ < ENNReal.ofReal R)
    {A : ℝ → E} (hA : isLiftOn (framedExpMap g p) c.extend (Metric.ball (0 : E) R) 0 0 1 A)
    (hA1 : A 1 ≠ 0) : loopTransport g p hdom hloc c hc z hbudget ≠ z := by
  intro hfix
  let F : E → M := framedExpMap g p
  let r := (radialPath g p (normalFrame g p (z : E)) (hdom z.property)).withSittingInstants
  let P := Classical.choose (exists_loopRadialPath_lift g p hdom hloc c hc z hbudget)
  have hP : isLiftOn F (c.trans r).extend (Metric.ball (0 : E) R) 0 0 1 P :=
    Classical.choose_spec (exists_loopRadialPath_lift g p hdom hloc c hc z hbudget)
  have hzR : ‖(z : E)‖ < R := by
    simpa only [Metric.mem_ball, dist_zero_right] using z.property
  have hzero : F 0 = p := by
    simp only [F, framedExpMap_apply, map_zero, expMap_zero]
  have hB : isLiftOn F (Path.refl p).extend (Metric.ball (0 : E) R) 0 0 1
      (fun _ : ℝ => (0 : E)) := by
    refine ⟨continuousOn_const, rfl, ?_⟩
    intro t _
    exact ⟨Metric.mem_ball_self ((norm_nonneg _).trans_lt hzR), hzero⟩
  let Q : ℝ → E := fun t => Real.smoothTransition (3 * (2 * t - 1) - 1) • (z : E)
  have hQ : isLiftOn F ((Path.refl p).trans r).extend (Metric.ball (0 : E) R) 0 0 1 Q := by
    refine ⟨?_, ?_, ?_⟩
    · exact (Real.smoothTransition.continuous.comp
        ((continuous_const.mul
          ((continuous_const.mul continuous_id).sub continuous_const)).sub continuous_const)).smul
            continuous_const |>.continuousOn
    · dsimp only [Q]
      rw [Real.smoothTransition.zero_of_nonpos (by norm_num), zero_smul]
    · intro t _
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right]
        dsimp only [Q]
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact (mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)).trans_lt hzR
      · by_cases ht : t ≤ 1 / 2
        · rw [Path.extend_trans_of_le_half _ _ ht]
          change F (Real.smoothTransition (3 * (2 * t - 1) - 1) • (z : E)) = p
          rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_smul]
          exact hzero
        · rw [Path.extend_trans_of_half_le _ _ (not_le.mp ht).le]
          dsimp only [Q, r, F]
          rw [extend_radialPath_withSittingInstants, framedExpMap_apply, map_smul]
  have hend : P 1 = Q 1 := by
    have hp : P 1 = (z : E) := congrArg Subtype.val hfix
    rw [hp]
    dsimp only [Q]
    rw [Real.smoothTransition.one_of_one_le (by norm_num), one_smul]
  exact hA1 (isLiftOn.end_eq_of_append Metric.isOpen_ball hloc hA hB hP hQ hend)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
