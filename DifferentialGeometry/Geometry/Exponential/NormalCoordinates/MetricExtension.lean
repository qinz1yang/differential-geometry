import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Curve
import DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic
import DifferentialGeometry.Geometry.Comparison.RadialLength
import DifferentialGeometry.Geometry.Exponential.GaussLemma.Framed
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Geodesic.Naturality.MetricLocality
import DifferentialGeometry.Geometry.Geodesic.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Distance.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Exponential Geodesic

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem exists_subtype_curve_extension {n : ℕ∞} {γ : ℝ → M} {a b : ℝ}
    (U : Opens M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hstay : MapsTo γ (uIcc a b) U) :
    ∃ Γ : ℝ → U, ContMDiff 𝓘(ℝ, ℝ) I n Γ ∧
      ∀ t ∈ uIcc a b, (Subtype.val ∘ Γ) =ᶠ[𝓝 t] γ := by
  classical
  let η : ℝ → U := fun t => if ht : γ t ∈ U then ⟨γ t, ht⟩
    else ⟨γ a, hstay left_mem_uIcc⟩
  have hV : IsOpen (γ ⁻¹' (U : Set M)) := U.isOpen.preimage hγ.continuous
  have hηEq (t : ℝ) (ht : γ t ∈ U) : (Subtype.val ∘ η) =ᶠ[𝓝 t] γ := by
    filter_upwards [hV.mem_nhds ht] with s hs
    change γ s ∈ U at hs
    simp only [η, Function.comp_apply, dif_pos hs]
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) I n η (γ ⁻¹' (U : Set M)) := by
    intro t ht
    have hval : ContMDiffAt 𝓘(ℝ, ℝ) I n (Subtype.val ∘ η) t :=
      hγ.contMDiffAt.congr_of_eventuallyEq (hηEq t ht)
    have hsub : ContMDiffWithinAt 𝓘(ℝ, ℝ) I n η univ t := by
      exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp 𝓘(ℝ, ℝ) I (↑n)) η univ t).mp
          hval.contMDiffWithinAt
    exact (show ContMDiffAt 𝓘(ℝ, ℝ) I n η t from hsub).contMDiffWithinAt
  obtain ⟨Γ, hΓ, hEq⟩ := hη.exists_extension_uIcc hV hstay
  refine ⟨Γ, hΓ, ?_⟩
  intro t ht
  exact ((hEq t ht).fun_comp Subtype.val).trans (hηEq t (hstay ht))

end

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]

private theorem exists_geodesic_restriction
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (U : Opens V) (gU : SmoothRiemannianMetric 𝓘(ℝ, V) U)
    (gE : SmoothRiemannianMetric 𝓘(ℝ, V) V) {γ : ℝ → V}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) ∞ γ)
    (hgeo : IsGeodesic gE γ) {B : ℝ}
    (hball : Metric.closedBall (0 : V) B ⊆ (U : Set V))
    (hfence : MapsTo γ (Icc (0 : ℝ) 1) (Metric.ball (0 : V) B))
    (hmetric : ∀ z : U, ‖(z : V)‖ < B → ∀ v w : V,
      (gE.restrictOpen U).inner z v w = gU.inner z v w) :
    ∃ γU : ℝ → U, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) ∞ γU ∧
      IsGeodesicOn gU γU (Icc (0 : ℝ) 1) ∧
      EqOn (Subtype.val ∘ γU) γ (Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖(γU t : V)‖ < B := by
  have hstay : MapsTo γ (uIcc (0 : ℝ) 1) U := by
    rw [uIcc_of_le zero_le_one]
    exact fun t ht => hball (Metric.ball_subset_closedBall (hfence ht))
  obtain ⟨γU, hγU, hGerm⟩ :=
    exists_subtype_curve_extension (I := 𝓘(ℝ, V))
      (n := (⊤ : ℕ∞)) U hγ hstay
  have hEq : EqOn (Subtype.val ∘ γU) γ (Icc (0 : ℝ) 1) :=
    fun t ht => (hGerm t (by rwa [uIcc_of_le zero_le_one])).eq_of_nhds
  have hfenceU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖(γU t : V)‖ < B := by
    have hm := hfence ht
    rw [Metric.mem_ball, dist_zero_right] at hm
    change ‖(Subtype.val ∘ γU) t‖ < B
    rw [hEq ht]
    exact hm
  have hgeoE : IsGeodesicOn gE (Subtype.val ∘ γU) (Icc (0 : ℝ) 1) := by
    intro t ht
    have heq := hGerm t (by rwa [uIcc_of_le zero_le_one])
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at heq.eq_of_nhds heq (hgeo t)
  refine ⟨γU, hγU, ?_, hEq, hfenceU⟩
  apply (isGeodesicOn_iff_of_metric_eventuallyEq (gE.restrictOpen U) gU ?_).mp
    ((geodesicOn_open_iff gE U γU (Icc (0 : ℝ) 1)).mpr hgeoE)
  intro t ht
  have hn : {z : U | ‖(z : V)‖ < B} ∈ 𝓝 (γU t) :=
    (isOpen_lt (continuous_subtype_val.norm) continuous_const).mem_nhds (hfenceU t ht)
  filter_upwards [hn] with z hz
  exact hmetric z hz

private theorem curve_fenced
    (g : SmoothRiemannianMetric I M) (p : M) (U : Opens E)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    {B : ℝ}
    (hball : Metric.closedBall (0 : E) B ⊆ (U : Set E))
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ (z : U), ‖(z : E)‖ ≤ B → ∀ v w : E,
      gExt.inner (z : E) v w =
        g.inner (framedExpMap g p z)
          (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) (z : E) v)
          (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) (z : E) w))
    {γ : ℝ → E} (hγ : ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1))
    (hlen : let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
        ⟨gExt.toRiemannianMetric⟩
      Manifold.pathELength 𝓘(ℝ, E) γ 0 1 < ENNReal.ofReal (B - ‖γ 0‖)) :
    MapsTo γ (Icc (0 : ℝ) 1) (Metric.ball (0 : E) B) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  have hExt : ∀ (z : E) (v : TangentSpace 𝓘(ℝ, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) := by
    intro z v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hrad (z : E) (hz : z ∈ Metric.closedBall (0 : E) B) (v : E) :
      inner ℝ z v ≤ ‖z‖ * Real.sqrt (gExt.inner z v v) := by
    let zU : U := ⟨z, hball hz⟩
    have hzNorm : ‖z‖ ≤ B := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [hmetric zU hzNorm v v]
    exact (le_abs_self _).trans (framedExpMap_radial_lower_bound g p v (hdom hz))
  apply Manifold.mapsTo_ball_of_pathELength_comp_lt_of_radial_bound
    gExt.toContinuousRiemannianMetric hExt id zero_le_one hγ
    (fun _ _ => contMDiffAt_id) ?_ hlen
  intro z hz v
  simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using! hrad z hz v

theorem exists_geodesic_restriction_of_pullback_extension
    (g : SmoothRiemannianMetric I M) (p : M) (U : Opens E)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞ (framedExpMap g p) U)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete gExt) {B : ℝ}
    (hball : Metric.closedBall (0 : E) B ⊆ (U : Set E))
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ (z : U), ‖(z : E)‖ ≤ B → ∀ v w : E,
      gExt.inner (z : E) v w =
        g.inner (framedExpMap g p z)
          (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) (z : E) v)
          (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) (z : E) w))
    (x y : E)
    (hbudget : ENNReal.ofReal ‖(x : E)‖ + riemannianEDistOf gExt (x : E) (y : E) <
      ENNReal.ofReal B) :
    let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
      (isLocalDiffeomorph_restrict_open U hloc)
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
      ⟨gExt.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
    let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
    let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
    let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    let : CompleteSpace E := hcomplete.complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(ℝ, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) := by
      intro z v
      rw [← ofReal_norm, norm_eq_sqrt_real_inner]
      rfl
    ∃ γU : ℝ → U, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γU ∧
      IsGeodesicOn gPull γU (Icc (0 : ℝ) 1) ∧ (γU 0 : E) = x ∧ (γU 1 : E) = y ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖(γU t : E)‖ < B) ∧
      Manifold.pathELength 𝓘(ℝ, E) (Subtype.val ∘ γU) 0 1 =
        riemannianEDistOf gExt (x : E) (y : E) ∧
      ∀ hdim : NeZero (Module.finrank ℝ E),
        letI := hdim
        EqOn (Subtype.val ∘ γU) (minJoin gExt hExt (x : E) (y : E)) (Icc (0 : ℝ) 1) := by
  dsimp only
  let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
    (isLocalDiffeomorph_restrict_open U hloc)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(ℝ, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) := by
    intro z v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  let d := riemannianEDistOf gExt (x : E) (y : E)
  have hxlt : ENNReal.ofReal ‖(x : E)‖ < ENNReal.ofReal B :=
    (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ d from bot_le)).trans_lt hbudget
  have hstart : ‖(x : E)‖ < B := (ENNReal.ofReal_lt_ofReal_iff'.mp hxlt).1
  have hB : 0 < B := (norm_nonneg (x : E)).trans_lt hstart
  have hdlt : d < ENNReal.ofReal B :=
    (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal ‖(x : E)‖ from bot_le)).trans_lt
      hbudget
  have hfin : d ≠ ⊤ := ne_top_of_lt hdlt
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    have hxy : x = y := Subsingleton.elim _ _
    let xU : U := ⟨x, hball (by simpa only [Metric.mem_closedBall, dist_zero_right] using hstart.le)⟩
    refine ⟨fun _ => xU, contMDiff_const, ?_, rfl, hxy, fun _ _ => hstart, ?_, ?_⟩
    · exact fun t _ => isGeodesic_const gPull xU t
    · change Manifold.pathELength 𝓘(ℝ, E) (fun _ : ℝ => (x : E)) 0 1 =
        riemannianEDistOf gExt (x : E) (y : E)
      rw [← hxy]
      change Manifold.pathELength 𝓘(ℝ, E) (fun _ : ℝ => (x : E)) 0 1 =
        Manifold.riemannianEDist 𝓘(ℝ, E) (x : E) (x : E)
      rw [Manifold.riemannianEDist_self]
      simp [Manifold.pathELength, mfderiv_const]
    · intro hdim'
      exact False.elim (hdim'.out hdim)
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    let γ := minJoin gExt hExt (x : E) (y : E)
    have hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ :=
      intrinsicGeodesic_contMDiff gExt hExt (x : E) (minimizingVec gExt hExt (x : E) (y : E))
    have hγ0 : γ 0 = (x : E) := minJoin_zero gExt hExt (x : E) (y : E)
    have hγ1 : γ 1 = (y : E) := minJoin_one gExt hExt (x : E) (y : E)
    have hgeo : IsGeodesic gExt γ :=
      intrinsicGeodesic_isGeodesic gExt hExt (x : E) (minimizingVec gExt hExt (x : E) (y : E))
    have hfull : Manifold.pathELength 𝓘(ℝ, E) γ 0 1 = d :=
      (minJoin_pathLen gExt hExt (x : E) (y : E)).trans (ENNReal.ofReal_toReal hfin)
    have hsum : ‖(x : E)‖ + d.toReal < B := by
      apply (ENNReal.ofReal_lt_ofReal_iff hB).mp
      rw [ENNReal.ofReal_add (norm_nonneg _) ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]
      exact hbudget
    have hsmall : Manifold.pathELength 𝓘(ℝ, E) (id ∘ γ) 0 1 <
        ENNReal.ofReal (B - ‖γ 0‖) := by
      rw [Function.id_comp, hfull, hγ0, ← ENNReal.ofReal_toReal hfin]
      apply (ENNReal.ofReal_lt_ofReal_iff (sub_pos.mpr hstart)).mpr
      linarith
    have hfence : MapsTo γ (Icc (0 : ℝ) 1) (Metric.ball (0 : E) B) :=
      curve_fenced g p U gExt hball hdom hmetric
        (contMDiffOn_iff_contDiffOn.mp (hγ.of_le (by decide)).contMDiffOn)
        (by simpa only [Function.id_comp] using hsmall)
    have hmetricPull (z : U) (hz : ‖(z : E)‖ ≤ B) (v w : E) :
        (gExt.restrictOpen U).inner z v w = gPull.inner z v w := by
      have hD : mfderiv 𝓘(ℝ, E) I (fun z : U => framedExpMap g p z) z =
          mfderiv 𝓘(ℝ, E) I (framedExpMap g p) (z : E) :=
        mfderiv_restrict_open (framedExpMap g p) U z
      have hp := localPullMetric_inner g (fun z : U => framedExpMap g p z)
        (isLocalDiffeomorph_restrict_open U hloc) z
        (show TangentSpace 𝓘(ℝ, E) z from v) (show TangentSpace 𝓘(ℝ, E) z from w)
      rw [hD] at hp
      exact (hmetric z hz v w).trans hp.symm
    have hrestricted : ∃ γU : ℝ → U,
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γU ∧
        IsGeodesicOn gPull γU (Icc (0 : ℝ) 1) ∧
        EqOn (Subtype.val ∘ γU) γ (Icc (0 : ℝ) 1) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ‖(γU t : E)‖ < B := by
      exact exists_geodesic_restriction (V := E) (γ := γ) U gPull gExt
        hγ hgeo hball hfence (fun z hz v w => hmetricPull z hz.le v w)
    obtain ⟨γU, hγU, hgeoU, hEq, hfenceU⟩ := hrestricted
    refine ⟨γU, hγU, hgeoU, ?_, ?_, hfenceU, ?_, ?_⟩
    · exact (hEq (by norm_num : (0 : ℝ) ∈ Icc 0 1)).trans hγ0
    · exact (hEq (by norm_num : (1 : ℝ) ∈ Icc 0 1)).trans hγ1
    · exact (Manifold.pathELength_congr hEq).trans hfull
    · intro hdim'
      exact hEq

private theorem restriction_pathELength_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Opens V) (gU : SmoothRiemannianMetric 𝓘(ℝ, V) U)
    (gE : SmoothRiemannianMetric 𝓘(ℝ, V) V)
    {γ : ℝ → U} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, V) 1 γ (Icc a b))
    (hmetric : ∀ t ∈ Ioo a b, ∀ v w : V,
      gE.inner (γ t : V) v w = gU.inner (γ t) v w) :
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, V) : U → Type _) :=
      ⟨gU.toRiemannianMetric⟩
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, V) : V → Type _) :=
      ⟨gE.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(ℝ, V) (Subtype.val ∘ γ) a b =
      Manifold.pathELength 𝓘(ℝ, V) γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, V) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, V) : V → Type _) :=
    ⟨gE.toRiemannianMetric⟩
  apply Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq (Subtype.val : U → V)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact ((hγ.mdifferentiableOn one_ne_zero) t (Ioo_subset_Icc_self ht)).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact Eventually.of_forall fun _ =>
      (contMDiff_subtype_val (I := 𝓘(ℝ, V)) (U := U) (n := (1 : ℕ∞ω))).mdifferentiableAt
        one_ne_zero
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    let v : TangentSpace 𝓘(ℝ, V) (γ t) := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) γ t 1
    have hnorm : ‖(show TangentSpace 𝓘(ℝ, V) (γ t : V) from v)‖ₑ = ‖v‖ₑ := by
      calc
        _ = ENNReal.ofReal (Real.sqrt (gE.inner (γ t : V) v v)) := by
          rw [← ofReal_norm, norm_eq_sqrt_real_inner]
          rfl
        _ = ENNReal.ofReal (Real.sqrt (gU.inner (γ t) v v)) :=
          congrArg ENNReal.ofReal (congrArg Real.sqrt (hmetric t ht v v))
        _ = ‖v‖ₑ := by
          rw [← ofReal_norm, norm_eq_sqrt_real_inner]
          rfl
    simpa only [mfderiv_subtype_val_apply] using! hnorm

private theorem pullback_curve_fenced
    (g : SmoothRiemannianMetric I M) (p : M) (U : Opens E)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞ (framedExpMap g p) U)
    {B : ℝ} (hball : Metric.closedBall (0 : E) B ⊆ (U : Set E))
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    {γ : ℝ → U} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc (0 : ℝ) 1))
    (hlen : let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
              (isLocalDiffeomorph_restrict_open U hloc)
            let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) :=
        ⟨gPull.toRiemannianMetric⟩
            Manifold.pathELength 𝓘(ℝ, E) γ 0 1 < ENNReal.ofReal (B - ‖(γ 0 : E)‖)) :
    MapsTo (Subtype.val ∘ γ) (Icc (0 : ℝ) 1) (Metric.ball (0 : E) B) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hEnorm : ∀ (z : M) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner z v v)) := by
    intro z v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
    (isLocalDiffeomorph_restrict_open U hloc)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) :=
    ⟨gPull.toRiemannianMetric⟩
  have hη : ContDiffOn ℝ 1 (Subtype.val ∘ γ) (Icc (0 : ℝ) 1) :=
    contMDiffOn_iff_contDiffOn.mp
      ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := (1 : ℕ∞ω))).comp_contMDiffOn hγ)
  apply Manifold.mapsTo_ball_of_pathELength_comp_lt_of_radial_bound
    g.toContinuousRiemannianMetric hEnorm (framedExpMap g p) zero_le_one hη
    (fun z hz => ((hloc.contMDiffOn z (hball hz)).contMDiffAt
      (U.isOpen.mem_nhds (hball hz))).of_le (by decide))
    (fun z hz v => (le_abs_self _).trans (framedExpMap_radial_lower_bound g p v (hdom hz)))
  have heq := localPull_pathLen g hEnorm (fun z : U => framedExpMap g p z)
    (isLocalDiffeomorph_restrict_open U hloc) hγ
  exact heq.trans_lt hlen

theorem riemannianEDistOf_eq_of_pullback_extension
    (g : SmoothRiemannianMetric I M) (p : M) (U : Opens E)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞ (framedExpMap g p) U)
    (gExt : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    {B : ℝ}
    (hball : Metric.closedBall (0 : E) B ⊆ (U : Set E))
    (hdom : MapsTo (normalFrame g p) (Metric.closedBall (0 : E) B) (expDomain g p))
    (hmetric : ∀ (z : U), ‖(z : E)‖ ≤ B → ∀ v w : E,
      gExt.inner (z : E) v w =
        g.inner (framedExpMap g p z)
          (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) (z : E) v)
          (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) (z : E) w))
    (x y : U)
    (hbudget : ENNReal.ofReal ‖(x : E)‖ + riemannianEDistOf gExt (x : E) (y : E) <
      ENNReal.ofReal B) :
    riemannianEDistOf
        (localPullMetric g (fun z : U => framedExpMap g p z)
          (isLocalDiffeomorph_restrict_open U hloc)) x y =
      riemannianEDistOf gExt (x : E) (y : E) := by
  let gPull := localPullMetric g (fun z : U => framedExpMap g p z)
    (isLocalDiffeomorph_restrict_open U hloc)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) :=
    ⟨gPull.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  have hmetricPull (z : U) (hz : ‖(z : E)‖ ≤ B) (v w : E) :
      gExt.inner (z : E) v w = gPull.inner z v w := by
    have hD : mfderiv 𝓘(ℝ, E) I (fun z : U => framedExpMap g p z) z =
        mfderiv 𝓘(ℝ, E) I (framedExpMap g p) (z : E) :=
      mfderiv_restrict_open (framedExpMap g p) U z
    have hp := localPullMetric_inner g (fun z : U => framedExpMap g p z)
      (isLocalDiffeomorph_restrict_open U hloc) z
      (show TangentSpace 𝓘(ℝ, E) z from v) (show TangentSpace 𝓘(ℝ, E) z from w)
    rw [hD] at hp
    exact (hmetric z hz v w).trans hp.symm
  let d := riemannianEDistOf gExt (x : E) (y : E)
  have hstart : ‖(x : E)‖ < B :=
    (ENNReal.ofReal_lt_ofReal_iff'.mp ((le_add_right
      (le_refl (ENNReal.ofReal ‖(x : E)‖))).trans_lt hbudget)).1
  have hB : 0 < B := (norm_nonneg _).trans_lt hstart
  have hfin : d ≠ ⊤ := ne_top_of_lt
    ((le_add_left (le_refl d)).trans_lt hbudget)
  have hsum : ‖(x : E)‖ + d.toReal < B := by
    apply (ENNReal.ofReal_lt_ofReal_iff hB).mp
    rw [ENNReal.ofReal_add (norm_nonneg _) ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hfin]
    exact hbudget
  have hdsmall : d < ENNReal.ofReal (B - ‖(x : E)‖) := by
    rw [← ENNReal.ofReal_toReal hfin]
    apply (ENNReal.ofReal_lt_ofReal_iff (sub_pos.mpr hstart)).mpr
    linarith
  change Manifold.riemannianEDist 𝓘(ℝ, E) x y =
    Manifold.riemannianEDist 𝓘(ℝ, E) (x : E) (y : E)
  apply le_antisymm
  · by_contra hnot
    classical
    have hlt : d < Manifold.riemannianEDist 𝓘(ℝ, E) x y := lt_of_not_ge hnot
    obtain ⟨L, hdL, hL⟩ := exists_between (lt_min hlt hdsmall)
    obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hdL
    have hfence : MapsTo γ (Icc (0 : ℝ) 1) (Metric.ball (0 : E) B) :=
      curve_fenced g p U gExt hball hdom hmetric (contMDiffOn_iff_contDiffOn.mp hγ)
        (by rw [hγ0]; exact hlen.trans (lt_min_iff.mp hL).2)
    let γU : ℝ → U := fun t => if ht : γ t ∈ U then ⟨γ t, ht⟩ else x
    have hEq : EqOn (Subtype.val ∘ γU) γ (Icc (0 : ℝ) 1) := by
      intro t ht
      have hm : γ t ∈ U := hball (Metric.ball_subset_closedBall (hfence ht))
      simp only [γU, Function.comp_apply, dif_pos hm]
    have hγU : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γU (Icc (0 : ℝ) 1) := by
      intro t ht
      apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1) γU (Icc (0 : ℝ) 1) t).mp
      exact (hγ t ht).congr hEq (hEq ht)
    have hγU0 : γU 0 = x := Subtype.ext ((hEq (by norm_num)).trans hγ0)
    have hγU1 : γU 1 = y := Subtype.ext ((hEq (by norm_num)).trans hγ1)
    have hlenEq : Manifold.pathELength 𝓘(ℝ, E) (Subtype.val ∘ γU) 0 1 =
        Manifold.pathELength 𝓘(ℝ, E) γU 0 1 := by
      apply restriction_pathELength_eq U gPull gExt hγU
      intro t ht
      have hm := hfence (Ioo_subset_Icc_self ht)
      rw [Metric.mem_ball, dist_zero_right, ← hEq (Ioo_subset_Icc_self ht)] at hm
      exact hmetricPull (γU t) hm.le
    have hltU : Manifold.pathELength 𝓘(ℝ, E) γU 0 1 <
        Manifold.riemannianEDist 𝓘(ℝ, E) x y := by
      rw [← hlenEq, Manifold.pathELength_congr hEq]
      exact hlen.trans (lt_min_iff.mp hL).1
    exact (not_lt_of_ge
      (Manifold.riemannianEDist_le_pathELength hγU hγU0 hγU1 zero_le_one)) hltU
  · by_contra hnot
    have hlt : Manifold.riemannianEDist 𝓘(ℝ, E) x y <
        Manifold.riemannianEDist 𝓘(ℝ, E) (x : E) (y : E) := lt_of_not_ge hnot
    obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hlt
    have hfence : MapsTo (Subtype.val ∘ γ) (Icc (0 : ℝ) 1)
        (Metric.ball (0 : E) B) :=
      pullback_curve_fenced g p U hloc hball hdom hγ
        (by rw [hγ0]; exact hlen.trans hdsmall)
    have hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (Subtype.val ∘ γ) (Icc (0 : ℝ) 1) :=
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := (1 : ℕ∞ω))).comp_contMDiffOn hγ
    have hη0 : (Subtype.val ∘ γ) 0 = (x : E) := congrArg Subtype.val hγ0
    have hη1 : (Subtype.val ∘ γ) 1 = (y : E) := congrArg Subtype.val hγ1
    have hlenEq : Manifold.pathELength 𝓘(ℝ, E) (Subtype.val ∘ γ) 0 1 =
        Manifold.pathELength 𝓘(ℝ, E) γ 0 1 := by
      apply restriction_pathELength_eq U gPull gExt hγ
      intro t ht
      have hm := hfence (Ioo_subset_Icc_self ht)
      rw [Metric.mem_ball, dist_zero_right] at hm
      exact hmetricPull (γ t) hm.le
    exact (not_lt_of_ge
      ((Manifold.riemannianEDist_le_pathELength hη hη0 hη1 zero_le_one).trans_eq hlenEq)) hlen

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
