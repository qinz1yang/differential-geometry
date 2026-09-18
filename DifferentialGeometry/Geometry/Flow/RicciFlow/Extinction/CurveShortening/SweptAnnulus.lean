import DifferentialGeometry.Geometry.Metric.CompactConvexSourceLipschitz
import DifferentialGeometry.Topology.LoopSpace.Lipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SweptAreaEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SlopeEstimateReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SpanningArea
import DifferentialGeometry.Analysis.Integration.Integral.ComplexSquare

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
theorem CurveMap.continuous_sweptAnnulus (c : CurveMap M) {a b s t : ℝ}
    (hc : c.SmoothOn (I := I) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) :
    Continuous (fun p : Width.Annulus => c p.2 (s + (t - s) * (p.1 : ℝ))) := by
  have hmem (r : Icc (0 : ℝ) 1) : s + (t - s) * (r : ℝ) ∈ Icc a b := by
    constructor
    · nlinarith [r.property.1, hs.1, ht.1]
    · nlinarith [r.property.2, ht.1, ht.2]
  have hreindex : Continuous (fun p : Icc (0 : ℝ) 1 × ℝ =>
      (p.2, s + (t - s) * (p.1 : ℝ))) := by fun_prop
  have hval : Continuous (fun p : Icc (0 : ℝ) 1 × ℝ =>
      c.lift p.2 (s + (t - s) * (p.1 : ℝ))) :=
    hc.continuousOn.comp_continuous hreindex
      (fun p => ⟨mem_univ _, hmem p.1⟩)
  exact (IsOpenQuotientMap.id.prodMap
    QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff.mp hval

theorem CurveMap.isLipschitz_sweptAnnulus (c : CurveMap M)
    (g : SmoothRiemannianMetric I M) {a b s t : ℝ}
    (hc : c.SmoothOn (I := I) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) :
    ∃ C : ℝ≥0, ∀ p q : Width.Annulus,
      riemannianEDistOf g (c p.2 (s + (t - s) * (p.1 : ℝ)))
        (c q.2 (s + (t - s) * (q.1 : ℝ))) ≤ (C : ℝ≥0∞) * edist p q := by
  let f : ℝ × ℝ → M := fun p => c.lift p.2 (s + (t - s) * p.1)
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.2, s + (t - s) * p.1))
      (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) (univ ×ˢ Icc a b) := by
    intro p hp
    refine ⟨mem_univ _, ?_, ?_⟩
    · nlinarith [hp.1.1, hs.1, ht.1]
    · nlinarith [hp.1.2, ht.1, ht.2]
  have hreindex : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.2, s + (t - s) * p.1)) := by
    fun_prop
  have hreindexM : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p : ℝ × ℝ => (p.2, s + (t - s) * p.1)) (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :=
    hreindex.contMDiff.contMDiffOn
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 f (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :=
    (hc.comp hreindexM hmap).of_le (by simp)
  have huniq : UniqueMDiffOn 𝓘(ℝ, ℝ × ℝ) (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    rw [uniqueMDiffOn_iff_uniqueDiffOn]
    exact (uniqueDiffOn_Icc zero_lt_one).prod uniqueDiffOn_univ
  obtain ⟨C, hC⟩ := Geometry.exists_compact_convex_source_riemannian_lipschitz g hf huniq
    (isCompact_Icc.prod isCompact_Icc)
    ((convex_Icc (0 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 2))
    (Set.prod_mono Subset.rfl (subset_univ (Icc (-1 : ℝ) 2)))
  refine ⟨C, fun p q => ?_⟩
  obtain ⟨x, d, hx0, hx1, hd0, hd1, hxp, hxdq, hdist⟩ :=
    DifferentialGeometry.Topology.exists_short_circle_lifts q.2 p.2
  have hx : x ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hxd : x + d ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hed : edist x (x + d) = edist p.2 q.2 := by
    rw [edist_dist, edist_dist, Real.dist_eq, show x - (x + d) = -d by ring,
      abs_neg, dist_comm p.2 q.2, hdist]
  have hpq : edist ((p.1 : ℝ), x) ((q.1 : ℝ), x + d) = edist p q := by
    rw [Prod.edist_eq, Prod.edist_eq, hed]
    rfl
  have hbound := hC ((p.1 : ℝ), x) ⟨p.1.property, hx⟩
    ((q.1 : ℝ), x + d) ⟨q.1.property, hxd⟩
  simpa only [f, lift, hxp, hxdq, hpq] using hbound

noncomputable def CurveMap.sweptAnnulus (c : CurveMap M)
    (g : SmoothRiemannianMetric I M) {a b s t : ℝ}
    (hc : c.SmoothOn (I := I) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) : Width.LipschitzAnnulus g where
  map := ⟨fun p => c p.2 (s + (t - s) * (p.1 : ℝ)), c.continuous_sweptAnnulus hc hs ht⟩
  isLipschitz := c.isLipschitz_sweptAnnulus g hc hs ht

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CurveMap.riemannianAreaDensity_sweptAnnulus_le (c : CurveMap M)
    (g : SmoothRiemannianMetric I M) {a b s t : ℝ}
    (hc : c.SmoothOn (I := I) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) (hst : s < t)
    (z : ℂ) (hz : z.re ∈ Ioo (0 : ℝ) 1) :
    Geometry.riemannianAreaDensity g
        (fun w : ℂ => c.lift w.im (s + (t - s) * w.re)) z ≤
      (t - s) * Real.sqrt (c.normSq (fun _ => g) (c.velocity (I := I) (Icc a b))
        z.im (s + (t - s) * z.re)) *
          c.speed (fun _ => g) z.im (s + (t - s) * z.re) := by
  let tau := s + (t - s) * z.re
  let F : ℝ × ℝ → M := fun p => c.lift p.1 p.2
  let P : ℂ → ℝ × ℝ := fun w => (w.im, s + (t - s) * w.re)
  have htau : tau ∈ Ioo a b := by
    dsimp only [tau]
    constructor
    · nlinarith [hs.1, hz.1]
    · nlinarith [ht.2, hz.2]
  have hnhds : (univ : Set ℝ) ×ˢ Icc a b ∈ 𝓝 (z.im, tau) :=
    prod_mem_nhds (Filter.univ_mem) (Icc_mem_nhds htau.1 htau.2)
  have hF : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I F (z.im, tau) :=
    ((hc (z.im, tau) ⟨mem_univ _, Ioo_subset_Icc_self htau⟩).contMDiffAt hnhds).mdifferentiableAt (by simp)
  have hP : HasFDerivAt P (Complex.imCLM.prod ((t - s) • Complex.reCLM)) z := by
    simpa only [P, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] using!
      Complex.imCLM.hasFDerivAt.prodMk
        (((Complex.reCLM.hasFDerivAt).const_mul (t - s)).const_add s)
  have hchain : mfderiv 𝓘(ℝ, ℂ) I (F ∘ P) z =
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I F (z.im, tau)).comp
        (Complex.imCLM.prod ((t - s) • Complex.reCLM)) := by
    rw [mfderiv_comp z hF hP.differentiableAt.mdifferentiableAt,
      mfderiv_eq_fderiv, hP.fderiv]
    rfl
  have htime : mfderiv 𝓘(ℝ, ℝ × ℝ) I F (z.im, tau) (0, 1) =
      c.velocity (I := I) (Icc a b) z.im tau := by
    have hin : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun u : ℝ => (z.im, u)) tau := by
      exact (differentiableAt_const z.im).prodMk differentiableAt_id |>.mdifferentiableAt
    have heq := mfderiv_comp_apply tau hF hin (1 : ℝ)
    rw [mfderiv_eq_fderiv, (hasFDerivAt_prodMk_right z.im tau).fderiv] at heq
    rw [CurveMap.velocity, mfderivWithin_of_mem_nhds (Icc_mem_nhds htau.1 htau.2)]
    exact heq.symm
  have hspace : mfderiv 𝓘(ℝ, ℝ × ℝ) I F (z.im, tau) (1, 0) =
      c.X (I := I) z.im tau := by
    have hin : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun u : ℝ => (u, tau)) z.im := by
      exact differentiableAt_id.prodMk (differentiableAt_const tau) |>.mdifferentiableAt
    have heq := mfderiv_comp_apply z.im hF hin (1 : ℝ)
    rw [mfderiv_eq_fderiv, (hasFDerivAt_prodMk_left z.im tau).fderiv] at heq
    exact heq.symm
  have hre : mfderiv 𝓘(ℝ, ℂ) I (F ∘ P) z (1 : ℂ) =
      (t - s) • c.velocity (I := I) (Icc a b) z.im tau := by
    rw [hchain]
    change mfderiv 𝓘(ℝ, ℝ × ℝ) I F (z.im, tau) (0, (t - s) * 1) = _
    rw [mul_one]
    let Df : ℝ × ℝ →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) I F (z.im, tau)
    change Df (0, t - s) = _
    rw [show ((0, t - s) : ℝ × ℝ) = (t - s) • ((0, 1) : ℝ × ℝ) by simp,
      map_smul]
    exact congrArg (fun v : E => (t - s) • v) htime
  have him : mfderiv 𝓘(ℝ, ℂ) I (F ∘ P) z Complex.I = c.X (I := I) z.im tau := by
    rw [hchain]
    change mfderiv 𝓘(ℝ, ℝ × ℝ) I F (z.im, tau) (1, (t - s) * 0) = _
    rw [mul_zero]
    exact hspace
  have hle := Geometry.riemannianAreaDensity_le_mfderiv_speeds g (F ∘ P) z
  rw [hre, him] at hle
  have hscale : Real.sqrt (g.inner (c.lift z.im tau)
      ((t - s) • c.velocity (I := I) (Icc a b) z.im tau)
      ((t - s) • c.velocity (I := I) (Icc a b) z.im tau)) =
      (t - s) * Real.sqrt (g.inner (c.lift z.im tau)
        (c.velocity (I := I) (Icc a b) z.im tau)
        (c.velocity (I := I) (Icc a b) z.im tau)) := by
    have hmul : g.inner (c.lift z.im tau)
        ((t - s) • c.velocity (I := I) (Icc a b) z.im tau)
        ((t - s) • c.velocity (I := I) (Icc a b) z.im tau) =
        (t - s) ^ 2 * g.inner (c.lift z.im tau)
          (c.velocity (I := I) (Icc a b) z.im tau)
          (c.velocity (I := I) (Icc a b) z.im tau) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [hmul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_pos (sub_pos.mpr hst)]
  exact hle.trans_eq (congrArg
    (fun x => x * c.speed (fun _ => g) z.im tau) hscale)

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CurveMap.annulusArea_sweptAnnulus_self (c : CurveMap M)
    (g : SmoothRiemannianMetric I M) {a b s : ℝ}
    (hc : c.SmoothOn (I := I) (Icc a b)) (hs : s ∈ Icc a b) :
    Width.annulusArea g (c.sweptAnnulus g hc hs ⟨le_rfl, hs.2⟩).map = 0 := by
  let A := c.sweptAnnulus g hc hs ⟨le_rfl, hs.2⟩
  let U : ℂ → M := fun z => c.lift z.im s
  have hconv : Convex ℝ Width.annulusRectangle :=
    ((convex_Icc (0 : ℝ) 1).linear_preimage Complex.reLm).inter
      ((convex_Icc (0 : ℝ) 1).linear_preimage Complex.imLm)
  have hext : EqOn (Width.annulusExtension A.map) U Width.annulusRectangle := by
    intro z hz
    rw [Width.annulusExtension_agrees _ hz]
    simp [A, CurveMap.sweptAnnulus, U, CurveMap.lift]
  have hzero (z : ℂ) : Geometry.riemannianAreaDensity g U z = 0 := by
    let f : ℝ → M := fun x => c.lift x s
    let phase : ℂ → ℝ := Complex.im
    have hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f (phase z) :=
      (c.smooth_slice hc hs).mdifferentiableAt (by simp)
    have hp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) phase z :=
      Complex.imCLM.mdifferentiableAt
    have hcomp : U = f ∘ phase := by rfl
    have hd := mfderiv_comp z hf hp
    let A : ℝ →L[ℝ] TangentSpace I (f (phase z)) := mfderiv 𝓘(ℝ, ℝ) I f (phase z)
    let B : ℂ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) phase z
    have hcol (w : ℂ) :
        mfderiv 𝓘(ℝ, ℂ) I (f ∘ phase) z w = B w • A 1 := by
      have he := congrArg (fun L : ℂ →L[ℝ] TangentSpace I (f (phase z)) => L w) hd
      change mfderiv 𝓘(ℝ, ℂ) I (f ∘ phase) z w = A (B w) at he
      calc
        _ = A (B w) := he
        _ = A (B w • (1 : ℝ)) := congrArg A (by simp)
        _ = B w • A 1 := A.map_smul _ _
    rw [hcomp]
    unfold Geometry.riemannianAreaDensity Geometry.tangentTwoJacobian
    rw [hcol, hcol]
    simp only [map_smul, smul_apply, smul_eq_mul]
    apply Real.sqrt_eq_zero_of_nonpos
    exact le_of_eq (by ring)
  unfold Width.annulusArea
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (show MeasurableSet Width.annulusRectangle by
      unfold Width.annulusRectangle; measurability),
    Width.parametricJacobian_ae_eq_riemannianAreaDensity_of_convex g U hconv]
    with z hz hzdensity
  exact ((Width.parametricJacobian_congr_on g hext hz).trans hzdensity).trans (hzero z)

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

omit [CompactSpace M] [I.Boundaryless] in
theorem CurveMap.riemannianAreaDensity_sweptAnnulus_metric_le
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M) {s t : ℝ} (hc : c.SmoothOn (I := I) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) (hst : s < t)
    (z : ℂ) (hz : z.re ∈ Ioo (0 : ℝ) 1) :
    Geometry.riemannianAreaDensity (B.family.metric t)
        (fun w : ℂ => c.lift w.im (s + (t - s) * w.re)) z ≤
      (Real.exp (2 * B.B₀ * (t - s)) * (t - s)) *
        (Real.sqrt (c.normSq B.family.metric (c.velocity (I := I) (Icc a b))
          z.im (s + (t - s) * z.re)) *
            c.speed B.family.metric z.im (s + (t - s) * z.re)) := by
  let tau := s + (t - s) * z.re
  have htau : tau ∈ Icc s t := by
    dsimp only [tau]
    constructor <;> nlinarith [hz.1, hz.2]
  have htauab : tau ∈ Icc a b := ⟨hs.1.trans htau.1, htau.2.trans ht.2⟩
  have hmetric (p : M) (v : TangentSpace I p) :
      (B.family.metric t).inner p v v ≤
        Real.exp (2 * B.B₀ * (t - s)) * (B.family.metric tau).inner p v v := by
    have h := B.inner_le_exp_mul_inner ⟨hs.1.trans ht.1, ht.2⟩ htauab p v
    rw [abs_of_nonneg (sub_nonneg.mpr htau.2)] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (sub_le_sub_left htau.1 t) (mul_nonneg (by norm_num) B.B₀_nonneg)))
      (DifferentialGeometry.metric_inner_self_nonneg _ _ _))
  have hmetricArea := Geometry.riemannianAreaDensity_metric_upper
    (B.family.metric tau) (B.family.metric t) (Real.exp_pos (2 * B.B₀ * (t - s)))
    hmetric (fun w : ℂ => c.lift w.im (s + (t - s) * w.re)) z
  have hpoint := c.riemannianAreaDensity_sweptAnnulus_le (B.family.metric tau) hc hs ht hst z hz
  have hle := hmetricArea.trans (mul_le_mul_of_nonneg_left hpoint (Real.exp_pos _).le)
  simpa only [CurveMap.normSq, CurveMap.speed, tau, mul_assoc] using hle

private theorem CurveMap.annulusArea_sweptAnnulus_le_of_lt
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M) {s t : ℝ} (hc : c.SmoothOn (I := I) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) (hst : s < t) :
    Width.annulusArea (B.family.metric t) (c.sweptAnnulus (B.family.metric t) hc hs ht).map ≤
      Real.exp (2 * B.B₀ * (t - s)) *
        ∫ v in s..t, c.sweptDensity B.family.metric (Icc a b) v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let A := c.sweptAnnulus (B.family.metric t) hc hs ht
  let U : ℂ → M := fun z => c.lift z.im (s + (t - s) * z.re)
  let f := Geometry.riemannianAreaDensity (B.family.metric t) U
  let tau : ℝ → ℝ := fun v => s + (t - s) * v
  let C : ℝ := Real.exp (2 * B.B₀ * (t - s))
  let q : ℝ × ℝ → ℝ := fun p =>
    Real.sqrt (c.normSq B.family.metric (c.velocity (I := I) (Icc a b)) p.1 p.2) *
      c.speed B.family.metric p.1 p.2
  have hq : ContinuousOn q (univ ×ˢ Icc a b) := c.continuousOn_sweptIntegrand B hc
  have htaumem (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : tau v ∈ Icc a b := by
    dsimp only [tau]
    constructor
    · nlinarith [hv.1, hs.1]
    · nlinarith [hv.2, ht.2]
  have hconv : Convex ℝ Width.annulusRectangle :=
    ((convex_Icc (0 : ℝ) 1).linear_preimage Complex.reLm).inter
      ((convex_Icc (0 : ℝ) 1).linear_preimage Complex.imLm)
  have hext : EqOn (Width.annulusExtension A.map) U Width.annulusRectangle := by
    intro z hz
    rw [Width.annulusExtension_agrees _ hz]
    rfl
  have hjac : Width.parametricJacobian (B.family.metric t)
      (Width.annulusExtension A.map) Width.annulusRectangle =ᵐ[volume.restrict Width.annulusRectangle]
        f := by
    filter_upwards [ae_restrict_mem (show MeasurableSet Width.annulusRectangle by
        unfold Width.annulusRectangle; measurability),
      Width.parametricJacobian_ae_eq_riemannianAreaDensity_of_convex
        (B.family.metric t) U hconv] with z hz hzdensity
    exact (Width.parametricJacobian_congr_on (B.family.metric t) hext hz).trans hzdensity
  have hf : IntegrableOn f Analysis.unitSquare := A.integrable_jacobian.congr hjac
  have harea : Width.annulusArea (B.family.metric t) A.map =
      ∫ z in Analysis.unitSquare, f z := integral_congr_ae hjac
  have hprod : Integrable (fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact Analysis.integrable_unitSquare_coordinates hf
  have hS : ContinuousOn (fun v => c.sweptDensity B.family.metric (Icc a b) v) (Icc a b) :=
    continuousOn_intervalIntegral_of_continuousOn_rectangle B.lt.le
      (hq.mono (Set.prod_mono (subset_univ _) Subset.rfl))
  have hR : ContinuousOn (fun v => (C * (t - s)) *
      c.sweptDensity B.family.metric (Icc a b) (tau v)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul (hS.comp (by fun_prop) htaumem)
  have htime : ∀ᵐ v ∂volume.restrict (Icc (0 : ℝ) 1), v ∈ Ioo (0 : ℝ) 1 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hbound : ∀ᵐ v ∂volume.restrict (Icc (0 : ℝ) 1),
      (∫ theta in Icc (0 : ℝ) 1, f (Complex.measurableEquivRealProd.symm (v, theta))) ≤
        (C * (t - s)) * c.sweptDensity B.family.metric (Icc a b) (tau v) := by
    filter_upwards [htime, hprod.prod_right_ae] with v hv hvint
    have hslice : ContinuousOn (fun theta => q (theta, tau v)) (Icc (0 : ℝ) 1) :=
      hq.comp (by fun_prop) (fun theta _ => ⟨mem_univ _, htaumem v (Ioo_subset_Icc_self hv)⟩)
    have hpoint : ∀ theta : ℝ,
        f (Complex.measurableEquivRealProd.symm (v, theta)) ≤ (C * (t - s)) * q (theta, tau v) :=
      fun theta => c.riemannianAreaDensity_sweptAnnulus_metric_le B hc hs ht hst
        (Complex.measurableEquivRealProd.symm (v, theta)) hv
    calc
      _ ≤ ∫ theta in Icc (0 : ℝ) 1, (C * (t - s)) * q (theta, tau v) :=
        integral_mono_ae hvint (hslice.const_mul _).integrableOn_Icc
          (ae_of_all _ hpoint)
      _ = (C * (t - s)) * c.sweptDensity B.family.metric (Icc a b) (tau v) := by
        rw [integral_const_mul]
        congr 1
        rw [CurveMap.sweptDensity, intervalIntegral.integral_of_le zero_le_one,
          integral_Icc_eq_integral_Ioc]
  rw [harea, Analysis.integral_unitSquare_eq_iterated hf]
  calc
    _ ≤ ∫ v in Icc (0 : ℝ) 1,
        (C * (t - s)) * c.sweptDensity B.family.metric (Icc a b) (tau v) :=
      integral_mono_ae hprod.integral_prod_left hR.integrableOn_Icc hbound
    _ = C * ∫ v in s..t, c.sweptDensity B.family.metric (Icc a b) v := by
      rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one, mul_assoc]
      congr 1
      have h := intervalIntegral.smul_integral_comp_add_mul
        (c.sweptDensity B.family.metric (Icc a b)) (a := (0 : ℝ)) (b := 1) (t - s) s
      simp only [smul_eq_mul, mul_zero, add_zero, mul_one] at h
      rw [show s + (t - s) = t by ring] at h
      exact h

theorem CurveMap.annulusArea_sweptAnnulus_le
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M) {s t : ℝ} (hc : c.SmoothOn (I := I) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) :
    Width.annulusArea (B.family.metric t) (c.sweptAnnulus (B.family.metric t) hc hs ht).map ≤
      Real.exp (2 * B.B₀ * (t - s)) *
        ∫ v in s..t, c.sweptDensity B.family.metric (Icc a b) v := by
  rcases ht.1.eq_or_lt with hst | hst
  · subst t
    rw [c.annulusArea_sweptAnnulus_self (B.family.metric s) hc hs,
      intervalIntegral.integral_same, mul_zero]
  · exact c.annulusArea_sweptAnnulus_le_of_lt B hc hs ht hst

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
theorem loopFamily_homotopic_of_smoothOn
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop M) {a b s t : ℝ}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) : (γ s).Homotopic (γ t) := by
  refine ⟨{
    toFun := fun p => γ (s + (t - s) * (p.1 : ℝ)) p.2
    continuous_toFun := (curveOfLoopFamily γ).continuous_sweptAnnulus hγ hs ht
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro θ
    simp
  · intro θ
    simp

theorem loopFamilyLeastArea_eq_zero_of_not_isContractibleLoop
    (g : ℝ → SmoothRiemannianMetric I M) (γ : ℝ → Surgery.Topology.ContinuousFreeLoop M)
    (t : ℝ) (hγ : ¬ Surgery.Topology.IsContractibleLoop (γ t)) :
    loopFamilyLeastArea g γ t = 0 := by
  rw [loopFamilyLeastArea, Width.competitorAreas_eq_empty_of_not_isContractibleLoop _ _ hγ,
    Real.sInf_empty]

variable [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    [I.Boundaryless] {D : RealTimeInterval} {a b : ℝ}

theorem loopFamilyLeastArea_le_add_annulusArea
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop M) {s t : ℝ}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) :
    loopFamilyLeastArea (fun _ => g) γ t ≤ loopFamilyLeastArea (fun _ => g) γ s +
      Width.annulusArea g ((curveOfLoopFamily γ).sweptAnnulus g hγ hs ht).map := by
  by_cases hctr : Surgery.Topology.IsContractibleLoop (γ s)
  · have htt : t ∈ Icc a b := ⟨hs.1.trans ht.1, ht.2⟩
    have hctr' : Surgery.Topology.IsContractibleLoop (γ t) := by
      obtain ⟨q, hq⟩ := hctr
      exact ⟨q, (loopFamily_homotopic_of_smoothOn γ hγ hs ht).symm.trans hq⟩
    let A := (curveOfLoopFamily γ).sweptAnnulus g hγ hs ht
    refine Width.leastArea_le_add_of_disk_attachment g (γ s) (γ t) hctr hctr'
      ((regularLoopSlice γ hγ s hs).isLipschitz g)
      ((regularLoopSlice γ hγ t htt).isLipschitz g) A ?_
    intro u
    refine Width.disk_annulus_gluing g (γ s) (γ t) u A ?_ ?_
    · intro θ
      simp [A, CurveMap.sweptAnnulus, curveOfLoopFamily]
    · intro θ
      simp [A, CurveMap.sweptAnnulus, curveOfLoopFamily]
  · have hctr' : ¬ Surgery.Topology.IsContractibleLoop (γ t) := by
      rintro ⟨q, hq⟩
      exact hctr ⟨q, (loopFamily_homotopic_of_smoothOn γ hγ hs ht).trans hq⟩
    rw [loopFamilyLeastArea_eq_zero_of_not_isContractibleLoop _ γ s hctr,
      loopFamilyLeastArea_eq_zero_of_not_isContractibleLoop _ γ t hctr', zero_add]
    exact Width.annulusArea_nonneg g _

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

theorem loopFamilyLeastArea_le_exp_mul_add_integral_sweptDensity
    (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → Surgery.Topology.ContinuousFreeLoop M) {s t : ℝ}
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) :
    loopFamilyLeastArea B.family.metric γ t ≤ Real.exp (2 * B.B₀ * (t - s)) *
      (loopFamilyLeastArea B.family.metric γ s +
        ∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have htt : t ∈ Icc a b := ⟨hs.1.trans ht.1, ht.2⟩
  have hmetric : loopFamilyLeastArea (fun _ => B.family.metric t) γ s ≤
      Real.exp (2 * B.B₀ * (t - s)) * loopFamilyLeastArea B.family.metric γ s := by
    by_cases hctr : Surgery.Topology.IsContractibleLoop (γ s)
    · exact B.leastArea_le_exp_mul_leastArea_of_le hs htt ht.1 (γ s) hctr
        ((regularLoopSlice γ hγ s hs).isLipschitz (B.family.metric s))
        ((regularLoopSlice γ hγ s hs).isLipschitz (B.family.metric t))
    · rw [loopFamilyLeastArea_eq_zero_of_not_isContractibleLoop _ γ s hctr,
        loopFamilyLeastArea_eq_zero_of_not_isContractibleLoop _ γ s hctr, mul_zero]
  have hattach := loopFamilyLeastArea_le_add_annulusArea (B.family.metric t) γ hγ hs ht
  have harea := (curveOfLoopFamily γ).annulusArea_sweptAnnulus_le B hγ hs ht
  calc
    loopFamilyLeastArea B.family.metric γ t ≤
        loopFamilyLeastArea (fun _ => B.family.metric t) γ s +
          Width.annulusArea (B.family.metric t)
            ((curveOfLoopFamily γ).sweptAnnulus (B.family.metric t) hγ hs ht).map := hattach
    _ ≤ Real.exp (2 * B.B₀ * (t - s)) * loopFamilyLeastArea B.family.metric γ s +
        Real.exp (2 * B.B₀ * (t - s)) *
          ∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v :=
      add_le_add hmetric harea
    _ = _ := (mul_add _ _ _).symm

theorem RicciBackground.curveShorteningLeastAreaIntegratedBound
    (B : RicciBackground (I := I) (M := M) D a b) :
    curveShorteningLeastAreaIntegratedBound B := by
  intro γ hγ _ s hs t ht
  exact loopFamilyLeastArea_le_exp_mul_add_integral_sweptDensity B γ hγ hs ht

theorem RicciBackground.curveShorteningLeastAreaSlope
    (B : RicciBackground (I := I) (M := M) D a b) :
    curveShorteningLeastAreaSlope B := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact curveShorteningLeastAreaSlope_of_integratedBound B B.curveShorteningLeastAreaIntegratedBound

end

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
