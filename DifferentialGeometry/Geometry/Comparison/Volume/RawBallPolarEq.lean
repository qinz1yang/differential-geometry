import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Basic
import DifferentialGeometry.Geometry.Exponential.Radial
import DifferentialGeometry.Geometry.Exponential.CompactBall
import DifferentialGeometry.Geometry.Exponential.VolumeDensity
import DifferentialGeometry.Geometry.Geodesic.Flow.VelocityLift
import DifferentialGeometry.Analysis.Integration.Measure.Chart.HaarBasis
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import DifferentialGeometry.Analysis.Integration.Measure.Polar.Evaluation
import DifferentialGeometry.Analysis.Integration.Measure.Polar.NullSets
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Area
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Basic
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Density
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Basic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.RadialSurjectivity
import DifferentialGeometry.Geometry.Geodesic.Maximal.Rescaling
import DifferentialGeometry.Geometry.Geodesic.Equation.ProjectionDerivative

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold MeasureTheory Set
open Filter
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private theorem rawSegInt_geo
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : v ∈ extendibleMinimizingDomain (I := I) g p) :
    ∃ (c : ℝ) (γ : ℝ → M) (J : Set ℝ), 1 < c ∧
      c • v ∈ minimizingDomain (I := I) g p ∧ IsOpen J ∧ IsPreconnected J ∧
      Icc (0 : ℝ) c ⊆ J ∧
      Geodesic.IsGeodesicOnWithInitial (I := I) g γ J p
        (show TangentSpace I p from v) ∧
      (∀ t ∈ Icc (0 : ℝ) c, γ =ᶠ[𝓝 t]
        (fun s => expMap (I := I) g p
          (show TangentSpace I p from s • v))) ∧
      γ 1 = expMap (I := I) g p
        (show TangentSpace I p from v) ∧
      γ c = expMap (I := I) g p
        (show TangentSpace I p from c • v) := by
  rcases hv with ⟨c, hc, hcraw⟩
  have hcpos : 0 < c := one_pos.trans hc
  have hcdom : (show TangentSpace I p from c • v) ∈ expDomain (I := I) g p :=
    minimizingDomain_subset_expDomain (I := I) g p hcraw
  obtain ⟨γ, J, hJopen, hJconn, hsegment, hγ, hγeq⟩ :=
    Exponential.exists_isGeodesicOnWithInitial_eqOn_expMap
      (v := show TangentSpace I p from v) hcdom
  have hIcc : Icc (0 : ℝ) c ⊆ J := by
    simpa only [uIcc_of_le hcpos.le] using hsegment
  have hγgerm : ∀ t ∈ Icc (0 : ℝ) c, γ =ᶠ[𝓝 t]
      (fun s => expMap (I := I) g p
        (show TangentSpace I p from s • v)) :=
    fun t ht => Filter.eventuallyEq_of_mem
      (hJopen.mem_nhds (hIcc ht)) (fun _ hs => hγeq hs)
  have hγone : γ 1 = expMap (I := I) g p (show TangentSpace I p from v) := by
    have h := hγeq (hIcc ⟨zero_le_one, hc.le⟩)
    change γ 1 = expMap (I := I) g p
      (show TangentSpace I p from (1 : ℝ) • v) at h
    simpa only [one_smul] using h
  have hγc : γ c = expMap (I := I) g p (show TangentSpace I p from c • v) :=
    hγeq (hIcc ⟨hcpos.le, le_rfl⟩)
  exact ⟨c, γ, J, hc, hcraw, hJopen, hJconn, hIcc, hγ, hγgerm, hγone, hγc⟩

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private theorem rawSegInt_ext
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : v ∈ extendibleMinimizingDomain (I := I) g p) :
    ∃ (c : ℝ) (γ : ℝ → M), 1 < c ∧ c • v ∈ minimizingDomain (I := I) g p ∧
      ContMDiff 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) γ ∧
      Geodesic.IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) c) ∧
      ∀ t ∈ Icc (0 : ℝ) c, γ =ᶠ[𝓝 t]
        (fun s => expMap (I := I) g p
          (show TangentSpace I p from s • v)) := by
  obtain ⟨c, γ, J, hc, hcraw, hJopen, _hJconn, hIcc, hγ, hγraw, _hγone,
    _hγc⟩ := rawSegInt_geo (I := I) g p hv
  have hcpos : 0 < c := one_pos.trans hc
  have hcdom : (show TangentSpace I p from c • v) ∈ expDomain (I := I) g p :=
    minimizingDomain_subset_expDomain (I := I) g p hcraw
  obtain ⟨γg, hγgsmooth, hγgerm⟩ :=
    exists_contMDiff_extension_expMap_smul (I := I) g p v hcdom
  rw [uIcc_of_le hcpos.le] at hγgerm
  have hγeq : ∀ t ∈ Icc (0 : ℝ) c, γg =ᶠ[𝓝 t] γ := by
    intro t ht
    exact (hγgerm t ht).trans (hγraw t ht).symm
  have hγgeo : Geodesic.IsGeodesicOn (I := I) g γ J := by
    intro t ht
    exact (hγ.isGeodesicAt (hJopen.mem_nhds ht)).hasGeodesicEquationAt g
  have hγggeo : Geodesic.IsGeodesicOn (I := I) g γg (Icc (0 : ℝ) c) := by
    intro t ht
    have heq := hγeq t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
      heq.eq_of_nhds heq (hγgeo t (hIcc ht))
  exact ⟨c, γg, hc, hcraw, hγgsmooth, hγggeo, hγgerm⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private theorem mfderiv_shift
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (T a : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (s + T)) a (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I γ (a + T) (1 : ℝ) : E) := by
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + T)
      a (ContinuousLinearMap.id ℝ ℝ) := by
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    exact (hasFDerivAt_id a).add_const T
  have hγat : HasMFDerivAt 𝓘(ℝ, ℝ) I γ (a + T)
      (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)) :=
    (hγ.contMDiffAt.mdifferentiableAt (by norm_num)).hasMFDerivAt
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I (γ ∘ (fun s : ℝ => s + T)) a =
      (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)).comp (ContinuousLinearMap.id ℝ ℝ) :=
    (hγat.comp a hshift).mfderiv
  change (mfderiv 𝓘(ℝ, ℝ) I (γ ∘ (fun s : ℝ => s + T)) a (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I γ (a + T) (1 : ℝ) : E)
  rw [hcomp]
  change (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)) ((ContinuousLinearMap.id ℝ ℝ) (1 : ℝ)) =
      (mfderiv 𝓘(ℝ, ℝ) I γ (a + T)) (1 : ℝ)
  simp

omit [NeZero (Module.finrank ℝ E)] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private theorem geo_init_vel
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {J : Set ℝ}
    {p : M} {v : TangentSpace I p} (hJ : IsOpen J) (h0J : (0 : ℝ) ∈ J)
    (hγ : Geodesic.IsGeodesicOnWithInitial (I := I) g γ J p v) :
    (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (v : E) := by
  obtain ⟨f, hproj, hf0, hf⟩ := hγ
  have hfat : IsMIntegralCurveAt f (Geodesic.geodesicVectorField (I := I) g) 0 :=
    hf.isMIntegralCurveAt (hJ.mem_nhds h0J)
  have hprojcont : ContinuousAt (fun t => (f t).proj) 0 :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hfat.continuousAt
  have hsrc0 : (f 0).proj ∈ (chartAt H p).source := by
    rw [hf0]
    exact mem_chart_source H p
  have hsrc : (fun t => (f t).proj) ⁻¹' (chartAt H p).source ∈ 𝓝 (0 : ℝ) :=
    hprojcont.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc0)
  have hfchart : IsMIntegralCurveAt f
      (Geodesic.geodesicVectorFieldChart (I := I) g p) 0 := by
    rw [isMIntegralCurveAt_iff]
    refine ⟨J ∩ (fun t => (f t).proj) ⁻¹' (chartAt H p).source,
      Filter.inter_mem (hJ.mem_nhds h0J) hsrc, ?_⟩
    apply (Geodesic.isMIntegralCurveOn_geodesicVectorFieldChart_iff
      (I := I) g p (fun _ ht => ht.2)).mpr
    exact hf.mono inter_subset_left
  have hvel := Geodesic.IsMIntegralCurveAt.mfderiv_proj_one (I := I) hfchart hsrc0
  have hfun : (fun t => (f t).proj) = γ := funext hproj
  rw [hfun, hf0] at hvel
  exact hvel

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private theorem rawExp_inj_seg
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    Set.InjOn (fun v : E => expMap (I := I) g p
      (show TangentSpace I p from v)) (extendibleMinimizingDomain (I := I) g p) := by
  intro v hv w hw heq
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hvraw : v ∈ minimizingDomain (I := I) g p := extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hv
  have hwraw : w ∈ minimizingDomain (I := I) g p := extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hw
  have hlen := sqrt_inner_self_eq_of_mem_minimizingDomain_of_expMap_eq (I := I) g p hvraw hwraw heq
  by_cases hv0 : v = 0
  · subst v
    have hw0 : w = 0 := by
      have hzero : Real.sqrt
          (g.inner p (show TangentSpace I p from w)
            (show TangentSpace I p from w)) = 0 := by
        rw [← hlen]
        change Real.sqrt (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) = 0
        simp
      by_contra hw0
      exact (Real.sqrt_pos.mpr (g.pos p w hw0)).ne' hzero
    subst w
    rfl
  let L : ℝ := Real.sqrt (g.inner p (show TangentSpace I p from v)
    (show TangentSpace I p from v))
  have hLpos : 0 < L := Real.sqrt_pos.mpr (g.pos p v hv0)
  have hLne : L ≠ 0 := hLpos.ne'
  have hvinner : g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v) = L ^ 2 := by
    have hsq := Real.sq_sqrt (gInner_self_nonneg (I := I) g p v)
    simpa only [L] using hsq.symm
  have hwinner : g.inner p (show TangentSpace I p from w)
      (show TangentSpace I p from w) = L ^ 2 := by
    have hsq := Real.sq_sqrt (gInner_self_nonneg (I := I) g p w)
    rw [← hlen] at hsq
    exact hsq.symm
  let u : E := L⁻¹ • v
  let z : E := L⁻¹ • w
  have huunit : g.inner p (show TangentSpace I p from u)
      (show TangentSpace I p from u) = 1 := by
    dsimp only [u]
    change g.inner p (L⁻¹ • (show TangentSpace I p from v))
      (L⁻¹ • (show TangentSpace I p from v)) = 1
    rw [gInner_smul_self (I := I) g p L⁻¹ (show TangentSpace I p from v), hvinner]
    field_simp [hLne]
  have hzunit : g.inner p (show TangentSpace I p from z)
      (show TangentSpace I p from z) = 1 := by
    dsimp only [z]
    change g.inner p (L⁻¹ • (show TangentSpace I p from w))
      (L⁻¹ • (show TangentSpace I p from w)) = 1
    rw [gInner_smul_self (I := I) g p L⁻¹ (show TangentSpace I p from w), hwinner]
    field_simp [hLne]
  have hLu : L • u = v := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hLne, one_smul]
  have hLz : L • z = w := by
    dsimp only [z]
    rw [smul_smul, mul_inv_cancel₀ hLne, one_smul]
  obtain ⟨c, hc, hcv⟩ := hv
  obtain ⟨d, hd, hdw⟩ := hw
  have hcpos : 0 < c := one_pos.trans hc
  have hdpos : 0 < d := one_pos.trans hd
  let C : ℝ := c * L
  let D : ℝ := d * L
  let ell : ℝ := (c - 1) * L
  have hCpos : 0 < C := mul_pos hcpos hLpos
  have hDpos : 0 < D := mul_pos hdpos hLpos
  have hellpos : 0 < ell := mul_pos (sub_pos.mpr hc) hLpos
  have hCeq : L + ell = C := by
    dsimp only [C, ell]
    ring
  have hcvdom : (show TangentSpace I p from c • v) ∈ expDomain (I := I) g p :=
    minimizingDomain_subset_expDomain (I := I) g p hcv
  have hdwdom : (show TangentSpace I p from d • w) ∈ expDomain (I := I) g p :=
    minimizingDomain_subset_expDomain (I := I) g p hdw
  have hCu : C • u = c • v := by
    dsimp only [C, u]
    rw [smul_smul, show c * L * L⁻¹ = c by field_simp [hLne]]
  have hDz : D • z = d • w := by
    dsimp only [D, z]
    rw [smul_smul, show d * L * L⁻¹ = d by field_simp [hLne]]
  have hdomu : ∀ t ∈ Icc (0 : ℝ) C,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p := by
    intro t ht
    have hratio : t / C ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hCpos.le, (div_le_one hCpos).mpr ht.2⟩
    have hscale := Exponential.smul_mem_expDomain (I := I) (g := g) (p := p)
      (v := show TangentSpace I p from c • v) hcvdom hratio
    have hscale_eq : (t / C) • (c • v) = t • u := by
      dsimp only [C, u]
      rw [smul_smul, smul_smul]
      congr 1
      field_simp [hcpos.ne', hLne]
    change (show TangentSpace I p from (t / C) • (c • v)) ∈
      expDomain (I := I) g p at hscale
    change (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p
    rwa [hscale_eq] at hscale
  have hdomz : ∀ t ∈ Icc (0 : ℝ) D,
      (show TangentSpace I p from t • z) ∈ expDomain (I := I) g p := by
    intro t ht
    have hratio : t / D ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hDpos.le, (div_le_one hDpos).mpr ht.2⟩
    have hscale := Exponential.smul_mem_expDomain (I := I) (g := g) (p := p)
      (v := show TangentSpace I p from d • w) hdwdom hratio
    have hscale_eq : (t / D) • (d • w) = t • z := by
      dsimp only [D, z]
      rw [smul_smul, smul_smul]
      congr 1
      field_simp [hdpos.ne', hLne]
    change (show TangentSpace I p from (t / D) • (d • w)) ∈
      expDomain (I := I) g p at hscale
    change (show TangentSpace I p from t • z) ∈ expDomain (I := I) g p
    rwa [hscale_eq] at hscale
  obtain ⟨γv, Jv, hJvopen, hJvconn, hsegmentv, hγv, hJvraw⟩ :=
    Exponential.exists_isGeodesicOnWithInitial_eqOn_expMap
      (v := show TangentSpace I p from u) (hdomu C ⟨hCpos.le, le_rfl⟩)
  have hIv : Icc (0 : ℝ) C ⊆ Jv := by
    simpa only [uIcc_of_le hCpos.le] using hsegmentv
  have hγvraw := hJvraw.mono hIv
  obtain ⟨γw, Jw, hJwopen, hJwconn, hsegmentw, hγw, hJwraw⟩ :=
    Exponential.exists_isGeodesicOnWithInitial_eqOn_expMap
      (v := show TangentSpace I p from z) (hdomz D ⟨hDpos.le, le_rfl⟩)
  have hIw : Icc (0 : ℝ) D ⊆ Jw := by
    simpa only [uIcc_of_le hDpos.le] using hsegmentw
  have hγwraw := hJwraw.mono hIw
  obtain ⟨γvg, hγvgsmooth, hγvgraw⟩ :=
    exists_contMDiff_extension_expMap_smul (I := I) g p u (hdomu C ⟨hCpos.le, le_rfl⟩)
  rw [uIcc_of_le hCpos.le] at hγvgraw
  obtain ⟨γwg, hγwgsmooth, hγwgraw⟩ :=
    exists_contMDiff_extension_expMap_smul (I := I) g p z (hdomz D ⟨hDpos.le, le_rfl⟩)
  rw [uIcc_of_le hDpos.le] at hγwgraw
  have hγvggeo : Geodesic.IsGeodesicOn (I := I) g γvg (Icc (0 : ℝ) C) := by
    intro t ht
    have hraw := hγvgraw t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
      hraw.eq_of_nhds hraw
      (hasGeodesicEquationAt_expMap_smul (I := I) g p (show TangentSpace I p from u) (hdomu t ht))
  have hγwggeo : Geodesic.IsGeodesicOn (I := I) g γwg (Icc (0 : ℝ) D) := by
    intro t ht
    have hraw := hγwgraw t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
      hraw.eq_of_nhds hraw
      (hasGeodesicEquationAt_expMap_smul (I := I) g p (show TangentSpace I p from z) (hdomz t ht))
  have hγvgunit : ∀ t ∈ Icc (0 : ℝ) C,
      g.inner (γvg t) (mfderiv 𝓘(ℝ, ℝ) I γvg t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γvg t (1 : ℝ)) = 1 := by
    intro t ht
    have hraw := hγvgraw t ht
    rw [hraw.eq_of_nhds, hraw.mfderiv_eq]
    change g.inner (radialCurve (I := I) g p u t)
      (Variation.curveVelocity (I := I) (radialCurve (I := I) g p u) t)
      (Variation.curveVelocity (I := I) (radialCurve (I := I) g p u) t) = 1
    have hspeed : g.inner (radialCurve (I := I) g p u t)
        (Variation.curveVelocity (I := I) (radialCurve (I := I) g p u) t)
        (Variation.curveVelocity (I := I) (radialCurve (I := I) g p u) t) =
        g.inner p u u := by
      simpa only [radialCurve] using!
        inner_curveVelocity_expMap_smul (I := I) g p u (hdomu t ht)
    rw [hspeed]
    exact huunit
  have hγwgunit : ∀ t ∈ Icc (0 : ℝ) D,
      g.inner (γwg t) (mfderiv 𝓘(ℝ, ℝ) I γwg t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γwg t (1 : ℝ)) = 1 := by
    intro t ht
    have hraw := hγwgraw t ht
    rw [hraw.eq_of_nhds, hraw.mfderiv_eq]
    change g.inner (radialCurve (I := I) g p z t)
      (Variation.curveVelocity (I := I) (radialCurve (I := I) g p z) t)
      (Variation.curveVelocity (I := I) (radialCurve (I := I) g p z) t) = 1
    have hspeed : g.inner (radialCurve (I := I) g p z t)
        (Variation.curveVelocity (I := I) (radialCurve (I := I) g p z) t)
        (Variation.curveVelocity (I := I) (radialCurve (I := I) g p z) t) =
        g.inner p z z := by
      simpa only [radialCurve] using!
        inner_curveVelocity_expMap_smul (I := I) g p z (hdomz t ht)
    rw [hspeed]
    exact hzunit
  have hLC : L < C := by
    dsimp only [C]
    nlinarith
  have hLD : L < D := by
    dsimp only [D]
    nlinarith
  have hLmemC : L ∈ Icc (0 : ℝ) C := ⟨hLpos.le, hLC.le⟩
  have hLmemD : L ∈ Icc (0 : ℝ) D := ⟨hLpos.le, hLD.le⟩
  have hγvrawL : γv =ᶠ[𝓝 L]
      (fun s => expMap (I := I) g p (show TangentSpace I p from s • u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hLpos, hLC⟩] with s hs
    exact hγvraw ⟨hs.1.le, hs.2.le⟩
  have hγwrawL : γw =ᶠ[𝓝 L]
      (fun s => expMap (I := I) g p (show TangentSpace I p from s • z)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hLpos, hLD⟩] with s hs
    exact hγwraw ⟨hs.1.le, hs.2.le⟩
  have hγvgL : γvg =ᶠ[𝓝 L] γv :=
    (hγvgraw L hLmemC).trans hγvrawL.symm
  have hγwgL : γwg =ᶠ[𝓝 L] γw :=
    (hγwgraw L hLmemD).trans hγwrawL.symm
  let σ : ℝ → M := fun s => γvg (s + L)
  have hσsmooth : ContMDiff 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) σ := by
    dsimp only [σ]
    exact hγvgsmooth.comp (contMDiff_id.add contMDiff_const)
  have hσgeo : Geodesic.IsGeodesicOn (I := I) g σ (Icc (0 : ℝ) ell) := by
    have hsub : Icc (0 : ℝ) ell ⊆ {t : ℝ | 1 * t + L ∈ Icc (0 : ℝ) C} := by
      intro t ht
      constructor
      · simpa only [one_mul] using add_nonneg ht.1 hLpos.le
      · rw [one_mul]
        calc
          t + L = L + t := add_comm _ _
          _ = t + L := add_comm _ _
          _ ≤ ell + L := by linarith [ht.2]
          _ = L + ell := add_comm _ _
          _ = C := hCeq
    simpa only [σ, one_mul] using
      (Geodesic.isGeodesicOn_comp_affine (I := I) (c := 1) (d := L)
        hγvggeo).mono hsub
  have hσunit : ∀ t ∈ Icc (0 : ℝ) ell,
      g.inner (σ t) (mfderiv 𝓘(ℝ, ℝ) I σ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I σ t (1 : ℝ)) = 1 := by
    intro t ht
    have hderiv := mfderiv_shift (I := I) hγvgsmooth L t
    change g.inner (γvg (t + L))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γvg (s + L)) t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γvg (s + L)) t (1 : ℝ)) = 1
    rw [hderiv]
    exact hγvgunit (t + L) ⟨add_nonneg ht.1 hLpos.le, by
      calc
        t + L = L + t := add_comm _ _
        _ = t + L := add_comm _ _
        _ ≤ ell + L := by linarith [ht.2]
        _ = L + ell := add_comm _ _
        _ = C := hCeq⟩
  have hγwg0 : γwg 0 = p := by
    rw [(hγwgraw 0 ⟨le_rfl, hDpos.le⟩).eq_of_nhds]
    change expMap (I := I) g p
      (show TangentSpace I p from (0 : ℝ) • z) = p
    rw [show (show TangentSpace I p from (0 : ℝ) • z) = 0 by
      change (0 : ℝ) • (show TangentSpace I p from z) = 0
      exact zero_smul ℝ _]
    exact expMap_zero (I := I) g p
  have hσell : σ ell = expMap (I := I) g p
      (show TangentSpace I p from c • v) := by
    have hCuT : (C : ℝ) • (show TangentSpace I p from u) =
        (c : ℝ) • (show TangentSpace I p from v) := by
      change C • u = c • v
      exact hCu
    change γvg (ell + L) = expMap (I := I) g p
      (show TangentSpace I p from c • v)
    calc
      γvg (ell + L) = γvg C := by rw [add_comm ell L, hCeq]
      _ = expMap (I := I) g p
          ((C : ℝ) • (show TangentSpace I p from u)) :=
        (hγvgraw C ⟨hCpos.le, le_rfl⟩).eq_of_nhds
      _ = expMap (I := I) g p
          ((c : ℝ) • (show TangentSpace I p from v)) :=
        congrArg (expMap (I := I) g p) hCuT
  have hdistc : riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from c • v)) = ENNReal.ofReal C := by
    simp only [minimizingDomain, Set.mem_ofPred_eq] at hcv
    have hcLen : Real.sqrt
        (g.inner p (show TangentSpace I p from c • v)
          (show TangentSpace I p from c • v)) = C := by
      dsimp only [C, L]
      exact sqrt_gInner_smul_self (I := I) g p hcpos.le
        (show TangentSpace I p from v)
    rw [hcLen] at hcv
    exact hcv.symm
  have hjunc : γwg L = σ 0 := by
    have hLzT : (L : ℝ) • (show TangentSpace I p from z) =
        (show TangentSpace I p from w) := by
      change L • z = w
      exact hLz
    have hLuT : (L : ℝ) • (show TangentSpace I p from u) =
        (show TangentSpace I p from v) := by
      change L • u = v
      exact hLu
    change γwg L = γvg (0 + L)
    calc
      γwg L = expMap (I := I) g p
          ((L : ℝ) • (show TangentSpace I p from z)) :=
        (hγwgraw L hLmemD).eq_of_nhds
      _ = expMap (I := I) g p
          ((L : ℝ) • (show TangentSpace I p from u)) := by
        rw [hLzT, hLuT]
        exact heq.symm
      _ = γvg (0 + L) := by
        rw [zero_add]
        exact (hγvgraw L hLmemC).eq_of_nhds.symm
  have hmin : riemannianEDist I (γwg 0) (σ ell) = ENNReal.ofReal (L + ell) := by
    rw [hγwg0, hσell, hdistc]
    rw [hCeq]
  have hmatchg := broken_minimizer_velocity_match (I := I) g hEnorm hLpos hellpos
    (fun t ht => hγwggeo t ⟨ht.1, ht.2.trans hLD.le⟩) hσgeo hγwgsmooth hσsmooth
    (fun t ht => hγwgunit t ⟨ht.1, ht.2.trans hLD.le⟩) hσunit hjunc hmin
  have hmatch : (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I γv L (1 : ℝ) : E) := by
    have hγwg : (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I γwg L (1 : ℝ) : E) :=
      congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) hγwgL.mfderiv_eq.symm
    have hσ0 : (mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I γvg L (1 : ℝ) : E) := by
      have hshift := mfderiv_shift (I := I) hγvgsmooth L 0
      dsimp only [σ]
      have hzero : (0 : ℝ) + L = L := by ring
      rw [hzero] at hshift
      with_unfolding_all exact hshift
    have hγvg : (mfderiv 𝓘(ℝ, ℝ) I γvg L (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I γv L (1 : ℝ) : E) :=
      congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) hγvgL.mfderiv_eq
    rw [hγwg, ← hγvg, ← hσ0]
    exact hmatchg
  obtain ⟨fv, hfvproj, hfv0, hfv⟩ := hγv
  obtain ⟨fw, hfwproj, hfw0, hfw⟩ := hγw
  have hγvinit : Geodesic.IsGeodesicOnWithInitial (I := I) g γv Jv p
      (show TangentSpace I p from u) := ⟨fv, hfvproj, hfv0, hfv⟩
  have hγwinit : Geodesic.IsGeodesicOnWithInitial (I := I) g γw Jw p
      (show TangentSpace I p from z) := ⟨fw, hfwproj, hfw0, hfw⟩
  have hγvgeo : Geodesic.IsGeodesicOn (I := I) g γv Jv := by
    intro t ht
    exact (hγvinit.isGeodesicAt (hJvopen.mem_nhds ht)).hasGeodesicEquationAt g
  have hγwgeo : Geodesic.IsGeodesicOn (I := I) g γw Jw := by
    intro t ht
    exact (hγwinit.isGeodesicAt (hJwopen.mem_nhds ht)).hasGeodesicEquationAt g
  have hγvcont : ContinuousOn γv Jv :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn hfv.continuousOn).congr
      (fun t _ => (hfvproj t).symm)
  have hγwcont : ContinuousOn γw Jw :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn hfw.continuousOn).congr
      (fun t _ => (hfwproj t).symm)
  have h0Jv : (0 : ℝ) ∈ Jv := hIv ⟨le_rfl, hCpos.le⟩
  have h0Jw : (0 : ℝ) ∈ Jw := hIw ⟨le_rfl, hDpos.le⟩
  have hfoot : γw L = γv L := by
    calc
      γw L = expMap (I := I) g p (show TangentSpace I p from L • z) := hγwraw hLmemD
      _ = expMap (I := I) g p (show TangentSpace I p from L • u) := by
        rw [hLz, hLu]
        exact heq.symm
      _ = γv L := (hγvraw hLmemC).symm
  have hγvlift := Geodesic.isMIntegralCurveOn_velocityLift (I := I) g hJvopen hγvgeo hγvcont
  have hγwlift := Geodesic.isMIntegralCurveOn_velocityLift (I := I) g hJwopen hγwgeo hγwcont
  let Jvshift : Set ℝ := {s : ℝ | s + L ∈ Jv}
  let Jwshift : Set ℝ := {s : ℝ | s + L ∈ Jw}
  let K : Set ℝ := Jwshift ∩ Jvshift
  have hJvshiftopen : IsOpen Jvshift :=
    hJvopen.preimage (continuous_id.add continuous_const)
  have hJwshiftopen : IsOpen Jwshift :=
    hJwopen.preimage (continuous_id.add continuous_const)
  have hJvshiftconn : IsPreconnected Jvshift :=
    (hJvconn.ordConnected.preimage_mono (f := fun s : ℝ => s + L)
      (fun _ _ hst => by linarith)).isPreconnected
  have hJwshiftconn : IsPreconnected Jwshift :=
    (hJwconn.ordConnected.preimage_mono (f := fun s : ℝ => s + L)
      (fun _ _ hst => by linarith)).isPreconnected
  have hKopen : IsOpen K := hJwshiftopen.inter hJvshiftopen
  have hKconn : IsPreconnected K :=
    (hJwshiftconn.ordConnected.inter hJvshiftconn.ordConnected).isPreconnected
  have h0K : (0 : ℝ) ∈ K := by
    constructor
    · change 0 + L ∈ Jw
      simpa using hIw hLmemD
    · change 0 + L ∈ Jv
      simpa using hIv hLmemC
  have hnegK : (-L : ℝ) ∈ K := by
    constructor
    · change -L + L ∈ Jw
      simpa using h0Jw
    · change -L + L ∈ Jv
      simpa using h0Jv
  have hlift0 :
      (DifferentialGeometry.velocityLift (I := I) γw ∘ fun s : ℝ => s + L) 0 =
        (DifferentialGeometry.velocityLift (I := I) γv ∘ fun s : ℝ => s + L) 0 := by
    simp only [Function.comp_apply, zero_add]
    apply TotalSpace.ext
    · exact hfoot
    · apply heq_of_eq
      exact hmatch
  have hlifteq := Geodesic.integralCurve_eqOn (I := I) g hKopen hKconn h0K
    ((hγwlift.comp_add L).mono inter_subset_left)
    ((hγvlift.comp_add L).mono inter_subset_right) hlift0
  have hvel0 : (mfderiv 𝓘(ℝ, ℝ) I γw 0 (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I γv 0 (1 : ℝ) : E) := by
    have hneg := hlifteq hnegK
    simp only [Function.comp_apply, neg_add_cancel] at hneg
    have hsnd := congrArg (fun q : TangentBundle I M => (q.snd : E)) hneg
    simpa only [DifferentialGeometry.velocityLift_snd] using! hsnd
  have hinitw := geo_init_vel (I := I) g hJwopen h0Jw hγwinit
  have hinitv := geo_init_vel (I := I) g hJvopen h0Jv hγvinit
  have hzu : (z : E) = (u : E) := by
    rw [hinitw, hinitv] at hvel0
    exact hvel0
  calc
    v = L • u := hLu.symm
    _ = L • z := congrArg (fun y : E => L • y) hzu.symm
    _ = w := hLz

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
    [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] in
private lemma riemannianEDist_congr_enorm_local
    (x y : M)
    (A B : ∀ x : M, ENorm (TangentSpace I x))
    (h : ∀ (x : M) (v : TangentSpace I x),
      @enorm (TangentSpace I x) (A x) v = @enorm (TangentSpace I x) (B x) v) :
    @riemannianEDist E _ _ H _ I M _ _ A x y =
      @riemannianEDist E _ _ H _ I M _ _ B x y := by
  rw [riemannianEDist_def, riemannianEDist_def]
  apply iInf_congr
  intro γ
  apply iInf_congr
  intro hγ
  apply lintegral_congr
  intro s
  exact h (γ s) (mfderiv% γ s 1)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem raw_exp_density_local
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p) :
    paramDensity (I := I) g
        (fun b : E => expMap (I := I) g p
          (show TangentSpace I p from b)) v =
      curveDensity (I := I) g
        (fun t : ℝ => expMap (I := I) g p
          (show TangentSpace I p from t • v))
        (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
          mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
            expMap (I := I) g p
              (show TangentSpace I p from
                t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1 := by
  have hfield :
      (fun i : Fin (Module.finrank ℝ E) =>
        radialJacobiField (I := I) g p v (chartModelBasis E i)) =
      (fun i : Fin (Module.finrank ℝ E) => fun t : ℝ =>
        (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
          expMap (I := I) g p
            (show TangentSpace I p from
              t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ))) := by
    funext i t
    simpa only [zero_smul, add_zero] using
      (radialJacobiField_eq (I := I) g p v (chartModelBasis E i) t)
  rw [← hfield]
  change paramDensity (I := I) g
      (fun b : E => expMap (I := I) g p
        (show TangentSpace I p from b)) v =
    curveDensity (I := I) g (radialCurve (I := I) g p v)
      (fun i : Fin (Module.finrank ℝ E) =>
        radialJacobiField (I := I) g p v (chartModelBasis E i)) 1
  exact paramDensity_expMap_eq_curveDensity (I := I) g p v hv

private theorem isCompact_rawSeg
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    IsCompact (minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R) := by
  classical
  let S : Set E := closedGBall (I := I) g p R
  have hS : IsCompact S := by
    simpa only [S] using isCompact_closedGBall (I := I) g p R
  have hdom : S ⊆ expDomain (I := I) g p := by
    intro v hv
    change Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) ≤ R at hv
    apply mem_expDomain_of_isCompact_closedEBall (I := I) g hEnorm p
      (show TangentSpace I p from v)
    · exact lt_of_le_of_lt hv hRR₀
    · exact hcpt
  let A : Set S := {v | ENNReal.ofReal
      (Real.sqrt (g.inner p (show TangentSpace I p from (v : E))
        (show TangentSpace I p from (v : E)))) =
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from (v : E)))}
  have hleft : Continuous (fun v : S => Real.sqrt
      (g.inner p (show TangentSpace I p from (v : E))
        (show TangentSpace I p from (v : E)))) := by
    have hinner : Continuous (fun v : E => g.inner p
        (show TangentSpace I p from v) (show TangentSpace I p from v)) := by
      with_unfolding_all exact continuous_gInner_self (I := I) g p
    exact Real.continuous_sqrt.comp (hinner.comp continuous_subtype_val)
  have hexp : Continuous (fun v : S => expMap (I := I) g p
      (show TangentSpace I p from (v : E))) := by
    have hcont : ContinuousOn (fun v : E => expMap (I := I) g p
        (show TangentSpace I p from v)) S :=
      ((contMDiffOn_expMap (I := I) g p).continuousOn).mono hdom
    exact hcont.domRestrict
  have hright : Continuous (fun v : S => riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from (v : E)))) := by
    let AENorm : ∀ x : M, ENorm (TangentSpace I x) := fun x =>
      (inferInstance : ContinuousENorm (TangentSpace I x)).toENorm
    have hdist : Continuous (fun q : M => riemannianEDist I p q) := by
      let _ : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      let RBNAG : ∀ x : M, NormedAddCommGroup (TangentSpace I x) :=
        fun x => Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
          (E := fun x : M => TangentSpace I x) x
      let RBENorm : ∀ x : M, ENorm (TangentSpace I x) := fun x =>
        (@SeminormedAddGroup.toContinuousENorm (TangentSpace I x)
          (@SeminormedAddCommGroup.toSeminormedAddGroup (TangentSpace I x)
            (@NormedAddCommGroup.toSeminormedAddCommGroup (TangentSpace I x) (RBNAG x)))).toENorm
      have hEnormRB : ∀ (x : M) (v : TangentSpace I x),
          @enorm (TangentSpace I x) (RBENorm x) v =
            ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
        intro x v
        have h₁ : @enorm (TangentSpace I x) (RBENorm x) v = ENNReal.ofReal ‖v‖ := by
          change (‖v‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖v‖
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg v)]
          rfl
        rw [h₁]
        rw [norm_eq_sqrt_real_inner]
        congr 1
      have hnorm_eq : ∀ (x : M) (v : TangentSpace I x),
          @enorm (TangentSpace I x) (AENorm x) v =
            @enorm (TangentSpace I x) (RBENorm x) v := by
        intro x v
        rw [hEnorm x v, hEnormRB x v]
      have hdist_eq (q : M) :
          @riemannianEDist E _ _ H _ I M _ _ RBENorm p q =
            @riemannianEDist E _ _ H _ I M _ _ AENorm p q := by
        exact (riemannianEDist_congr_enorm_local (I := I) p q AENorm RBENorm hnorm_eq).symm
      have hdistRB : Continuous (fun q : M =>
          @riemannianEDist E _ _ H _ I M _ _ RBENorm p q) := by
        let _ : IsContinuousRiemannianBundle E
            (fun x : M => TangentSpace I x) :=
          ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
        simpa only [RBENorm, RBNAG] using
          (continuous_riemannianEDist (I := I) g p)
      apply Continuous.congr hdistRB
      intro q
      exact hdist_eq q
    apply Continuous.congr (hdist.comp hexp)
    intro v
    simp only [Function.comp_apply]
  have hAclosed : IsClosed A := by
    apply isClosed_eq
    · exact ENNReal.continuous_ofReal.comp hleft
    · exact hright
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hA : IsCompact A := hAclosed.isCompact
  have himage : IsCompact ((fun v : S => (v : E)) '' A) :=
    hA.image continuous_subtype_val
  have heq : (fun v : S => (v : E)) '' A =
      minimizingDomain (I := I) g p ∩ S := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, w.property⟩
    · intro hv
      refine ⟨⟨v, hv.2⟩, ?_, rfl⟩
      exact hv.1
  rw [heq] at himage
  simpa only [S] using himage

theorem rawSegInt_ball_meas
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hR : 0 < R) (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    MeasurableSet
      (extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R) := by
  classical
  let S : ℝ := (R + R₀) / 2
  let K : Set E := minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p S
  let Q : Set ℚ := {q | (1 : ℝ) < (q : ℝ) ∧ (q : ℝ) < S / R}
  let A : ℚ → Set E := fun q =>
    (fun v : E => (q : ℝ) • v) ⁻¹' K ∩ gBall (I := I) g p R
  have hRS : R < S := by
    dsimp only [S]
    linarith
  have hSR₀ : S < R₀ := by
    dsimp only [S]
    linarith
  have hSdiv : 1 < S / R := by
    rw [lt_div_iff₀ hR]
    simpa only [one_mul] using hRS
  have hK : IsCompact K := by
    simpa only [K] using isCompact_rawSeg (I := I) g hEnorm p hSR₀ hcpt
  have hA (q : ℚ) : MeasurableSet (A q) := by
    exact (hK.measurableSet.preimage
      (continuous_const_smul (q : ℝ)).measurable).inter
        (measurableSet_gBall (I := I) g p R)
  have hEq : extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R =
      ⋃ q ∈ Q, A q := by
    ext v
    constructor
    · rintro ⟨hv, hvball⟩
      obtain ⟨c, hc, hcv⟩ := hv
      have hlim : 1 < min c (S / R) := lt_min hc hSdiv
      obtain ⟨q : ℚ, hq1, hqlim⟩ := exists_rat_btwn hlim
      have hqc : (q : ℝ) < c := hqlim.trans_le (min_le_left _ _)
      have hqS : (q : ℝ) < S / R := hqlim.trans_le (min_le_right _ _)
      have hqpos : 0 < (q : ℝ) := lt_trans zero_lt_one hq1
      have hqraw : (q : ℝ) • v ∈ minimizingDomain (I := I) g p := by
        apply extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p
        refine ⟨c / (q : ℝ), (one_lt_div hqpos).2 hqc, ?_⟩
        simpa only [smul_smul, div_mul_cancel₀ _ hqpos.ne'] using hcv
      have hqR : (q : ℝ) * R < S := (lt_div_iff₀ hR).mp hqS
      have hqball : (q : ℝ) • v ∈ closedGBall (I := I) g p S := by
        change Real.sqrt
          (g.inner p ((q : ℝ) • (show TangentSpace I p from v))
            ((q : ℝ) • (show TangentSpace I p from v))) ≤ S
        change Real.sqrt
          (g.inner p (show TangentSpace I p from v)
            (show TangentSpace I p from v)) < R at hvball
        rw [sqrt_gInner_smul_self (I := I) g p hqpos.le]
        exact le_of_lt
          ((mul_le_mul_of_nonneg_left (le_of_lt hvball) hqpos.le).trans_lt hqR)
      refine mem_iUnion₂.mpr ⟨q, ⟨hq1, hqS⟩, ?_⟩
      exact ⟨⟨hqraw, hqball⟩, hvball⟩
    · rintro hv
      obtain ⟨q, hqQ, hqv⟩ := mem_iUnion₂.mp hv
      exact ⟨⟨(q : ℝ), hqQ.1, hqv.1.1⟩, hqv.2⟩
  rw [hEq]
  exact MeasurableSet.biUnion (Set.to_countable Q) fun q _ => hA q

private theorem rawSegInt_image_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hR : 0 < R) (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((fun v : E => expMap (I := I) g p
          (show TangentSpace I p from v)) ''
          (extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R)) =
      ∫⁻ v in extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
        ∂(modelHaar (E := E)) := by
  let K : Set E := extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  let U : Set E := {v : E | (show TangentSpace I p from v) ∈
    expDomain (I := I) g p}
  have hK : MeasurableSet K := by
    simpa only [K] using rawSegInt_ball_meas (I := I) g hEnorm p hR hRR₀ hcpt
  have hKdom : K ⊆ expDomain (I := I) g p := by
    intro v hv
    change v ∈ extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R at hv
    exact minimizingDomain_subset_expDomain (I := I) g p
      (extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hv.1)
  have hU : IsOpen U := by
    exact isOpen_expDomain (I := I) g p
  have hKU : K ⊆ U := by
    intro v hv
    change (show TangentSpace I p from v) ∈ expDomain (I := I) g p
    exact hKdom hv
  have hF : ContMDiffOn 𝓘(ℝ, E) I 1 F U := by
    change ContMDiffOn 𝓘(ℝ, E) I 1 F (expDomain (I := I) g p)
    simpa only [F] using
      (contMDiffOn_expMap (I := I) g p).of_le (by norm_num)
  have hinj : Set.InjOn F K := by
    simpa only [F, K] using
      (rawExp_inj_seg (I := I) g hEnorm p).mono Set.inter_subset_left
  have hcov := riemannianVolumeMeasure_image_eq (I := I) g (f := F) (U := U)
    hU hK hKU hF hinj
  have hjac : ∀ v ∈ K,
      paramDensity (I := I) g F v =
        curveDensity (I := I) g
          (fun t : ℝ => expMap (I := I) g p
            (show TangentSpace I p from t • v))
          (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
            mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
            expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1 := by
    intro v hv
    simpa only [F] using raw_exp_density_local (I := I) g p v (hKdom hv)
  have hint :
      (∫⁻ v in K, ENNReal.ofReal (paramDensity (I := I) g F v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
          ∂(modelHaar (E := E)) := by
    refine setLIntegral_congr_fun hK (fun v hv => ?_)
    exact congrArg ENNReal.ofReal (hjac v hv)
  simpa only [F, K] using hcov.trans hint

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem rawSegEnd_ray_sub
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) :
    ({r : Ioi (0 : ℝ) |
      r.1 • u ∈ minimizingDomain (I := I) g p \ extendibleMinimizingDomain (I := I) g p} :
      Set (Ioi (0 : ℝ))).Subsingleton := by
  rintro ⟨a, ha0⟩ ⟨haD, haI⟩ ⟨b, hb0⟩ ⟨hbD, hbI⟩
  have ha_pos : 0 < a := ha0
  have hb_pos : 0 < b := hb0
  apply Subtype.ext
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    apply haI
    refine ⟨b / a, (one_lt_div ha_pos).2 hab, ?_⟩
    rw [smul_smul, div_mul_cancel₀ b ha_pos.ne']
    exact hbD
  · exact hab
  · exfalso
    apply hbI
    refine ⟨a / b, (one_lt_div hb_pos).2 hab, ?_⟩
    rw [smul_smul, div_mul_cancel₀ a hb_pos.ne']
    exact haD

theorem rawSegEnd_null
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    (modelHaar (E := E))
        ((minimizingDomain (I := I) g p \ extendibleMinimizingDomain (I := I) g p) ∩
          closedGBall (I := I) g p R) = 0 := by
  let _ : Measure.IsAddHaarMeasure (modelHaar (E := E)) := modelHaar_isAddHaarMeasure
  let K : Set E := minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R
  have hK : IsCompact K := isCompact_rawSeg (I := I) g hEnorm p hRR₀ hcpt
  apply measure_mono_null ?_ (hK.measure_setOf_forall_smul_notMem (modelHaar (E := E)))
  rintro v ⟨⟨hv, hvnot⟩, hvball⟩
  refine ⟨⟨hv, hvball⟩, ?_⟩
  intro c hc hcv
  exact hvnot ⟨c, hc, hcv.1⟩

private theorem rawSegEnd_nullMeas
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    NullMeasurableSet
      ((minimizingDomain (I := I) g p \ extendibleMinimizingDomain (I := I) g p) ∩
        closedGBall (I := I) g p R)
      (modelHaar (E := E)) :=
  NullMeasurableSet.of_null (rawSegEnd_null (I := I) g hEnorm p hRR₀ hcpt)

omit [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
private theorem gSphere_null
    (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    (modelHaar (E := E))
        {v : E | Real.sqrt
          (g.inner p (show TangentSpace I p from v)
            (show TangentSpace I p from v)) = R} = 0 := by
  classical
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let q : E → ℝ := fun v => Real.sqrt
    (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v))
  let level : Set E := {v | q v = R}
  have hq_cont : Continuous q := by
    exact Real.continuous_sqrt.comp
      (by
        change Continuous (fun v : TangentSpace I p => g.inner p v v)
        exact continuous_gInner_self (I := I) g p)
  have hlevel_meas : MeasurableSet level :=
    (isClosed_eq hq_cont continuous_const).measurableSet
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  have hlevel_eq : level = L '' Metric.sphere (0 : E) R := by
    ext v
    constructor
    · intro hv
      refine ⟨L.symm v, ?_, L.apply_symm_apply v⟩
      rw [mem_sphere_zero_iff_norm]
      have hqv : q v = R := hv
      have hsqrt : q v = ‖L.symm v‖ := by
        have hs := normalFrame_sqrt (I := I) g p (L.symm v)
        change q (L (L.symm v)) = ‖L.symm v‖ at hs
        simpa only [L.apply_symm_apply] using hs
      exact hsqrt.symm.trans hqv
    · rintro ⟨w, hw, rfl⟩
      have hnorm : ‖w‖ = R := by
        simpa only [mem_sphere_zero_iff_norm] using hw
      change q (L w) = R
      have hs := normalFrame_sqrt (I := I) g p w
      change q (L w) = ‖w‖ at hs
      exact hs.trans hnorm
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    b.map L.toLinearEquiv
  have hmap : Measure.map L (modelHaar (E := E)) = b'.addHaar := by
    simpa only [b, b', modelHaar] using Module.Basis.map_addHaar b L
  have hlevel_map : b'.addHaar level = 0 := by
    rw [← hmap, Measure.map_apply_of_aemeasurable
      L.continuous.measurable.aemeasurable hlevel_meas, hlevel_eq,
      L.injective.preimage_image]
    exact Measure.addHaar_sphere (modelHaar (E := E)) (0 : E) R
  have hlevel_zero : (modelHaar (E := E)) level = 0 := by
    change b.addHaar level = 0
    rw [← Module.Basis.det_smul_addHaar b b', Measure.smul_apply,
      hlevel_map, smul_zero]
  simpa only [level, q] using hlevel_zero

omit [NeZero (Module.finrank ℝ E)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private theorem riemVol_rawExp_le
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K)
    (hKdom : K ⊆ expDomain (I := I) g p) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((fun v : E => expMap (I := I) g p
          (show TangentSpace I p from v)) '' K) ≤
      ∫⁻ v in K, ENNReal.ofReal
        (paramDensity (I := I) g
          (fun v : E => expMap (I := I) g p
            (show TangentSpace I p from v)) v)
        ∂(modelHaar (E := E)) := by
  let U : Set E := {v : E | (show TangentSpace I p from v) ∈
    expDomain (I := I) g p}
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  have hU : IsOpen U := by
    exact isOpen_expDomain (I := I) g p
  have hKU : K ⊆ U := by
    intro v hv
    exact hKdom hv
  have hF : ContMDiffOn 𝓘(ℝ, E) I 1 F U := by
    change ContMDiffOn 𝓘(ℝ, E) I 1 F (expDomain (I := I) g p)
    simpa only [F] using
      (contMDiffOn_expMap (I := I) g p).of_le (by norm_num)
  simpa only [F] using
    riemannianVolumeMeasure_image_le_of_isCompact (I := I) g hU hK hKU hF

private theorem ball_sub_rawSeg
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R ≤ R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    {q : M | riemannianEDist I p q < ENNReal.ofReal R} ⊆
      (fun v : E => expMap (I := I) g p
        (show TangentSpace I p from v)) ''
        (minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R) := by
  intro q hq
  have hqR₀ : riemannianEDist I p q < ENNReal.ofReal R₀ :=
    hq.trans_le (ENNReal.ofReal_mono hRR₀)
  obtain ⟨v, _hvdom, hvexp, hvlen⟩ :=
    RadialSurjectivity.minExp_of_cptBall (I := I) g hEnorm p q hqR₀ hcpt
  refine ⟨v, ⟨?_, ?_⟩, hvexp⟩
  · subst q
    exact hvlen
  · change Real.sqrt (g.inner p v v) ≤ R
    exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (Real.sqrt_nonneg _)).mp (hvlen.trans_lt hq))

theorem rawBall_integral_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hR : 0 < R) (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal R} =
      ∫⁻ v in extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
        ∂(modelHaar (E := E)) := by
  classical
  let B : Set M := {q : M | riemannianEDist I p q < ENNReal.ofReal R}
  let K : Set E := extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R
  let L : Set E := minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  let D : E → ENNReal := fun v => ENNReal.ofReal
    (curveDensity (I := I) g
      (fun t : ℝ => expMap (I := I) g p
        (show TangentSpace I p from t • v))
      (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
        mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
          expMap (I := I) g p
            (show TangentSpace I p from
              t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
  have hL : IsCompact L := by
    simpa only [L] using isCompact_rawSeg (I := I) g hEnorm p hRR₀ hcpt
  have hLdom : L ⊆ expDomain (I := I) g p := by
    intro v hv
    change v ∈ minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R at hv
    exact minimizingDomain_subset_expDomain (I := I) g p hv.1
  have hKsubL : K ⊆ L := by
    intro v hv
    change v ∈ extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R at hv
    refine ⟨extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hv.1, ?_⟩
    change Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) ≤ R
    have hvball := hv.2
    change Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) < R at hvball
    exact le_of_lt hvball
  have hdiff_sub :
      L \ K ⊆
        ((minimizingDomain (I := I) g p \ extendibleMinimizingDomain (I := I) g p) ∩
          closedGBall (I := I) g p R) ∪
          {v : E | Real.sqrt
            (g.inner p (show TangentSpace I p from v)
              (show TangentSpace I p from v)) = R} := by
    rintro v ⟨hvL, hvK⟩
    change v ∈ minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R at hvL
    change v ∉ extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R at hvK
    rcases hvL with ⟨hvraw, hvclosed⟩
    by_cases hvint : v ∈ extendibleMinimizingDomain (I := I) g p
    · right
      change Real.sqrt
        (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v)) = R
      apply le_antisymm hvclosed
      apply le_of_not_gt
      intro hvball
      apply hvK
      exact ⟨hvint, hvball⟩
    · left
      exact ⟨⟨hvraw, hvint⟩, hvclosed⟩
  have hdiff : (modelHaar (E := E)) (L \ K) = 0 := by
    apply measure_mono_null hdiff_sub
    apply measure_union_null
    · simpa only [L] using rawSegEnd_null (I := I) g hEnorm p hRR₀ hcpt
    · exact gSphere_null (I := I) (E := E) g p R
  have hLKae : L =ᵐ[modelHaar (E := E)] K := by
    rw [ae_eq_set]
    refine ⟨hdiff, ?_⟩
    rw [sdiff_eq_empty.mpr hKsubL, measure_empty]
  have hInt : (∫⁻ v in L, D v ∂(modelHaar (E := E))) =
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) :=
    setLIntegral_congr hLKae
  have hcover : B ⊆ F '' L := by
    simpa only [B, F, L] using
      ball_sub_rawSeg (I := I) g hEnorm p hRR₀.le hcpt
  have hupper : riemannianVolumeMeasure (I := I) (M := M) g B ≤
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) := by
    calc
      riemannianVolumeMeasure (I := I) (M := M) g B ≤
          riemannianVolumeMeasure (I := I) (M := M) g (F '' L) :=
        measure_mono hcover
      _ ≤ ∫⁻ v in L, D v ∂(modelHaar (E := E)) := by
        have hparam :
            riemannianVolumeMeasure (I := I) (M := M) g (F '' L) ≤
              ∫⁻ v in L, ENNReal.ofReal (paramDensity (I := I) g
                (fun v : E => expMap (I := I) g p
                  (show TangentSpace I p from v)) v)
                ∂(modelHaar (E := E)) := by
          simpa only [F] using riemVol_rawExp_le (I := I) g p hL hLdom
        have hreplace :
            (∫⁻ v in L, ENNReal.ofReal (paramDensity (I := I) g
                (fun v : E => expMap (I := I) g p
                  (show TangentSpace I p from v)) v)
                ∂(modelHaar (E := E))) =
              ∫⁻ v in L, D v ∂(modelHaar (E := E)) := by
          refine setLIntegral_congr_fun hL.measurableSet (fun v hv => ?_)
          exact congrArg ENNReal.ofReal
            (by simpa only [F, D] using
              raw_exp_density_local (I := I) g p v (hLdom hv))
        exact hparam.trans_eq hreplace
      _ = ∫⁻ v in K, D v ∂(modelHaar (E := E)) := hInt
  have hFKsub : F '' K ⊆ B := by
    rintro q ⟨v, hvK, rfl⟩
    change v ∈ extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R at hvK
    change riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v)) < ENNReal.ofReal R
    have hvraw : v ∈ minimizingDomain (I := I) g p :=
      extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hvK.1
    change ENNReal.ofReal
      (Real.sqrt (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v))) =
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) at hvraw
    rw [← hvraw]
    have hvball := hvK.2
    change Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) < R at hvball
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _)).mpr hvball
  have himage : riemannianVolumeMeasure (I := I) (M := M) g (F '' K) =
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) := by
    simpa only [F, K, D] using
      rawSegInt_image_eq (I := I) g hEnorm p hR hRR₀ hcpt
  apply le_antisymm hupper
  calc
    ∫⁻ v in K, D v ∂(modelHaar (E := E)) =
        riemannianVolumeMeasure (I := I) (M := M) g (F '' K) := himage.symm
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) g B := measure_mono hFKsub

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
