import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Basic
import DifferentialGeometry.Geometry.Geodesic.Flow.VelocityLift
import DifferentialGeometry.Geometry.Geodesic.Equation.ProjectionDerivative

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set Filter
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open VolumeComparison (radialCurve)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private theorem mfderiv_comp_add_const_apply_one
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

omit [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private theorem mfderiv_zero_eq_initial_velocity
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

theorem injOn_expMap_extendibleMinimizingDomain
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    Set.InjOn (fun v : E => expMap (I := I) g p
      (show TangentSpace I p from v)) (extendibleMinimizingDomain (I := I) g p) := by
  intro v hv w hw heq
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hvmin : v ∈ minimizingDomain (I := I) g p :=
    extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hv
  have hwmin : w ∈ minimizingDomain (I := I) g p :=
    extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hw
  have hlen := sqrt_inner_self_eq_of_mem_minimizingDomain_of_expMap_eq
    (I := I) g p hvmin hwmin heq
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
    have hscale := smul_mem_expDomain (I := I) (g := g) (p := p)
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
    have hscale := smul_mem_expDomain (I := I) (g := g) (p := p)
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
  obtain ⟨γv, Jv, hJvopen, hJvconn, hsegmentv, hγv, hJvexp⟩ :=
    exists_isGeodesicOnWithInitial_eqOn_expMap
      (v := show TangentSpace I p from u) (hdomu C ⟨hCpos.le, le_rfl⟩)
  have hIv : Icc (0 : ℝ) C ⊆ Jv := by
    simpa only [uIcc_of_le hCpos.le] using hsegmentv
  have hγvexp := hJvexp.mono hIv
  obtain ⟨γw, Jw, hJwopen, hJwconn, hsegmentw, hγw, hJwexp⟩ :=
    exists_isGeodesicOnWithInitial_eqOn_expMap
      (v := show TangentSpace I p from z) (hdomz D ⟨hDpos.le, le_rfl⟩)
  have hIw : Icc (0 : ℝ) D ⊆ Jw := by
    simpa only [uIcc_of_le hDpos.le] using hsegmentw
  have hγwexp := hJwexp.mono hIw
  obtain ⟨γvg, hγvgsmooth, hγvgexp⟩ :=
    exists_contMDiff_extension_expMap_smul (I := I) g p u (hdomu C ⟨hCpos.le, le_rfl⟩)
  rw [uIcc_of_le hCpos.le] at hγvgexp
  obtain ⟨γwg, hγwgsmooth, hγwgexp⟩ :=
    exists_contMDiff_extension_expMap_smul (I := I) g p z (hdomz D ⟨hDpos.le, le_rfl⟩)
  rw [uIcc_of_le hDpos.le] at hγwgexp
  have hγvggeo : Geodesic.IsGeodesicOn (I := I) g γvg (Icc (0 : ℝ) C) := by
    intro t ht
    have hexp := hγvgexp t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
      hexp.eq_of_nhds hexp
      (hasGeodesicEquationAt_expMap_smul (I := I) g p (show TangentSpace I p from u) (hdomu t ht))
  have hγwggeo : Geodesic.IsGeodesicOn (I := I) g γwg (Icc (0 : ℝ) D) := by
    intro t ht
    have hexp := hγwgexp t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
      hexp.eq_of_nhds hexp
      (hasGeodesicEquationAt_expMap_smul (I := I) g p (show TangentSpace I p from z) (hdomz t ht))
  have hγvgunit : ∀ t ∈ Icc (0 : ℝ) C,
      g.inner (γvg t) (mfderiv 𝓘(ℝ, ℝ) I γvg t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γvg t (1 : ℝ)) = 1 := by
    intro t ht
    have hexp := hγvgexp t ht
    rw [hexp.eq_of_nhds, hexp.mfderiv_eq]
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
    have hexp := hγwgexp t ht
    rw [hexp.eq_of_nhds, hexp.mfderiv_eq]
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
  have hγvexpL : γv =ᶠ[𝓝 L]
      (fun s => expMap (I := I) g p (show TangentSpace I p from s • u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hLpos, hLC⟩] with s hs
    exact hγvexp ⟨hs.1.le, hs.2.le⟩
  have hγwexpL : γw =ᶠ[𝓝 L]
      (fun s => expMap (I := I) g p (show TangentSpace I p from s • z)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hLpos, hLD⟩] with s hs
    exact hγwexp ⟨hs.1.le, hs.2.le⟩
  have hγvgL : γvg =ᶠ[𝓝 L] γv :=
    (hγvgexp L hLmemC).trans hγvexpL.symm
  have hγwgL : γwg =ᶠ[𝓝 L] γw :=
    (hγwgexp L hLmemD).trans hγwexpL.symm
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
    have hderiv := mfderiv_comp_add_const_apply_one (I := I) hγvgsmooth L t
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
    rw [(hγwgexp 0 ⟨le_rfl, hDpos.le⟩).eq_of_nhds]
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
        (hγvgexp C ⟨hCpos.le, le_rfl⟩).eq_of_nhds
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
        (hγwgexp L hLmemD).eq_of_nhds
      _ = expMap (I := I) g p
          ((L : ℝ) • (show TangentSpace I p from u)) := by
        rw [hLzT, hLuT]
        exact heq.symm
      _ = γvg (0 + L) := by
        rw [zero_add]
        exact (hγvgexp L hLmemC).eq_of_nhds.symm
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
      have hshift := mfderiv_comp_add_const_apply_one (I := I) hγvgsmooth L 0
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
      γw L = expMap (I := I) g p (show TangentSpace I p from L • z) := hγwexp hLmemD
      _ = expMap (I := I) g p (show TangentSpace I p from L • u) := by
        rw [hLz, hLu]
        exact heq.symm
      _ = γv L := (hγvexp hLmemC).symm
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
  have hinitw := mfderiv_zero_eq_initial_velocity (I := I) g hJwopen h0Jw hγwinit
  have hinitv := mfderiv_zero_eq_initial_velocity (I := I) g hJvopen h0Jv hγvinit
  have hzu : (z : E) = (u : E) := by
    rw [hinitw, hinitv] at hvel0
    exact hvel0
  calc
    v = L • u := hLu.symm
    _ = L • z := congrArg (fun y : E => L • y) hzu.symm
    _ = w := hLz

end DifferentialGeometry.Geometry.Riemannian.Exponential
