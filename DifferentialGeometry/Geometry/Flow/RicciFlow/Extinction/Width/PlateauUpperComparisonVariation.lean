import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonIntegrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiffeomorphismTransport
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskFirstVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskAreaMetricFirstVariation

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [hT2 : T2Space Q] [hCompact : CompactSpace Q] [hSigma : SigmaCompactSpace Q]
  [hBoundary : I.Boundaryless]

variable {g : ℝ → SmoothRiemannianMetric I Q} {D : RealTimeInterval}
  {hG : MetricFamilySmoothOn D g} {t₀ : ℝ}

omit hSigma in
theorem SmoothDisk.hasDerivAt_transportedArea_isotopy_flux
    (c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    (hG : MetricFamilySmoothOn D g)
    (ht₀ : D.regular ∈ 𝓝 t₀)
    (u : SmoothDisk (I := I) (Q := Q))
    (hconf : u.IsConformal (g t₀)) (hharm : u.IsHarmonic (g t₀))
    {T : Set ℝ} (hT : IsOpen T) (hT₀ : t₀ ∈ T)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ T))
    (hid : ∀ q, Phi t₀ q = q) :
    IntegrableOn (diskExtension (u.metricVariationDensity g T t₀))
        (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryFluxDensity (g t₀) (u.isotopyVelocity Phi T t₀ hid))
        volume 0 1 ∧
      HasDerivAt (u.transportedArea g Phi)
        ((1 / 2 : ℝ) *
          (∫ z in Metric.closedBall (0 : ℂ) 1,
            diskExtension (u.metricVariationDensity g T t₀) z) -
          u.boundaryFlux (g t₀) (u.isotopyVelocity Phi T t₀ hid)) t₀ := by
  obtain ⟨hintDensity, hderivMetric⟩ :=
    SmoothDisk.hasDerivAt_diskArea_metricFamily (I := I) (Q := Q) (hG := hG) c u g T ht₀
      (hT.mem_nhds hT₀) hconf
  obtain ⟨U, hUeq, N, hN, hDN, hUN⟩ :=
    SmoothDisk.exists_smoothExtension (I := I) (Q := Q) (hne := ⟨u.map diskCenter⟩) u
  let φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ c.Q := c.equiv
  let g' : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) c.Q :=
    fun t => DifferentialGeometry.Diffeomorph.pullbackMetricCross (g t) φ.symm
  have hg' : MetricFamilySmoothOn D g' :=
    MetricFamilySmoothOn.of_pullback hG g' (fun x => φ.symm x) φ.symm.contMDiff
      (fun t x v w => DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner (g t) φ.symm x v w)
  let U' : ℂ → c.Q := fun z => φ (U z)
  have hU'sm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U' N := φ.contMDiff.comp_contMDiffOn hUN
  let u' : C(Metric.closedBall (0 : ℂ) 1, c.Q) :=
    ⟨fun z => U' (z : ℂ), (hU'sm.mono hDN).continuousOn.domRestrict⟩
  have hExt' : Geometry.SmoothDiskExtension (E := E) u' U' := ⟨fun _ => rfl, N, hN, hDN, hU'sm⟩
  have hu'eq : ∀ z : Disk, U' (z : ℂ) = (SmoothDisk.compDiffeomorph φ u).map z := by
    intro z
    simp only [U', SmoothDisk.comp_diffeomorph_map]
    rw [hUeq z]
  have hw : Geometry.SmoothDiskExtension (E := E) (SmoothDisk.compDiffeomorph φ u).map U' :=
    ⟨fun z => (hu'eq z).symm ▸ rfl, N, hN, hDN, hU'sm⟩
  have hwconf : (SmoothDisk.compDiffeomorph φ u).IsConformal (g' t₀) :=
    SmoothDisk.isConformal_comp_diffeomorph φ (g t₀) u hconf
  have hconf' : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (g' t₀) U' z :=
    (SmoothDisk.isConformal_iff_diskMapConformalAt (SmoothDisk.compDiffeomorph φ u)
      (g' t₀) hw).mp hwconf
  have hwharm : (SmoothDisk.compDiffeomorph φ u).IsHarmonic (g' t₀) :=
    SmoothDisk.isHarmonic_comp_diffeomorph φ (g t₀) u hharm
  have hharm' : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension (g' t₀) U' z = 0 := by
    intro z hz
    have h1 : (diskMapTension (g' t₀) (diskExtension (SmoothDisk.compDiffeomorph φ u).map) z : E)
        = 0 :=
      SmoothDisk.diskMapTension_eq_zero_of_isHarmonic_interior
        (SmoothDisk.compDiffeomorph φ u) (g' t₀) hwharm hz
    have hmem : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
    have hgerm : (diskExtension (SmoothDisk.compDiffeomorph φ u).map) =ᶠ[𝓝 z] U' := by
      filter_upwards [hmem] with w hw'
      rw [diskExtension_coe _ ⟨w, hw'⟩]
      exact (hu'eq ⟨w, hw'⟩).symm
    rw [← diskMapTension_congr_of_eventuallyEq (g' t₀) hgerm]
    exact h1
  let Φ' : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) c.Q c.Q ∞ :=
    fun t => (φ.symm.trans (Phi t)).trans φ
  have hΦ'id : Φ' t₀ = Diffeomorph.refl 𝓘(ℝ, E) c.Q ∞ := by
    ext y
    simp only [Φ', Diffeomorph.coe_trans, Function.comp_apply]
    rw [hid (φ.symm y), φ.apply_symm_apply]
    rfl
  have hΦ'sm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × c.Q => Φ' p.1 p.2) (T ×ˢ univ) := by
    intro p hp
    have hψ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ℝ × c.Q => (φ.symm q.2, q.1)) p := by
      rw [contMDiffAt_prod_iff]
      exact ⟨φ.symm.contMDiff.contMDiffAt.comp p contMDiffAt_snd, contMDiffAt_fst⟩
    have hx : (φ.symm p.2, p.1) ∈ (univ : Set Q) ×ˢ T := ⟨trivial, hp.1⟩
    have hbase : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun q : Q × ℝ => Phi q.2 q.1)
        (φ.symm p.2, p.1) :=
      hPhi.contMDiffAt ((isOpen_univ.prod hT).mem_nhds hx)
    have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
        (fun q : ℝ × c.Q => Phi q.1 (φ.symm q.2)) p :=
      hbase.comp p hψ
    exact (φ.contMDiff.contMDiffAt.comp p h1).contMDiffWithinAt
  obtain ⟨hintDens', hintFlux', hderiv'⟩ :=
    SmoothDiskExtension.hasDerivAt_area_isotopy_flux (u := u') (U := U') hExt' hg' ht₀
      hT hT₀ hΦ'sm hΦ'id hconf' hharm'
  let b' : ℝ → ℝ := fun θ =>
    (g' t₀).inner (U' (circleMap 0 1 θ))
      (show TangentSpace 𝓘(ℝ, E) (U' (circleMap 0 1 θ)) from
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ' r (U' (circleMap 0 1 θ))) t₀ 1)
      (diskMapInwardConormal (g' t₀) U' (circleMap 0 1 θ)) *
      Real.sqrt (diskMapConformalCoefficient (g' t₀) U' (circleMap 0 1 θ))
  have hfl : IntervalIntegrable b' volume (-Real.pi) Real.pi := hintFlux'
  have hLHS : (fun t => riemannianDiskArea (g' t)
        ((⟨Φ' t, (Φ' t).contMDiff.continuous⟩ : C(c.Q, c.Q)).comp u')) =
      u.transportedArea g Phi := by
    funext t
    rw [SmoothDisk.transportedArea]
    have h1 : (⇑((⟨Φ' t, (Φ' t).contMDiff.continuous⟩ : C(c.Q, c.Q)).comp u') : Disk → c.Q) =
        fun z : Disk => Φ' t (U' z) := by
      funext z
      rfl
    have h2 : ∀ z : Disk, φ.symm (Φ' t (U' (z : ℂ))) = Phi t (u.map z) := by
      intro z
      have hs : φ.symm (U' (z : ℂ)) = u.map z := by
        change φ.symm (φ (U (z : ℂ))) = u.map z
        rw [φ.symm_apply_apply, hUeq z]
      have hΦ : Φ' t (U' (z : ℂ)) = φ (Phi t (u.map z)) := by
        simp only [Φ', Diffeomorph.coe_trans, Function.comp_apply, hs]
      rw [hΦ, φ.symm_apply_apply]
    rw [h1, ← diskArea_eq_riemannianDiskArea (g' t) (fun z : Disk => Φ' t (U' (z : ℂ))),
      diskArea_pullbackMetricCross (g t) φ.symm (fun z : Disk => Φ' t (U' (z : ℂ)))]
    rw [show (fun z : Disk => φ.symm (Φ' t (U' (z : ℂ)))) =
      (fun z : Disk => Phi t (u.map z)) from funext h2]
  have hfunFix : (fun t => riemannianDiskArea (g' t) (⇑u')) = fun t => diskArea (g t) u.map := by
    funext t
    have h1 : (⇑u' : Disk → c.Q) = fun z : Disk => φ (u.map z) := by
      funext z
      change U' (z : ℂ) = φ (u.map z)
      rw [show U' (z : ℂ) = φ (U (z : ℂ)) from rfl, hUeq z]
    rw [h1, ← diskArea_eq_riemannianDiskArea (g' t) (fun z : Disk => φ (u.map z)),
      diskArea_pullbackMetricCross (g t) φ.symm (fun z : Disk => φ (u.map z))]
    rw [show (fun z : Disk => φ.symm (φ (u.map z))) = (fun z : Disk => u.map z) from by
      funext z
      rw [φ.symm_apply_apply]]
  have hDensInt : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity g' t₀ U' z) =
      (1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity g T t₀) z) := by
    have ha : HasDerivAt (fun t => riemannianDiskArea (g' t) (⇑u'))
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity g' t₀ U' z) t₀ :=
      (SmoothDiskExtension.hasDerivAt_area_metric (u := u') (U := U') hExt' hg' ht₀ hconf').2
    have hb : HasDerivAt (fun t => riemannianDiskArea (g' t) (⇑u'))
        ((1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity g T t₀) z)) t₀ := by
      rw [hfunFix]
      exact hderivMetric
    exact ha.unique hb
  have hfluxPt : ∀ x : ℝ, b' (2 * Real.pi * x) * (2 * Real.pi) =
      u.boundaryFluxDensity (g t₀) (u.isotopyVelocity Phi T t₀ hid) x := by
    intro x
    set z : Disk := diskBoundary (x : Surgery.Topology.Circle) with hzdef
    set ζ : ℂ := circleMap 0 1 (2 * Real.pi * x) with hζdef
    have hmem : ζ ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [hζdef]
      exact circleMap_mem_closedBall 0 (by norm_num) _
    have hz : (z : ℂ) = ζ := by
      rw [hzdef, hζdef]
      have h := diskBoundary_angle (2 * Real.pi * x)
      rwa [mul_div_cancel_left₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at h
    have hconfz := hconf' ζ hmem
    have hUi : U' ζ = φ (u.map z) := by
      rw [← hz]
      change φ (U (z : ℂ)) = φ (u.map z)
      exact congrArg φ (hUeq z)
    have hinward : diskMapInwardConormal (g' t₀) U' ζ =
        (mfderiv I 𝓘(ℝ, E) (⇑φ) (u.map z)) (u.inwardConormal (g t₀) z) := by
      rw [← hz]
      exact (SmoothDisk.inwardConormal_eq_diskMapInwardConormal (E := E) (Q := c.Q)
          (SmoothDisk.compDiffeomorph φ u) (g' t₀) hw z).symm.trans
        (SmoothDisk.inwardConormal_comp_diffeomorph (E := E) (A := c.Q) φ (g t₀) u z)
    have hspeed : u.boundarySpeed (g t₀) x =
        Real.sqrt (diskMapConformalCoefficient (g' t₀) U' ζ) * (2 * Real.pi) := by
      rw [← SmoothDisk.boundarySpeed_comp_diffeomorph (E := E) (A := c.Q) φ (g t₀) u x]
      rw [mul_comm]
      exact SmoothDisk.boundarySpeed_eq_diskMapConformalCoefficient (E := E) (Q := c.Q)
        (SmoothDisk.compDiffeomorph φ u) (g' t₀) hw x hconfz
    have hV : (u.isotopyVelocity Phi T t₀ hid) z =
        mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) t₀ 1 := by
      change mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) T t₀ 1 = _
      rw [mfderivWithin_of_mem_nhds (hT.mem_nhds hT₀)]
    have hpair : (g' t₀).inner (U' ζ)
          (show TangentSpace 𝓘(ℝ, E) (U' ζ) from
            mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => Φ' r (U' ζ)) t₀ 1)
          (diskMapInwardConormal (g' t₀) U' ζ) =
        (g t₀).inner (u.map z) ((u.isotopyVelocity Phi T t₀ hid) z)
          (u.inwardConormal (g t₀) z) := by
      change (DifferentialGeometry.Diffeomorph.pullbackMetricCross (g t₀) φ.symm).inner (U' ζ)
          (show TangentSpace 𝓘(ℝ, E) (U' ζ) from
            mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => Φ' r (U' ζ)) t₀ 1)
          (diskMapInwardConormal (g' t₀) U' ζ) = _
      rw [hUi, hinward]
      have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) t₀ := by
        have hbase : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
            (u.map z, t₀) :=
          hPhi.contMDiffAt ((isOpen_univ.prod hT).mem_nhds ⟨trivial, hT₀⟩)
        exact (hbase.mdifferentiableAt (by simp)).comp t₀
          (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
      have hcomp := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, E)) t₀
        (f := fun r : ℝ => Phi r (u.map z)) (g := (⇑φ : Q → c.Q))
        (φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hdiff
      rw [show (Phi t₀) (u.map z) = u.map z from hid (u.map z)] at hcomp
      have hchain : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
            ((⇑φ : Q → c.Q) ∘ (fun r : ℝ => Phi r (u.map z))) t₀ 1 =
          mfderiv I 𝓘(ℝ, E) (⇑φ) (u.map z)
            (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) t₀ 1) :=
        congrArg (fun L => L 1) hcomp
      have hfun : (fun r : ℝ => Φ' r (φ (u.map z))) =
          (⇑φ : Q → c.Q) ∘ (fun r : ℝ => Phi r (u.map z)) := by
        funext r
        simp only [Φ', Diffeomorph.coe_trans, Function.comp_apply, φ.symm_apply_apply]
      have hvel : (show TangentSpace 𝓘(ℝ, E) (φ (u.map z)) from
            mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => Φ' r (φ (u.map z))) t₀ 1) =
          mfderiv I 𝓘(ℝ, E) (⇑φ) (u.map z)
            (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) t₀ 1) := by
        rw [hfun]
        exact hchain
      rw [hvel, DifferentialGeometry.Diffeomorph.inner_pullbackMetricCross_comp (g t₀) φ
        (u.map z) (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) t₀ 1)
        (u.inwardConormal (g t₀) z)]
      rw [hV]
    dsimp only [b']
    rw [hpair, SmoothDisk.boundaryFluxDensity, hspeed]
    ring
  have hper : Function.Periodic b' (2 * Real.pi) := by
    intro θ
    simp only [b']
    rw [periodic_circleMap 0 1 θ]
  have hFluxInt : (∫ θ in -Real.pi..Real.pi, b' θ) =
      u.boundaryFlux (g t₀) (u.isotopyVelocity Phi T t₀ hid) := by
    rw [SmoothDisk.boundaryFlux]
    have hshift : (∫ θ in -Real.pi..Real.pi, b' θ) = ∫ θ in (0 : ℝ)..2 * Real.pi, b' θ := by
      have h := hper.intervalIntegral_add_eq (-Real.pi) 0
      have h1 : -Real.pi + 2 * Real.pi = Real.pi := by ring
      have h2 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
      simpa only [h1, h2] using h
    have hscale : (∫ x in (0 : ℝ)..1, b' (2 * Real.pi * x) * (2 * Real.pi)) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, b' θ := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_comp_mul_left (b') (by positivity : (2 * Real.pi) ≠ 0)]
      simp only [mul_zero, mul_one, smul_eq_mul]
      have h2pi : ((2 * Real.pi)⁻¹ *
          ∫ (x : ℝ) in (0 : ℝ)..2 * Real.pi, b' x) * (2 * Real.pi) =
          ∫ (x : ℝ) in (0 : ℝ)..2 * Real.pi, b' x := by
        field_simp
      rw [h2pi]
    rw [hshift, ← hscale]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    exact hfluxPt x
  have hFluxHint : IntervalIntegrable
      (u.boundaryFluxDensity (g t₀) (u.isotopyVelocity Phi T t₀ hid)) volume 0 1 := by
    have hper1 : Function.Periodic (fun x : ℝ => b' (2 * Real.pi * x)) 1 := by
      intro x
      have h := hper (2 * Real.pi * x)
      simpa only [mul_add, mul_one] using h
    have h3 : IntervalIntegrable (fun x : ℝ => b' (2 * Real.pi * x)) volume
        (-Real.pi / (2 * Real.pi)) (Real.pi / (2 * Real.pi)) :=
      hfl.comp_mul_left (c := 2 * Real.pi)
    have h2 : IntervalIntegrable (fun x : ℝ => b' (2 * Real.pi * x)) volume (-1 / 2) (1 / 2) := by
      have hp : -Real.pi / (2 * Real.pi) = (-1 / 2 : ℝ) := by
        field_simp
      have hq : Real.pi / (2 * Real.pi) = (1 / 2 : ℝ) := by
        field_simp
      rwa [hp, hq] at h3
    have h2' : IntervalIntegrable (fun x : ℝ => b' (2 * Real.pi * x)) volume (-1 / 2) (-1 / 2 + 1) := by
      have he : (-1 / 2 + 1 : ℝ) = 1 / 2 := by norm_num
      rw [he]
      exact h2
    have h4 : IntervalIntegrable (fun x : ℝ => b' (2 * Real.pi * x)) volume (0 : ℝ) 1 := by
      have h := (hper1.intervalIntegrable_iff (t₁ := (-1 / 2 : ℝ)) (t₂ := 0)).mp h2'
      simpa using h
    have h6 : IntervalIntegrable (fun x : ℝ => b' (2 * Real.pi * x) * (2 * Real.pi)) volume 0 1 :=
      h4.mul_const _
    refine h6.congr (fun x _ => ?_)
    exact hfluxPt x
  rw [hLHS] at hderiv'
  rw [hDensInt, hFluxInt] at hderiv'
  exact ⟨hintDensity, hFluxHint, hderiv'⟩



omit hSigma in
theorem rfs_plateau_upper_comparison_of_minimizingDiskCompetitor
    (c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (gamma t : Surgery.Topology.Circle → Q))
    (himm : ∀ t ∈ Icc a b, ∀ x, loopVelocity (I := I) (gamma t).toContinuousLoop x ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop (gamma t₀).toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma t₀ (sigma.map theta))
    (hconformal : u.IsConformal (W.family.metric t₀))
    (hharmonic : u.IsHarmonic (W.family.metric t₀))
    (hmin : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.1.map)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta) :
    let V := u.isotopyVelocity Phi (Icc a b) t₀ hid
    let metricTerm := u.metricVariationDensity W.family.metric (Icc a b) t₀
    let variation := (1 / 2 : ℝ) *
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension metricTerm z) -
        u.boundaryFlux (W.family.metric t₀) V
    IntegrableOn (diskExtension metricTerm) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryFluxDensity (W.family.metric t₀) V) volume 0 1 ∧
      (∀ t ∈ Icc a b,
        loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t ≤
          u.transportedArea W.family.metric Phi t) ∧
      loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀ =
        u.transportedArea W.family.metric Phi t₀ ∧
      HasDerivWithinAt (u.transportedArea W.family.metric Phi) variation (Icc a b) t₀ ∧
      ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, t₀ + h ≤ b →
        (loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) (t₀ + h) -
          loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀) / h ≤
            variation + epsilon := by
  have ht₀Ico : t₀ ∈ Ico a b := ⟨ht₀.1.le, ht₀.2⟩
  have hreg : D.regular ∈ 𝓝 t₀ :=
    D.regular_isOpen.mem_nhds (W.regular ⟨ht₀.1.le, ht₀.2.le⟩)
  have hφIoo : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Ioo a b) :=
    hPhi.mono (Set.prod_mono Subset.rfl Ioo_subset_Icc_self)
  obtain ⟨hIntIoo, hFluxIoo, hDerivIoo⟩ :=
    SmoothDisk.hasDerivAt_transportedArea_isotopy_flux c W.smooth hreg u hconformal hharmonic
      isOpen_Ioo ht₀ Phi hφIoo hid
  have hvel : u.isotopyVelocity Phi (Icc a b) t₀ hid =
      u.isotopyVelocity Phi (Ioo a b) t₀ hid := by
    funext z
    change mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) (Icc a b) t₀ 1 =
      mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) (Ioo a b) t₀ 1
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr ⟨ht₀.1, ht₀.2⟩),
      mfderivWithin_of_mem_nhds (Ioo_mem_nhds ht₀.1 ht₀.2)]
  have hdiff₁ (z : Disk) : DifferentiableAt ℝ (fun t : ℝ =>
      (W.family.metric t).inner (u.map z) (u.differential z (1 : ℂ))
        (u.differential z (1 : ℂ))) t₀ :=
    ((W.smooth.coeff (u.map z) (u.differential z (1 : ℂ)) (u.differential z (1 : ℂ))).contDiffAt
      hreg).differentiableAt (by simp)
  have hdiff₂ (z : Disk) : DifferentiableAt ℝ (fun t : ℝ =>
      (W.family.metric t).inner (u.map z) (u.differential z Complex.I)
        (u.differential z Complex.I)) t₀ :=
    ((W.smooth.coeff (u.map z) (u.differential z Complex.I) (u.differential z Complex.I)).contDiffAt
      hreg).differentiableAt (by simp)
  have hdensInt : (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric (Ioo a b) t₀) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z := by
    refine setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
    rw [show diskExtension (u.metricVariationDensity W.family.metric (Ioo a b) t₀) z =
        u.metricVariationDensity W.family.metric (Ioo a b) t₀ ⟨z, hz⟩ from dite_eq_left hz,
      show diskExtension (u.metricVariationDensity W.family.metric (Icc a b) t₀) z =
        u.metricVariationDensity W.family.metric (Icc a b) t₀ ⟨z, hz⟩ from dite_eq_left hz]
    simp only [SmoothDisk.metricVariationDensity]
    split_ifs with hpos
    · rw [derivWithin_of_mem_nhds (Ioo_mem_nhds ht₀.1 ht₀.2),
        derivWithin_of_mem_nhds (Ioo_mem_nhds ht₀.1 ht₀.2),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀Ico (hdiff₁ ⟨z, hz⟩),
        derivWithin_Icc_eq_deriv_of_mem_Ico ht₀Ico (hdiff₂ ⟨z, hz⟩)]
    · rfl
  refine rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_transportedAreaDeriv
    W t₀ ht₀Ico gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic hmin Phi hPhi hid
    hboundary (SmoothDisk.integrableOn_diskExtension_metricVariationDensity c W ht₀Ico u hconformal)
    ?_ ?_
  · rw [hvel]
    exact hFluxIoo
  · have hb : HasDerivWithinAt (u.transportedArea W.family.metric Phi)
        ((1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity W.family.metric (Ioo a b) t₀) z) -
          u.boundaryFlux (W.family.metric t₀) (u.isotopyVelocity Phi (Ioo a b) t₀ hid))
        (Icc a b) t₀ := hDerivIoo.hasDerivWithinAt
    convert hb using 1
    rw [hdensInt, hvel]

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end

section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [hT2 : T2Space Q] [hCompact : CompactSpace Q] [hSigma : SigmaCompactSpace Q]
  [hBoundary : I.Boundaryless]

variable {g : ℝ → SmoothRiemannianMetric I Q} {D : RealTimeInterval}
  {hG : MetricFamilySmoothOn D g} {t₀ : ℝ}

omit hSigma in
theorem SmoothDisk.hasDerivWithinAt_transportedArea_isotopy_flux_on_Icc
    (c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    (hG : MetricFamilySmoothOn D g)
    (u : SmoothDisk (I := I) (Q := Q))
    (hconf : u.IsConformal (g t₀)) (hharm : u.IsHarmonic (g t₀))
    {a b : ℝ} (hT₀ : t₀ ∈ Ico a b) (hreg : Icc a b ⊆ D.regular)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ (Icc a b)))
    (hid : ∀ q, Phi t₀ q = q) :
    IntegrableOn (diskExtension (u.metricVariationDensity g (Icc a b) t₀))
        (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryFluxDensity (g t₀) (u.isotopyVelocity Phi (Icc a b) t₀ hid))
        volume 0 1 ∧
      HasDerivWithinAt (u.transportedArea g Phi)
        ((1 / 2 : ℝ) *
          (∫ z in Metric.closedBall (0 : ℂ) 1,
            diskExtension (u.metricVariationDensity g (Icc a b) t₀) z) -
          u.boundaryFlux (g t₀) (u.isotopyVelocity Phi (Icc a b) t₀ hid)) (Icc a b) t₀ := by
  have hab : a < b := lt_of_le_of_lt hT₀.1 hT₀.2
  have ht₀ : D.regular ∈ 𝓝 t₀ := D.regular_isOpen.mem_nhds (hreg ⟨hT₀.1, hT₀.2.le⟩)
  obtain ⟨hintDensity, hderivMetric⟩ :=
    SmoothDisk.hasDerivAt_diskArea_metricFamily_of_uniqueDiffWithinAt (I := I) (Q := Q) (hG := hG) c u g (Icc a b) ht₀
      (uniqueDiffOn_Icc hab t₀ ⟨hT₀.1, hT₀.2.le⟩) hconf
  obtain ⟨U, hUeq, N, hN, hDN, hUN⟩ :=
    SmoothDisk.exists_smoothExtension (I := I) (Q := Q) (hne := ⟨u.map diskCenter⟩) u
  let φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ c.Q := c.equiv
  let g' : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) c.Q :=
    fun t => DifferentialGeometry.Diffeomorph.pullbackMetricCross (g t) φ.symm
  have hg' : MetricFamilySmoothOn D g' :=
    MetricFamilySmoothOn.of_pullback hG g' (fun x => φ.symm x) φ.symm.contMDiff
      (fun t x v w => DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner (g t) φ.symm x v w)
  let U' : ℂ → c.Q := fun z => φ (U z)
  have hU'sm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U' N := φ.contMDiff.comp_contMDiffOn hUN
  let u' : C(Metric.closedBall (0 : ℂ) 1, c.Q) :=
    ⟨fun z => U' (z : ℂ), (hU'sm.mono hDN).continuousOn.domRestrict⟩
  have hExt' : Geometry.SmoothDiskExtension (E := E) u' U' := ⟨fun _ => rfl, N, hN, hDN, hU'sm⟩
  have hu'eq : ∀ z : Disk, U' (z : ℂ) = (SmoothDisk.compDiffeomorph φ u).map z := by
    intro z
    simp only [U', SmoothDisk.comp_diffeomorph_map]
    rw [hUeq z]
  have hw : Geometry.SmoothDiskExtension (E := E) (SmoothDisk.compDiffeomorph φ u).map U' :=
    ⟨fun z => (hu'eq z).symm ▸ rfl, N, hN, hDN, hU'sm⟩
  have hwconf : (SmoothDisk.compDiffeomorph φ u).IsConformal (g' t₀) :=
    SmoothDisk.isConformal_comp_diffeomorph φ (g t₀) u hconf
  have hconf' : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (g' t₀) U' z :=
    (SmoothDisk.isConformal_iff_diskMapConformalAt (SmoothDisk.compDiffeomorph φ u)
      (g' t₀) hw).mp hwconf
  have hwharm : (SmoothDisk.compDiffeomorph φ u).IsHarmonic (g' t₀) :=
    SmoothDisk.isHarmonic_comp_diffeomorph φ (g t₀) u hharm
  have hharm' : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension (g' t₀) U' z = 0 := by
    intro z hz
    have h1 : (diskMapTension (g' t₀) (diskExtension (SmoothDisk.compDiffeomorph φ u).map) z : E)
        = 0 :=
      SmoothDisk.diskMapTension_eq_zero_of_isHarmonic_interior
        (SmoothDisk.compDiffeomorph φ u) (g' t₀) hwharm hz
    have hmem : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
    have hgerm : (diskExtension (SmoothDisk.compDiffeomorph φ u).map) =ᶠ[𝓝 z] U' := by
      filter_upwards [hmem] with w hw'
      rw [diskExtension_coe _ ⟨w, hw'⟩]
      exact (hu'eq ⟨w, hw'⟩).symm
    rw [← diskMapTension_congr_of_eventuallyEq (g' t₀) hgerm]
    exact h1
  let Φ' : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) c.Q c.Q ∞ :=
    fun t => (φ.symm.trans (Phi t)).trans φ
  have hΦ'id : Φ' t₀ = Diffeomorph.refl 𝓘(ℝ, E) c.Q ∞ := by
    ext y
    simp only [Φ', Diffeomorph.coe_trans, Function.comp_apply]
    rw [hid (φ.symm y), φ.apply_symm_apply]
    rfl
  have hΦ'sm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × c.Q => Φ' p.1 p.2) ((Icc a b) ×ˢ univ) := by
    intro p hp
    have hψ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ℝ × c.Q => (φ.symm q.2, q.1)) p := by
      rw [contMDiffAt_prod_iff]
      exact ⟨φ.symm.contMDiff.contMDiffAt.comp p contMDiffAt_snd, contMDiffAt_fst⟩
    have hx : (φ.symm p.2, p.1) ∈ (univ : Set Q) ×ˢ (Icc a b) := ⟨trivial, hp.1⟩
    have hbase := hPhi _ hx
    have h1 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
        (fun q : ℝ × c.Q => Phi q.1 (φ.symm q.2)) (Icc a b ×ˢ univ) p :=
      hbase.comp (f := fun q : ℝ × c.Q => (φ.symm q.2, q.1)) p
        (hψ.contMDiffWithinAt (s := Icc a b ×ˢ univ))
        (show MapsTo (fun q : ℝ × c.Q => (φ.symm q.2, q.1))
          (Icc a b ×ˢ univ) (univ ×ˢ Icc a b) from fun q hq => ⟨trivial, hq.1⟩)
    exact φ.contMDiff.contMDiffAt.comp_contMDiffWithinAt p h1
  obtain ⟨hintDens', hintFlux', hderiv'⟩ :=
    SmoothDiskExtension.hasDerivWithinAt_area_isotopy_flux_on_Icc (u := u') (U := U') hExt' hg' hT₀ hreg hΦ'sm hΦ'id hconf' hharm'
  let b' : ℝ → ℝ := fun θ =>
    (g' t₀).inner (U' (circleMap 0 1 θ))
      (show TangentSpace 𝓘(ℝ, E) (U' (circleMap 0 1 θ)) from
        mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ' r (U' (circleMap 0 1 θ))) (Icc a b) t₀ 1)
      (diskMapInwardConormal (g' t₀) U' (circleMap 0 1 θ)) *
      Real.sqrt (diskMapConformalCoefficient (g' t₀) U' (circleMap 0 1 θ))
  have hfl : IntervalIntegrable b' volume (-Real.pi) Real.pi := hintFlux'
  have hLHS : (fun t => riemannianDiskArea (g' t)
        ((⟨Φ' t, (Φ' t).contMDiff.continuous⟩ : C(c.Q, c.Q)).comp u')) =
      u.transportedArea g Phi := by
    funext t
    rw [SmoothDisk.transportedArea]
    have h1 : (⇑((⟨Φ' t, (Φ' t).contMDiff.continuous⟩ : C(c.Q, c.Q)).comp u') : Disk → c.Q) =
        fun z : Disk => Φ' t (U' z) := by
      funext z
      rfl
    have h2 : ∀ z : Disk, φ.symm (Φ' t (U' (z : ℂ))) = Phi t (u.map z) := by
      intro z
      have hs : φ.symm (U' (z : ℂ)) = u.map z := by
        change φ.symm (φ (U (z : ℂ))) = u.map z
        rw [φ.symm_apply_apply, hUeq z]
      have hΦ : Φ' t (U' (z : ℂ)) = φ (Phi t (u.map z)) := by
        simp only [Φ', Diffeomorph.coe_trans, Function.comp_apply, hs]
      rw [hΦ, φ.symm_apply_apply]
    rw [h1, ← diskArea_eq_riemannianDiskArea (g' t) (fun z : Disk => Φ' t (U' (z : ℂ))),
      diskArea_pullbackMetricCross (g t) φ.symm (fun z : Disk => Φ' t (U' (z : ℂ)))]
    rw [show (fun z : Disk => φ.symm (Φ' t (U' (z : ℂ)))) =
      (fun z : Disk => Phi t (u.map z)) from funext h2]
  have hfunFix : (fun t => riemannianDiskArea (g' t) (⇑u')) = fun t => diskArea (g t) u.map := by
    funext t
    have h1 : (⇑u' : Disk → c.Q) = fun z : Disk => φ (u.map z) := by
      funext z
      change U' (z : ℂ) = φ (u.map z)
      rw [show U' (z : ℂ) = φ (U (z : ℂ)) from rfl, hUeq z]
    rw [h1, ← diskArea_eq_riemannianDiskArea (g' t) (fun z : Disk => φ (u.map z)),
      diskArea_pullbackMetricCross (g t) φ.symm (fun z : Disk => φ (u.map z))]
    rw [show (fun z : Disk => φ.symm (φ (u.map z))) = (fun z : Disk => u.map z) from by
      funext z
      rw [φ.symm_apply_apply]]
  have hDensInt : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity g' t₀ U' z) =
      (1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity g (Icc a b) t₀) z) := by
    have ha : HasDerivAt (fun t => riemannianDiskArea (g' t) (⇑u'))
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapMetricVariationDensity g' t₀ U' z) t₀ :=
      (SmoothDiskExtension.hasDerivAt_area_metric (u := u') (U := U') hExt' hg' ht₀ hconf').2
    have hb : HasDerivAt (fun t => riemannianDiskArea (g' t) (⇑u'))
        ((1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
          diskExtension (u.metricVariationDensity g (Icc a b) t₀) z)) t₀ := by
      rw [hfunFix]
      exact hderivMetric
    exact ha.unique hb
  have hfluxPt : ∀ x : ℝ, b' (2 * Real.pi * x) * (2 * Real.pi) =
      u.boundaryFluxDensity (g t₀) (u.isotopyVelocity Phi (Icc a b) t₀ hid) x := by
    intro x
    set z : Disk := diskBoundary (x : Surgery.Topology.Circle) with hzdef
    set ζ : ℂ := circleMap 0 1 (2 * Real.pi * x) with hζdef
    have hmem : ζ ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [hζdef]
      exact circleMap_mem_closedBall 0 (by norm_num) _
    have hz : (z : ℂ) = ζ := by
      rw [hzdef, hζdef]
      have h := diskBoundary_angle (2 * Real.pi * x)
      rwa [mul_div_cancel_left₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at h
    have hconfz := hconf' ζ hmem
    have hUi : U' ζ = φ (u.map z) := by
      rw [← hz]
      change φ (U (z : ℂ)) = φ (u.map z)
      exact congrArg φ (hUeq z)
    have hinward : diskMapInwardConormal (g' t₀) U' ζ =
        (mfderiv I 𝓘(ℝ, E) (⇑φ) (u.map z)) (u.inwardConormal (g t₀) z) := by
      rw [← hz]
      exact (SmoothDisk.inwardConormal_eq_diskMapInwardConormal (E := E) (Q := c.Q)
          (SmoothDisk.compDiffeomorph φ u) (g' t₀) hw z).symm.trans
        (SmoothDisk.inwardConormal_comp_diffeomorph (E := E) (A := c.Q) φ (g t₀) u z)
    have hspeed : u.boundarySpeed (g t₀) x =
        Real.sqrt (diskMapConformalCoefficient (g' t₀) U' ζ) * (2 * Real.pi) := by
      rw [← SmoothDisk.boundarySpeed_comp_diffeomorph (E := E) (A := c.Q) φ (g t₀) u x]
      rw [mul_comm]
      exact SmoothDisk.boundarySpeed_eq_diskMapConformalCoefficient (E := E) (Q := c.Q)
        (SmoothDisk.compDiffeomorph φ u) (g' t₀) hw x hconfz
    have hV : (u.isotopyVelocity Phi (Icc a b) t₀ hid) z =
        mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) (Icc a b) t₀ 1 := rfl
    have hpair : (g' t₀).inner (U' ζ)
          (show TangentSpace 𝓘(ℝ, E) (U' ζ) from
            mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => Φ' r (U' ζ)) (Icc a b) t₀ 1)
          (diskMapInwardConormal (g' t₀) U' ζ) =
        (g t₀).inner (u.map z) ((u.isotopyVelocity Phi (Icc a b) t₀ hid) z)
          (u.inwardConormal (g t₀) z) := by
      change (DifferentialGeometry.Diffeomorph.pullbackMetricCross (g t₀) φ.symm).inner (U' ζ)
          (show TangentSpace 𝓘(ℝ, E) (U' ζ) from
            mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => Φ' r (U' ζ)) (Icc a b) t₀ 1)
          (diskMapInwardConormal (g' t₀) U' ζ) = _
      rw [hUi, hinward]
      have hdiff : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I
          (fun r : ℝ => Phi r (u.map z)) (Icc a b) t₀ := by
        have hbase := hPhi (u.map z, t₀) ⟨trivial, hT₀.1, hT₀.2.le⟩
        exact ((hbase.comp t₀
          (contMDiffWithinAt_const.prodMk contMDiffWithinAt_id)
          (fun r hr => ⟨trivial, hr⟩)).mdifferentiableWithinAt (by simp))
      have hcomp := mfderiv_comp_mfderivWithin (I := 𝓘(ℝ, ℝ)) (I' := I)
        (I'' := 𝓘(ℝ, E)) t₀
        (f := fun r : ℝ => Phi r (u.map z)) (g := (⇑φ : Q → c.Q))
        (φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hdiff
        (uniqueDiffOn_Icc hab t₀ ⟨hT₀.1, hT₀.2.le⟩).uniqueMDiffWithinAt
      rw [show (Phi t₀) (u.map z) = u.map z from hid (u.map z)] at hcomp
      have hchain : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
            ((⇑φ : Q → c.Q) ∘ (fun r : ℝ => Phi r (u.map z))) (Icc a b) t₀ 1 =
          mfderiv I 𝓘(ℝ, E) (⇑φ) (u.map z)
            (mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) (Icc a b) t₀ 1) :=
        congrArg (fun L => L 1) hcomp
      have hfun : (fun r : ℝ => Φ' r (φ (u.map z))) =
          (⇑φ : Q → c.Q) ∘ (fun r : ℝ => Phi r (u.map z)) := by
        funext r
        simp only [Φ', Diffeomorph.coe_trans, Function.comp_apply, φ.symm_apply_apply]
      have hvel : (show TangentSpace 𝓘(ℝ, E) (φ (u.map z)) from
            mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => Φ' r (φ (u.map z))) (Icc a b) t₀ 1) =
          mfderiv I 𝓘(ℝ, E) (⇑φ) (u.map z)
            (mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) (Icc a b) t₀ 1) := by
        rw [hfun]
        exact hchain
      rw [hvel, DifferentialGeometry.Diffeomorph.inner_pullbackMetricCross_comp (g t₀) φ
        (u.map z) (mfderivWithin 𝓘(ℝ, ℝ) I (fun r : ℝ => Phi r (u.map z)) (Icc a b) t₀ 1)
        (u.inwardConormal (g t₀) z)]
      rw [hV]
    dsimp only [b']
    rw [hpair, SmoothDisk.boundaryFluxDensity, hspeed]
    ring
  have hper : Function.Periodic b' (2 * Real.pi) := by
    intro θ
    simp only [b']
    rw [periodic_circleMap 0 1 θ]
  have hFluxInt : (∫ θ in -Real.pi..Real.pi, b' θ) =
      u.boundaryFlux (g t₀) (u.isotopyVelocity Phi (Icc a b) t₀ hid) := by
    rw [SmoothDisk.boundaryFlux]
    have hshift : (∫ θ in -Real.pi..Real.pi, b' θ) = ∫ θ in (0 : ℝ)..2 * Real.pi, b' θ := by
      have h := hper.intervalIntegral_add_eq (-Real.pi) 0
      have h1 : -Real.pi + 2 * Real.pi = Real.pi := by ring
      have h2 : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
      simpa only [h1, h2] using h
    have hscale : (∫ x in (0 : ℝ)..1, b' (2 * Real.pi * x) * (2 * Real.pi)) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, b' θ := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_comp_mul_left (b') (by positivity : (2 * Real.pi) ≠ 0)]
      simp only [mul_zero, mul_one, smul_eq_mul]
      have h2pi : ((2 * Real.pi)⁻¹ *
          ∫ (x : ℝ) in (0 : ℝ)..2 * Real.pi, b' x) * (2 * Real.pi) =
          ∫ (x : ℝ) in (0 : ℝ)..2 * Real.pi, b' x := by
        field_simp
      rw [h2pi]
    rw [hshift, ← hscale]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    exact hfluxPt x
  have hFluxHint : IntervalIntegrable
      (u.boundaryFluxDensity (g t₀) (u.isotopyVelocity Phi (Icc a b) t₀ hid)) volume 0 1 := by
    have hper1 : Function.Periodic (fun x : ℝ => b' (2 * Real.pi * x)) 1 := by
      intro x
      have h := hper (2 * Real.pi * x)
      simpa only [mul_add, mul_one] using h
    have h3 : IntervalIntegrable (fun x : ℝ => b' (2 * Real.pi * x)) volume
        (-Real.pi / (2 * Real.pi)) (Real.pi / (2 * Real.pi)) :=
      hfl.comp_mul_left (c := 2 * Real.pi)
    have h2 : IntervalIntegrable (fun x : ℝ => b' (2 * Real.pi * x)) volume (-1 / 2) (1 / 2) := by
      have hp : -Real.pi / (2 * Real.pi) = (-1 / 2 : ℝ) := by
        field_simp
      have hq : Real.pi / (2 * Real.pi) = (1 / 2 : ℝ) := by
        field_simp
      rwa [hp, hq] at h3
    have h2' : IntervalIntegrable (fun x : ℝ => b' (2 * Real.pi * x)) volume (-1 / 2) (-1 / 2 + 1) := by
      have he : (-1 / 2 + 1 : ℝ) = 1 / 2 := by norm_num
      rw [he]
      exact h2
    have h4 : IntervalIntegrable (fun x : ℝ => b' (2 * Real.pi * x)) volume (0 : ℝ) 1 := by
      have h := (hper1.intervalIntegrable_iff (t₁ := (-1 / 2 : ℝ)) (t₂ := 0)).mp h2'
      simpa using h
    have h6 : IntervalIntegrable (fun x : ℝ => b' (2 * Real.pi * x) * (2 * Real.pi)) volume 0 1 :=
      h4.mul_const _
    refine h6.congr (fun x _ => ?_)
    exact hfluxPt x
  rw [hLHS] at hderiv'
  rw [hDensInt, hFluxInt] at hderiv'
  exact ⟨hintDensity, hFluxHint, hderiv'⟩



end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end

end
