import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageScalarRayCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedComponentCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedBallFootprintCXSP
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Curves
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar

set_option autoImplicit false

/-!
# CX-SPINE：实际原 stage escape 数据组装 scalar-blowup ray

每条新段连接本 stage 的 anchor 与本次 scalar-escape 点 z。
原 p 到旧坏点的段不参与本构造。
紧 stage 的 finite-edist component 生产真实 minimizing segment，允许退化长度零。
公共 Curves:355 生产 ray；公共 Scalar:172 从 inverse convergence
生产逐点 scalar 收敛。
同 Awork 的整段包含由 anchor-seed 距离、ell -> rho 和明确 fit margin 证明。
最后调用 P6StageScalarRay 的 IVT/canonical-radius 论证，不索取 Good/Dt/gradient。
所有几何都在原 history 的实际查询 stage 上，包括 birth/horizon。
Awork 为本次 TimeCore 与 seed-volume 参数；没有查询或扩大 kappa window。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private theorem stage_segment_of_finite_edist_CXSP
    (P : OrientedThreeStage.{u}) (g : P.Metric) (x y : P.Carrier)
    (hfinite : riemannianEDistOf g x y ≠ ⊤) :
    let ell := (riemannianEDistOf g x y).toReal
    ∃ γ : ℝ → P.Carrier, γ 0 = x ∧ γ ell = y ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
      ∀ v ∈ Icc (0 : ℝ) ell, ∀ w ∈ Icc (0 : ℝ) ell,
        riemannianEDistOf g (γ v) (γ w) = ENNReal.ofReal |v - w| := by
  classical
  intro ell
  by_cases hxy : x = y
  · subst y
    have he : ell = 0 := by
      dsimp only [ell]
      rw [riemannianEDistOf_self, ENNReal.toReal_zero]
    refine ⟨fun _ => x, rfl, rfl, contMDiff_const, ?_⟩
    intro v hv w hw
    rw [he] at hv hw
    have hv0 : v = 0 := le_antisymm hv.2 hv.1
    have hw0 : w = 0 := le_antisymm hw.2 hw.1
    subst v w
    simp only [riemannianEDistOf_self, sub_self, abs_zero, ENNReal.ofReal_zero]
  · have hball : y ∈ riemannianBallOf g x (ell + 1) := by
      change riemannianEDistOf g x y < ENNReal.ofReal (ell + 1)
      calc
        _ = ENNReal.ofReal ell := (ENNReal.ofReal_toReal hfinite).symm
        _ < ENNReal.ofReal (ell + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by dsimp only [ell]; positivity)).mpr
            (lt_add_one _)
    obtain ⟨len, γ, hlen, _hshort, hzero, hend, hsmooth, _hcomponent, hmin⟩ :=
      exists_seed_segment_of_compact_CXSP g x y hball hxy
    have hd := hmin 0 ⟨le_rfl, hlen⟩ len ⟨hlen, le_rfl⟩
    rw [hzero, hend, zero_sub, abs_neg, abs_of_nonneg hlen] at hd
    have hlenEq : len = ell := by
      simpa only [ENNReal.toReal_ofReal hlen] using (congrArg ENNReal.toReal hd).symm
    subst len
    exact ⟨γ, hzero, hend, hsmooth, hmin⟩

/-- 实际 first-level metric convergence 与新 escape 点生产 scalar-blowup ray；
完整段的 Awork footprint 由明确 anchor/radius margin 实证。 -/
theorem exists_stage_escape_scalar_ray_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hcore : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime)
    (Awork : ℝ) (hA : 0 < Awork) (idx : ℕ → ℕ)
    (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).horizon)
    (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
    (r : ℕ → ℝ) (htime : ∀ i, 2 * r i ^ 2 < (t i : ℝ))
    (hsmall : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory
      (t i) (p i) (r i))
    (hvol : ∀ i, ENNReal.ofReal (Awork⁻¹ * r i ^ 3) ≤ ballVolume
      ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i))
    (htlim : Tendsto (fun i => (t i : ℝ)) atTop atTop)
    (Hbase : ℝ) (hHbase : 0 < Hbase) (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    (hscale : ∀ i, Q i * r i ^ 2 = Hbase)
    (dAnchor : ℝ) (hdAnchor : 0 ≤ dAnchor)
    (hanchor : ∀ i, riemannianEDistOf
      ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i))
      (p i) (anchor i) ≤ ENNReal.ofReal (dAnchor * r i))
    (rho : ℝ) (hrho : 0 < rho)
    (hfit : dAnchor + (rho + 1) / Real.sqrt Hbase < Awork) :
    let stage := fun i => (F.tower.history (idx i)).toHistory.stageAt (t i)
    let metric := fun i => (F.tower.history (idx i)).toHistory.stageMetric
      ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun i =>
          { M := (stage i).Carrier
            basepoint := anchor i
            metric := scaleMetric (Q i) (hQ i) (metric i) } }
    ∀ (σ : ℕ → ℕ), StrictMono σ →
    ∀ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
      (maps : PointedRiemannianConvergenceMaps X Pl σ)
      (M : MetricConvergenceData maps),
      (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
    ∀ rad : ℕ → ℝ, (∀ n, 0 < rad n) → Tendsto rad atTop (𝓝 rho) →
      (∀ n, riemannianClosedBallOf (X.obj (σ n)).metric
        (X.obj (σ n)).basepoint (rad n) ⊆ maps.target n) →
      (∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop, ∀ y ∈ maps.source n,
        ∀ v : TangentSpace ThreeModel y,
          (1 - eta) * Pl.metric.inner y v v ≤
            (X.obj (σ n)).metric.inner (maps.map n y)
              (mfderiv ThreeModel ThreeModel (maps.map n) y v)
              (mfderiv ThreeModel ThreeModel (maps.map n) y v)) →
      (∀ R : ℝ, 0 ≤ R → R < rho →
        IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) →
      (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) →
    ∀ z : ∀ n, (stage (σ n)).Carrier,
      (∀ n, riemannianEDistOf (X.obj (σ n)).metric (anchor (σ n)) (z n) ≠ ⊤) →
      Tendsto (fun n =>
        (riemannianEDistOf (X.obj (σ n)).metric (anchor (σ n)) (z n)).toReal)
        atTop (𝓝 rho) →
      Tendsto (fun n => metricScalarAt (metric (σ n)) (z n) / Q (σ n)) atTop atTop →
    let _ : EMetricSpace Pl.M := Pl.emetricSpace
    ∃ (ell : ℕ → ℝ) (γ : ∀ n, ℝ → (stage (σ n)).Carrier),
      (∀ n, ell n =
        (riemannianEDistOf (X.obj (σ n)).metric (anchor (σ n)) (z n)).toReal) ∧
      Tendsto ell atTop (𝓝 rho) ∧
      (∀ n, γ n 0 = anchor (σ n) ∧ γ n (ell n) = z n ∧
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (γ n)) ∧
      (∀ n, ∀ v ∈ Icc (0 : ℝ) (ell n), ∀ w ∈ Icc (0 : ℝ) (ell n),
        riemannianEDistOf (X.obj (σ n)).metric (γ n v) (γ n w) =
          ENNReal.ofReal |v - w|) ∧
      (∀ᶠ n in atTop, ∀ v ∈ Icc (0 : ℝ) (ell n),
        γ n v ∈ riemannianBallOf (metric (σ n)) (p (σ n)) (Awork * r (σ n))) ∧
    ∃ (φ : ℕ → ℕ) (ray : C(Ico (0 : ℝ) rho, Pl.M)), StrictMono φ ∧ Isometry ray ∧
      ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
      (∀ K : Set (Ico (0 : ℝ) rho), IsCompact K →
        TendstoUniformlyOn (fun n (v : Ico (0 : ℝ) rho) =>
          (maps.partialDiffeomorph (φ n)).symm (γ (φ n) v)) ray atTop K) ∧
      (∀ v : Ico (0 : ℝ) rho, ∀ᶠ n in atTop, γ (φ n) v ∈ maps.target (φ n)) ∧
      (∀ v : Ico (0 : ℝ) rho, Tendsto (fun n =>
        metricScalarAt (metric (σ (φ n))) (γ (φ n) v) / Q (σ (φ n)))
        atTop (𝓝 (metricScalarAt Pl.metric (ray v)))) ∧
      Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
        (cocompact Pl.M) ∧
      (∀ x : Pl.M, ¬ Tendsto ray
        (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 x)) ∧
      Tendsto (fun v => metricScalarAt Pl.metric (ray v))
        (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop := by
  classical
  intro stage metric X σ hσ Pl maps M hcanonical rad hrad hradlim
    htarget hlower hcompact hradial z hfinite hdist hhigh
  let ell := fun n =>
    (riemannianEDistOf (X.obj (σ n)).metric (anchor (σ n)) (z n)).toReal
  have hell : ∀ n, 0 ≤ ell n := fun _ => ENNReal.toReal_nonneg
  have helllim : Tendsto ell atTop (𝓝 rho) := hdist
  choose γ hstart hend hsmooth hmin using fun n =>
    stage_segment_of_finite_edist_CXSP (stage (σ n))
      (X.obj (σ n)).metric (anchor (σ n)) (z n) (hfinite n)
  have hsegment : ∀ᶠ n in atTop, ∀ v ∈ Icc (0 : ℝ) (ell n),
      γ n v ∈ riemannianBallOf (metric (σ n)) (p (σ n)) (Awork * r (σ n)) := by
    filter_upwards [helllim.eventually (Iio_mem_nhds (lt_add_one rho))] with n hn
    intro v hv
    have hd := hmin n 0 ⟨le_rfl, hell n⟩ v hv
    rw [hstart n, zero_sub, abs_neg, abs_of_nonneg hv.1] at hd
    have hball : γ n v ∈ riemannianClosedBallOf (X.obj (σ n)).metric
        (anchor (σ n)) (rho + 1) := by
      change riemannianEDistOf _ _ _ ≤ _
      rw [hd]
      exact ENNReal.ofReal_le_ofReal (hv.2.trans hn.le)
    have hphysical := hball
    change γ n v ∈ riemannianClosedBallOf
      (scaleMetric (Q (σ n)) (hQ (σ n)) (metric (σ n)))
      (anchor (σ n)) (rho + 1) at hphysical
    rw [scaled_seed_closedBall_eq_CXSP] at hphysical
    have hQeq : Q (σ n) = Hbase * (r (σ n) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, eq_div_iff (pow_ne_zero 2 (hsmall (σ n)).1.ne')]
      exact hscale (σ n)
    rw [hQeq] at hphysical
    have hb := seed_closedBall_distance_CXSP (metric (σ n)) hHbase (hsmall (σ n)).1
      (by linarith : 0 ≤ rho + 1) hdAnchor le_rfl (hanchor (σ n)) _ hphysical
    exact hb.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (mul_pos hA (hsmall (σ n)).1)).mpr (mul_lt_mul_of_pos_right hfit (hsmall (σ n)).1))
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hupper : ∀ K : Set Pl.M, IsCompact K → ∀ D : ℝ, 1 < D → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace ThreeModel x,
        (X.obj (σ n)).metric.inner (maps.partialDiffeomorph n x)
          (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v)
          (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v) ≤
            D ^ 2 * Pl.metric.inner x v v := by
    intro K hK D hD
    obtain ⟨N, hN⟩ := Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control
      M (fun n => by rw [hcanonical n]; rfl) K hK (D ^ 2 - 1) (by nlinarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x hx v
    have hh := (abs_le.mp ((hN n hn).2 x hx v)).2
    change (X.obj (σ n)).metric.inner (maps.partialDiffeomorph n x)
      (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v)
      (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v) -
        Pl.metric.inner x v v ≤ (D ^ 2 - 1) * Pl.metric.inner x v v at hh
    nlinarith
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  obtain ⟨φ, ray, hφ, hray, hbase, hconv, hescape, hmissing⟩ :=
    maps.exists_isometric_segment_subseq_limit_with_missing_endpoint hrho rad ell
      hrad hell hradlim helllim (fun n y hy => htarget n
        (show riemannianEDistOf _ _ _ ≤ _ from hy.le)) hlower hupper
      hcompact hradial γ (fun n => (hsmooth n).contMDiffOn.of_le (by simp)) hstart hmin
  have hstay (v : Ico (0 : ℝ) rho) : ∀ᶠ n in atTop, γ (φ n) v ∈ maps.target (φ n) := by
    filter_upwards [hφ.tendsto_atTop.eventually
      (hradlim.eventually_const_lt v.property.2), hφ.tendsto_atTop.eventually
      (helllim.eventually_const_lt v.property.2)] with n hn hn'
    apply htarget (φ n)
    change riemannianEDistOf (X.obj (σ (φ n))).metric
      (anchor (σ (φ n))) (γ (φ n) v) ≤ ENNReal.ofReal (rad (φ n))
    have hd := hmin (φ n) 0 ⟨le_rfl, hell (φ n)⟩ v ⟨v.property.1, hn'.le⟩
    rw [hstart, zero_sub, abs_neg, abs_of_nonneg v.property.1] at hd
    rw [hd]
    exact ENNReal.ofReal_le_ofReal hn.le
  let maps' := maps.compSubseq φ hφ
  have hcanonical' (n : ℕ) : (M.compSubseq φ hφ).domain n =
      CanonicalMetricCompactness.canonicalSourceData maps' n := by
    change (M.domain (φ n)).compSubseq φ hφ n = _
    rw [hcanonical (φ n)]
    rfl
  have hlimit (v : Ico (0 : ℝ) rho) : Tendsto (fun n =>
      metricScalarAt (metric (σ (φ n))) (γ (φ n) v) / Q (σ (φ n)))
      atTop (𝓝 (metricScalarAt Pl.metric (ray v))) := by
    have hh := pointedScalar_tendsto_of_inverse_tendsto (M.compSubseq φ hφ) hcanonical'
      (fun n => γ (φ n) v) (hstay v)
      ((hconv {v} isCompact_singleton).tendsto_at (mem_singleton v))
    convert hh using 1
    funext n
    change metricScalarAt (metric (σ (φ n))) (γ (φ n) v) / Q (σ (φ n)) =
      metricScalarAt (scaleMetric (Q (σ (φ n))) (hQ (σ (φ n)))
        (metric (σ (φ n)))) (γ (φ n) v)
    rw [metricScalarAt_scaleMetric, inv_mul_eq_div]
  refine ⟨ell, γ, fun _ => rfl, helllim, fun n =>
    ⟨hstart n, hend n, hsmooth n⟩, hmin, hsegment, φ, ray, hφ, hray, hbase,
    hconv, hstay, hlimit, hescape, hmissing, ?_⟩
  have hhigh' : Tendsto (fun n =>
      metricScalarAt (metric (σ n)) (γ n (ell n)) / Q (σ n)) atTop atTop := by
    convert hhigh using 1
    funext n
    rw [hend n]
  exact scalar_limit_tendsto_atTop_of_timeCore_segments_CXSP hcore Awork hA
    (fun n => idx (σ (φ n))) (fun n => t (σ (φ n))) (fun n => p (σ (φ n)))
    (fun n => r (σ (φ n))) (fun n => htime (σ (φ n)))
    (fun n => hsmall (σ (φ n))) (fun n => hvol (σ (φ n)))
    (htlim.comp (hσ.comp hφ).tendsto_atTop) Hbase hHbase
    (fun n => Q (σ (φ n))) (fun n => hQ (σ (φ n))) (fun n => hscale (σ (φ n)))
    rho hrho (fun n => ell (φ n)) (helllim.comp hφ.tendsto_atTop)
    (fun n => γ (φ n)) (fun n => (hsmooth (φ n)).continuous.continuousOn)
    (fun n => hmin (φ n)) (hφ.tendsto_atTop.eventually hsegment)
    (hhigh'.comp hφ.tendsto_atTop) (fun v => metricScalarAt Pl.metric (ray v)) hlimit

end GC.LongTime.Ch11

end
