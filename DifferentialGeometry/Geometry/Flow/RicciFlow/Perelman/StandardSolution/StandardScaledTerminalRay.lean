import DifferentialGeometry.Geometry.Metric.CurveScaling
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.SegmentScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalRay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardParabolicConvergence

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth PointedFlowData.t2
  PointedFlowData.sigmaCompact PointedFlowData.t2TangentBundle
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

private theorem exists_pointed_convergence_of_seq_eq
    (X Y : PointedRiemannianSeq (𝓡 3)) (h : X = Y)
    (L : PointedRiemannianManifold (𝓡 3)) (sigma : ℕ → ℕ)
    (F : PointedRiemannianConvergenceMaps Y L sigma)
    (C : PointedRiemannianConverges Y L sigma F)
    (hcanonical : ∀ n, C.metrics.domain n = CanonicalMetricCompactness.canonicalSourceData F n) :
    ∃ F' : PointedRiemannianConvergenceMaps X L sigma,
      ∃ C' : PointedRiemannianConverges X L sigma F',
        HEq F'.partialDiffeomorph F.partialDiffeomorph ∧
        ∀ n, C'.metrics.domain n = CanonicalMetricCompactness.canonicalSourceData F' n := by
  subst Y
  exact ⟨F, C, HEq.rfl, hcanonical⟩

theorem exists_standard_parabolic_isometric_segment_of_scalar_escape
    (B : ℝ) (hB : 0 < B)
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point y : ℕ → E3)
    {rho : ℝ} (hrho : 0 < rho)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1)
    (hscalar : ∀ r : ℝ, 0 < r → r < rho → ∃ A : ℝ, ∀ᶠ i in atTop,
      ∀ z ∈ riemannianClosedBallOf ((S i).metric (time i)) (point i) r,
        metricScalarAt ((S i).metric (time i)) z ≤ A)
    (hdistance : Tendsto (fun i => (riemannianEDistOf ((S i).metric (time i))
      (point i) (y i)).toReal) atTop (𝓝 rho))
    (hblowup : Tendsto (fun i => metricScalarAt ((S i).metric (time i)) (y i)) atTop atTop) :
    let X := standardParabolicSequence B hB S time point htime
    let Z := X.atTime 0
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ L : PointedRiemannianManifold (𝓡 3), ∃ _ : PathConnectedSpace L.M,
      ∃ maps : PointedRiemannianConvergenceMaps Z L sigma,
      ∃ C : PointedRiemannianConverges Z L sigma maps,
        (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData maps k) ∧
        (∀ r : ℝ, 0 ≤ r → r < Real.sqrt B * rho →
          IsCompact (riemannianClosedBallOf L.metric L.basepoint r)) ∧
        (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x <
          ENNReal.ofReal (Real.sqrt B * rho)) ∧
        (∀ (x : L.M) (v w : TangentSpace (𝓡 3) x),
          0 ≤ metricRm04StandardAt L.metric x v w w v) ∧
        let _ : EMetricSpace L.M := L.emetricSpace
        let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
          (fun x z => riemannianEDistOf_ne_top L.metric x z)
        ∃ (gamma : ∀ n, ℝ → (Z.obj (sigma n)).M) (ell : ℕ → ℝ)
          (g : C(Ico 0 (Real.sqrt B * rho), L.M)),
          Tendsto ell atTop (𝓝 (Real.sqrt B * rho)) ∧
          (∀ n, 0 ≤ ell n ∧ gamma n 0 = (Z.obj (sigma n)).basepoint ∧
            gamma n (ell n) = y (sigma n) ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (gamma n) ∧
            ∀ s ∈ Icc 0 (ell n), ∀ t ∈ Icc 0 (ell n),
              riemannianEDistOf (Z.obj (sigma n)).metric (gamma n s) (gamma n t) =
                ENNReal.ofReal |s - t|) ∧
          Tendsto (fun n => metricScalarAt (Z.obj (sigma n)).metric (gamma n (ell n))) atTop atTop ∧
          Isometry g ∧ g ⟨0, le_rfl, mul_pos (Real.sqrt_pos.mpr hB) hrho⟩ = L.basepoint ∧
          (∀ t : Ico 0 (Real.sqrt B * rho), ∀ᶠ n in atTop, gamma n t ∈ maps.target n) ∧
          (∀ t : Ico 0 (Real.sqrt B * rho), Tendsto
            (fun n => (maps.partialDiffeomorph n).symm (gamma n t)) atTop (𝓝 (g t))) ∧
          (∀ t : Ico 0 (Real.sqrt B * rho), Tendsto
            (fun n => metricScalarAt (Z.obj (sigma n)).metric (gamma n t))
            atTop (𝓝 (metricScalarAt L.metric (g t)))) ∧
          Tendsto (fun t => metricScalarAt L.metric (g t))
            (comap (Subtype.val : Ico 0 (Real.sqrt B * rho) → ℝ)
              (𝓝 (Real.sqrt B * rho))) atTop ∧
          ∃ q : UniformSpace.Completion L.M,
            Tendsto (fun t => (g t : UniformSpace.Completion L.M))
              (comap (Subtype.val : Ico 0 (Real.sqrt B * rho) → ℝ)
                (𝓝 (Real.sqrt B * rho))) (𝓝 q) ∧
            (∀ t : Ico 0 (Real.sqrt B * rho),
              dist q (g t : UniformSpace.Completion L.M) = Real.sqrt B * rho - t) ∧
            q ∉ range (fun x : L.M => (x : UniformSpace.Completion L.M)) := by
  dsimp only
  let Z : PointedRiemannianSeq (𝓡 3) :=
    ⟨fun i => ((S i).pointedFlow.atTime (time i)).repoint (point i)⟩
  obtain ⟨f, hf, radius, hradius, hradiusconv, L, hL, maps, C, hcanonical,
    htargets, hradial, hmetrics, hcompact, hsec, phi, gamma, g, hphi, hg,
    hgbase, hgamma, hconv, hstay, hlimit, hscalarblow, hescape, hmissing, q, hq⟩ :=
    exists_standard_terminal_isometric_segment_of_scalar_escape S time point y
      (by norm_num : (0 : ℝ) < 3 / 4) hrho htime hscalar hdistance hblowup
  let _ : PathConnectedSpace L.M := hL
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x z => riemannianEDistOf_ne_top L.metric x z)
  let raw := (standardParabolicSequence B hB S time point htime).atTime 0
  have hraw : raw = Z.scaleMetric B hB := standardParabolicSequence_atTime_zero B hB S time point htime
  let LB := L.scaleMetric B hB
  let _ : PathConnectedSpace LB.M := hL
  let mapsB := (maps.compSubseq phi hphi).scaleMetric B hB
  let CB := (C.compSubseq phi hphi).scaleMetric B hB
  have hcanonical' (n : ℕ) : (C.metrics.compSubseq phi hphi).domain n =
      CanonicalMetricCompactness.canonicalSourceData (maps.compSubseq phi hphi) n := by
    change (C.metrics.domain (phi n)).compSubseq phi hphi n = _
    rw [hcanonical (phi n)]
    rfl
  have hcanonicalB (n : ℕ) : CB.metrics.domain n =
      CanonicalMetricCompactness.canonicalSourceData mapsB n :=
    (C.metrics.compSubseq phi hphi).scaleMetric_domain_eq_canonical hcanonical' B hB n
  obtain ⟨mapsR, CR, hmapR, hcanR⟩ := exists_pointed_convergence_of_seq_eq
    raw (Z.scaleMetric B hB) hraw LB (f ∘ phi) mapsB CB hcanonicalB
  have hmaps (n : ℕ) : mapsR.partialDiffeomorph n = mapsB.partialDiffeomorph n :=
    congrFun (eq_of_heq hmapR) n
  have hmet (n : ℕ) : (raw.obj n).metric = ((Z.scaleMetric B hB).obj n).metric := by
    change ((standardParabolicSequence B hB S time point htime).term n).S.base.metric 0 = _
    simp only [standardParabolicSequence_metric, zero_div, add_zero]
    rfl
  have hk := Real.sqrt_pos.mpr hB
  have hcompactB (r : ℝ) (hr : 0 ≤ r) (hrrho : r < Real.sqrt B * rho) :
      IsCompact (riemannianClosedBallOf LB.metric LB.basepoint r) := by
    have heq : r = Real.sqrt B * (r / Real.sqrt B) := (mul_div_cancel₀ r hk.ne').symm
    change IsCompact (riemannianClosedBallOf (scaleMetric B hB L.metric) L.basepoint r)
    rw [heq, riemannianClosedBallOf_scaleMetric]
    exact hcompact _ (div_nonneg hr hk.le) ((div_lt_iff₀ hk).mpr (by simpa [mul_comm] using hrrho))
  have hradialB (x : LB.M) : riemannianEDistOf LB.metric LB.basepoint x <
      ENNReal.ofReal (Real.sqrt B * rho) := by
    change L.M at x
    change riemannianEDistOf (scaleMetric B hB L.metric) L.basepoint x < _
    rw [edistOf_scale, ENNReal.ofReal_mul hk.le]
    simpa only [mul_comm] using ENNReal.mul_lt_mul_left
      (ENNReal.ofReal_pos.mpr hk).ne' ENNReal.ofReal_ne_top (hradial x)
  have hsecB (x : LB.M) (v w : TangentSpace (𝓡 3) x) :
      0 ≤ metricRm04StandardAt LB.metric x v w w v := by
    change L.M at x
    change TangentSpace (𝓡 3) x at v w
    change 0 ≤ metricRm04StandardAt (scaleMetric B hB L.metric) x v w w v
    rw [metricRmStandard_scale]
    exact mul_nonneg hB.le (hsec x v w)
  obtain ⟨gB, hgBdef, hgB, hgBbase, hblowB, qB, hqB⟩ :=
    L.exists_isometric_segment_scaleMetric hL B hB hrho g hg hgbase hscalarblow
  let gammaB : ℕ → ℝ → E3 := fun n t => gamma n (t / Real.sqrt B)
  let ell : ℕ → ℝ := fun n => (riemannianEDistOf ((S (f (phi n))).metric (time (f (phi n))))
    (point (f (phi n))) (y (f (phi n)))).toReal
  let ellB : ℕ → ℝ := fun n => Real.sqrt B * ell n
  have hell : Tendsto ell atTop (𝓝 rho) := hdistance.comp (hf.comp hphi).tendsto_atTop
  have hellB : Tendsto ellB atTop (𝓝 (Real.sqrt B * rho)) := tendsto_const_nhds.mul hell
  have hgammaB (n : ℕ) : 0 ≤ ellB n ∧ gammaB n 0 = (Z.obj ((f ∘ phi) n)).basepoint ∧
      gammaB n (ellB n) = y ((f ∘ phi) n) ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (gammaB n) ∧
      ∀ s ∈ Icc 0 (ellB n), ∀ t ∈ Icc 0 (ellB n),
        riemannianEDistOf ((Z.scaleMetric B hB).obj ((f ∘ phi) n)).metric
          (gammaB n s) (gammaB n t) = ENNReal.ofReal |s - t| := by
    obtain ⟨hsmooth, hzero, hend, hmin⟩ := Geometry.distance_parametrized_segment_scaleMetric
      ((S (f (phi n))).metric (time (f (phi n)))) B hB (gamma n)
      (hgamma n).2.2.1 (hgamma n).2.2.2
    exact ⟨mul_nonneg hk.le ENNReal.toReal_nonneg, hzero.trans (hgamma n).1,
      hend.trans (hgamma n).2.1, hsmooth, hmin⟩
  have hpointblow : Tendsto
      (fun n => metricScalarAt ((Z.scaleMetric B hB).obj ((f ∘ phi) n)).metric
        (gammaB n (ellB n))) atTop atTop := by
    have hh := (hblowup.comp (hf.comp hphi).tendsto_atTop).const_mul_atTop (inv_pos.mpr hB)
    convert hh using 1
    funext n
    change metricScalarAt (scaleMetric B hB ((S (f (phi n))).metric (time (f (phi n)))))
      (gammaB n (ellB n)) = B⁻¹ * metricScalarAt ((S (f (phi n))).metric (time (f (phi n))))
        (y (f (phi n)))
    rw [metricScalarAt_scaleMetric, (hgammaB n).2.2.1]
    rfl
  let d : Ico 0 (Real.sqrt B * rho) → Ico 0 rho := fun t =>
    ⟨t / Real.sqrt B, div_nonneg t.property.1 hk.le,
      (div_lt_iff₀ hk).mpr (by simpa [mul_comm] using t.property.2)⟩
  have hstayB (t : Ico 0 (Real.sqrt B * rho)) :
      ∀ᶠ n in atTop, gammaB n t ∈ mapsB.target n := hstay (d t)
  have hconvB (t : Ico 0 (Real.sqrt B * rho)) :
      Tendsto (fun n => (mapsB.partialDiffeomorph n).symm (gammaB n t)) atTop (𝓝 (gB t)) := by
    rw [hgBdef t]
    exact (hconv {d t} isCompact_singleton).tendsto_at (mem_singleton (d t))
  have hlimitB (t : Ico 0 (Real.sqrt B * rho)) : Tendsto
      (fun n => metricScalarAt ((Z.scaleMetric B hB).obj ((f ∘ phi) n)).metric (gammaB n t))
      atTop (𝓝 (metricScalarAt LB.metric (gB t))) :=
    pointedScalar_tendsto_of_inverse_tendsto CB.metrics hcanonicalB
      (fun n => gammaB n t) (hstayB t) (hconvB t)
  have hstayR (t : Ico 0 (Real.sqrt B * rho)) :
      ∀ᶠ n in atTop, gammaB n t ∈ mapsR.target n := by
    filter_upwards [hstayB t] with n hn
    change gammaB n t ∈ (mapsR.partialDiffeomorph n).target
    rw [hmaps n]
    exact hn
  have hconvR (t : Ico 0 (Real.sqrt B * rho)) :
      Tendsto (fun n => (mapsR.partialDiffeomorph n).symm (gammaB n t)) atTop (𝓝 (gB t)) := by
    convert hconvB t using 1
    funext n
    rw [hmaps n]
    rfl
  refine ⟨f ∘ phi, hf.comp hphi, LB, hL, mapsR, CR, hcanR, hcompactB, hradialB, hsecB,
    gammaB, ellB, gB, hellB, ?_, ?_, hgB, hgBbase, hstayR, hconvR, ?_,
    hblowB, qB, hqB⟩
  · intro n
    refine ⟨(hgammaB n).1, (hgammaB n).2.1, (hgammaB n).2.2.1, (hgammaB n).2.2.2.1, ?_⟩
    intro s hs t ht
    change riemannianEDistOf (raw.obj ((f ∘ phi) n)).metric (gammaB n s) (gammaB n t) = _
    rw [hmet]
    exact (hgammaB n).2.2.2.2 s hs t ht
  · convert hpointblow using 1
    funext n
    change metricScalarAt (raw.obj ((f ∘ phi) n)).metric _ = _
    rw [hmet]
    rfl
  · intro t
    convert hlimitB t using 1
    funext n
    change metricScalarAt (raw.obj ((f ∘ phi) n)).metric _ = _
    rw [hmet]
    rfl

end DifferentialGeometry.PDE.RicciFlow
