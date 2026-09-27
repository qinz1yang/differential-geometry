import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

variable {M N : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N]

omit [T2Space M] [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem exists_isometric_inverse_of_injective (g : SmoothRiemannianMetric I3 M)
    {f : N → M} (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Injective f) (w : N) :
    ∃ e : PartialDiffeomorph I3 I3 M N ∞, e.source = range f ∧ (∀ y, e (f y) = y) ∧
      ∀ z ∈ e.source, ∀ v u : TangentSpace I3 z,
        (localPullMetric g f hf).inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z u) =
          g.inner z v u := by
  obtain ⟨d, hs, ht, hd⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (hf.isLocalDiffeomorphOn univ) isOpen_univ ⟨w, trivial⟩ hinj.injOn
  have hd' : (d : N → M) = f := hd
  have hsrc : ∀ y : N, y ∈ d.source := fun y => by
    rw [hs]
    exact mem_univ y
  refine ⟨d.symm, ?_, fun y => ?_, ?_⟩
  · change d.toPartialEquiv.target = range f
    rw [ht, image_univ]
  · have h := d.left_inv' (hsrc y)
    rw [← hd']
    exact h
  intro z hz v u
  have hz' : z ∈ d.target := hz
  have hloc : (⇑d ∘ ⇑d.symm) =ᶠ[𝓝 z] id :=
    Filter.eventuallyEq_of_mem (d.open_target.mem_nhds hz') fun q hq => d.right_inv' hq
  have hcomp := mfderiv_comp z (d.mdifferentiableAt (by decide) (hsrc (d.symm z)))
    (d.symm.mdifferentiableAt (by decide) hz)
  rw [hloc.mfderiv_eq, mfderiv_id] at hcomp
  have hinv : ∀ a : TangentSpace I3 z,
      mfderiv I3 I3 d (d.symm z) (mfderiv I3 I3 d.symm z a) = a := fun a =>
    (DFunLike.congr_fun hcomp a).symm
  have hval : d (d.symm z) = z := d.right_inv' hz'
  rw [localPullMetric_inner]
  rw [← hd'] at hf ⊢
  rw [hinv v, hinv u]
  generalize d (d.symm z) = q at hval ⊢
  subst hval
  rfl

def SpatialCanonicalWitness.localPullOfInjective {g : SmoothRiemannianMetric I3 M}
    {eps C1 C2 : ℝ} {f : N → M} (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Injective f)
    {w : N} (W : SpatialCanonicalWitness g eps C1 C2 (f w)) {R : ℝ} (hR : 2 * W.radius < R)
    (hcpt : IsCompact (riemannianClosedBallOf g (f w) R))
    (hsrc : riemannianClosedBallOf g (f w) R ⊆ range f)
    (hneck : ∀ n, W.alternative = .neck n →
      ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ range f)
    (hcap : ∀ c d, W.alternative = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ range f) :
    SpatialCanonicalWitness (localPullMetric g f hf) eps C1 C2 w :=
  let e := Classical.choose (exists_isometric_inverse_of_injective g hf hinj w)
  have hspec := Classical.choose_spec (exists_isometric_inverse_of_injective g hf hinj w)
  hspec.2.1 w ▸ W.pushforward e hspec.2.2 hR hcpt (hspec.1 ▸ hsrc)
    (fun n hn z hz => hspec.1 ▸ hneck n hn z hz)
    (fun c d hc i z hz => hspec.1 ▸ hcap c d hc i z hz)

theorem SpatialCanonicalWitness.capTubeHasNeckChart.localPullOfInjective
    {g : SmoothRiemannianMetric I3 M} {eps C1 C2 alpha : ℝ} {f : N → M}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Injective f)
    {w : N} {W : SpatialCanonicalWitness g eps C1 C2 (f w)} (hW : W.capTubeHasNeckChart alpha)
    {R : ℝ} (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf g (f w) R))
    (hsrc : riemannianClosedBallOf g (f w) R ⊆ range f)
    (hneck : ∀ n, W.alternative = .neck n →
      ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ range f)
    (hcap : ∀ c d, W.alternative = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ range f)
    (hchart : ∀ c d, W.alternative = .cap c d → ∀ (v : M) (nk : SpatialNeck g alpha v),
      (∀ z, c.tubeMap z = nk.map z) →
        ∀ z ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map z ∈ range f) :
    (W.localPullOfInjective hf hinj hR hcpt hsrc hneck hcap).capTubeHasNeckChart alpha := by
  have hspec := Classical.choose_spec (exists_isometric_inverse_of_injective g hf hinj w)
  set e := Classical.choose (exists_isometric_inverse_of_injective g hf hinj w)
  have hsrc' : riemannianClosedBallOf g (f w) R ⊆ e.source := by rw [hspec.1]; exact hsrc
  exact SpatialCanonicalWitness.capTubeHasNeckChart_cast _
    (hW.pushforward e hspec.2.2 hR hcpt hsrc' _ _
      fun c d hc v nk hnk z hz => by rw [hspec.1]; exact hchart c d hc v nk hnk z hz)

theorem exists_spatialCanonicalWitness_scaleMetric_localPullMetric
    {g : SmoothRiemannianMetric I3 M} {eps C1 C2 alpha : ℝ} {f : N → M}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Injective f) {c : ℝ} (hc : 0 < c)
    {w : N} (W : SpatialCanonicalWitness g eps C1 C2 (f w)) (hW : W.capTubeHasNeckChart alpha)
    {R : ℝ} (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf g (f w) R))
    (hsrc : riemannianClosedBallOf g (f w) R ⊆ range f)
    (hneck : ∀ n, W.alternative = .neck n →
      ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ range f)
    (hcap : ∀ c d, W.alternative = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ range f)
    (hchart : ∀ c d, W.alternative = .cap c d → ∀ (v : M) (nk : SpatialNeck g alpha v),
      (∀ z, c.tubeMap z = nk.map z) →
        ∀ z ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map z ∈ range f) :
    ∃ W' : SpatialCanonicalWitness (scaleMetric c hc (localPullMetric g f hf)) eps C1 C2 w,
      W'.capTubeHasNeckChart alpha :=
  ⟨((W.localPullOfInjective hf hinj hR hcpt hsrc hneck hcap).scaleMetric c hc),
    (hW.localPullOfInjective hf hinj hR hcpt hsrc hneck hcap hchart).scaleMetric c hc⟩

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem abs_derivWithin_parabolic_le_of_abs_derivWithin_le {φ : ℝ → ℝ} {t Q C s : ℝ}
    (hQ : 0 < Q) (hC : 0 ≤ C)
    (hb : |derivWithin φ (Iic (t + s / Q)) (t + s / Q)| ≤ C * φ (t + s / Q) ^ 2) :
    |derivWithin (fun s' => Q⁻¹ * φ (t + s' / Q)) (Iic s) s| ≤
      C * (Q⁻¹ * φ (t + s / Q)) ^ 2 := by
  have htime : HasDerivAt (fun s' : ℝ => t + s' / Q) Q⁻¹ s := by
    have hh : HasDerivAt (fun s' : ℝ => s' / Q) (1 / Q) s := (hasDerivAt_id s).div_const Q
    rw [one_div] at hh
    exact hh.const_add t
  have hmaps : MapsTo (fun s' : ℝ => t + s' / Q) (Iic s) (Iic (t + s / Q)) := by
    intro s' hs'
    have : s' / Q ≤ s / Q := div_le_div_of_nonneg_right hs' hQ.le
    change t + s' / Q ≤ t + s / Q
    linarith
  by_cases hd : DifferentiableWithinAt ℝ φ (Iic (t + s / Q)) (t + s / Q)
  · have hcomp : HasDerivWithinAt (fun s' : ℝ => φ (t + s' / Q))
        (derivWithin φ (Iic (t + s / Q)) (t + s / Q) * Q⁻¹) (Iic s) s :=
      hd.hasDerivWithinAt.comp_of_eq s htime.hasDerivWithinAt hmaps rfl
    rw [((hcomp.const_mul Q⁻¹).derivWithin (uniqueDiffWithinAt_Iic s))]
    have hQi : 0 < Q⁻¹ := inv_pos.mpr hQ
    rw [abs_mul, abs_mul, abs_of_pos hQi]
    calc Q⁻¹ * (|derivWithin φ (Iic (t + s / Q)) (t + s / Q)| * Q⁻¹)
        ≤ Q⁻¹ * (C * φ (t + s / Q) ^ 2 * Q⁻¹) := by gcongr
      _ = C * (Q⁻¹ * φ (t + s / Q)) ^ 2 := by ring
  · have hnd : ¬ DifferentiableWithinAt ℝ (fun s' => Q⁻¹ * φ (t + s' / Q)) (Iic s) s := by
      intro hg
      apply hd
      have hback : HasDerivAt (fun v : ℝ => (v - t) * Q) Q (t + s / Q) := by
        simpa using ((hasDerivAt_id (t + s / Q)).sub_const t).mul_const Q
      have hmaps' : MapsTo (fun v : ℝ => (v - t) * Q) (Iic (t + s / Q)) (Iic s) := by
        intro v hv
        have hv' : v - t ≤ s / Q := by change v ≤ t + s / Q at hv; linarith
        change (v - t) * Q ≤ s
        calc (v - t) * Q ≤ s / Q * Q := mul_le_mul_of_nonneg_right hv' hQ.le
          _ = s := div_mul_cancel₀ s hQ.ne'
      have hpt : (t + s / Q - t) * Q = s := by field_simp; ring
      have hg' : DifferentiableWithinAt ℝ (fun s' => Q⁻¹ * φ (t + s' / Q)) (Iic s)
          ((t + s / Q - t) * Q) := by rw [hpt]; exact hg
      have h1 : DifferentiableWithinAt ℝ
          (fun v => Q * (Q⁻¹ * φ (t + (v - t) * Q / Q))) (Iic (t + s / Q)) (t + s / Q) :=
        (hg'.comp (t + s / Q) hback.differentiableAt.differentiableWithinAt hmaps').const_mul Q
      have key : ∀ v, Q * (Q⁻¹ * φ (t + (v - t) * Q / Q)) = φ v := fun v => by
        rw [mul_div_cancel_right₀ _ hQ.ne', add_sub_cancel, ← mul_assoc, mul_inv_cancel₀ hQ.ne',
          one_mul]
      exact h1.congr (fun v _ => (key v).symm) (key _).symm
    rw [derivWithin_zero_of_not_differentiableWithinAt hnd, abs_zero]
    positivity

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem abs_derivWithin_scalar_le_of_scaleMetric_localPullMetric
    {h : ℝ → SmoothRiemannianMetric I3 N} {G : ℝ → SmoothRiemannianMetric I3 M} {f : N → M}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) {Q t s C : ℝ} (hQ : 0 < Q) (hC : 0 ≤ C)
    (heq : ∀ᶠ s' in 𝓝[Iic s] s, h s' = scaleMetric Q hQ (localPullMetric (G (t + s' / Q)) f hf))
    (hs : h s = scaleMetric Q hQ (localPullMetric (G (t + s / Q)) f hf)) (z : N)
    (hb : |derivWithin (fun v => metricScalarAt (G v) (f z)) (Iic (t + s / Q)) (t + s / Q)| ≤
      C * metricScalarAt (G (t + s / Q)) (f z) ^ 2) :
    |derivWithin (fun s' => metricScalarAt (h s') z) (Iic s) s| ≤
      C * metricScalarAt (h s) z ^ 2 := by
  have hval (s' : ℝ) (he : h s' = scaleMetric Q hQ (localPullMetric (G (t + s' / Q)) f hf)) :
      metricScalarAt (h s') z = Q⁻¹ * metricScalarAt (G (t + s' / Q)) (f z) := by
    rw [he, metricScalarAt_scaleMetric, metricScalarAt_localPull]
  have hderiv : derivWithin (fun s' => metricScalarAt (h s') z) (Iic s) s =
      derivWithin (fun s' => Q⁻¹ * metricScalarAt (G (t + s' / Q)) (f z)) (Iic s) s :=
    Filter.EventuallyEq.derivWithin_eq (heq.mono fun s' hs' => hval s' hs') (hval s hs)
  rw [hderiv, hval s hs]
  exact abs_derivWithin_parabolic_le_of_abs_derivWithin_le
    (φ := fun v => metricScalarAt (G v) (f z)) hQ hC hb

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.mem_Icc_of_mem_window from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

universe u

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

theorem mem_stageDomain_activeStage_of_le (H : ObservedHistory.{u}) (v : Icc (0 : ℝ) H.horizon)
    {v' : ℝ} (h1 : H.time (H.activeStage v) ≤ v') (h2 : v' ≤ v) :
    v' ∈ H.stageDomain (H.activeStage v) := by
  have hmem := H.activeStage_mem v
  generalize H.activeStage v = k at h1 hmem ⊢
  cases k using Fin.lastCases with
  | last =>
    simp only [stageDomain, Fin.lastCases_last] at hmem ⊢
    exact ⟨h1, h2.trans hmem.2⟩
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc] at hmem ⊢
    exact ⟨h1, h2.trans_lt hmem.2⟩

theorem abs_derivWithin_scalar_le_of_survivor_maps (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) {R θ q qD C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hqD : q ≤ R * qD)
    {W : TopologicalSpace.Opens (H.stageAt t).Carrier}
    {h : ℝ → SmoothRiemannianMetric ThreeModel W}
    (a : Icc (0 : ℝ) H.horizon) (ha : (a : ℝ) = t - θ / R)
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
      (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hp : ∀ s ∈ Icc (-θ) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
      (t : ℝ) + s / R ∈ H.stageDomain j.val →
        h s = scaleMetric R hR
          (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j)))
    (hstage : ∀ v : Icc (0 : ℝ) H.horizon, (v : ℝ) < t → H.time (H.activeStage v) < v →
      ∀ p : (H.stageAt v).Carrier, q < metricScalarAt (H.stageMetric (H.activeStage v) v) p →
        |derivWithin (fun v' => metricScalarAt (H.stageMetric (H.activeStage v) v') p)
          (Iic (v : ℝ)) v| ≤ C * metricScalarAt (H.stageMetric (H.activeStage v) v) p ^ 2)
    {s : ℝ} (hs : s ∈ Ioo (-θ) 0)
    (hreg : ∀ hv : (t : ℝ) + s / R ∈ Icc (0 : ℝ) H.horizon,
      H.time (H.activeStage ⟨_, hv⟩) < (t : ℝ) + s / R)
    (z : W) (hz : qD < metricScalarAt (h s) z) :
    |derivWithin (fun s' => metricScalarAt (h s') z) (Iic s) s| ≤
      C * metricScalarAt (h s) z ^ 2 := by
  have hvI := ObservedHistory.mem_Icc_of_mem_window hR ha
    (⟨hs.1.le, hs.2.le⟩ : s ∈ Icc (-θ) 0)
  let v : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) + s / R, a.2.1.trans hvI.1, hvI.2.trans t.2.2⟩
  have hav : a ≤ v := hvI.1
  have hvt : v ≤ t := hvI.2
  have hvt' : (v : ℝ) < t := by
    change (t : ℝ) + s / R < t
    have : s / R < 0 := div_neg_of_neg_of_pos hs.2 hR
    linarith
  have hreg' := hreg v.2
  let j : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩
  have hlow : H.time (H.activeStage v) - t < s / R := by
    change H.time (H.activeStage v) < (t : ℝ) + s / R at hreg'
    linarith
  have hlowR : (H.time (H.activeStage v) - t) * R < s := by
    rwa [lt_div_iff₀ hR] at hlow
  have hev : ∀ᶠ s' in 𝓝[Iic s] s, h s' = scaleMetric R hR
      (localPullMetric (H.stageMetric j.val ((t : ℝ) + s' / R)) (f j) (hf j)) := by
    filter_upwards [Ioc_mem_nhdsLE (max_lt hs.1 hlowR)] with s' hs'
    have h1 : -θ < s' := (le_max_left _ _).trans_lt hs'.1
    have h2 : (H.time (H.activeStage v) - t) * R < s' := (le_max_right _ _).trans_lt hs'.1
    refine hp s' ⟨h1.le, hs'.2.trans hs.2.le⟩ j
      (H.mem_stageDomain_activeStage_of_le v ?_ ?_)
    · have : H.time (H.activeStage v) - t < s' / R := by rwa [lt_div_iff₀ hR]
      linarith
    · change (t : ℝ) + s' / R ≤ (t : ℝ) + s / R
      have := div_le_div_of_nonneg_right hs'.2 hR.le
      linarith
  have hs0 := hp s ⟨hs.1.le, hs.2.le⟩ j (H.activeStage_mem v)
  have hRz : metricScalarAt (h s) z =
      R⁻¹ * metricScalarAt (H.stageMetric j.val ((t : ℝ) + s / R)) (f j z) := by
    rw [hs0, metricScalarAt_scaleMetric, metricScalarAt_localPull]
  have hqz : q < metricScalarAt (H.stageMetric (H.activeStage v) v) (f j z) := by
    have h1 : R * qD < R * metricScalarAt (h s) z := mul_lt_mul_of_pos_left hz hR
    rw [hRz, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at h1
    exact hqD.trans_lt h1
  exact abs_derivWithin_scalar_le_of_scaleMetric_localPullMetric (hf j) hR hC hev hs0 z
    (hstage v hvt' hreg' (f j z) hqz)

end ObservedHistory

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)

theorem abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds {Ctime : NNReal}
    {qcan : ℝ} {t : Icc (0 : ℝ) H.toHistory.horizon}
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (hvt : (v : ℝ) < t)
    (hv : H.toHistory.time (H.toHistory.activeStage v) < v)
    (p : (H.toHistory.stageAt v).Carrier)
    (hq : qcan < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p) :
    |derivWithin (fun v' => metricScalarAt
        (H.toHistory.stageMetric (H.toHistory.activeStage v) v') p) (Iic (v : ℝ)) v| ≤
      Ctime * metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p ^ 2 := by
  have hmono : H.toHistory.activeStage v ≤ H.toHistory.activeStage t :=
    H.toHistory.activeStage_mono (show (v : ℝ) ≤ t from hvt.le)
  have hmem := H.toHistory.activeStage_mem v
  change (H.toHistory.stage (H.toHistory.activeStage v)).Carrier at p
  generalize H.toHistory.activeStage v = k at hmono hv hmem p hq ⊢
  cases k using Fin.lastCases with
  | last =>
    have hlt : H.time (Fin.last H.eventCount) < H.horizon := hv.trans_le v.2.2
    have hkt : H.toHistory.activeStage t = Fin.last H.eventCount :=
      le_antisymm (Fin.le_last _) hmono
    have hval : ∀ v' : ℝ, metricScalarAt (H.toHistory.stageMetric (Fin.last H.eventCount) v') p =
        ((H.finalSlab hlt).restrictIncoming le_rfl hlt le_rfl).flow.scalar v' p := by
      intro v'
      rw [ObservedHistory.stageMetric_last_of_lt (h := hlt)]
      rfl
    simp only [hval] at hq ⊢
    exact hfinal hlt hkt p v ⟨hv, hvt⟩ hq
  | cast i =>
    have hnext : (v : ℝ) < H.time i.succ := by
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hmem
      exact hmem.2
    have hval : ∀ v' : ℝ, metricScalarAt (H.toHistory.stageMetric i.castSucc v') p =
        (H.toHistory.event i).incoming.flow.scalar v' p := by
      intro v'
      rw [ObservedHistory.stageMetric_castSucc_apply]
      rfl
    simp only [hval] at hq ⊢
    rcases hmono.lt_or_eq with hlt | heq
    · exact hslabs i hlt p v ⟨hv, hnext⟩ hq
    · exact hcurrent i heq p v ⟨hv, hvt⟩ hq

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
