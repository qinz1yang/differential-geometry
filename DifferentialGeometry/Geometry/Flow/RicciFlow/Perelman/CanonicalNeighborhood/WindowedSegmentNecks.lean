import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedUniformCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LongSegmentNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckRadius
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseDistanceControl

set_option autoImplicit false
noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.almost_isometric_inverse_segment_of_center_distance_le
    {eps kappa A B delta : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t)
    (hA : 0 < A) (hB : 0 ≤ B) (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (heps : eps ≤ delta / (1 + delta))
    (hradius : (1 + delta) * (3 * (A + B) + 2) ≤ modelRadius eps)
    (γ : ℝ → M)
    (hcenter : riemannianEDistOf
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x (γ 0) ≤ ENNReal.ofReal B)
    (hsegment : ∀ s ∈ Icc (-A) A, ∀ r ∈ Icc (-A) A,
      riemannianEDistOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
        (γ s) (γ r) = ENNReal.ofReal |s - r|) :
    riemannianEDistOf (W.model.S.family.metric 0)
      W.model.basepoint (W.embedding.symm (γ 0)) ≤ ENNReal.ofReal ((1 + delta) * B) ∧
      ∀ s ∈ Icc (-A) A, ∀ r ∈ Icc (-A) A,
        ENNReal.ofReal ((1 - delta) * |s - r|) ≤
          riemannianEDistOf (W.model.S.family.metric 0)
            (W.embedding.symm (γ s)) (W.embedding.symm (γ r)) ∧
        riemannianEDistOf (W.model.S.family.metric 0)
            (W.embedding.symm (γ s)) (W.embedding.symm (γ r)) ≤
          ENNReal.ofReal ((1 + delta) * |s - r|) := by
  let L := 1 + delta
  let R := L * (3 * (A + B) + 2)
  let g := W.model.S.base.metric 0
  let h := rescaledMetric S t (S.scalar t x) W.scalar_pos 0
  have hL : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have heps_delta : eps ≤ delta := heps.trans (div_le_self hdelta.le hLone)
  have heps_mul : eps * L ≤ delta := (le_div_iff₀ hL).mp heps
  have hfactor : 1 ≤ L * (1 - eps) := by dsimp only [L] at *; nlinarith
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hsource : riemannianClosedBallOf g W.model.basepoint R ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono _ _
      (hradius.trans (le_add_of_nonneg_right zero_le_one))).trans W.buffered_ball
  have hcompact : IsCompact (riemannianClosedBallOf g W.model.basepoint R) := by
    apply RiemannianMetricComplete.closedEBall_isCompact
    exact ⟨MetricComplete.complete (W.model.atTime 0) (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))⟩
  have hquad (y : W.model.M) (hy : y ∈ riemannianClosedBallOf g W.model.basepoint R)
      (v : TangentSpace I3 y) :
      h.inner (W.embedding y) (mfderiv I3 I3 W.embedding y v)
          (mfderiv I3 I3 W.embedding y v) ≤ L ^ 2 * g.inner y v v ∧
      g.inner y v v ≤ L ^ 2 * h.inner (W.embedding y)
          (mfderiv I3 I3 W.embedding y v) (mfderiv I3 I3 W.embedding y v) := by
    have hyfull := riemannianClosedBallOf_mono g W.model.basepoint hradius hy
    have hc := W.comparison.equivalence 0
      (show (0 : ℝ) ∈ Icc (-modelDepth eps) 0 from
        ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩) y hyfull v
    rw [W.comparison.pullback_eq 0 y hyfull (fun _ => v)] at hc
    have ha := inner_self_nonneg g y v
    have hb := inner_self_nonneg h (W.embedding y) (mfderiv I3 I3 W.embedding y v)
    constructor
    · exact hc.2.trans (mul_le_mul_of_nonneg_right
        ((by dsimp only [L]; nlinarith : 1 + eps ≤ L ^ 2)) ha)
    · have hbound : g.inner y v v ≤ L * h.inner (W.embedding y)
          (mfderiv I3 I3 W.embedding y v) (mfderiv I3 I3 W.embedding y v) := by
        calc
          _ ≤ (L * (1 - eps)) * g.inner y v v := le_mul_of_one_le_left ha hfactor
          _ = L * ((1 - eps) * g.inner y v v) := mul_assoc _ _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left hc.1 hL.le
      exact hbound.trans (mul_le_mul_of_nonneg_right hLsq hb)
  have hcontrol := KappaSolutions.inverse_distance_control_on_buffered_metric_ball
    g h W.embedding W.model.basepoint hLone (add_nonneg hA.le hB) hcompact hsource
    (fun y hy v => (hquad y hy v).1) (fun y hy v => (hquad y hy v).2)
  have hbaseSource : W.model.basepoint ∈ W.embedding.source :=
    hsource (by change riemannianEDistOf g _ _ ≤ _; rw [riemannianEDistOf_self]; exact bot_le)
  have hinvBase : W.embedding.symm (W.embedding W.model.basepoint) = W.model.basepoint :=
    W.embedding.left_inv' hbaseSource
  have hbaseBall : W.embedding W.model.basepoint ∈
      riemannianClosedBallOf h (W.embedding W.model.basepoint) (A + B) := by
    change riemannianEDistOf h _ _ ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  have hball (a : ℝ) (ha : a ∈ Icc (-A) A) :
      γ a ∈ riemannianClosedBallOf h (W.embedding W.model.basepoint) (A + B) := by
    change riemannianEDistOf h (W.embedding W.model.basepoint) (γ a) ≤ _
    rw [W.base_map]
    have hd : riemannianEDistOf h (γ 0) (γ a) ≤ ENNReal.ofReal A := by
      rw [hsegment 0 ⟨by linarith, hA.le⟩ a ha]
      simp only [zero_sub, abs_neg]
      exact ENNReal.ofReal_le_ofReal (abs_le.mpr ha)
    calc
      _ ≤ riemannianEDistOf h x (γ 0) + riemannianEDistOf h (γ 0) (γ a) :=
        riemannianEDistOf_triangle h _ _ _
      _ ≤ ENNReal.ofReal B + ENNReal.ofReal A := add_le_add hcenter hd
      _ = ENNReal.ofReal (A + B) := by rw [← ENNReal.ofReal_add hB hA.le, add_comm]
  refine ⟨?_, ?_⟩
  · have hp := (hcontrol.2 (W.embedding W.model.basepoint) hbaseBall
      (γ 0) (hball 0 ⟨by linarith, hA.le⟩)).1
    rw [hinvBase, W.base_map] at hp
    exact hp.trans ((mul_le_mul_right hcenter (ENNReal.ofReal L)).trans_eq
      (ENNReal.ofReal_mul hL.le).symm)
  · intro s hs r hr
    have hp := hcontrol.2 (γ s) (hball s hs) (γ r) (hball r hr)
    rw [hsegment s hs r hr] at hp
    have hupper : riemannianEDistOf g (W.embedding.symm (γ s)) (W.embedding.symm (γ r)) ≤
        ENNReal.ofReal (L * |s - r|) := by
      rw [ENNReal.ofReal_mul hL.le]
      exact hp.1
    have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hp.2
    rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hL.le] at hreal
    have hlower : (1 - delta) * |s - r| ≤
        (riemannianEDistOf g (W.embedding.symm (γ s)) (W.embedding.symm (γ r))).toReal := by
      have hb := mul_le_mul_of_nonneg_left hreal (sub_nonneg.mpr hdelta_one.le)
      have hn := ENNReal.toReal_nonneg
        (a := riemannianEDistOf g (W.embedding.symm (γ s)) (W.embedding.symm (γ r)))
      dsimp only [L] at hb
      nlinarith [mul_nonneg (sq_nonneg delta) hn]
    exact ⟨(ENNReal.ofReal_le_ofReal hlower).trans_eq (ENNReal.ofReal_toReal hfinite), hupper⟩

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.almost_isometric_inverse_segment
    {eps kappa A delta : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t)
    (hA : 0 < A) (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (heps : eps ≤ delta / (1 + delta))
    (hradius : (1 + delta) * (3 * A + 2) ≤ modelRadius eps)
    (γ : ℝ → M) (hcenter : γ 0 = x)
    (hsegment : ∀ s ∈ Icc (-A) A, ∀ r ∈ Icc (-A) A,
      riemannianEDistOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
        (γ s) (γ r) = ENNReal.ofReal |s - r|) :
    W.embedding.symm (γ 0) = W.model.basepoint ∧
      ∀ s ∈ Icc (-A) A, ∀ r ∈ Icc (-A) A,
        ENNReal.ofReal ((1 - delta) * |s - r|) ≤
          riemannianEDistOf (W.model.S.family.metric 0)
            (W.embedding.symm (γ s)) (W.embedding.symm (γ r)) ∧
        riemannianEDistOf (W.model.S.family.metric 0)
            (W.embedding.symm (γ s)) (W.embedding.symm (γ r)) ≤
          ENNReal.ofReal ((1 + delta) * |s - r|) := by
  have hdist : riemannianEDistOf
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x (γ 0) ≤ ENNReal.ofReal 0 := by
    rw [hcenter, riemannianEDistOf_self]
    exact bot_le
  have hc := W.almost_isometric_inverse_segment_of_center_distance_le
    hA (B := 0) le_rfl hdelta hdelta_one heps (by simpa only [add_zero] using hradius)
    γ hdist hsegment
  refine ⟨?_, hc.2⟩
  have hbaseSource : W.model.basepoint ∈ W.embedding.source :=
    W.buffered_ball (by change riemannianEDistOf _ _ _ ≤ _; rw [riemannianEDistOf_self]; exact bot_le)
  exact (congrArg (fun z => W.embedding.symm z)
    (hcenter.trans W.base_map.symm)).trans (W.embedding.left_inv' hbaseSource)


theorem exists_windowed_strongNeck_near_minimizing_segment (kappa B : ℝ)
    (hB : 0 ≤ B)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ A epsStar : ℝ, 0 < A ∧ 0 < epsStar ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (eps : ℝ) (x : M) (t : ℝ)
          (W : WindowedModelWitness eps kappa S x t),
          eps ≤ epsStar →
          (∀ s ∈ Ioo (-modelDepth eps) 0,
            parabolicTime t (S.scalar t x) s ∈ D.regular) →
          Nonempty (TangentOrientationSection W.model.M) →
          ∀ γ : ℝ → M,
            riemannianEDistOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
              x (γ 0) ≤ ENNReal.ofReal B →
            (∀ s ∈ Icc (-A) A, ∀ r ∈ Icc (-A) A,
              riemannianEDistOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
                (γ s) (γ r) = ENNReal.ofReal |s - r|) →
            Nonempty (StrongNeck S (2 * alpha) x t) := by
  have htol : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le_smallness alpha).trans_lt
      ((backgroundJetSmallness_ceil_lt_self _ ha hsmall).trans (by linarith))
  obtain ⟨A, delta, hA, hdelta, hdelta_one, hneck⟩ :=
    KappaSolutions.exists_strongNeck_radius_near_almost_isometric_segment.{u}
      kappa (2 * B) (mul_nonneg (by norm_num) hB) (neckModelTolerance_pos ha) htol
  obtain ⟨epsTransfer, hepsTransfer, htransfer⟩ := exists_windowed_neck_transfer_threshold.{u} ha hsmall
  let R := (1 + delta) * (3 * (A + B) + 2)
  have hR : 0 < R := mul_pos (by linarith) (by linarith)
  let epsStar := min epsTransfer (min (delta / (1 + delta)) ((R + 1)⁻¹ ^ 2))
  have hepsStar : 0 < epsStar := lt_min hepsTransfer
    (lt_min (div_pos hdelta (by linarith)) (sq_pos_of_pos (inv_pos.mpr (by linarith))))
  refine ⟨A, epsStar, hA, hepsStar, ?_⟩
  intro M _ _ _ _ _ D S hS eps x t W heps hreg horient γ hcenter hsegment
  have heps_cmp : eps ≤ delta / (1 + delta) :=
    heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heps_radius : eps ≤ (R + 1)⁻¹ ^ 2 :=
    heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hradius : R ≤ modelRadius eps := by
    have hh := modelRadius_anti W.eps_pos heps_radius
    have heq : modelRadius ((R + 1)⁻¹ ^ 2) = R + 1 := by
      rw [modelRadius, Real.sqrt_sq (inv_nonneg.mpr (by linarith)), inv_inv]
    rw [heq] at hh
    linarith
  obtain ⟨hbase, hmodelSegment⟩ := W.almost_isometric_inverse_segment_of_center_distance_le
    hA hB hdelta hdelta_one heps_cmp hradius γ hcenter hsegment
  obtain ⟨nk⟩ := hneck W.model W.model_ancient W.model_scalar_base horient
    (fun s => W.embedding.symm (γ s))
    (hbase.trans (ENNReal.ofReal_le_ofReal (by nlinarith))) hmodelSegment
  obtain ⟨nk', _⟩ := htransfer M D S hS eps kappa x t W
    (heps.trans (min_le_left _ _)) hreg nk
  exact ⟨nk'⟩

theorem exists_windowed_strongNeck_of_minimizing_segment (kappa : ℝ)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ A epsStar : ℝ, 0 < A ∧ 0 < epsStar ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (eps : ℝ) (x : M) (t : ℝ)
          (W : WindowedModelWitness eps kappa S x t),
          eps ≤ epsStar →
          (∀ s ∈ Ioo (-modelDepth eps) 0,
            parabolicTime t (S.scalar t x) s ∈ D.regular) →
          Nonempty (TangentOrientationSection W.model.M) →
          ∀ γ : ℝ → M, γ 0 = x →
            (∀ s ∈ Icc (-A) A, ∀ r ∈ Icc (-A) A,
              riemannianEDistOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
                (γ s) (γ r) = ENNReal.ofReal |s - r|) →
            Nonempty (StrongNeck S (2 * alpha) x t) := by
  obtain ⟨A, epsStar, hA, hepsStar, hneck⟩ :=
    exists_windowed_strongNeck_near_minimizing_segment.{u} kappa 0 le_rfl ha hsmall
  refine ⟨A, epsStar, hA, hepsStar, ?_⟩
  intro M _ _ _ _ _ D S hS eps x t W heps hreg horient γ hcenter hsegment
  apply hneck M D S hS eps x t W heps hreg horient γ _ hsegment
  rw [hcenter, riemannianEDistOf_self]
  exact bot_le

theorem exists_windowed_strongNeck_near_long_minimizing_segment (kappa B : ℝ)
    (hB : 0 ≤ B)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ A epsStar : ℝ, 0 < A ∧ 0 < epsStar ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (eps : ℝ) (x : M) (t : ℝ)
          (W : WindowedModelWitness eps kappa S x t),
          eps ≤ epsStar →
          (∀ s ∈ Ioo (-modelDepth eps) 0,
            parabolicTime t (S.scalar t x) s ∈ D.regular) →
          Nonempty (TangentOrientationSection W.model.M) →
          ∀ (γ : ℝ → M) (a b tau : ℝ),
            (∀ s ∈ Icc a b, ∀ r ∈ Icc a b,
              riemannianEDistOf (S.base.metric t) (γ s) (γ r) = ENNReal.ofReal |s - r|) →
            ENNReal.ofReal (Real.sqrt (S.scalar t x)) *
              riemannianEDistOf (S.base.metric t) x (γ tau) ≤ ENNReal.ofReal B →
            A ≤ Real.sqrt (S.scalar t x) * (tau - a) →
            A ≤ Real.sqrt (S.scalar t x) * (b - tau) →
            Nonempty (StrongNeck S (2 * alpha) x t) := by
  obtain ⟨A, epsStar, hA, hepsStar, hneck⟩ :=
    exists_windowed_strongNeck_near_minimizing_segment.{u} kappa B hB ha hsmall
  refine ⟨A, epsStar, hA, hepsStar, ?_⟩
  intro M _ _ _ _ _ D S hS eps x t W heps hreg horient γ a b tau hsegment hnear hleft hright
  let Q := S.scalar t x
  have hQpos : 0 < Q := W.scalar_pos
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hcenterScaled : riemannianEDistOf
      (rescaledMetric S t Q W.scalar_pos 0) x (γ tau) ≤ ENNReal.ofReal B := by
    simpa only [rescaledMetric, parabolicTime_zero, edistOf_scale] using hnear
  apply hneck M D S hS eps x t W heps hreg horient
    (fun s => γ (tau + s / Real.sqrt Q))
    (by simpa only [zero_div, add_zero] using hcenterScaled)
  have hmem (s : ℝ) (hs : s ∈ Icc (-A) A) : tau + s / Real.sqrt Q ∈ Icc a b := by
    have hlow : -(tau - a) ≤ s / Real.sqrt Q := by
      apply (le_div_iff₀ hsqrt).mpr
      nlinarith [hs.1]
    have hhigh : s / Real.sqrt Q ≤ b - tau := by
      apply (div_le_iff₀ hsqrt).mpr
      nlinarith [hs.2]
    exact ⟨by linarith, by linarith⟩
  intro s hs r hr
  simp only [rescaledMetric, parabolicTime_zero]
  rw [edistOf_scale, hsegment _ (hmem s hs) _ (hmem r hr),
    ← ENNReal.ofReal_mul hsqrt.le]
  congr 1
  have hdiff : tau + s / Real.sqrt Q - (tau + r / Real.sqrt Q) =
      (s - r) / Real.sqrt Q := by ring
  rw [hdiff, abs_div, abs_of_pos hsqrt]
  field_simp

theorem exists_eventually_windowed_strongNeck_near_scalar_blowup_endpoint (kappa : ℝ)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ (M : ℕ → Type u) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
        [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]
        (D : ℕ → RealTimeInterval)
        (S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)),
        (∀ i, IsSolutionOn (S i)) → ∀ (eps : ℝ), eps ≤ epsStar →
          ∀ (t : ℕ → ℝ) (γ : ∀ i, ℝ → M i) (ell : ℕ → ℝ) (rho : ℝ),
            0 < rho → Tendsto ell atTop (𝓝 rho) → ∀ R : Ico 0 rho → ℝ,
              (∀ i, ∀ s ∈ Icc 0 (ell i), ∀ r ∈ Icc 0 (ell i),
                riemannianEDistOf ((S i).base.metric (t i)) (γ i s) (γ i r) =
                  ENNReal.ofReal |s - r|) →
              (∀ tau : Ico 0 rho,
                Tendsto (fun i => (S i).scalar (t i) (γ i tau)) atTop (𝓝 (R tau))) →
              Tendsto R (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop →
              Tendsto (fun i => (S i).scalar (t i) (γ i (ell i))) atTop atTop →
              (∀ tau : Ico 0 rho, 2 < R tau → ∀ᶠ i in atTop,
                ∃ W : WindowedModelWitness eps kappa (S i) (γ i tau) (t i),
                  (∀ s ∈ Ioo (-modelDepth eps) 0,
                    parabolicTime (t i) ((S i).scalar (t i) (γ i tau)) s ∈ (D i).regular) ∧
                  Nonempty (TangentOrientationSection W.model.M)) →
              ∀ᶠ tau : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
                ∀ᶠ i in atTop, Nonempty (StrongNeck (S i) (2 * alpha) (γ i tau) (t i)) := by
  obtain ⟨A, epsNeck, hA, hepsNeck, hneck⟩ :=
    exists_windowed_strongNeck_near_long_minimizing_segment.{u} kappa 0 le_rfl ha hsmall
  obtain ⟨epsEnd, hepsEnd, hend⟩ :=
    exists_windowed_scalar_mul_sq_distance_limit_lower_bound.{u}
      (r := 2 * A) (by positivity)
  refine ⟨min epsNeck epsEnd, lt_min hepsNeck hepsEnd, ?_⟩
  intro M _ _ _ _ _ D S hS eps heps t γ ell rho hrho hell R hsegment hscalar hblow hy hgood
  have htime : Tendsto (Subtype.val : Ico 0 rho → ℝ)
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 rho) := tendsto_comap
  have hleft := hblow.atTop_mul_pos (sq_pos_of_pos hrho) (htime.pow 2)
  filter_upwards [htime.eventually (eventually_gt_nhds hrho),
    hblow.eventually (eventually_gt_atTop 2),
    hleft.eventually (eventually_gt_atTop (A ^ 2))] with tau htau hR hleft
  have hRpos : 0 < R tau := by linarith only [hR]
  have hw := hgood tau hR
  have hdist : ∀ᶠ i in atTop,
      riemannianEDistOf ((S i).base.metric (t i)) (γ i tau) (γ i (ell i)) ≤
        ENNReal.ofReal (ell i - tau) := by
    filter_upwards [hell.eventually (eventually_gt_nhds tau.property.2)] with i hi
    rw [hsegment i tau ⟨tau.property.1, hi.le⟩ (ell i)
      ⟨tau.property.1.trans hi.le, le_rfl⟩,
      abs_of_nonpos (sub_nonpos.mpr hi.le), neg_sub]
  have hrightReserve := hend M D S (fun _ => eps) (fun _ => kappa) t
    (fun i => γ i tau) (fun i => γ i (ell i)) (R tau) (rho - tau)
    (fun i => ell i - tau)
    (hw.mono fun _ hi => by obtain ⟨W, _, _⟩ := hi; exact ⟨W⟩)
    (Eventually.of_forall fun _ => heps.trans (min_le_right _ _))
    hRpos (hscalar tau) hy (hell.sub_const tau) hdist
  have hroot := Real.sqrt_pos.mpr hRpos
  have hleft' : A < Real.sqrt (R tau) * tau := by
    nlinarith [Real.sq_sqrt hRpos.le, mul_pos hroot htau]
  have hright' : A < Real.sqrt (R tau) * (rho - tau) := by
    nlinarith [Real.sq_sqrt hRpos.le, mul_pos hroot (sub_pos.mpr tau.property.2),
      sq_pos_of_pos hA]
  have hsqrt := (Real.continuous_sqrt.tendsto (R tau)).comp (hscalar tau)
  have hleftLim := hsqrt.mul_const (tau : ℝ)
  have hrightLim := hsqrt.mul (hell.sub_const (tau : ℝ))
  filter_upwards [hw, hleftLim.eventually (eventually_gt_nhds hleft'),
    hrightLim.eventually (eventually_gt_nhds hright')] with i hi hlefti hrighti
  obtain ⟨W, hreg, horient⟩ := hi
  apply hneck (M i) (D i) (S i) (hS i) eps (γ i tau) (t i) W
    (heps.trans (min_le_left _ _)) hreg horient (γ i) 0 (ell i) tau (hsegment i)
  · simp only [riemannianEDistOf_self, mul_zero, ENNReal.ofReal_zero, le_refl]
  · simpa only [sub_zero, Function.comp_def] using hlefti.le
  · exact hrighti.le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end
