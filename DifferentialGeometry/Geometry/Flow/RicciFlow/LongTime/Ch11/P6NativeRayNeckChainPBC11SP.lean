import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeRayNeckChainC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeScalarAnchorPBC11SP

set_option autoImplicit false

/-!
# PB-twin of `hflowNRay_of_NJseg_C11SP`（O-CH11-NRPRIME-WIRE G3 层 L5，后缀 `_PB_C11SP`）

生成器 `build-logs/scratch/O-CH11-NRPRIME-WIRE/gen/gen_twin.py`；
源 `P6NativeRayNeckChainC11SP.lean`（tracked，不改）。
PB 合取 `(Rmod ≤ ·.modelRadius ∧ mmod ≤ ·.modelOrder)`（lead 统一形，与 HPBASE-V8 对齐）只加在 PB 透传
binder 与结论；冻结 binder 不动；其余逐字。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- **PB-twin（O-CH11-NRPRIME-WIRE G3）** of `hflowNRay_of_NJseg_C11SP`：
binder `hNJ` 与结论在 `2 ≤ ·.modelOrder →` 后加 PB 合取；证明逐字 + `hPB` 透传。 -/
theorem hflowNRay_of_NJseg_PB_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Rmod : ℝ) (mmod : ℕ)
    (hNJ :
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
          {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
          (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
          (q : CutoffParameters), F.tower = S.tower →
          (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
            q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
          pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
          2 ≤ pBase.modelOrder → (Rmod ≤ pBase.modelRadius ∧ mmod ≤ pBase.modelOrder) →
          CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
        ∀ Afac : ℝ, 1 < Afac →
        ∃ (Haux : ℝ) (hHaux : 4 ≤ Haux),
          ∀ d0 Δ gamma : ℝ, 0 ≤ d0 → 0 < Δ → 0 < gamma → d0 + Δ + gamma ≤ Afac →
          ∀ chi : ℝ, ∀ hchi : 1 ≤ chi,
          ∀ Rad dAnchor : ℝ, 0 ≤ dAnchor →
            dAnchor + Rad / Real.sqrt (chi * Haux) ≤ d0 →
          ∀ idx : ℕ → ℕ,
          let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
          ∀ (time : ∀ i, Icc (0 : ℝ) (H i).horizon)
            (p anchor : ∀ i, ((H i).stageAt (time i)).Carrier) (r : ℕ → ℝ),
            (∀ i, 2 * r i ^ 2 < (time i : ℝ)) →
          ∀ hsmall : ∀ i, hasSmallParabolicCurvature (H i) (time i) (p i) (r i),
            (∀ i, ENNReal.ofReal (Afac⁻¹ * r i ^ 3) ≤
              ballVolume ((H i).stageMetric ((H i).activeStage (time i)) (time i)) (p i) (r i)) →
            (∀ i, r i < q.neckRadius (time i)) →
            Tendsto (fun i => (time i : ℝ)) atTop atTop →
          let stage : ℕ → OrientedThreeStage.{u} := fun i => (H i).stageAt (time i)
          let metric : ∀ i, (stage i).Metric :=
            fun i => (H i).stageMetric ((H i).activeStage (time i)) (time i)
          let Qbase : ℕ → ℝ := fun i => chi * (Haux * (r i ^ 2)⁻¹)
          let hQbase : ∀ i, 0 < Qbase i := fun i =>
            mul_pos (zero_lt_one.trans_le hchi)
              (mul_pos (by linarith only [hHaux]) (inv_pos.mpr (sq_pos_of_pos (hsmall i).1)))
          let Xall : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
            { obj := fun i =>
                { M := (stage i).Carrier
                  basepoint := anchor i
                  metric := scaleMetric (Qbase i) (hQbase i) (metric i) } };
            (∀ i, metricScalarAt (metric i) (anchor i) = Qbase i) →
            (∀ i, riemannianEDistOf (metric i) (p i) (anchor i) ≤
              ENNReal.ofReal (dAnchor * r i)) →
          ∀ R Rwide : ℝ, 0 < R → R < Rwide → Rwide ≤ Rad →
          ∀ B : ℝ, (∀ᶠ i in atTop, ∀ z : (stage i).Carrier,
              riemannianEDistOf (Xall.obj i).metric (anchor i) z < ENNReal.ofReal Rwide →
              metricScalarAt (metric i) z / Qbase i ≤ B) →
          ∀ k : ℕ, ∃ J : ℝ, 0 ≤ J ∧
            ∀ᶠ i in atTop, HasLocalCurvDerivBound (Xall.obj i) (Xall.obj i).basepoint R k J) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → (Rmod ≤ pBase.modelRadius ∧ mmod ≤ pBase.modelOrder) →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
        ε ≤ coneAccuracy →
        C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
      ∀ A : ℝ, 0 < A →
      ∀ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
        (∀ i, (s i).time = (t i : ℝ)) →
      ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
        Tendsto (fun i => (t i : ℝ)) atTop atTop →
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
        (∀ i, r i < q.neckRadius (t i)) →
        Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
      ∃ (rho : ℝ) (hrho : 0 < rho),
        ∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
        let _ : EMetricSpace Pl.M := Pl.emetricSpace
        ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
          (metricScalarAt Pl.metric Pl.basepoint = 1 ∧
           (∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
             algebraicCurvatureOperatorNonnegativeCone) ∧
           (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
           (∀ R : ℝ, 0 ≤ R → R < rho →
             IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
           Isometry ray ∧ ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
           Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
             (cocompact Pl.M) ∧
           (∀ y : Pl.M, ¬ Tendsto ray
             (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 y)) ∧
           Tendsto (fun v => metricScalarAt Pl.metric (ray v))
             (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop ∧
           ∀ᶠ v : Ico (0 : ℝ) rho in
               comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
             Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v))) ∧
          ∀ W : TopologicalSpace.Opens Pl.M,
          ∀ (xW : ℕ → W),
            (∃ times : ℕ → Ico (0 : ℝ) rho, (∀ n, (xW n : Pl.M) = ray (times n)) ∧
              Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho)) →
          ∀ (R₀ : ℝ), 0 < R₀ →
            (∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M)) →
            Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop →
            (∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
              (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M))))) →
            ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
              Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
              ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
                (V : TopologicalSpace.Opens P₂.M)
                (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
                (g : ℝ → SmoothRiemannianMetric ThreeModel V),
                g 0 = P₂.metric.restrictOpen V ∧
                IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
                  (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
                (∀ t ∈ Icc (-tau) 0, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
                  algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
                metricScalarAt P₂.metric P₂.basepoint = 1 ∧
                ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
                  (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
                  ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
                  (∀ᶠ n in atTop,
                    riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
                    riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                      (xW (j n)) (r / 4) ⊆
                        (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
                  ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
                    ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
                    ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
                      |(riemannianEDistOf
                          (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                          (C n a) (C n b)).toReal -
                        (riemannianEDistOf (g 0) a b).toReal| < eta := by
  obtain ⟨ε₀, hε₀, hguardEscape⟩ := native_scalarEscape_anchor_of_NJ_PB_C11SP P g Rmod mmod hNJ
  obtain ⟨ε₂, hε₂, hG4⟩ := hneckRaySeg_C11SP P g
  refine ⟨min ε₀ ε₂, lt_min hε₀ hε₂, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hradM hord hPB hb hε _hC1 _hC2 A hA
  have hacc₀ : pBase.modelAccuracy ≤ ε₀ := hacc.trans (min_le_left _ _)
  have hacc₂ : pBase.modelAccuracy ≤ ε₂ := hacc.trans (min_le_right _ _)
  obtain ⟨Hbase, hHbase, hproduce⟩ :=
    hguardEscape S F q hTower hdiag hacc₀ hradM hord hPB hb A hA
  have hHb : 0 < Hbase := by linarith only [hHbase]
  intro idx H t s hs p x r htime hsmall hvol hx htlim hbad hnat _hzero hratio
  obtain ⟨N, hrest⟩ := hproduce idx t p x r htime hsmall hvol hx htlim hbad hnat
  let φ : ℕ → ℕ := fun i => i + N
  obtain ⟨hφ, anchor, Q, hQ, hscale, hanchorR, hanchorDist, _hOldSegments,
    _hOldDistance, _hOldBlow, rho, hrho, hrhoBound, ind, hind, z,
    f, hf, rad, hrad, hradlim, Pl, maps, M, hbaseR, hcanonical,
    hradial, hcompact, htarget, hmetric, hfinite, hdist, hhigh⟩ := hrest
  let stage := fun i => (H (φ (ind i))).stageAt (t (φ (ind i)))
  let metric := fun i => (H (φ (ind i))).stageMetric
    ((H (φ (ind i))).activeStage (t (φ (ind i)))) (t (φ (ind i)))
  let idx' : ℕ → ℕ := fun i => idx (φ (ind i))
  let t' : ∀ i, Icc (0 : ℝ) (F.tower.history (idx' i)).horizon :=
    fun i => t (φ (ind i))
  let p' : ∀ i, (stage i).Carrier := fun i => p (φ (ind i))
  let anchor' : ∀ i, (stage i).Carrier := fun i => anchor (ind i)
  let r' : ℕ → ℝ := fun i => r (φ (ind i))
  let Q' : ℕ → ℝ := fun i => Q (ind i)
  have hQ' (i : ℕ) : 0 < Q' i := hQ (ind i)
  let U := fun i => connectedComponentOpen (I := ThreeModel) (anchor' i)
  let hp := fun i => (mem_connectedComponent : anchor' i ∈ U i)
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
    { obj := fun i =>
        { M := (stage i).Carrier
          basepoint := anchor' i
          metric := scaleMetric (Q' i) (hQ' i) (metric i) } }
  let maps0 := maps.liftTargetOpen (S := X) U hp
  have hscaleDiv (i : ℕ) : Q' i = Hbase / r' i ^ 2 := by
    simpa only [div_eq_mul_inv] using hscale (ind i)
  have hscaleMul (i : ℕ) : Q' i * r' i ^ 2 = Hbase :=
    (eq_div_iff (pow_ne_zero 2 (hsmall (φ (ind i))).1.ne')).mp (hscaleDiv i)
  have htime' (i : ℕ) : 2 * r' i ^ 2 < (t' i : ℝ) := htime (φ (ind i))
  have hsmall' (i : ℕ) : hasSmallParabolicCurvature
      (F.tower.history (idx' i)).toHistory (t' i) (p' i) (r' i) := hsmall (φ (ind i))
  have ht' (i : ℕ) : 0 < (t' i : ℝ) :=
    (mul_nonneg (by norm_num) (sq_nonneg (r' i))).trans_lt (htime' i)
  have hmono : StrictMono (fun i => φ (ind i)) := hφ.comp hind
  have htlim' : Tendsto (fun i => (t' i : ℝ)) atTop atTop := htlim.comp hmono.tendsto_atTop
  have hratio' : Tendsto (fun i => r' i / Real.sqrt (t' i : ℝ)) atTop (𝓝 0) :=
    hratio.comp hmono.tendsto_atTop
  have hnonnegative := curvatureOperator_nonnegative_of_prepared_stage_limit_CXSP
    S F hTower Hbase hHb idx' t' anchor' r' Q' ht' (fun i => (hsmall' i).1)
    hQ' hscaleDiv hratio' f hf Pl maps0 M hcanonical
  let Awork : ℝ := 4 * A + 4
  have hAwork : 0 < Awork := by dsimp only [Awork]; positivity
  have hAAwork : A ≤ Awork := by dsimp only [Awork]; linarith only [hA]
  have hvol' (i : ℕ) : ENNReal.ofReal (Awork⁻¹ * r' i ^ 3) ≤
      ballVolume (metric i) (p' i) (r' i) :=
    seed_volume_of_parameter_le_CXSP (hsmall' i) hA hAAwork (hvol (φ (ind i)))
  have hsqrt : 2 ≤ Real.sqrt Hbase := by
    nlinarith only [Real.sq_sqrt hHb.le, Real.sqrt_nonneg Hbase, hHbase]
  have hrhoDiv : (rho + 1) / Real.sqrt Hbase ≤ A + 1 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hHb)).mpr
    nlinarith only [hrhoBound, hsqrt]
  have hfit : A + (rho + 1) / Real.sqrt Hbase < Awork := by
    dsimp only [Awork]
    linarith only [hrhoDiv, hA]
  have hlower (eta : ℝ) (heta : 0 < eta) : ∀ᶠ n in atTop, ∀ y ∈ maps0.source n,
      ∀ v : TangentSpace ThreeModel y,
        (1 - eta) * Pl.metric.inner y v v ≤
          (scaleMetric (Q' (f n)) (hQ' (f n)) (metric (f n))).inner (maps0.map n y)
            (mfderiv ThreeModel ThreeModel (maps0.map n) y v)
            (mfderiv ThreeModel ThreeModel (maps0.map n) y v) := by
    filter_upwards [hmetric eta heta] with n hn y hy v
    exact (hn y hy v).1
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  obtain ⟨ell, γ, _hellEq, helllim, hends, hmin, hsegment,
    ψ, ray, hψ, hray, hrayBase, hconv, _hstay, hscalar, hrayEscape, hmissing, hblow⟩ :=
    exists_stage_escape_scalar_ray_CXSP hb Awork hAwork idx' t' p' anchor' r'
      htime' hsmall' hvol' htlim' Hbase hHb Q' hQ' hscaleMul A hA.le
      (fun i => hanchorDist (ind i)) rho hrho hfit f hf Pl maps0 M hcanonical
      rad (fun n => (hrad n).1) hradlim htarget hlower hcompact hradial
      (fun n => z (f n)) hfinite hdist hhigh
  let maps1 := maps0.compSubseq ψ hψ
  have hcanonical1 (n : ℕ) : (M.compSubseq ψ hψ).domain n =
      CanonicalMetricCompactness.canonicalSourceData maps1 n := by
    change (M.domain (ψ n)).compSubseq ψ hψ n = _
    rw [hcanonical (ψ n)]
    rfl
  have hhighSegment : Tendsto (fun n =>
      metricScalarAt (metric (f n)) (γ n (ell n)) / Q' (f n)) atTop atTop := by
    convert hhigh using 1
    funext n
    rw [(hends n).2.1]
  have hnecks := eventually_stage_ray_necks_of_timeCore_CXSP hb hε
    Awork hAwork idx' t' p' anchor' r' htime' hsmall' hvol' htlim'
    Hbase hHb Q' hQ' hscaleMul (fun i => hanchorR (ind i)) rho hrho
    (f ∘ ψ) (hf.comp hψ) Pl maps1 (M.compSubseq ψ hψ) hcanonical1 hcompact
    (ell ∘ ψ) (fun n => γ (ψ n)) (helllim.comp hψ.tendsto_atTop)
    (fun n => (hends (ψ n)).1) (fun n => hmin (ψ n))
    (hψ.tendsto_atTop.eventually hsegment) (hhighSegment.comp hψ.tendsto_atTop) ray
    (fun v => (hconv {v} isCompact_singleton).tendsto_at (mem_singleton v)) hscalar hblow
  refine ⟨rho, hrho, Pl, ray, ⟨hbaseR, hnonnegative, hradial, hcompact,
    hray, hrayBase, hrayEscape, hmissing, hblow, hnecks.2⟩, ?_⟩
  intro W xW hadm R₀ hR₀ hQW hQWlim hcompactW
  obtain ⟨times, hxt, htimes⟩ := hadm
  refine native_coneFlow_of_neckTraced_C11SP S F hTower hb A hA Hbase hHbase rho hrhoBound idx'
    t' p' anchor' r' (fun i => (hsmall' i).1) htlim' htime' hsmall' (fun i => hvol (φ (ind i)))
    (fun i => hanchorDist (ind i)) Q' hQ' (fun i => hscale (ind i)) (f ∘ ψ) (hf.comp hψ) Pl maps1
    (M.compSubseq ψ hψ) hcanonical1 hradial W xW R₀ hR₀ hQW hQWlim hcompactW ?_
  filter_upwards [hG4 S F q hTower hdiag hacc₂ hradM hord hb A hA Hbase hHbase rho hrho
    hrhoBound idx' t' (fun i => s (φ (ind i))) p' anchor' r' (fun i => hs (φ (ind i)))
    (fun i => (hsmall' i).1) htlim' htime' hsmall'
    (fun i => hvol (φ (ind i))) (fun i => hnat (φ (ind i))) (fun i => hanchorDist (ind i))
    Q' hQ' (fun i => hscale (ind i)) (f ∘ ψ) (hf.comp hψ) Pl maps1 (M.compSubseq ψ hψ)
    hcanonical1 hradial ray hray hblow (ell ∘ ψ) (fun n => γ (ψ n))
    (helllim.comp hψ.tendsto_atTop) (fun n => hmin (ψ n)) _hstay
    (fun v => (hconv {v} isCompact_singleton).tendsto_at (mem_singleton v))
    (hhighSegment.comp hψ.tendsto_atTop) times htimes] with m hm
  rw [hxt m]
  exact hm

end GC.LongTime.Ch11
