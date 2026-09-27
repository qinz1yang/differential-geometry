import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckDepthInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckExtendHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAtBefore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitScalarBound

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (SpatialCanonicalWitness SpatialCanonicalAlternative)
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

private local instance {M : Type u} [TopologicalSpace M] (U : Opens M) : MeasurableSpace U :=
  borel U

private local instance {M : Type u} [TopologicalSpace M] (U : Opens M) : BorelSpace U := ⟨rfl⟩

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_bounded_ancient_pointed_flow_limit_extendAt_of_forall_neckAlternative :
    ∃ epsW : ℝ, 0 < epsW ∧
    ∀ {P₀ : ℕ → OrientedThreeStage.{u}} (H Hext : ∀ n, RetainedCoreHistory (P₀ n))
      (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) {s τ : ℕ → ℝ}
      (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
        ((H n).time (Fin.last (H n).eventCount)) (s n))
      (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
        (H n).initialMetric (Fin.last (H n).eventCount))
      (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < τ n) (hτs : ∀ n, τ n < s n),
      (∀ n, Hext n = (H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)) →
    ∀ (t : ∀ n, Icc (0 : ℝ) (Hext n).toHistory.horizon), (∀ n, (t n : ℝ) = τ n) →
    ∀ (y : ∀ n, ((Hext n).toHistory.stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n),
      Tendsto R atTop atTop → Tendsto (fun n => R n * τ n) atTop atTop →
    ∀ {κ ε ε₁ C1 C2 qcan : ℝ} {Ctime : ℝ≥0} {phi : ℝ → ℝ}, 0 < κ → 0 < ε → ε ≤ epsW →
      ε₁ ≤ 1 / 30000 → (∀ n, qcan ≤ R n) → Perelman.AdmissiblePinchingFunction phi →
      (∀ n, (H n).EventSlabsPinched phi) →
      (∀ n, Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi) →
      (∀ n, (H n).EventSlabsDerivative Ctime qcan (Fin.last (H n).eventCount)) →
      (∀ n, (G n).DerivativeBoundBefore Ctime qcan (s n)) →
      (∀ n, (H n).EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan (Fin.last (H n).eventCount)) →
      (∀ n, (H n).StronglyCanonicalBefore (Fin.last (H n).eventCount) (G n) ε ε₁ C1 C2 qcan
        (s n)) →
      (∀ n, (H n).NoncollapsedBefore κ ε ((H n).time (Fin.last (H n).eventCount))) →
      (∀ n, (H n).TerminalNoncollapsedBefore (hend n) (G n) (hG n) κ ε (τ n)) →
    ∀ {Qup : ℝ},
      (∀ A : ℝ, 0 < A → ∃ Qlow : ℝ, 0 < Qlow ∧ ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage (t n)) (t n)) (y n)
            (A / Real.sqrt (R n)),
          Qlow * R n ≤ metricScalarAt
              ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage (t n)) (t n)) x ∧
            metricScalarAt
              ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage (t n)) (t n)) x ≤
                Qup * R n) →
      (∀ T : ℝ, 0 ≤ T →
        (∀ A T' : ℝ, 0 < A → 0 < T' → T' ≤ T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
          (Hext n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T' / R n)
            (K * R n)) →
        ∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop,
          ∀ x ∈ riemannianBallOf
              ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage (t n)) (t n)) (y n)
              (A / Real.sqrt (R n)),
          ∀ v : Icc (0 : ℝ) (Hext n).toHistory.horizon, (t n : ℝ) - T / R n ≤ v →
          ∀ hvt : v ≤ t n, (Hext n).time ((Hext n).toHistory.activeStage v) < v →
          ∀ B : BackwardPointTrace (Hext n).toHistory ((Hext n).toHistory.activeStage v)
              ((Hext n).toHistory.activeStage (t n)) ((Hext n).toHistory.activeStage_mono hvt) x,
            c * R n ≤ metricScalarAt
              ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage v) v)
              (B.point ((Hext n).toHistory.activeStage v) le_rfl
                ((Hext n).toHistory.activeStage_mono hvt)) →
            ∀ W : SpatialCanonicalWitness
                ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage v) v) ε C1 C2
                (B.point ((Hext n).toHistory.activeStage v) le_rfl
                  ((Hext n).toHistory.activeStage_mono hvt)),
              W.capTubeHasNeckChart ε →
                ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((Hext n).toHistory.stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage (t n)) (t n)) } }
    ∃ (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
      (h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)),
      (∀ k : ℕ, ∀ᶠ n in atTop,
        (W k n : Set (X.obj n).M) =
          riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) ∧
        IsSolutionOn ({ base.metric := h k n } : SolutionOn (I := ThreeModel) (M := W k n)
          (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
            (neg_nonpos.mpr (Nat.cast_nonneg _)))) ∧
        (∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
          (t n : ℝ) + s / R n ∈
            (Hext n).toHistory.stageDomain ((Hext n).toHistory.activeStage (t n)) →
          h k n s = scaleMetric (R n) (hR n)
            (((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage (t n))
              ((t n : ℝ) + s / R n)).restrictOpen (W k n))) ∧
        (∃ (a : Icc (0 : ℝ) (Hext n).toHistory.horizon) (hat : a ≤ t n),
          (a : ℝ) = t n - 2 * ((k + 2 : ℕ) : ℝ) / R n ∧
          ∃ f : (j : (Hext n).toHistory.StageInterval ((Hext n).toHistory.activeStage a)
              ((Hext n).toHistory.activeStage (t n))) →
              W k n → ((Hext n).toHistory.stage j.val).Carrier,
            ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
              (∀ j, Function.Injective (f j)) ∧
              (∀ (i : Fin (Hext n).toHistory.eventCount)
                  (hi : (Hext n).toHistory.activeStage a ≤ i.castSucc)
                  (hl : i.succ ≤ (Hext n).toHistory.activeStage (t n)), ∀ x : W k n,
                ((Hext n).toHistory.event i).RegularCrossing
                  (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                  (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
              (∀ x : W k n,
                f ⟨(Hext n).toHistory.activeStage (t n), (Hext n).toHistory.activeStage_mono hat,
                  le_rfl⟩ x = x.val) ∧
              ∀ s ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0,
                ∀ j : (Hext n).toHistory.StageInterval ((Hext n).toHistory.activeStage a)
                    ((Hext n).toHistory.activeStage (t n)),
                  (t n : ℝ) + s / R n ∈ (Hext n).toHistory.stageDomain j.val →
                    h k n s = scaleMetric (R n) (hR n)
                      (localPullMetric ((Hext n).toHistory.stageMetric j.val ((t n : ℝ) + s / R n))
                        (f j) (hf j))) ∧
        ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, (t n : ℝ) + σ / R n < t n → ∀ z : W k n,
          ∀ r : ℝ, 0 < r →
          r ≤ ε * Real.sqrt (R n) → Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
          IsCompact (riemannianClosedBallOf (h k n σ) z r) →
          (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
            r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
          ENNReal.ofReal (κ * r ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
              (riemannianBallOf (h k n σ) z r)) ∧
      (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) ∧
      (∀ k : ℕ, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0, ∀ x : W k n,
        metricScalarAt (h k n s) x ≤ B) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ (x : W k n)
        (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) ∧
      ∃ (f : ℕ → ℕ), StrictMono f ∧
        ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (F : PointedRiemannianConvergenceMaps X P f),
          (∃ C : MetricConvergenceData F,
            ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
          MetricComplete P ∧ ConnectedSpace P.M ∧
          (∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
            riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint R ⊆
              F.target n) ∧
          ∃ (V : ℕ → Opens P.M) (N : ℕ → ℕ),
            (∀ k, (V k : Set P.M) =
              riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) ∧
            (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) ∧
            ∃ (φ : ∀ k j, N k ≤ j → V k → W k (f j))
              (hφ : ∀ k j (hj : N k ≤ j),
                IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)),
              (∀ k j (hj : N k ≤ j) (z : V k), ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) =
                F.map j z) ∧
              ∃ G : ℝ → SmoothRiemannianMetric ThreeModel P.M,
                G 0 = P.metric ∧
                IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
                  (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
                ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                  (∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η) ∧
                  (∀ ρ' : ℝ, 0 < ρ' → Perelman.ParabolicallyKappaNoncollapsedBelowScale
                    ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
                      (RealTimeInterval.infiniteClosed 0 0 le_rfl)) (κ / 250) ρ') ∧
                  ∃ C : ℝ, ∀ s ≤ 0, ∀ x : P.M, metricScalarAt (G s) x ≤ C := by
  obtain ⟨epsW, hepsW, hB13⟩ :=
    ObservedHistory.exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before.{u}
  refine ⟨epsW, hepsW, ?_⟩
  intro P₀ H Hext hend s τ G hG hat hτs hext t ht y R hR hRlim hRt κ ε ε₁ C1 C2 qcan Ctime phi hκ
    hε hεW hε₁ hqR hphi hpinch hpinchG hderiv hderivG hclass hcanG hnc hncG Qup hball hsupply
  obtain rfl : Hext = fun n => (H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n) :=
    funext hext
  have hlastv : ∀ n (v : Icc (0 : ℝ)
      ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.horizon),
      (H n).time (Fin.last (H n).eventCount) ≤ v →
      ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage v =
        Fin.last (H n).eventCount := fun n v hv =>
    (H n).activeStage_extendHorizon_eq_last _ _ _ v hv
  have hlastt : ∀ n,
      ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage (t n) =
        Fin.last (H n).eventCount := fun n =>
    hlastv n (t n) (by rw [ht n]; exact (hat n).le)
  have htraced := exists_isTracedRegion_of_forall_neckAlternative_of_depth_induction
    (fun n => (H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)) t y R hRlim
    (by simpa only [ht] using hRt) hphi (fun n => hpinch n)
    (fun n _ => extendHorizon_finalSlab_phiAlmostNonnegative (hT := hat n) (hTs := hτs n)
      (hpinchG n))
    (fun n => by rw [hlastt n, ht n]; exact hat n) hε₁
    (fun c hc => (hRlim.eventually_gt_atTop (qcan / c)).mono fun n hn => by
      rwa [div_lt_iff₀ hc, mul_comm] at hn)
    (fun n => ((H n).eventSlabsStronglyCanonical_extendHorizon_iff _ _ _ _ ε ε₁ C1 C2 qcan
      _).2 (hclass n))
    (fun n v _ _ hv => (H n).exists_slab_stronglyCanonicalBefore_extendHorizon_closedPrefix
      (hend n) (G n) (hG n) (hat n) (hτs n) (hcanG n) v hv)
    hball hsupply
  refine hB13 (fun n => ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory) t y R hR
    hRlim htraced hκ hε (t₀ := fun n => t n) (by simp) ?_ hphi ?_ hε hεW (C1 := C1) (C2 := C2)
    (Cs := 1) (Cq := 1) (Ctime := Ctime)
    (qs := fun _ => qcan) (qcan := fun _ => qcan) (fun n => by simpa using hqR n)
    (fun n => by simpa using hqR n) ?_ ?_
  · intro n v p r hv hr hball'
    exact (H n).volume_ge_extendAt_of_terminalNoncollapsedBefore (hend n) (G n) (hG n) (hat n)
      (hτs n) (hnc n) (hncG n) v p r (hv.trans_eq (ht n)) hr hball'
  · intro n v _ x
    exact (H n).curvatureOperatorLowerBoundAt_extendAt_of_pinched (hend n) (G n) (hG n) (hat n)
      (hτs n) (hpinch n) (hpinchG n) v x
  · intro n v hv hev p hq
    exact (H n).exists_spatialCanonicalWitness_extendAt_of_before (hend n) (G n) (hG n) (hat n)
      (hτs n) (fun j hj => (hclass n j hj).spatiallyCanonicalBefore)
      (hcanG n).spatiallyCanonicalBefore v ((hv.trans_eq (ht n)).trans (hτs n)) hev p hq
  · intro n v hv hev p hq
    refine ((H n).extendAt (hend n) (G n) (hG n) (hat n)
      (hτs n)).abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt (t := t n)
      (t₀ := t n) le_rfl ?_ ?_ ?_ v hv hev p hq
    · rw [hlastt n]
      exact hderiv n
    · intro j hj
      exact absurd (hj.trans (hlastt n)) (Fin.castSucc_lt_last j).ne
    · intro h _
      exact extendHorizon_finalSlab_derivativeBoundBefore (hderivG n)
        (by rw [ht n]; exact (hτs n).le) h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
