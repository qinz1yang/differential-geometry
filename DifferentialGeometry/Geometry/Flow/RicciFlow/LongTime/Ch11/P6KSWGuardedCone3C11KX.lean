import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWGuardedTCC11KX

/-!
# KSW-EXIT G8：叶 C3（Cone3）证书 ⇒ guarded ShortSLT 无 binder（O-CH11-KSWEXIT，后缀 `_C11KX`）

G7 剩余 binder C3 = `GuardedCone3Leaf_C11KX`（Cone3Window_P6WA:69 的 guarded 形）。Cone3 证明里 U 侧数据只经
两个子叶：
* Cone2Window_P6WA:47（scaled tests 的 pointed convergence）——其内部只调 Cone / TTC window 叶 = 本车道
  S1 / S2（Tendsto 年龄 ⇒ Age_β：`age_of_tendsto_C11KS2`）⇒ guarded 副本
  `RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_guarded_C11KX`（PROVED）；
* TTC2Window_P6WA:79（historical solution with curvature bounds）——在树内叶
  `curvDerivNorm_historical_localPullback_le_of_backwardPointTrace_window_P6WA` 调用点（buffer 球 `K` 上
  `R ≤ 2·A·Q`、窗口 `[s − θ/Q, s)`、`6·C·(A·θ) ≤ 1`）把 `U` 缩成 `U′ := U ∩ {Rtop ≤ 2·A·Q}`（同 S2）
  ⇒ guarded 副本 `ObservedHistory.exists_eventually_historical_solution_guarded_C11KX`（PROVED；
  TTC2 私有 helper 逐字复制，源文件超宽行折行）。
* `guardedCone3Leaf_C11KX : GuardedCone3Leaf_C11KX`（**C3 PROVED**；Cone3 证明逐字，两处改调上面两条，
  `Rtop := R(s, ·)`、一致性 `metricScalarAt_restrictOpen`）。
**主定理** `shortSLT_guarded_C11KX (hθ : 0 < θ) : ShortSLTGuarded_C11KX θ`——**无 binder**
（G1 壳 ∘ G2 L1 / L2 ∘ G3 ∘ G4 ∘ G5 S2 ∘ G6 S1 ∘ G7 ∘ 本文件 C3）。
-/

set_option autoImplicit false

section

noncomputable section
open Set Filter Manifold Bundle TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem centered_ball_in_scaled_buffer_C11KX (g : SmoothRiemannianMetric I M)
    {Q R r : ℝ} (hQ : 0 < Q) (hR : 0 < R) (hr : 0 < r) {x z : M}
    (hK : IsCompact (riemannianClosedBallOf (scaleMetric Q hQ g) x (R + r)))
    (hz : riemannianEDistOf (scaleMetric Q hQ g) x z < ENNReal.ofReal R) :
    IsCompact (riemannianClosedBallOf g z (r / Real.sqrt Q)) ∧
      riemannianBallOf g z (r / Real.sqrt Q) ⊆
        interior (riemannianClosedBallOf (scaleMetric Q hQ g) x (R + r)) := by
  have heq : riemannianClosedBallOf (scaleMetric Q hQ g) z r =
      riemannianClosedBallOf g z (r / Real.sqrt Q) := by
    conv_lhs => rw [show r = Real.sqrt Q * (r / Real.sqrt Q) by field_simp]
    exact riemannianClosedBallOf_scaleMetric Q hQ g z _
  have hsub : riemannianClosedBallOf g z (r / Real.sqrt Q) ⊆
      riemannianBallOf (scaleMetric Q hQ g) x (R + r) := by
    intro y hy
    have hy' : riemannianEDistOf (scaleMetric Q hQ g) z y ≤ ENNReal.ofReal r := by
      change y ∈ riemannianClosedBallOf (scaleMetric Q hQ g) z r
      rwa [heq]
    change riemannianEDistOf (scaleMetric Q hQ g) x y < _
    calc
      _ ≤ riemannianEDistOf (scaleMetric Q hQ g) x z +
          riemannianEDistOf (scaleMetric Q hQ g) z y := riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal R + ENNReal.ofReal r :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy') hz hy'
      _ = ENNReal.ofReal (R + r) := (ENNReal.ofReal_add hR.le hr.le).symm
  refine ⟨hK.of_isClosed_subset (isClosed_riemannianClosedBallOf g z _) ?_, ?_⟩
  · intro y hy
    exact (show riemannianEDistOf (scaleMetric Q hQ g) x y < ENNReal.ofReal (R + r) from hsub hy).le
  · intro y hy
    exact riemannianBallOf_subset_interior_riemannianClosedBallOf _ _ _ (hsub (show
        riemannianEDistOf g z y ≤ ENNReal.ofReal (r / Real.sqrt Q) from le_of_lt hy))

end DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
      PointedRiemannianManifold.sigmaCompact
private local instance {H : ObservedHistory.{u}} {last : Fin (H.eventCount + 1)} {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **`_window_P6WA`**：`_P6L` 的时间窗版；原
`ObservedHistory.exists_eventually_historical_solution_with_curvature_bounds_of_pointed_convergence`
（`TracedTerminalCompactness:1576`）。改动：`U` 后加 `c`、`hQc`；`hderiv` / `hfinal` guard
`c n ≤ t`，pinching 取 `Ici (c n)`。结论逐字。 -/
theorem
    exists_eventually_historical_solution_guarded_C11KX
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    {s : ℕ → ℝ} (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (x : ∀ i, (G i).terminalRegularOpen)
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (q Q : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqQ : ∀ i, q i ≤ Q i)
    (hQ : ∀ i, 1 ≤ Q i)
    (Rtop : ∀ i, ((H i).stage (last i)).Carrier → ℝ)
    (hRtop : ∀ i (y : (G i).terminalRegularOpen), metricScalarAt (L i).metric y = Rtop i y.val)
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps
      { obj := fun i =>
          { M := (G i).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric (Q i) (zero_lt_one.trans_le (hQ i)) (L i).metric } } P phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hradial : ∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf P.metric P.basepoint R))
    (hupper : ∀ K : Set P.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric).inner
            (F.map i z)
          (mfderiv ThreeModel ThreeModel (F.map i) z v)
          (mfderiv ThreeModel ThreeModel (F.map i) z v) ≤ C ^ 2 * P.metric.inner z v v)
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (U : ∀ n, Set ((H n).stage (last n)).Carrier) (c : ℕ → ℝ)
    (hQc : Tendsto (fun i => Q (phi i) * (s (phi i) - c (phi i))) atTop atTop)
    (hU : ∀ n, ∀ y ∈ riemannianBallOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) rho, y.val ∈ U n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
      ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last n,
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n) first (last n) hle z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ), c n ≤ t →
      q n < ((H n).event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      GuardKX_C11KX (Rtop n) (q n) C (s n) t z →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), c n ≤ t → q n < (G n).flow.scalar t y →
      GuardKX_C11KX (Rtop n) (q n) C (s n) t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (c n)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n) ∩ Ici (c n)) Phi)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧ ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (x (phi i)) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (x (phi i)) (R + r), metricScalarAt (L (phi i)).metric y ≤ 2 * (A * Q (phi i))) ∧
        ∃ first : Fin ((H (phi i)).eventCount + 1), ∃ hle : first ≤ last (phi i),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
            (x (phi i)) (R + r),
            Nonempty (BackwardPointTrace (H (phi i)) first (last (phi i)) hle y.val)) ∧
          (H (phi i)).time first ≤ s (phi i) - θ / Q (phi i))
    (V : TopologicalSpace.Opens P.M) (hV : IsCompact (closure (V : Set P.M))) :
    ∃ R r A θ : ℝ, ∃ hθ : 0 < θ, ∃ B : ℕ → ℝ,
      0 < R ∧ 0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 6 * C * (A * θ) ≤ 1 ∧
      (∀ m, 0 ≤ B m) ∧ ∀ᶠ i in atTop,
      ∃ first : Fin ((H (phi i)).eventCount + 1), ∃ hle : first ≤ last (phi i),
      ∃ (Ψ : V → (H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
        (G (phi i)) (riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi
              i)) (R + r)))
        (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
        (hFv : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : V => F.map i z.val))
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x
                  (phi i)) (R + r))))
        (S : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le))),
        (V : Set P.M) ⊆ F.source i ∧
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (x (phi i)) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (x (phi i)) (R + r), metricScalarAt (L (phi i)).metric y ≤ 2 * (A * Q (phi i))) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi
              i)) (R + r),
          Nonempty (BackwardPointTrace (H (phi i)) first (last (phi i)) hle y.val)) ∧
        (H (phi i)).time first ≤ s (phi i) - θ / Q (phi i) ∧
        Function.Injective Ψ ∧
        (H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
          (G (phi i)) (riemannianClosedBallOf
            (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x
                (phi i)) (R + r)) ∘ Ψ =
              (fun z : V => F.map i z.val) ∧
        IsSolutionOn S ∧
        S.base.metric 0 = localPullMetric
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (fun z : V => F.map i z.val) hFv ∧
        (∀ t, S.base.metric t = localPullMetric
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (gflow (s (phi i) + t / Q
              (phi i)))) Ψ hΨ) ∧
        (∀ (j : Fin (H (phi i)).eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last (phi i)),
          ∀ t ∈ Icc ((H (phi i)).time j.castSucc) ((H (phi i)).time j.succ),
            gflow t = (((H (phi i)).backwardSurvivorSlabMetric first (last (phi i)) hle j hf hl
                t).restrictOpen ((H (phi i)).backwardSurvivorIncomingDomain first (last (phi i)) hle
                (G (phi i)))).restrictOpen
                  ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
                    (G (phi i)) (riemannianClosedBallOf
                      (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi
                          i)).metric) (x (phi i)) (R + r)))) ∧
        (∀ t ∈ Icc ((H (phi i)).time (last (phi i))) (s (phi i)),
          gflow t = ((H (phi i)).backwardSurvivorIncomingMetric first (last (phi i)) hle
            (G (phi i)) (L (phi i)) t).restrictOpen
              ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
                (G (phi i)) (riemannianClosedBallOf
                  (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
                      (x (phi i)) (R + r)))) ∧
        gflow (s (phi i)) = localPullMetric (L (phi i)).metric
          ((H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x
                  (phi i)) (R + r)))
          ((H (phi i)).backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (last (phi
              i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x
                  (phi i)) (R + r))) ∧
        ∀ m : ℕ, ∀ t ∈ Icc (-(θ / 2)) 0, ∀ z : V,
          curvDerivNorm m (S.base.metric t) z ≤ B m := by
  obtain ⟨R, hR, hRrho, hmaps⟩ :=
    F.exists_eventually_image_compact_subset_inner_ball hrho hradial hcompact hupper hV
  obtain ⟨r, A, θ, hr, hRr, hA, hθ, htime, hbuffer⟩ := hbuffer R hR hRrho
  let b := 4 * Real.sqrt 3 * A * (1 + Phi 4 + Phi 0)
  let B : ℕ → ℝ := fun m => shiLocalUniformBound 3 m (b * (θ / 4))
    (((r / 2) / (4 * Real.exp (9 * b * θ))) * Real.sqrt b /
      (4 * Real.exp (9 * b * (θ / 4)))) * b / Real.sqrt (θ / 4) ^ m
  have hb : 0 < b := by dsimp only [b]; positivity [hPhi.pos 4, hPhi.pos 0]
  refine ⟨R, r, A, θ, hθ, B, hR, hr, hRr, hA, htime, fun m => ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hb.le) (by positivity)
  filter_upwards [hmaps, hbuffer, hQc.eventually_ge_atTop θ] with i hi hbi hθi
  obtain ⟨hK, hscalar, first, hle, htrace, hstart⟩ := hbi
  have hQp : 0 < Q (phi i) := zero_lt_one.trans_le (hQ (phi i))
  have hwi : c (phi i) ≤ s (phi i) - θ / Q (phi i) := by
    have h1 : θ / Q (phi i) ≤ s (phi i) - c (phi i) := (div_le_iff₀ hQp).mpr (by linarith)
    linarith
  have hIci : Ici (s (phi i) - θ / Q (phi i)) ⊆ Ici (c (phi i)) := Ici_subset_Ici.mpr hwi
  let K := riemannianClosedBallOf
    (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
    (x (phi i)) (R + r)
  have hKU : ∀ y ∈ K, y.val ∈ U (phi i) := fun y hy =>
    hU (phi i) y (riemannianClosedBallOf_subset_riemannianBallOf_P6L _ _ hRr hrho hy)
  let Fv : V → (G (phi i)).terminalRegularOpen := fun z => F.map i z.val
  have hFv : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Fv := by
    apply DifferentialGeometry.isLocalDiffeomorph_restrict_open V
    intro z
    exact (F.partialDiffeomorph i).isLocalDiffeomorphAt ThreeModel ThreeModel ∞
      (hi.1 (subset_closure z.property))
  have hinjF : Function.Injective Fv := by
    intro z w heq
    apply Subtype.ext
    exact (F.partialDiffeomorph i).toPartialEquiv.injOn
      (hi.1 (subset_closure z.property)) (hi.1 (subset_closure w.property)) heq
  have hnear (z : V) : riemannianEDistOf
      (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
      (x (phi i)) (Fv z) < ENNReal.ofReal R := hi.2 ⟨z.val, subset_closure z.property, rfl⟩
  have himage (z : V) : Fv z ∈ interior K := by
    apply Geometry.Metric.riemannianBallOf_subset_interior_riemannianClosedBallOf _ _ _
    exact (hnear z).trans_le (ENNReal.ofReal_le_ofReal (by linarith : R ≤ R + r))
  obtain ⟨Ψ, hΨ, gflow, S, hPsi, hmap, hS, hzero, hmetric, hslabs, hlast, hterminal⟩ :=
    (H (phi i)).exists_historical_localPullback_solution_from_incoming_slab first (last (phi i)) hle
      (G (phi i)) (L (phi i)) (hinit (phi i)) K htrace Fv hFv himage
      (zero_lt_one.trans_le (hQ (phi i))) hθ.le hstart
  have hinj : Function.Injective Ψ := by
    rw [hPsi]
    exact (H (phi i)).backwardSurvivorIncomingFootprintLift_injective first (last (phi i)) hle
      (G (phi i)) K htrace Fv himage hinjF
  refine ⟨first, hle, Ψ, hΨ, hFv, gflow, S, (fun z hz => hi.1 (subset_closure hz)), hK, hscalar,
      htrace, hstart, hinj, hmap, hS, hzero,
    hmetric, hslabs, hlast, hterminal, ?_⟩
  intro m t ht z
  obtain ⟨hcompactZ, hballZ⟩ :=
    Geometry.Metric.centered_ball_in_scaled_buffer_C11KX (L (phi i)).metric
    (zero_lt_one.trans_le (hQ (phi i))) hR hr hK (hnear z)
  have hpoint : (H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
      (G (phi i)) K (Ψ z) = Fv z := congrFun hmap z
  have hqAQ : q (phi i) ≤ A * Q (phi i) :=
    (hqQ (phi i)).trans (le_mul_of_one_le_left (by linarith [hQ (phi i)]) hA)
  have hAQp : 0 < A * Q (phi i) := mul_pos (zero_lt_one.trans_le hA) hQp
  have hMc : (C : ℝ) * (2 * (A * Q (phi i))) * (θ / Q (phi i)) ≤ 1 / 2 := by
    have h1 : (C : ℝ) * (2 * (A * Q (phi i))) * (θ / Q (phi i)) =
        2 * ((C : ℝ) * (A * θ)) * (Q (phi i) / Q (phi i)) := by ring
    rw [h1, div_self hQp.ne', mul_one]
    nlinarith [htime]
  have hqM : q (phi i) ≤ 2 * (A * Q (phi i)) := by linarith [hqAQ, hAQp]
  let U' : Set ((H (phi i)).stage (last (phi i))).Carrier :=
    {z | z ∈ U (phi i) ∧ Rtop (phi i) z ≤ 2 * (A * Q (phi i))}
  have hgd : ∀ z ∈ U', ∀ t, t ≤ s (phi i) → s (phi i) - θ / Q (phi i) ≤ t →
      GuardKX_C11KX (Rtop (phi i)) (q (phi i)) C (s (phi i)) t z :=
    fun z hz t hts hst => guardKX_of_ceiling_C11KX C.coe_nonneg hz.2 hqM hts hst hMc
  have hjs : ∀ j : Fin (H (phi i)).eventCount, j.succ ≤ last (phi i) →
      (H (phi i)).time j.succ ≤ s (phi i) :=
    fun j hl => ((H (phi i)).time_strictMono.monotone hl).trans (G (phi i)).lt.le
  have hKU' : ∀ y ∈ K, y.val ∈ U' := by
    intro y hy
    refine ⟨hKU y hy, ?_⟩
    rw [← hRtop (phi i) y]
    exact hscalar y hy
  have h := (H (phi i)).curvDerivNorm_historical_localPullback_le_of_backwardPointTrace_window_P6WA
    first (last (phi i)) hle (G (phi i)) (L (phi i)) (hinit (phi i)) K gflow hslabs hlast Ψ hΨ S
    (C := C)
    hr (hq (phi i)) hqAQ (hQ (phi i)) hA hθ (fun t _ => hmetric t) z
    (by simpa only [hpoint] using hcompactZ) (by simpa only [hpoint] using hballZ) hPhi
    U' hKU'
    (fun j hf hl z hz Bt t ht hct hqt => hderiv (phi i) j first hle hf hl z hz.1 Bt t ht
      (hwi.trans hct) hqt (hgd z hz t (ht.2.le.trans (hjs j hl)) hct))
    (fun y hy t ht hct hqt => hfinal (phi i) y.val (hKU y hy) t ht (hwi.trans hct) hqt
      (hgd y.val (hKU' y hy) t ht.2.le hct))
    (fun j _ hl => RetainedCoreHistory.phiAlmostNonnegative_mono_P6N (hpinch (phi i) j hl)
      (inter_subset_inter_right _ hIci))
    (RetainedCoreHistory.phiAlmostNonnegative_mono_P6N (hpinchFinal (phi i))
      (inter_subset_inter_right _ hIci)) hscalar htrace hstart
    (by nlinarith [htime])
  exact h m t ht

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u v

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

/-- **guarded Cone2（`_C11KX`，PROVED）**：Cone2Window_P6WA:47 逐字 + `Rtop` / 一致性 + guard；证明改调
S1 `guardedConeLeaf_C11KX` 与 S2 `ObservedHistory.guardedTTCLeaf_C11KX`（`age_of_tendsto_C11KS2`）。 -/
theorem
    RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_guarded_C11KX
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → RetainedCoreHistory.{u})
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hs : ∀ n, (H n).horizon < s n)
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (Rtop : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier → ℝ)
    (hRtop : ∀ n (y : (G n).terminalRegularOpen), metricScalarAt (L n).metric y = Rtop n y.val)
    (hscale : ∀ n, Q n = metricScalarAt (L n).metric (x n))
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (U : ∀ n, Set ((H n).stage (Fin.last (H n).eventCount)).Carrier) (c : ℕ → ℝ)
    (hQc : Tendsto (fun n => Q n * (s n - c n)) atTop atTop)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ), c n ≤ t →
      q n < ((H n).toHistory.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (Fin.le_last _)) →
      GuardKX_C11KX (Rtop n) (q n) C (s n) t z →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hfinal : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n), c n ≤ t →
      q n < (G n).flow.scalar t y → GuardKX_C11KX (Rtop n) (q n) C (s n) t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount,
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (c n)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∩ Ici (c n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hU : ∀ n, ∀ y ∈ riemannianBallOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) rho, y.val ∈ U n)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ first : Fin ((H n).eventCount + 1),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
              (Fin.le_last first) y.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ n, σ₀ ≤ σ n * Real.sqrt (Q n))
    (htested : ∀ n (t : ℝ) (ht : (H n).horizon < t) (hts : t < s n), c n ≤ t →
      let A := (H n).extendHorizon t ht.le
        ((G n).closedPrefix t ((H n).time_le_horizon.trans_lt ht) hts) (hinit n)
      let time : Icc (0 : ℝ) A.horizon := ⟨t, (H n).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ z ∈ U n, GuardKX_C11KX (Rtop n) (q n) C (s n) t z →
      ∀ (y : (A.toHistory.stageAt time).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ n →
        A.toHistory.isParabolicallyRmControlledBall time y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (A.toHistory.stageAt time).Carrier
              (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
              (riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time)
                y b)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
        let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ M : MetricConvergenceData F',
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho →
          IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆
          F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ z ∈ F'.source n, ∀ v : TangentSpace ThreeModel z,
          (1 - eps) * P.metric.inner z v v ≤
            (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) ∧
          (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) ≤
            (1 + eps) * P.metric.inner z v v := by
  have hvol :=
    guardedConeLeaf_C11KX
    Phi hPhi H s G L hinit hs x q Q Rtop hRtop hq hqQ hQ U c (age_of_tendsto_C11KS2 hQc) hderiv
      hfinal hpinch hpinchFinal
      hU hbuffer σ hκ hσ₀ hσQ htested
  obtain ⟨f, hf, r, hr, hrlim, P, F, M, hM, hradial, hcompactP, hcapture, hbounds⟩ :=
    ObservedHistory.guardedTTCLeaf_C11KX
      Phi hPhi (fun n => (H n).toHistory) (fun n => Fin.last (H n).eventCount) s G L hinit
      x q Q Rtop hRtop hq hqQ hQ U c (age_of_tendsto_C11KS2 hQc) (fun n j first _ hf _ => hderiv n
          j first hf) hfinal
      (fun n j _ => hpinch n j) hpinchFinal hrho hU (by
        intro R hR hRrho
        obtain ⟨r, A, θ, hr, hrrho, hA, hθ, hbudget, hb⟩ := hbuffer R hR hRrho
        refine ⟨r, A, θ, hr, hrrho, hA, hθ, hbudget, ?_⟩
        filter_upwards [hb] with n hn
        obtain ⟨first, htrace, hstart⟩ := hn.2.2
        exact ⟨hn.1, hn.2.1, first, Fin.le_last first, htrace, hstart⟩) hvol
  have hbase : metricScalarAt P.metric P.basepoint = 1 :=
    Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains M hM (by
      intro n
      change metricScalarAt (scaleMetric (Q (f n)) (zero_lt_one.trans_le (hQ (f n)))
        (L (f n)).metric) (x (f n)) = 1
      rw [metricScalarAt_scaleMetric, ← hscale (f n), inv_mul_cancel₀]
      exact ne_of_gt (zero_lt_one.trans_le (hQ (f n))))
  exact ⟨f, hf, r, hr, hrlim, P, F, M, hbase, hM, hradial, hcompactP, hcapture, hbounds⟩

/-- **`_P6L` 私有副本**：原 private `localPullMetric_restrict_inner`（`Cone:38`），逐字。 -/
private theorem localPullMetric_restrict_inner_C11KX {M N : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    (g : SmoothRiemannianMetric ThreeModel N) (Φ : PartialDiffeomorph ThreeModel ThreeModel M N ∞)
    (V : TopologicalSpace.Opens M)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : V => Φ z.val))
    (z : V) (v w : TangentSpace ThreeModel z) :
    (localPullMetric g (fun z : V => Φ z.val) hf).inner z v w =
      g.inner (Φ z) (mfderiv ThreeModel ThreeModel Φ z v)
        (mfderiv ThreeModel ThreeModel Φ z w) := by
  rw [localPullMetric_inner]
  have hd := DifferentialGeometry.mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel) Φ V z
  rw [hd]
  rfl


open ObservedHistory in
/-- **叶 C3 证书（`_C11KX`，PROVED）**：Cone3Window_P6WA:69 证明逐字；Cone2 / TTC2 两处调用改调 guarded 副本
（`Rtop := R(s, ·)`，一致性 `metricScalarAt_restrictOpen`）。 -/
theorem guardedCone3Leaf_C11KX : GuardedCone3Leaf_C11KX.{u, v} := by
  intro H s A hinit Ctime q hq U c hderiv hfinal x Q hQ hqQ hQlim hQc hU Phi hPhi hpinch hpinchFinal
    hbuffer hs hscale κ σ₀ σ hκ hσ₀ hσQ htested N _ _ _ _ Hn xN B R hR hBsource hBbase hcapture
    hBconv
  let G := fun n => (A n).restrictIncoming le_rfl (A n).lt le_rfl
  let L := fun n => (A n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))
  have hconv :=
    RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_guarded_C11KX
    Phi hPhi H s G L hinit hs x q Q (fun n => (A n).flow.scalar (s n))
    (fun n y => metricScalarAt_restrictOpen _ _ _) hscale hq hqQ hQ U c hQc hderiv hfinal hpinch
        hpinchFinal
    one_pos hU hbuffer σ hκ hσ₀ hσQ htested
  dsimp only at hconv
  obtain ⟨f₂, hf₂, _, _, _, P₂, F₂, M, hbase₂, hcanonical, hradial, hcompact, _, _⟩ := hconv
  let F := PointedRiemannianConvergenceMaps.liftTargetOpen
    (S := { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } })
    (fun i => connectedComponentOpen (I := ThreeModel) (x i))
    (fun i => (mem_connectedComponent : x i ∈ connectedComponentOpen (I := ThreeModel) (x i))) F₂
  let V : TopologicalSpace.Opens P₂.M := ⟨riemannianBallOf P₂.metric P₂.basepoint (1 / 2),
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const⟩
  have hp : P₂.basepoint ∈ V := by
    change riemannianEDistOf P₂.metric P₂.basepoint P₂.basepoint < ENNReal.ofReal (1 / 2)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hpath : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_riemannianBallOf P₂.metric P₂.basepoint (by norm_num))
  have hVc : IsCompact (closure (V : Set P₂.M)) := by
    apply (hcompact (1 / 2) (by norm_num) (by norm_num)).of_isClosed_subset isClosed_closure
    refine closure_minimal (fun z (hz : riemannianEDistOf P₂.metric P₂.basepoint z <
      ENNReal.ofReal (1 / 2)) => (le_of_lt hz : riemannianEDistOf P₂.metric P₂.basepoint z ≤
        ENNReal.ofReal (1 / 2))) ?_
    exact isClosed_le (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
  have hupper : ∀ K : Set P₂.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i)))
          (L (f₂ i)).metric).inner (F.map i z)
          (mfderiv ThreeModel ThreeModel (F.map i) z v)
          (mfderiv ThreeModel ThreeModel (F.map i) z v) ≤ C ^ 2 * P₂.metric.inner z v v := by
    intro K hK C hC
    have hconv : metricSourceConvergesOn F
        (CanonicalMetricCompactness.canonicalSourceData F) K 0 := by
      have heq : M.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
      rw [← heq]
      exact M.converges K hK 0
    filter_upwards [pointed_metric_eventually_quadratic_bounds hK hconv
      (by nlinarith : 0 < C ^ 2 - 1)] with i hi
    intro z hz v
    simpa only [add_sub_cancel] using (hi.2 z hz v).2
  have hbuffer' : ∀ R : ℝ, 0 < R → R < 1 → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < 1 ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧ ∀ᶠ i in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
          (x (f₂ i)) (R + r)) ∧
        (∀ z ∈ riemannianClosedBallOf
          (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
          (x (f₂ i)) (R + r), metricScalarAt (L (f₂ i)).metric z ≤ 2 * (Amax * Q (f₂ i))) ∧
        ∃ first : Fin ((H (f₂ i)).eventCount + 1),
          ∃ hle : first ≤ Fin.last (H (f₂ i)).eventCount,
          (∀ z ∈ riemannianClosedBallOf
            (scaleMetric (Q (f₂ i)) (zero_lt_one.trans_le (hQ (f₂ i))) (L (f₂ i)).metric)
            (x (f₂ i)) (R + r),
            Nonempty (BackwardPointTrace (H (f₂ i)).toHistory first
              (Fin.last (H (f₂ i)).eventCount) hle z.val)) ∧
          (H (f₂ i)).time first ≤ s (f₂ i) - θ / Q (f₂ i) := by
    intro R hR hR1
    obtain ⟨r, Amax, θ, hr, hRr, hA, hθ, hbud, hev⟩ := hbuffer R hR hR1
    refine ⟨r, Amax, θ, hr, hRr, hA, hθ, hbud, ?_⟩
    filter_upwards [hf₂.tendsto_atTop.eventually hev] with i hi
    obtain ⟨first, htr, hst⟩ := hi.2.2
    exact ⟨hi.1, hi.2.1, first, Fin.le_last first, htr, hst⟩
  open ObservedHistory in
  obtain ⟨Rr, rr, Amax, θ, hθ, Bd, _, _, _, _, _, hBd, hev⟩ :=
    exists_eventually_historical_solution_guarded_C11KX
      (fun n => (H n).toHistory) (fun n => Fin.last (H n).eventCount) G x L hinit q Q hq hqQ hQ
      (fun n => (A n).flow.scalar (s n)) (fun n y => metricScalarAt_restrictOpen _ _ _) F
      one_pos hradial hcompact hupper Phi hPhi U c (hQc.comp hf₂.tendsto_atTop) hU
      (fun n j first _ hf _ => hderiv n j first hf) hfinal
      (fun n j _ => hpinch n j) hpinchFinal hbuffer' V hVc
  have hwin : ∀ᶠ i in atTop, c (f₂ i) ≤ s (f₂ i) - θ / Q (f₂ i) := by
    filter_upwards [(hQc.comp hf₂.tendsto_atTop).eventually_ge_atTop θ] with i hi
    have hQp : 0 < Q (f₂ i) := zero_lt_one.trans_le (hQ (f₂ i))
    change θ ≤ Q (f₂ i) * (s (f₂ i) - c (f₂ i)) at hi
    have h1 : θ / Q (f₂ i) ≤ s (f₂ i) - c (f₂ i) := (div_le_iff₀ hQp).mpr (by linarith)
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hev.and hwin)
  have hwin' : ∀ j : ℕ, c (f₂ (j + N)) ≤ s (f₂ (j + N)) - θ / Q (f₂ (j + N)) :=
    fun j => (hN (j + N) (Nat.le_add_left N j)).2
  choose first hle Ψ hΨ hFv gflow S hsource _ _ _ hstart _ _ hS hzero hmetric hslabs hlast _
    hcurv using fun j : ℕ => (hN (j + N) (Nat.le_add_left N j)).1
  have hsh : StrictMono (fun j : ℕ => j + N) := fun a b h => Nat.add_lt_add_right h N
  let F₃ := F.compSubseq (fun j => j + N) hsh
  let M₃ := M.compSubseq (fun j => j + N) hsh
  have hcan₃ (j : ℕ) : M₃.domain j = CanonicalMetricCompactness.canonicalSourceData F₃ j := by
    change (M.domain (j + N)).compSubseq _ hsh j = _
    rw [hcanonical (j + N)]
    rfl
  have hterm : ∀ j (z : V) (v w : TangentSpace ThreeModel z),
      ((S j).base.metric 0).inner z v w =
        (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
          (L (f₂ (j + N))).metric).inner (F₃.partialDiffeomorph j z)
          (mfderiv ThreeModel ThreeModel (F₃.partialDiffeomorph j) z v)
          (mfderiv ThreeModel ThreeModel (F₃.partialDiffeomorph j) z w) := by
    intro j z v w
    refine (congrArg (fun g : SmoothRiemannianMetric ThreeModel V => g.inner z v w)
      (hzero j)).trans ?_
    exact localPullMetric_restrict_inner_C11KX _ (F.partialDiffeomorph (j + N)) V (hFv j) z v w
  have hcurv' : ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∃ B' : ℝ, 0 ≤ B' ∧ ∀ᶠ j in atTop,
      ∀ t ∈ Icc (-(θ / 2)) 0, ∀ z ∈ K, curvDerivNorm m ((S j).base.metric t) z ≤ B' :=
    fun _ _ m => ⟨Bd m, hBd m, Eventually.of_forall fun j t ht z _ => hcurv j m t ht z⟩
  have hpa (j : ℕ) : Perelman.PhiAlmostNonnegative (S j) (Icc (-θ) 0)
      (Perelman.rescalePinchingFunction (Q (f₂ (j + N))) Phi) :=
    phiAlmostNonnegative_parabolic_backwardSurvivorIncomingFootprint_localPullback_window_P6WA
      (H (f₂ (j + N))).toHistory (first j) (Fin.last (H (f₂ (j + N))).eventCount)
      (hle j) (G (f₂ (j + N))) (L (f₂ (j + N)))
      (riemannianClosedBallOf (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ _))
        (L (f₂ (j + N))).metric) (x (f₂ (j + N))) (Rr + rr))
      (gflow j) (hslabs j) (hlast j) hPhi.contDiff.continuous (hstart j)
      (sub_lt_self _ (div_pos hθ (zero_lt_one.trans_le (hQ (f₂ (j + N))))))
      (fun jj _ _ => RetainedCoreHistory.phiAlmostNonnegative_mono_P6N (hpinch (f₂ (j + N)) jj)
        (inter_subset_inter_right _ (Ici_subset_Ici.mpr (hwin' j))))
      (RetainedCoreHistory.phiAlmostNonnegative_mono_P6N (hpinchFinal (f₂ (j + N)))
        (inter_subset_inter_right _ (Ici_subset_Ici.mpr (hwin' j))))
      (zero_lt_one.trans_le (hQ (f₂ (j + N)))) le_rfl (Ψ j) (hΨ j) (S j)
      (fun v _ => hmetric j v)
  have hpinching : ∀ t ∈ Icc (-(θ / 2)) 0, ∀ᶠ j in atTop, ∀ z : V,
      curvatureOperatorLowerBoundAt ((S j).base.metric t) z
        (metricAlgebraicCurvatureTensorAt ((S j).base.metric t) z)
        (Perelman.rescalePinchingFunction (Q (f₂ (j + N))) Phi
          (metricScalarAt ((S j).base.metric t) z)) := by
    intro t ht
    exact Eventually.of_forall fun j z => hpa j t ⟨by linarith [ht.1], ht.2⟩ z
  have hBconv' : ∀ eta : ℝ, 0 < eta → ∀ᶠ j in atTop,
      ∀ y ∈ riemannianClosedBallOf (Hn (f₂ (j + N))) (xN (f₂ (j + N))) R,
      ∀ v : TangentSpace ThreeModel y,
        (1 - eta) * (Hn (f₂ (j + N))).inner y v v ≤
          (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
            (L (f₂ (j + N))).metric).inner (B (f₂ (j + N)) y)
            (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v)
            (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v) ∧
        (scaleMetric (Q (f₂ (j + N))) (zero_lt_one.trans_le (hQ (f₂ (j + N))))
          (L (f₂ (j + N))).metric).inner (B (f₂ (j + N)) y)
          (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v)
          (mfderiv ThreeModel ThreeModel (B (f₂ (j + N))) y v) ≤
            (1 + eta) * (Hn (f₂ (j + N))).inner y v v :=
    fun eta heta => (hf₂.comp hsh).tendsto_atTop.eventually (hBconv eta heta)
  obtain ⟨_, _, g, hgb, hsol, hnonneg, _, r, hr, hcpt, hcenter, hcap, hdist⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_nonnegative_local_flow_with_end_comparison
      F₃ M₃ hcan₃ V hp (fun j => hsource j) S hS (a := -(θ / 2)) (b := 0) (by linarith)
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩) (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
      hterm hcurv' hPhi (fun j => Q (f₂ (j + N))) (fun j => zero_lt_one.trans_le (hQ _))
      (hQlim.comp (hf₂.comp hsh).tendsto_atTop) hpinching
      (fun j => Hn (f₂ (j + N))) (fun j => xN (f₂ (j + N))) (fun j => B (f₂ (j + N))) hR
      (fun j => hBsource _) (fun j => hBbase _) (fun j => hcapture _) hBconv'
  exact ⟨fun j => f₂ (j + N), hf₂.comp hsh, P₂, V, hp, hpath, θ / 2, by positivity, g, hgb,
    hbase₂, hsol, hnonneg, _, hcenter, r, hr, hcpt, hcap, hdist⟩


/-- **KSW-EXIT 主定理（`_C11KX`，PROVED，无 binder）**：guarded ShortSLT 对任意 `θ > 0` 成立。 -/
theorem shortSLT_guarded_C11KX {θ : ℝ} (hθ : 0 < θ) : ShortSLTGuarded_C11KX.{u} θ :=
  shortSLT_guarded_of_cone3_C11KX guardedCone3Leaf_C11KX hθ

/-- consumer：guarded ShortSLT ⇒ 旧合同 ⇒ K-SW（`0 < θ₀ ≤ 1/2`），无 binder。 -/
example {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2) : KSW_C11KS.{u} θ₀ :=
  ksw_of_shortSLT_C11KS hθ₀ hθ₀2 (ShortSLTGuarded_C11KX.toShortSLT (shortSLT_guarded_C11KX hθ₀))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
