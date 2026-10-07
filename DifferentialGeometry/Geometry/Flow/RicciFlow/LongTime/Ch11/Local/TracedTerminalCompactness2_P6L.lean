import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedTerminalCompactness_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HistorySurvivorIncomingDerivatives2_P6L

/-!
# L6-B 第 2 层：`TracedTerminalCompactness:1576` 的局部化（`_P6L`）

局部化合同 §2：原
`ObservedHistory.exists_eventually_historical_solution_with_curvature_bounds_of_pointed_convergence`
（`ST/TracedTerminalCompactness.lean:1576`，Cone:365 的 historical solution 步）的 `hderiv`/`hfinal`
只经 `HistorySurvivorIncomingDerivatives:107` 在 buffer 球 `K = B_{Q·g}(x, R + r)` 的足迹上用
（`R + r < rho`）。这里加 `U`、`hU : ∀ n, B_{Q n·g}(x n, rho) ⊆ U n`（在 `hderiv` 之前），
`hderiv` 改 footprint 形、`hfinal` 限于 `U n`，叶子换 `…_P6L`。私有 `centered_ball_in_scaled_buffer`
（`:1534`）一并复制。证明体照抄。
-/

set_option autoImplicit false

section

set_option autoImplicit false
noncomputable section
open Set Filter Manifold Bundle TopologicalSpace
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem centered_ball_in_scaled_buffer_P6L (g : SmoothRiemannianMetric I M)
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
    exact riemannianBallOf_subset_interior_riemannianClosedBallOf _ _ _ (hsub (show riemannianEDistOf g z y ≤ ENNReal.ofReal (r / Real.sqrt Q) from le_of_lt hy))

end DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
private local instance {H : ObservedHistory.{u}} {last : Fin (H.eventCount + 1)} {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **`_P6L`**：原
`ObservedHistory.exists_eventually_historical_solution_with_curvature_bounds_of_pointed_convergence`
（`TracedTerminalCompactness:1576`）。改动：加 `U`、`hU`（`hderiv` 之前）；`hderiv` footprint 形、
`hfinal` 限于 `U n`。结论逐字。 -/
theorem exists_eventually_historical_solution_with_curvature_bounds_of_pointed_convergence_P6L
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    {s : ℕ → ℝ} (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (x : ∀ i, (G i).terminalRegularOpen)
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (q Q : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqQ : ∀ i, q i ≤ Q i)
    (hQ : ∀ i, 1 ≤ Q i)
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps
      { obj := fun i => { M := (G i).terminalRegularOpen, basepoint := x i, metric := scaleMetric (Q i) (zero_lt_one.trans_le (hQ i)) (L i).metric } } P phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hradial : ∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf P.metric P.basepoint R))
    (hupper : ∀ K : Set P.M, IsCompact K → ∀ C : ℝ, 1 < C → ∀ᶠ i in atTop,
      ∀ z ∈ K, ∀ v : TangentSpace ThreeModel z,
        (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric).inner (F.map i z)
          (mfderiv ThreeModel ThreeModel (F.map i) z v)
          (mfderiv ThreeModel ThreeModel (F.map i) z v) ≤ C ^ 2 * P.metric.inner z v v)
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (U : ∀ n, Set ((H n).stage (last n)).Carrier)
    (hU : ∀ n, ∀ y ∈ riemannianBallOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) rho, y.val ∈ U n)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
      ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last n,
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n) first (last n) hle z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n)) Phi)
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
    (V : Opens P.M) (hV : IsCompact (closure (V : Set P.M))) :
    ∃ R r A θ : ℝ, ∃ hθ : 0 < θ, ∃ B : ℕ → ℝ,
      0 < R ∧ 0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 6 * C * (A * θ) ≤ 1 ∧
      (∀ m, 0 ≤ B m) ∧ ∀ᶠ i in atTop,
      ∃ first : Fin ((H (phi i)).eventCount + 1), ∃ hle : first ≤ last (phi i),
      ∃ (Ψ : V → (H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
        (G (phi i)) (riemannianClosedBallOf
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r)))
        (hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ)
        (hFv : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : V => F.map i z.val))
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r))))
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
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r),
          Nonempty (BackwardPointTrace (H (phi i)) first (last (phi i)) hle y.val)) ∧
        (H (phi i)).time first ≤ s (phi i) - θ / Q (phi i) ∧
        Function.Injective Ψ ∧
        (H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
          (G (phi i)) (riemannianClosedBallOf
            (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r)) ∘ Ψ =
              (fun z : V => F.map i z.val) ∧
        IsSolutionOn S ∧
        S.base.metric 0 = localPullMetric
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric)
          (fun z : V => F.map i z.val) hFv ∧
        (∀ t, S.base.metric t = localPullMetric
          (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (gflow (s (phi i) + t / Q (phi i)))) Ψ hΨ) ∧
        (∀ (j : Fin (H (phi i)).eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last (phi i)),
          ∀ t ∈ Icc ((H (phi i)).time j.castSucc) ((H (phi i)).time j.succ),
            gflow t = (((H (phi i)).backwardSurvivorSlabMetric first (last (phi i)) hle j hf hl t).restrictOpen ((H (phi i)).backwardSurvivorIncomingDomain first (last (phi i)) hle
                (G (phi i)))).restrictOpen
                  ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
                    (G (phi i)) (riemannianClosedBallOf
                      (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r)))) ∧
        (∀ t ∈ Icc ((H (phi i)).time (last (phi i))) (s (phi i)),
          gflow t = ((H (phi i)).backwardSurvivorIncomingMetric first (last (phi i)) hle
            (G (phi i)) (L (phi i)) t).restrictOpen
              ((H (phi i)).backwardSurvivorIncomingFootprint first (last (phi i)) hle
                (G (phi i)) (riemannianClosedBallOf
                  (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r)))) ∧
        gflow (s (phi i)) = localPullMetric (L (phi i)).metric
          ((H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r)))
          ((H (phi i)).backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first (last (phi i)) hle
            (G (phi i)) (riemannianClosedBallOf
              (scaleMetric (Q (phi i)) (zero_lt_one.trans_le (hQ (phi i))) (L (phi i)).metric) (x (phi i)) (R + r))) ∧
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
  filter_upwards [hmaps, hbuffer] with i hi hbi
  obtain ⟨hK, hscalar, first, hle, htrace, hstart⟩ := hbi
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
  refine ⟨first, hle, Ψ, hΨ, hFv, gflow, S, (fun z hz => hi.1 (subset_closure hz)), hK, hscalar, htrace, hstart, hinj, hmap, hS, hzero,
    hmetric, hslabs, hlast, hterminal, ?_⟩
  intro m t ht z
  obtain ⟨hcompactZ, hballZ⟩ :=
    Geometry.Metric.centered_ball_in_scaled_buffer_P6L (L (phi i)).metric
    (zero_lt_one.trans_le (hQ (phi i))) hR hr hK (hnear z)
  have hpoint : (H (phi i)).backwardSurvivorIncomingFootprintMap first (last (phi i)) hle
      (G (phi i)) K (Ψ z) = Fv z := congrFun hmap z
  have hqAQ : q (phi i) ≤ A * Q (phi i) :=
    (hqQ (phi i)).trans (le_mul_of_one_le_left (by linarith [hQ (phi i)]) hA)
  have h := (H (phi i)).curvDerivNorm_historical_localPullback_le_of_backwardPointTrace_P6L
    first (last (phi i)) hle (G (phi i)) (L (phi i)) (hinit (phi i)) K gflow hslabs hlast Ψ hΨ S
    (C := C)
    hr (hq (phi i)) hqAQ (hQ (phi i)) hA hθ (fun t _ => hmetric t) z
    (by simpa only [hpoint] using hcompactZ) (by simpa only [hpoint] using hballZ) hPhi
    (U (phi i)) hKU (fun j hf hl => hderiv (phi i) j first hle hf hl)
    (fun y hy => hfinal (phi i) y.val (hKU y hy))
    (fun j _ hl => hpinch (phi i) j hl) (hpinchFinal (phi i)) hscalar htrace hstart
    (by nlinarith [htime])
  exact h m t ht

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end
