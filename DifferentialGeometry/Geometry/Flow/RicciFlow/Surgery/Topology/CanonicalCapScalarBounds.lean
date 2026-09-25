import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapInitialLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.MarkedScalarBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalIncomingScalarDerivative

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_uniform_scalar_derivative_bounds_at_canonical_cap_points_of_vanishing_age
    (N : ℕ) (hN : 2 ≤ N) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ Cphys : ℝ, 0 < C₀ ∧ 0 < Cphys ∧
      ∀ (C : ℝ≥0), ∃ (η ε₀ δ₀ : ℝ), 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      (∀ i, (parameters i).modelAccuracy ≤ ε₀) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ (q₀ a₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
      (∀ i, q₀ i ≤ C₀ * q i) → (∀ i, 1 ≤ a₀ i * q i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) (a₀ i) x) →
      (∀ i x, -3 / a₀ i ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ i < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (A i).flow.scalar t x →
        |derivWithin (fun v => (A i).flow.scalar v x) (Iic t) t| ≤ C * (A i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, ((H i).stage (last i)).Carrier)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i)),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      ∀ᶠ i in atTop,
        (∀ v : TangentSpace ThreeModel (x i),
          |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i) v)| ≤
            Cphys * (A i).flow.scalar (time i) (x i) * Real.sqrt ((A i).flow.scalar (time i) (x i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v)) ∧
        |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (time i)) (time i)| ≤
          Cphys * (A i).flow.scalar (time i) (x i) ^ 2 := by
  obtain ⟨C₀, B, Cderiv, hC₀, hB, hCderiv, huniform⟩ :=
    exists_uniform_canonical_cap_window_convergence_and_uniform_scalar_derivative_bounds_at_vanishing_age
      N D r eps heps hepssmall hr hfit
  have hcore : StandardCap.transitionEnd < r := by linarith [inv_pos.mpr heps]
  have hcoreD : StandardCap.transitionEnd < D + 1 := by linarith [hfit, inv_pos.mpr heps, StandardCap.transitionEnd_pos]
  obtain ⟨Cphys, hCphys, hphysical⟩ :=
    StandardCap.exists_eventually_relative_scalar_derivative_bounds_of_metric_cp_convergence
      hcoreD hN B (zero_le_one.trans hB)
  refine ⟨C₀, Cphys, hC₀, hCphys, ?_⟩
  intro C
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hproducer⟩ := huniform C
  refine ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H event last hle time A hinit parameters records boundary cap q age
    hcanonical hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth
  let G i := (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L i := (A i).endpointTerminalLimitMetric ((H i).stage (last i))
  let x' (i : ℕ) : (G i).terminalRegularOpen := ⟨x i, by
    change x i ∈ (G i).terminalRegularRegion
    rw [(A i).terminalRegularRegion_eq_univ ((H i).stage (last i))]
    trivial⟩
  obtain ⟨x₀, delta, order, datum, w, hwscalar, hwmetric, u, Ξ, hΞ, gflow, hmargin', hpos, S,
    hu, hucap, hΞsmooth, hΞbirth, hΞpoint, hslabs, hlast, hS, hgram, hjets, hbounds, hzero,
    hmetric, hterminal, hconvergence, hmarked, hcaps⟩ :=
    hproducer H event last hle time G L hinit parameters records boundary hcanonical hmargin hm
      herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal hage hagelim z x' trace hbirth
  have hagepos (i : ℕ) : 0 < age i := by
    exact mul_pos (cap i).neck.scale_pos
      (sub_pos.mpr (((H i).time_strictMono.monotone (hle i)).trans_lt (A i).lt))
  have hp := hphysical (fun i => RealTimeInterval.closed 0 (age i) (hpos i)) age hagepos
    S hS (fun _ => Subset.rfl) (fun _ => Subset.rfl)
    (fun i j hj t ht y hy => hjets i j (hj.trans hN) t ht y (hy.trans hcore.le))
    (hconvergence StandardCap.transitionEnd hcore)
    (fun i => (H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i))
    gflow Ξ hΞ q (fun i => (H i).time (event i).succ)
    (fun i => (cap i).neck.scale_pos) (fun i t _ => hmetric i t)
  filter_upwards [hp] with i hi
  have hb := hi (u i) (hu i)
  have hclock : (H i).time (event i).succ + age i / q i = time i := by
    dsimp only [age]
    rw [mul_div_cancel_left₀ _ (show q i ≠ 0 from (cap i).neck.scale_pos.ne')]
    ring
  rw [hclock] at hb
  have hpoint : (Ξ i (u i)).val.val = x i := congrArg Subtype.val (hΞpoint i)
  have hgradient := (H i).scalar_gradient_bound_closed_slab_endpoint_of_backwardSurvivorIncomingMetric
    (event i).succ (last i) (hle i) (A i) (gflow i (time i))
    (hlast i (time i) ⟨(A i).lt.le, le_rfl⟩) (Ξ i (u i)) hb.1
  have heq := (H i).scalar_eventually_eq_backwardSurvivorIncomingDomain_of_closed_slab_endpoint
    (event i).succ (last i) (hle i) (A i) (gflow i) (hlast i) (Ξ i (u i))
  have htime := hb.2
  rw [heq.derivWithin_eq_of_mem (mem_Iic.mpr le_rfl),
    heq.eq_of_nhdsWithin (mem_Iic.mpr le_rfl)] at htime
  rw [hpoint] at hgradient htime
  exact ⟨hgradient, htime⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

section

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (A : (H.stage last).ClosedSlab (H.time last) s)

variable {E XH X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
  [TopologicalSpace X] [ChartedSpace XH X] [IsManifold I ∞ X] [T2Space X]

private theorem backwardSurvivorIncoming_ambient_localPullMetric
    (Ψ : X → H.backwardSurvivorIncomingDomain first last hle
      (A.restrictIncoming le_rfl A.lt le_rfl))
    (hΨ : IsLocalDiffeomorph I ThreeModel ∞ Ψ)
    (hΨinj : Function.Injective Ψ) (q : ℝ) (hq : 0 < q) :
    let Φ : X → (H.stage last).Carrier := fun y => (Ψ y).val.val
    ∃ hΦ : IsLocalDiffeomorph I ThreeModel ∞ Φ, Function.Injective Φ ∧
      localPullMetric (scaleMetric q hq
        (H.backwardSurvivorIncomingMetric first last hle
          (A.restrictIncoming le_rfl A.lt le_rfl)
          (A.endpointTerminalLimitMetric (H.stage last)) s)) Ψ hΨ =
        localPullMetric (scaleMetric q hq (A.flow.base.metric s)) Φ hΦ := by
  let G := A.restrictIncoming le_rfl A.lt le_rfl
  let V := H.backwardSurvivorIncomingDomain first last hle G
  let f : V → (H.stage last).Carrier := fun y => y.val.val
  have hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    isLocalDiffeomorph_comp
      (isLocalDiffeomorph_subtype_val (H.backwardSurvivorDomain first last hle))
      (isLocalDiffeomorph_subtype_val V)
  have hΦ : IsLocalDiffeomorph I ThreeModel ∞ (f ∘ Ψ) :=
    isLocalDiffeomorph_comp hf hΨ
  refine ⟨hΦ, Subtype.val_injective.comp (Subtype.val_injective.comp hΨinj), ?_⟩
  have hmetric : H.backwardSurvivorIncomingMetric first last hle G
      (A.endpointTerminalLimitMetric (H.stage last)) s =
      localPullMetric (A.flow.base.metric s) f hf := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [backwardSurvivorIncomingMetric, localPullMetric_inner,
      A.endpointTerminalLimitMetric_extendedMetric_of_le le_rfl,
      SmoothRiemannianMetric.restrictOpen_inner, H.backwardSurvivorIncomingMap_mfderiv,
      localPullMetric_inner]
    have hd : mfderiv ThreeModel ThreeModel f y = ContinuousLinearMap.id ℝ ThreeSpace := by
      change mfderiv ThreeModel ThreeModel (fun z : V => z.val.val) y = _
      rw [mfderiv_subtypeVal_comp, mfderiv_subtype_val]
    rw [hd]
    rfl
  change localPullMetric (scaleMetric q hq
    (H.backwardSurvivorIncomingMetric first last hle G
      (A.endpointTerminalLimitMetric (H.stage last)) s)) Ψ hΨ = _
  rw [hmetric, ← localPullMetric_scaleMetric]
  exact localPullMetric_comp _ f Ψ hf hΨ hΦ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem exists_eventually_scalar_derivative_bounds_on_original_cap_window
    {D r : ℝ} (hrD : r < D + 1) {N : ℕ} (hN : 2 ≤ N)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ Cphys : ℝ, 0 < Cphys ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (first last : ∀ i, Fin ((H i).eventCount + 1))
      (hle : ∀ i, first i ≤ last i) (time q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
      (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
    let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
    let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (last i))
    let age := fun i => q i * (time i - (H i).time (first i))
    ∀ (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (G i)))
      (Psi : ∀ i, standardCapWindow D →
        (H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (G i))
      (hPsi : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Psi i))
      (S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 (age i)
          (by
            dsimp [age]
            exact mul_nonneg (hq i).le
              (sub_nonneg.mpr (((H i).time_strictMono.monotone (hle i)).trans (A i).lt.le))))),
    (∀ i, IsSolutionOn (S i)) →
    (∀ i t, t ∈ Icc 0 (age i) → (S i).base.metric t = localPullMetric
      (scaleMetric (q i) (hq i) (gflow i ((H i).time (first i) + t / q i))) (Psi i) (hPsi i)) →
    (∀ i t, t ∈ Icc ((H i).time (last i)) (time i) →
      gflow i t = (H i).backwardSurvivorIncomingMetric (first i) (last i) (hle i) (G i) (L i) t) →
    (∀ i j, j ≤ 2 → ∀ t ∈ Icc 0 (age i), ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
      curvDerivNormSq j ((S i).base.metric t) y ≤ B) →
    MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ r} N
      (fun i => (S i).base.metric (age i))
      (StandardCap.metric.restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) →
    ∀ᶠ i in atTop, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
      (∀ v : TangentSpace ThreeModel (Psi i y).val.val,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (Psi i y).val.val v)| ≤
          Cphys * (A i).flow.scalar (time i) (Psi i y).val.val *
            Real.sqrt ((A i).flow.scalar (time i) (Psi i y).val.val) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner (Psi i y).val.val v v)) ∧
      |derivWithin (fun t => (A i).flow.scalar t (Psi i y).val.val) (Iic (time i)) (time i)| ≤
        Cphys * (A i).flow.scalar (time i) (Psi i y).val.val ^ 2 := by
  obtain ⟨Cphys,hCphys,hphysical⟩ :=
    StandardCap.exists_eventually_relative_scalar_derivative_bounds_of_metric_cp_convergence hrD hN B hB
  refine ⟨Cphys,hCphys,?_⟩
  intro H first last hle time q hq A G L age gflow Psi hPsi S hS hmetric hlast hjets hconv
  have hage (i : ℕ) : 0 < age i :=
    mul_pos (hq i) (sub_pos.mpr (((H i).time_strictMono.monotone (hle i)).trans_lt (A i).lt))
  have hp := hphysical (fun i => RealTimeInterval.closed 0 (age i) (hage i).le) age hage S hS
    (fun _ => Subset.rfl) (fun _ => Subset.rfl) hjets hconv
    (fun i => (H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (G i))
    gflow Psi hPsi q (fun i => (H i).time (first i)) hq hmetric
  filter_upwards [hp] with i hi y hy
  have hb := hi y hy
  have hclock : (H i).time (first i) + age i / q i = time i := by
    dsimp only [age]
    rw [mul_div_cancel_left₀ _ (hq i).ne']
    ring
  rw [hclock] at hb
  have hgradient := (H i).scalar_gradient_bound_closed_slab_endpoint_of_backwardSurvivorIncomingMetric
    (first i) (last i) (hle i) (A i) (gflow i (time i))
    (hlast i (time i) ⟨(A i).lt.le,le_rfl⟩) (Psi i y) hb.1
  have heq := (H i).scalar_eventually_eq_backwardSurvivorIncomingDomain_of_closed_slab_endpoint
    (first i) (last i) (hle i) (A i) (gflow i) (hlast i) (Psi i y)
  have htime := hb.2
  rw [heq.derivWithin_eq_of_mem (mem_Iic.mpr le_rfl),
    heq.eq_of_nhdsWithin (mem_Iic.mpr le_rfl)] at htime
  exact ⟨hgradient,htime⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


private theorem exists_eventually_scalar_derivative_bounds_on_captured_cap_ball
    {D R₀ R₁ R₂ C d r : ℝ}
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ ≤ R₂) (hR₂D : R₂ < D + 1)
    (hC : 0 < C) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (hR₀₁ : R₀ < R₁) (hinner : 2 * R₀ + d * Real.sqrt C < R₁ / 2)
    (houter : 2 * R₀ + (d + r) * Real.sqrt C ≤ R₂ / 2) {N : ℕ} (hN : 2 ≤ N)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ Cphys : ℝ, 0 < Cphys ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (first last : ∀ i, Fin ((H i).eventCount + 1))
      (hle : ∀ i, first i ≤ last i) (time q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
      (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
    let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
    let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (last i))
    let age := fun i => q i * (time i - (H i).time (first i))
    ∀ (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (G i)))
      (Psi : ∀ i, standardCapWindow D →
        (H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (G i))
      (hPsi : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Psi i))
      (hPsiinj : ∀ i, Function.Injective (Psi i))
      (S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 (age i)
          (by
            dsimp [age]
            exact mul_nonneg (hq i).le
              (sub_nonneg.mpr (((H i).time_strictMono.monotone (hle i)).trans (A i).lt.le))))),
    (∀ i, IsSolutionOn (S i)) →
    (∀ i t, t ∈ Icc 0 (age i) → (S i).base.metric t = localPullMetric
      (scaleMetric (q i) (hq i) (gflow i ((H i).time (first i) + t / q i))) (Psi i) (hPsi i)) →
    (∀ i t, t ∈ Icc ((H i).time (last i)) (time i) →
      gflow i t = (H i).backwardSurvivorIncomingMetric (first i) (last i) (hle i) (G i) (L i) t) →
    (∀ i j, j ≤ 2 → ∀ t ∈ Icc 0 (age i), ∀ y : standardCapWindow D, ‖y.val‖ ≤ R₂ →
      curvDerivNormSq j ((S i).base.metric t) y ≤ B) →
    MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ R₂} N
      (fun i => (S i).base.metric (age i))
      (StandardCap.metric.restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) →
    ∀ (Q : ℕ → ℝ), (∀ i, 0 < Q i) → (∀ i, q i ≤ C * Q i) →
    ∀ (u : ℕ → standardCapWindow D), (∀ i, ‖(u i).val‖ ≤ R₀) →
    ∀ (x : ∀ i, ((H i).stage (last i)).Carrier),
    (∀ i, riemannianEDistOf ((A i).flow.base.metric (time i)) (Psi i (u i)).val.val (x i) ≤
      ENNReal.ofReal (d / Real.sqrt (Q i))) →
    ∀ᶠ i in atTop,
      (∃ y : standardCapWindow D, ‖y.val‖ ≤ R₁ ∧ (Psi i y).val.val = x i) ∧
      ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (x i) (r / Real.sqrt (Q i)),
        (∃ y : standardCapWindow D, ‖y.val‖ ≤ R₂ ∧ (Psi i y).val.val = z) ∧
        Nonempty (BackwardPointTrace (H i) (first i) (last i) (hle i) z) ∧
        q i / 2 < (A i).flow.scalar (time i) z ∧
        (∀ v : TangentSpace ThreeModel z,
          |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) z v)| ≤
            Cphys * (A i).flow.scalar (time i) z * Real.sqrt ((A i).flow.scalar (time i) z) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner z v v)) ∧
        |derivWithin (fun t => (A i).flow.scalar t z) (Iic (time i)) (time i)| ≤
          Cphys * (A i).flow.scalar (time i) z ^ 2 := by
  obtain ⟨Cphys, hCphys, hbounds⟩ :=
    exists_eventually_scalar_derivative_bounds_on_original_cap_window hR₂D hN B hB
  refine ⟨Cphys, hCphys, ?_⟩
  intro H first last hle time q hq A G L age gflow Psi hPsi hPsiinj S hS hmetric hlast hjets hconv Q hQ hscale u hu x hnear
  have hb := hbounds H first last hle time q hq A gflow Psi hPsi S hS hmetric hlast hjets hconv
  let Phi (i : ℕ) : standardCapWindow D → ((H i).stage (last i)).Carrier :=
    fun y => (Psi i y).val.val
  have hambient (i : ℕ) := (H i).backwardSurvivorIncoming_ambient_localPullMetric
    (first i) (last i) (hle i) (A i) (Psi i) (hPsi i) (hPsiinj i) (q i) (hq i)
  let hPhi (i : ℕ) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Phi i) :=
    (hambient i).choose
  have hinj (i : ℕ) : Function.Injective (Phi i) := (hambient i).choose_spec.1
  have hmet (i : ℕ) (y : standardCapWindow D) (v w : TangentSpace ThreeModel y) :
      ((S i).base.metric (age i)).inner y v w =
        (scaleMetric (q i) (hq i) ((A i).flow.base.metric (time i))).inner (Phi i y)
          (mfderiv ThreeModel ThreeModel (Phi i) y v) (mfderiv ThreeModel ThreeModel (Phi i) y w) := by
    have hage : 0 ≤ age i :=
      mul_nonneg (hq i).le
        (sub_nonneg.mpr (((H i).time_strictMono.monotone (hle i)).trans (A i).lt.le))
    have hclock : (H i).time (first i) + age i / q i = time i := by
      dsimp only [age]
      rw [mul_div_cancel_left₀ _ (hq i).ne']
      ring
    rw [hmetric i (age i) ⟨hage, le_rfl⟩, hclock,
      hlast i (time i) ⟨(A i).lt.le, le_rfl⟩, (hambient i).choose_spec.2]
    exact localPullMetric_inner _ _ _ _ _ _
  have hquad := StandardCap.eventually_window_scaled_metric_bounds_of_metric_cp_convergence hR₂D
    (fun i => (S i).base.metric (age i))
    (StandardCap.metric.restrictOpen (standardCapWindow D)) hconv
    (fun i => (A i).flow.base.metric (time i)) q hq Phi (fun i y _ v => hmet i y v v)
  have hscalar := StandardCap.eventually_half_lt_metricScalarAt_of_metric_cp_convergence
    hR₂D hN (fun i => (S i).base.metric (age i)) hconv
  filter_upwards [hb, hquad, hscalar] with i hi hqi hsi
  have hc := StandardCap.window_exists_preimage_and_ball_subset_image_of_scaled_metric_bounds
    ((A i).flow.base.metric (time i)) hR₁ hR₁₂ hR₂D (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) (hq i) (hQ i) hC (hscale i) hd hr
    (Phi i) (hPhi i) (hinj i) (fun y hy v => (hqi y hy v).1)
    (fun y hy v => (hqi y hy v).2) (u i) (hu i) hR₀₁ (x i) (hnear i) hinner houter
  refine ⟨hc.1, ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hc.2 hz
  have hscaled : (S i).base.metric (age i) =
      localPullMetric (scaleMetric (q i) (hq i) ((A i).flow.base.metric (time i)))
        (Phi i) (hPhi i) := by
    apply SmoothRiemannianMetric.ext_inner
    intro w v z
    exact (hmet i w v z).trans (localPullMetric_inner _ _ _ _ _ _).symm
  have hs := hsi y hy
  rw [hscaled, metricScalarAt_localPull, metricScalarAt_scaleMetric,
    ← div_eq_inv_mul] at hs
  have hpositive : q i / 2 < (A i).flow.scalar (time i) (Phi i y) := by
    have hh := (lt_div_iff₀ (hq i)).mp hs
    change q i / 2 < metricScalarAt ((A i).flow.base.metric (time i)) (Phi i y)
    nlinarith
  exact ⟨⟨y, hy, rfl⟩, (Psi i y).val.property, hpositive, hi y hy⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


theorem exists_uniform_scalar_derivative_bounds_on_balls_near_canonical_caps_of_vanishing_age
    (N : ℕ) (hN : 2 ≤ N) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D)
    (Cscale d b : ℝ) (hCscale : 0 < Cscale)
    (hd : 0 ≤ d) (hb : 0 < b)
    (hcapture : 2 * StandardCap.transitionEnd + (d + b) * Real.sqrt Cscale < r / 2) :
    ∃ C₀ Cphys : ℝ, 0 < C₀ ∧ 0 < Cphys ∧
      ∀ (C : ℝ≥0), ∃ (η ε₀ δ₀ : ℝ), 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      (∀ i, (parameters i).modelAccuracy ≤ ε₀) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ (q₀ a₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
      (∀ i, q₀ i ≤ C₀ * q i) → (∀ i, 1 ≤ a₀ i * q i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) (a₀ i) x) →
      (∀ i x, -3 / a₀ i ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ i < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (A i).flow.scalar t x →
        |derivWithin (fun v => (A i).flow.scalar v x) (Iic t) t| ≤ C * (A i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, ((H i).stage (last i)).Carrier)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i)),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      ∀ (Q : ℕ → ℝ), (∀ i, 0 < Q i) → (∀ i, q i ≤ Cscale * Q i) →
      ∀ y : ∀ i, ((H i).stage (last i)).Carrier,
      (∀ i, riemannianEDistOf ((A i).flow.base.metric (time i)) (x i) (y i) ≤
        ENNReal.ofReal (d / Real.sqrt (Q i))) →
      ∀ᶠ i in atTop,
        Nonempty (BackwardPointTrace (H i) (event i).succ (last i) (hle i) (y i)) ∧
        ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (y i) (b / Real.sqrt (Q i)),
          Nonempty (BackwardPointTrace (H i) (event i).succ (last i) (hle i) z) ∧
          q i / 2 < (A i).flow.scalar (time i) z ∧
          (∀ v : TangentSpace ThreeModel z,
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) z v)| ≤
              Cphys * (A i).flow.scalar (time i) z * Real.sqrt ((A i).flow.scalar (time i) z) *
                Real.sqrt (((A i).flow.base.metric (time i)).inner z v v)) ∧
          |derivWithin (fun t => (A i).flow.scalar t z) (Iic (time i)) (time i)| ≤
            Cphys * (A i).flow.scalar (time i) z ^ 2 := by
  obtain ⟨Rcap, hreserve, hRcap⟩ := exists_between
    (show 2 * (2 * StandardCap.transitionEnd + (d + b) * Real.sqrt Cscale) < r by linarith)
  have hcapture' : 2 * StandardCap.transitionEnd + (d + b) * Real.sqrt Cscale ≤ Rcap / 2 := by
    linarith
  obtain ⟨C₀, B, Cderiv, hC₀, hB, hCderiv, huniform⟩ :=
    exists_uniform_canonical_cap_window_convergence_and_uniform_scalar_derivative_bounds_at_vanishing_age
      N D r eps heps hepssmall hr hfit
  have hRcapD : Rcap < D + 1 := by
    linarith [hfit, inv_pos.mpr heps, StandardCap.transitionEnd_pos]
  have hroot : 0 < Real.sqrt Cscale := Real.sqrt_pos.mpr hCscale
  have hinner : 2 * StandardCap.transitionEnd + d * Real.sqrt Cscale < Rcap / 2 := by
    nlinarith
  have hcoreR : StandardCap.transitionEnd < Rcap := by
    nlinarith [StandardCap.transitionEnd_pos, mul_nonneg hd hroot.le]
  have hRpos : 0 < Rcap := StandardCap.transitionEnd_pos.trans hcoreR
  obtain ⟨Cphys, hCphys, hphysical⟩ :=
    exists_eventually_scalar_derivative_bounds_on_captured_cap_ball hRpos le_rfl hRcapD
      hCscale hd hb.le hcoreR hinner hcapture' hN B (zero_le_one.trans hB)
  refine ⟨C₀, Cphys, hC₀, hCphys, ?_⟩
  intro C
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hproducer⟩ := huniform C
  refine ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H event last hle time A hinit parameters records boundary cap q age
    hcanonical hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth Q hQ hscale y hnear
  let G i := (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L i := (A i).endpointTerminalLimitMetric ((H i).stage (last i))
  let x' (i : ℕ) : (G i).terminalRegularOpen := ⟨x i, by
    change x i ∈ (G i).terminalRegularRegion
    rw [(A i).terminalRegularRegion_eq_univ ((H i).stage (last i))]
    trivial⟩
  obtain ⟨x₀, delta, order, datum, w, hwscalar, hwmetric, u, Ξ, hΞ, gflow, hmargin', hpos, S,
    hu, hucap, hΞsmooth, hΞbirth, hΞpoint, hslabs, hlast, hS, hgram, hjets, hbounds, hzero,
    hmetric, hterminal, hconvergence, hmarked, hcaps⟩ :=
    hproducer H event last hle time G L hinit parameters records boundary hcanonical hmargin hm
      herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal hage hagelim z x' trace hbirth
  have hnear' (i : ℕ) :
      riemannianEDistOf ((A i).flow.base.metric (time i)) (Ξ i (u i)).val.val (y i) ≤
        ENNReal.ofReal (d / Real.sqrt (Q i)) := by
    have hpoint : (Ξ i (u i)).val.val = x i := congrArg Subtype.val (hΞpoint i)
    simpa only [hpoint] using hnear i
  have hresult := hphysical H (fun i => (event i).succ) last hle time q
    (fun i => (cap i).neck.scale_pos) A gflow Ξ hΞ
    (fun i => (hΞsmooth i).isEmbedding.injective) S hS (fun i t _ => hmetric i t) hlast
    (fun i j hj t ht w hw => hjets i j (hj.trans hN) t ht w (hw.trans hRcap.le))
    (hconvergence Rcap hRcap) Q hQ hscale u hu y hnear'
  filter_upwards [hresult] with i hi
  obtain ⟨w, hw, hwy⟩ := hi.1
  refine ⟨?_, fun z hz => (hi.2 z hz).2⟩
  rw [← hwy]
  exact (Ξ i w).val.property

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_scalar_derivative_contact_exclusion_near_canonical_caps_of_vanishing_age
    (N : ℕ) (hN : 2 ≤ N) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D)
    (Cscale d b : ℝ) (hCscale : 0 < Cscale)
    (hd : 0 ≤ d) (hb : 0 < b)
    (hcapture : 2 * StandardCap.transitionEnd + (d + b) * Real.sqrt Cscale < r / 2) :
    ∃ C₀ : ℝ, ∃ C : ℝ≥0, 0 < C₀ ∧ 0 < C ∧
      ∃ (η ε₀ δ₀ : ℝ), 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      (∀ i, (parameters i).modelAccuracy ≤ ε₀) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ (q₀ a₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
      (∀ i, q₀ i ≤ C₀ * q i) → (∀ i, 1 ≤ a₀ i * q i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) (a₀ i) x) →
      (∀ i x, -3 / a₀ i ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ i < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (A i).flow.scalar t x →
        |derivWithin (fun v => (A i).flow.scalar v x) (Iic t) t| ≤ C * (A i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, ((H i).stage (last i)).Carrier)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i)),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      ∀ (Q : ℕ → ℝ), (∀ i, 0 < Q i) → (∀ i, q i ≤ Cscale * Q i) →
      ∀ y : ∀ i, ((H i).stage (last i)).Carrier,
      (∀ i, riemannianEDistOf ((A i).flow.base.metric (time i)) (x i) (y i) ≤
        ENNReal.ofReal (d / Real.sqrt (Q i))) →
      (∀ i, (∃ v : TangentSpace ThreeModel (y i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (y i) * Real.sqrt ((A i).flow.scalar (time i) (y i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (y i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (y i) v)|) ∨
        C * (A i).flow.scalar (time i) (y i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (y i)) (Iic (time i)) (time i)|) → False := by
  obtain ⟨C₀, Cphys, hC₀, hCphys, hbound⟩ :=
    exists_uniform_scalar_derivative_bounds_on_balls_near_canonical_caps_of_vanishing_age
      N hN D r eps heps hepssmall hr hfit Cscale d b hCscale hd hb hcapture
  let C : ℝ≥0 := ⟨Cphys + 1, by positivity⟩
  have hC : 0 < C := by change 0 < Cphys + 1; positivity
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hmain⟩ := hbound C
  refine ⟨C₀, C, hC₀, hC, η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H event last hle time A hinit parameters records boundary cap q age
    hcanonical hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth Q hQ hscale y hnear hfail
  have hevent := hmain H event last hle time A hinit parameters records boundary hcanonical
    hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth Q hQ hscale y hnear
  obtain ⟨i, hi⟩ := hevent.exists
  have hy : y i ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (y i)
      (b / Real.sqrt (Q i)) := by
    change riemannianEDistOf ((A i).flow.base.metric (time i)) (y i) (y i) <
      ENNReal.ofReal (b / Real.sqrt (Q i))
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hb (Real.sqrt_pos.mpr (hQ i)))
  have hpositive : 0 < (A i).flow.scalar (time i) (y i) :=
    (half_pos (cap i).neck.scale_pos).trans (hi.2 (y i) hy).2.1
  have hbounds := (hi.2 (y i) hy).2.2
  have hc : Cphys < (C : ℝ) := by change Cphys < Cphys + 1; linarith
  rcases hfail i with ⟨v, hvzero, hv⟩ | ht
  · have hpos : 0 < (A i).flow.scalar (time i) (y i) *
        Real.sqrt ((A i).flow.scalar (time i) (y i)) *
          Real.sqrt (((A i).flow.base.metric (time i)).inner (y i) v v) := by
      exact mul_pos (mul_pos hpositive (Real.sqrt_pos.mpr hpositive))
        (Real.sqrt_pos.mpr (((A i).flow.base.metric (time i)).pos (y i) v hvzero))
    have hlt := mul_lt_mul_of_pos_right hc hpos
    have hh := hbounds.1 v
    nlinarith
  · have hlt := mul_lt_mul_of_pos_right hc (sq_pos_of_pos hpositive)
    exact (not_lt_of_ge ht) (hbounds.2.trans_lt hlt)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem exists_uniform_scalar_derivative_bounds_on_original_cap_window :
    ∃ Cphys : ℝ, 0 < Cphys ∧ ∀ {D r : ℝ}, r < D + 1 → ∀ {N : ℕ}, 4 ≤ N →
    ∀ (H : ℕ → ObservedHistory.{u}) (first last : ∀ i, Fin ((H i).eventCount + 1))
      (hle : ∀ i, first i ≤ last i) (time q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
      (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
    let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
    let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (last i))
    let age := fun i => q i * (time i - (H i).time (first i))
    ∀ (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (G i)))
      (Psi : ∀ i, standardCapWindow D →
        (H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (G i))
      (hPsi : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Psi i))
      (S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 (age i)
          (by
            dsimp [age]
            exact mul_nonneg (hq i).le
              (sub_nonneg.mpr (((H i).time_strictMono.monotone (hle i)).trans (A i).lt.le))))),
    (∀ i, IsSolutionOn (S i)) →
    (∀ i t, t ∈ Icc 0 (age i) → (S i).base.metric t = localPullMetric
      (scaleMetric (q i) (hq i) (gflow i ((H i).time (first i) + t / q i))) (Psi i) (hPsi i)) →
    (∀ i t, t ∈ Icc ((H i).time (last i)) (time i) →
      gflow i t = (H i).backwardSurvivorIncomingMetric (first i) (last i) (hle i) (G i) (L i) t) →
    MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ r} N
      (fun i => (S i).base.metric (age i))
      (StandardCap.metric.restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) →
    ∀ᶠ i in atTop, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
      (∀ v : TangentSpace ThreeModel (Psi i y).val.val,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (Psi i y).val.val v)| ≤
          Cphys * (A i).flow.scalar (time i) (Psi i y).val.val *
            Real.sqrt ((A i).flow.scalar (time i) (Psi i y).val.val) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner (Psi i y).val.val v v)) ∧
      |derivWithin (fun t => (A i).flow.scalar t (Psi i y).val.val) (Iic (time i)) (time i)| ≤
        Cphys * (A i).flow.scalar (time i) (Psi i y).val.val ^ 2 := by
  obtain ⟨Cphys,hCphys,hphysical⟩ :=
    StandardCap.exists_uniform_relative_scalar_derivative_bounds_of_terminal_metric_cp_convergence
  refine ⟨Cphys,hCphys,?_⟩
  intro D r hrD N hN H first last hle time q hq A G L age gflow Psi hPsi S hS hmetric hlast hconv
  have hage (i : ℕ) : 0 < age i :=
    mul_pos (hq i) (sub_pos.mpr (((H i).time_strictMono.monotone (hle i)).trans_lt (A i).lt))
  have hp := hphysical hrD hN (fun i => RealTimeInterval.closed 0 (age i) (hage i).le) age hage S hS
    (fun _ => Subset.rfl) (fun _ => Subset.rfl) hconv
    (fun i => (H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (G i))
    gflow Psi hPsi q (fun i => (H i).time (first i)) hq hmetric
  filter_upwards [hp] with i hi y hy
  have hb := hi y hy
  have hclock : (H i).time (first i) + age i / q i = time i := by
    dsimp only [age]
    rw [mul_div_cancel_left₀ _ (hq i).ne']
    ring
  rw [hclock] at hb
  have hgradient := (H i).scalar_gradient_bound_closed_slab_endpoint_of_backwardSurvivorIncomingMetric
    (first i) (last i) (hle i) (A i) (gflow i (time i))
    (hlast i (time i) ⟨(A i).lt.le,le_rfl⟩) (Psi i y) hb.1
  have heq := (H i).scalar_eventually_eq_backwardSurvivorIncomingDomain_of_closed_slab_endpoint
    (first i) (last i) (hle i) (A i) (gflow i) (hlast i) (Psi i y)
  have htime := hb.2
  rw [heq.derivWithin_eq_of_mem (mem_Iic.mpr le_rfl),
    heq.eq_of_nhdsWithin (mem_Iic.mpr le_rfl)] at htime
  exact ⟨hgradient,htime⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


private theorem exists_uniform_scalar_derivative_bounds_on_captured_cap_ball :
    ∃ Cphys : ℝ, 0 < Cphys ∧ ∀ {D R₀ R₁ R₂ C d r : ℝ},
    0 < R₁ → R₁ ≤ R₂ → R₂ < D + 1 → 0 < C → 0 ≤ d → 0 ≤ r →
    R₀ < R₁ → 2 * R₀ + d * Real.sqrt C < R₁ / 2 →
    2 * R₀ + (d + r) * Real.sqrt C ≤ R₂ / 2 → ∀ {N : ℕ}, 4 ≤ N →
    ∀ (H : ℕ → ObservedHistory.{u}) (first last : ∀ i, Fin ((H i).eventCount + 1))
      (hle : ∀ i, first i ≤ last i) (time q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
      (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
    let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
    let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (last i))
    let age := fun i => q i * (time i - (H i).time (first i))
    ∀ (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
        ((H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (G i)))
      (Psi : ∀ i, standardCapWindow D →
        (H i).backwardSurvivorIncomingDomain (first i) (last i) (hle i) (G i))
      (hPsi : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Psi i))
      (hPsiinj : ∀ i, Function.Injective (Psi i))
      (S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 (age i)
          (by
            dsimp [age]
            exact mul_nonneg (hq i).le
              (sub_nonneg.mpr (((H i).time_strictMono.monotone (hle i)).trans (A i).lt.le))))),
    (∀ i, IsSolutionOn (S i)) →
    (∀ i t, t ∈ Icc 0 (age i) → (S i).base.metric t = localPullMetric
      (scaleMetric (q i) (hq i) (gflow i ((H i).time (first i) + t / q i))) (Psi i) (hPsi i)) →
    (∀ i t, t ∈ Icc ((H i).time (last i)) (time i) →
      gflow i t = (H i).backwardSurvivorIncomingMetric (first i) (last i) (hle i) (G i) (L i) t) →
    MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ R₂} N
      (fun i => (S i).base.metric (age i))
      (StandardCap.metric.restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) →
    ∀ (Q : ℕ → ℝ), (∀ i, 0 < Q i) → (∀ i, q i ≤ C * Q i) →
    ∀ (u : ℕ → standardCapWindow D), (∀ i, ‖(u i).val‖ ≤ R₀) →
    ∀ (x : ∀ i, ((H i).stage (last i)).Carrier),
    (∀ i, riemannianEDistOf ((A i).flow.base.metric (time i)) (Psi i (u i)).val.val (x i) ≤
      ENNReal.ofReal (d / Real.sqrt (Q i))) →
    ∀ᶠ i in atTop,
      (∃ y : standardCapWindow D, ‖y.val‖ ≤ R₁ ∧ (Psi i y).val.val = x i) ∧
      ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (x i) (r / Real.sqrt (Q i)),
        (∃ y : standardCapWindow D, ‖y.val‖ ≤ R₂ ∧ (Psi i y).val.val = z) ∧
        Nonempty (BackwardPointTrace (H i) (first i) (last i) (hle i) z) ∧
        q i / 2 < (A i).flow.scalar (time i) z ∧
        (∀ v : TangentSpace ThreeModel z,
          |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) z v)| ≤
            Cphys * (A i).flow.scalar (time i) z * Real.sqrt ((A i).flow.scalar (time i) z) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner z v v)) ∧
        |derivWithin (fun t => (A i).flow.scalar t z) (Iic (time i)) (time i)| ≤
          Cphys * (A i).flow.scalar (time i) z ^ 2 := by
  obtain ⟨Cphys, hCphys, hbounds⟩ :=
    exists_uniform_scalar_derivative_bounds_on_original_cap_window
  refine ⟨Cphys, hCphys, ?_⟩
  intro D R₀ R₁ R₂ C d r hR₁ hR₁₂ hR₂D hC hd hr hR₀₁ hinner houter N hN H first last hle time q hq A G L age gflow Psi hPsi hPsiinj S hS hmetric hlast hconv Q hQ hscale u hu x hnear
  have hb := hbounds hR₂D hN H first last hle time q hq A gflow Psi hPsi S hS hmetric hlast hconv
  let Phi (i : ℕ) : standardCapWindow D → ((H i).stage (last i)).Carrier :=
    fun y => (Psi i y).val.val
  have hambient (i : ℕ) := backwardSurvivorIncoming_ambient_localPullMetric (H i)
    (first i) (last i) (hle i) (A i) (Psi i) (hPsi i) (hPsiinj i) (q i) (hq i)
  let hPhi (i : ℕ) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Phi i) :=
    (hambient i).choose
  have hinj (i : ℕ) : Function.Injective (Phi i) := (hambient i).choose_spec.1
  have hmet (i : ℕ) (y : standardCapWindow D) (v w : TangentSpace ThreeModel y) :
      ((S i).base.metric (age i)).inner y v w =
        (scaleMetric (q i) (hq i) ((A i).flow.base.metric (time i))).inner (Phi i y)
          (mfderiv ThreeModel ThreeModel (Phi i) y v) (mfderiv ThreeModel ThreeModel (Phi i) y w) := by
    have hage : 0 ≤ age i :=
      mul_nonneg (hq i).le
        (sub_nonneg.mpr (((H i).time_strictMono.monotone (hle i)).trans (A i).lt.le))
    have hclock : (H i).time (first i) + age i / q i = time i := by
      dsimp only [age]
      rw [mul_div_cancel_left₀ _ (hq i).ne']
      ring
    rw [hmetric i (age i) ⟨hage, le_rfl⟩, hclock,
      hlast i (time i) ⟨(A i).lt.le, le_rfl⟩, (hambient i).choose_spec.2]
    exact localPullMetric_inner _ _ _ _ _ _
  have hquad := StandardCap.eventually_window_scaled_metric_bounds_of_metric_cp_convergence hR₂D
    (fun i => (S i).base.metric (age i))
    (StandardCap.metric.restrictOpen (standardCapWindow D)) hconv
    (fun i => (A i).flow.base.metric (time i)) q hq Phi (fun i y _ v => hmet i y v v)
  have hscalar := StandardCap.eventually_half_lt_metricScalarAt_of_metric_cp_convergence
    hR₂D (by omega : 2 ≤ N) (fun i => (S i).base.metric (age i)) hconv
  filter_upwards [hb, hquad, hscalar] with i hi hqi hsi
  have hc := StandardCap.window_exists_preimage_and_ball_subset_image_of_scaled_metric_bounds
    ((A i).flow.base.metric (time i)) hR₁ hR₁₂ hR₂D (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) (hq i) (hQ i) hC (hscale i) hd hr
    (Phi i) (hPhi i) (hinj i) (fun y hy v => (hqi y hy v).1)
    (fun y hy v => (hqi y hy v).2) (u i) (hu i) hR₀₁ (x i) (hnear i) hinner houter
  refine ⟨hc.1, ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hc.2 hz
  have hscaled : (S i).base.metric (age i) =
      localPullMetric (scaleMetric (q i) (hq i) ((A i).flow.base.metric (time i)))
        (Phi i) (hPhi i) := by
    apply SmoothRiemannianMetric.ext_inner
    intro w v z
    exact (hmet i w v z).trans (localPullMetric_inner _ _ _ _ _ _).symm
  have hs := hsi y hy
  rw [hscaled, metricScalarAt_localPull, metricScalarAt_scaleMetric,
    ← div_eq_inv_mul] at hs
  have hpositive : q i / 2 < (A i).flow.scalar (time i) (Phi i y) := by
    have hh := (lt_div_iff₀ (hq i)).mp hs
    change q i / 2 < metricScalarAt ((A i).flow.base.metric (time i)) (Phi i y)
    nlinarith
  exact ⟨⟨y, hy, rfl⟩, (Psi i y).val.property, hpositive, hi y hy⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


theorem exists_scalar_derivative_constant_on_balls_near_canonical_caps_of_vanishing_age :
    ∃ Cphys : ℝ, 0 < Cphys ∧ ∀ (N : ℕ), 4 ≤ N → ∀ (D r eps : ℝ),
    0 < eps → eps ≤ 1 / 1000 → StandardCap.transitionEnd + eps⁻¹ + 1 < r →
    64 * (r + eps⁻¹) < D → ∀ (Cscale d b : ℝ), 0 < Cscale → 0 ≤ d → 0 < b →
    2 * StandardCap.transitionEnd + (d + b) * Real.sqrt Cscale < r / 2 →
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (C : ℝ≥0), ∃ (η ε₀ δ₀ : ℝ), 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      (∀ i, (parameters i).modelAccuracy ≤ ε₀) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ (q₀ a₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
      (∀ i, q₀ i ≤ C₀ * q i) → (∀ i, 1 ≤ a₀ i * q i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) (a₀ i) x) →
      (∀ i x, -3 / a₀ i ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ i < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (A i).flow.scalar t x →
        |derivWithin (fun v => (A i).flow.scalar v x) (Iic t) t| ≤ C * (A i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, ((H i).stage (last i)).Carrier)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i)),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      ∀ (Q : ℕ → ℝ), (∀ i, 0 < Q i) → (∀ i, q i ≤ Cscale * Q i) →
      ∀ y : ∀ i, ((H i).stage (last i)).Carrier,
      (∀ i, riemannianEDistOf ((A i).flow.base.metric (time i)) (x i) (y i) ≤
        ENNReal.ofReal (d / Real.sqrt (Q i))) →
      ∀ᶠ i in atTop,
        Nonempty (BackwardPointTrace (H i) (event i).succ (last i) (hle i) (y i)) ∧
        ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (y i) (b / Real.sqrt (Q i)),
          Nonempty (BackwardPointTrace (H i) (event i).succ (last i) (hle i) z) ∧
          q i / 2 < (A i).flow.scalar (time i) z ∧
          (∀ v : TangentSpace ThreeModel z,
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) z v)| ≤
              Cphys * (A i).flow.scalar (time i) z * Real.sqrt ((A i).flow.scalar (time i) z) *
                Real.sqrt (((A i).flow.base.metric (time i)).inner z v v)) ∧
          |derivWithin (fun t => (A i).flow.scalar t z) (Iic (time i)) (time i)| ≤
            Cphys * (A i).flow.scalar (time i) z ^ 2 := by
  obtain ⟨Cphys, hCphys, hphysical⟩ := exists_uniform_scalar_derivative_bounds_on_captured_cap_ball
  refine ⟨Cphys, hCphys, ?_⟩
  intro N hN D r eps heps hepssmall hr hfit Cscale d b hCscale hd hb hcapture
  obtain ⟨Rcap, hreserve, hRcap⟩ := exists_between
    (show 2 * (2 * StandardCap.transitionEnd + (d + b) * Real.sqrt Cscale) < r by linarith)
  have hcapture' : 2 * StandardCap.transitionEnd + (d + b) * Real.sqrt Cscale ≤ Rcap / 2 := by
    linarith
  obtain ⟨C₀, B, Cderiv, hC₀, hB, hCderiv, huniform⟩ :=
    exists_uniform_canonical_cap_window_convergence_and_uniform_scalar_derivative_bounds_at_vanishing_age
      N D r eps heps hepssmall hr hfit
  have hRcapD : Rcap < D + 1 := by
    linarith [hfit, inv_pos.mpr heps, StandardCap.transitionEnd_pos]
  have hroot : 0 < Real.sqrt Cscale := Real.sqrt_pos.mpr hCscale
  have hinner : 2 * StandardCap.transitionEnd + d * Real.sqrt Cscale < Rcap / 2 := by
    nlinarith
  have hcoreR : StandardCap.transitionEnd < Rcap := by
    nlinarith [StandardCap.transitionEnd_pos, mul_nonneg hd hroot.le]
  have hRpos : 0 < Rcap := StandardCap.transitionEnd_pos.trans hcoreR
  have hphysical' := hphysical hRpos le_rfl hRcapD
    hCscale hd hb.le hcoreR hinner hcapture' hN
  refine ⟨C₀, hC₀, ?_⟩
  intro C
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hproducer⟩ := huniform C
  refine ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H event last hle time A hinit parameters records boundary cap q age
    hcanonical hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth Q hQ hscale y hnear
  let G i := (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L i := (A i).endpointTerminalLimitMetric ((H i).stage (last i))
  let x' (i : ℕ) : (G i).terminalRegularOpen := ⟨x i, by
    change x i ∈ (G i).terminalRegularRegion
    rw [(A i).terminalRegularRegion_eq_univ ((H i).stage (last i))]
    trivial⟩
  obtain ⟨x₀, delta, order, datum, w, hwscalar, hwmetric, u, Ξ, hΞ, gflow, hmargin', hpos, S,
    hu, hucap, hΞsmooth, hΞbirth, hΞpoint, hslabs, hlast, hS, hgram, hjets, hbounds, hzero,
    hmetric, hterminal, hconvergence, hmarked, hcaps⟩ :=
    hproducer H event last hle time G L hinit parameters records boundary hcanonical hmargin hm
      herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal hage hagelim z x' trace hbirth
  have hnear' (i : ℕ) :
      riemannianEDistOf ((A i).flow.base.metric (time i)) (Ξ i (u i)).val.val (y i) ≤
        ENNReal.ofReal (d / Real.sqrt (Q i)) := by
    have hpoint : (Ξ i (u i)).val.val = x i := congrArg Subtype.val (hΞpoint i)
    simpa only [hpoint] using hnear i
  have hresult := hphysical' H (fun i => (event i).succ) last hle time q
    (fun i => (cap i).neck.scale_pos) A gflow Ξ hΞ
    (fun i => (hΞsmooth i).isEmbedding.injective) S hS (fun i t _ => hmetric i t) hlast
    (hconvergence Rcap hRcap) Q hQ hscale u hu y hnear'
  filter_upwards [hresult] with i hi
  obtain ⟨w, hw, hwy⟩ := hi.1
  refine ⟨?_, fun z hz => (hi.2 z hz).2⟩
  rw [← hwy]
  exact (Ξ i w).val.property

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_uniform_scalar_derivative_contact_exclusion_near_canonical_caps :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (N : ℕ), 4 ≤ N → ∀ (D r eps : ℝ),
    0 < eps → eps ≤ 1 / 1000 → StandardCap.transitionEnd + eps⁻¹ + 1 < r →
    64 * (r + eps⁻¹) < D → ∀ (Cscale d b : ℝ), 0 < Cscale → 0 ≤ d → 0 < b →
    2 * StandardCap.transitionEnd + (d + b) * Real.sqrt Cscale < r / 2 →
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ (η ε₀ δ₀ : ℝ), 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      (∀ i, (parameters i).modelAccuracy ≤ ε₀) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ (q₀ a₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
      (∀ i, q₀ i ≤ C₀ * q i) → (∀ i, 1 ≤ a₀ i * q i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) (a₀ i) x) →
      (∀ i x, -3 / a₀ i ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ i < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (A i).flow.scalar t x →
        |derivWithin (fun v => (A i).flow.scalar v x) (Iic t) t| ≤ C * (A i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, ((H i).stage (last i)).Carrier)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i)),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      ∀ (Q : ℕ → ℝ), (∀ i, 0 < Q i) → (∀ i, q i ≤ Cscale * Q i) →
      ∀ y : ∀ i, ((H i).stage (last i)).Carrier,
      (∀ i, riemannianEDistOf ((A i).flow.base.metric (time i)) (x i) (y i) ≤
        ENNReal.ofReal (d / Real.sqrt (Q i))) →
      (∀ i, (∃ v : TangentSpace ThreeModel (y i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (y i) * Real.sqrt ((A i).flow.scalar (time i) (y i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (y i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (y i) v)|) ∨
        C * (A i).flow.scalar (time i) (y i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (y i)) (Iic (time i)) (time i)|) → False := by
  obtain ⟨Cphys, hCphys, hbound⟩ :=
    exists_scalar_derivative_constant_on_balls_near_canonical_caps_of_vanishing_age
  let C : ℝ≥0 := ⟨Cphys + 1, by positivity⟩
  have hC : 0 < C := by change 0 < Cphys + 1; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN D r eps heps hepssmall hr hfit Cscale d b hCscale hd hb hcapture
  obtain ⟨C₀, hC₀, hbound'⟩ := hbound N hN D r eps heps hepssmall hr hfit
    Cscale d b hCscale hd hb hcapture
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hmain⟩ := hbound' C
  refine ⟨C₀, hC₀, η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H event last hle time A hinit parameters records boundary cap q age
    hcanonical hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth Q hQ hscale y hnear hfail
  have hevent := hmain H event last hle time A hinit parameters records boundary hcanonical
    hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth Q hQ hscale y hnear
  obtain ⟨i, hi⟩ := hevent.exists
  have hy : y i ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (y i)
      (b / Real.sqrt (Q i)) := by
    change riemannianEDistOf ((A i).flow.base.metric (time i)) (y i) (y i) <
      ENNReal.ofReal (b / Real.sqrt (Q i))
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hb (Real.sqrt_pos.mpr (hQ i)))
  have hpositive : 0 < (A i).flow.scalar (time i) (y i) :=
    (half_pos (cap i).neck.scale_pos).trans (hi.2 (y i) hy).2.1
  have hbounds := (hi.2 (y i) hy).2.2
  have hc : Cphys < (C : ℝ) := by change Cphys < Cphys + 1; linarith
  rcases hfail i with ⟨v, hvzero, hv⟩ | ht
  · have hpos : 0 < (A i).flow.scalar (time i) (y i) *
        Real.sqrt ((A i).flow.scalar (time i) (y i)) *
          Real.sqrt (((A i).flow.base.metric (time i)).inner (y i) v v) := by
      exact mul_pos (mul_pos hpositive (Real.sqrt_pos.mpr hpositive))
        (Real.sqrt_pos.mpr (((A i).flow.base.metric (time i)).pos (y i) v hvzero))
    have hlt := mul_lt_mul_of_pos_right hc hpos
    have hh := hbounds.1 v
    nlinarith
  · have hlt := mul_lt_mul_of_pos_right hc (sq_pos_of_pos hpositive)
    exact (not_lt_of_ge ht) (hbounds.2.trans_lt hlt)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end
