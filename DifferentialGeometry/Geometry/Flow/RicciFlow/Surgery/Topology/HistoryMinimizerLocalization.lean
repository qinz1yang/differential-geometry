import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Localization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFootprint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReducedAction
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback

noncomputable section

open Set Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor0SBundle

universe u

variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

private theorem lift_smooth_curve_eqOn
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (α : ℝ → (H.stage i.castSucc).Carrier) (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ α)
    (b : ℝ) (hb : 0 < b)
    (hstay : ∀ s ∈ Icc 0 b, α s ∈ Subtype.val '' interior K) :
    ∃ β : ℝ → H.backwardSurvivorFootprintInterior first i hle K,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ β ∧
      EqOn (fun s => (H.backwardSurvivorFootprintMap first i hle K (β s)).val) α (Icc 0 b) := by
  let U : Set (H.stage i.castSucc).Carrier := Subtype.val '' interior K
  have hU : IsOpen U :=
    (H.event i).incoming.terminalRegularOpen.isOpen.isOpenMap_subtype_val _ isOpen_interior
  obtain ⟨ρ, lo, hi, hlo, hhi, hρ, hρid, _, hρrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset
      (hU.preimage hα.continuous) hb hstay
  have hρsm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ρ := hρ.contMDiff
  have hmem (s : ℝ) : α (ρ s) ∈ (H.event i).incoming.terminalRegularOpen := by
    obtain ⟨x, _, hx⟩ := hρrange s
    rw [← hx]
    exact x.property
  let F : ℝ → (H.event i).incoming.terminalRegularOpen := fun s => ⟨α (ρ s), hmem s⟩
  have hF : range F ⊆ interior K := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨x, hx, heq⟩ := hρrange s
    have hxF : x = F s := Subtype.ext heq
    exact hxF ▸ hx
  have hFsmooth : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ F := by
    apply (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff
      (H.event i).incoming.terminalRegularOpen F).mp
    exact hα.comp hρsm
  let β := H.backwardSurvivorFootprintLift first i hle K htrace F hF
  refine ⟨β, H.backwardSurvivorFootprintLift_contMDiff first i hle K htrace F hF hFsmooth, ?_⟩
  intro s hs
  change α (ρ s) = α s
  rw [hρid ⟨hlo.le.trans hs.1, hs.2.trans hhi.le⟩]
  rfl

theorem exists_stage_reducedAction_minimizer_in_backwardSurvivorFootprint
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (C T b r : ℝ) (hb : 0 < b)
    (hleft : H.time i.castSucc < T - b ^ 2) (hright : T < H.time i.succ)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : (H.stage i.castSucc).Carrier,
      normSq0S ((H.event i).incoming.flow.base.metric t) x 4
        ((H.event i).incoming.flow.base.rm04 t x) ≤ C)
    (x y : (H.stage i.castSucc).Carrier)
    (α₀ : ℝ → (H.stage i.castSucc).Carrier)
    (hα₀ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₀) (h₀ : α₀ 0 = x) (h₁ : α₀ b = y)
    (hball : {z | riemannianEDistOf ((H.event i).incoming.flow.base.metric T) x z <
      ENNReal.ofReal r} ⊆ Subtype.val '' interior K)
    (hgap : Real.sqrt b * Real.sqrt
      (Real.exp (18 * Real.sqrt C * b ^ 2) *
        (Real.exp (18 * Real.sqrt C * b ^ 2) *
          curveEnergy ((H.event i).incoming.flow.base.metric T) α₀ 0 b +
          72 * b ^ 3 * Real.sqrt C)) < r) :
    ∃ β : ℝ → H.backwardSurvivorFootprintInterior first i hle K,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ β ∧
      (H.backwardSurvivorFootprintMap first i hle K (β 0)).val = x ∧
      (H.backwardSurvivorFootprintMap first i hle K (β b)).val = y ∧
      reducedAction (H.event i).incoming.flow.base.metric T (b ^ 2)
        (squareRootReparametrization
          (fun s => (H.backwardSurvivorFootprintMap first i hle K (β s)).val)) =
        reducedLength (H.event i).incoming.flow.base.metric T isRegularizedAdmissible
          x (b ^ 2) y := by
  have hreg : Icc (T - b ^ 2) T ⊆
      (RealTimeInterval.closedOpen (H.time i.castSucc) (H.time i.succ)
        (H.event i).incoming.lt).regular :=
    fun t ht => ⟨hleft.trans_le ht.1, ht.2.trans_lt hright⟩
  have hgap' : Real.sqrt b * Real.sqrt
      (Real.exp (2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C * b ^ 2) *
        (Real.exp (2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C * b ^ 2) *
          curveEnergy ((H.event i).incoming.flow.base.metric T) α₀ 0 b +
          8 * b ^ 3 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C)) < r := by
    have hn : (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 = 9 := by norm_num [ThreeSpace]
    rw [hn]
    have h18 : (2 : ℝ) * 9 = 18 := by norm_num
    have h72 : 8 * b ^ 3 * 9 * Real.sqrt C = 72 * b ^ 3 * Real.sqrt C := by ring
    simpa only [h18, h72] using hgap
  obtain ⟨α, hα, h0, h1, hmin, hstay⟩ := exists_contMDiff_lCost_minimizer_in_ball_of_curvature_bound
    (H.event i).incoming.flow (H.event i).incoming.equation C T b r hb hreg hRm
      x y α₀ hα₀ h₀ h₁ hgap'
  obtain ⟨β, hβ, heq⟩ := lift_smooth_curve_eqOn H first i hle K htrace α hα b hb
    (fun s hs => hball (hstay s hs))
  refine ⟨β, hβ, (heq ⟨le_rfl, hb.le⟩).trans h0,
    (heq ⟨hb.le, le_rfl⟩).trans h1, ?_⟩
  rw [reducedAction_eq_lLength, reducedLength_eq_lCost,
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ (sq_nonneg b),
    Real.sqrt_sq hb.le]
  rw [lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ (sq_nonneg b),
    Real.sqrt_sq hb.le] at hmin
  rw [← hmin]
  apply lRegularizedAction_congr
  intro s hs
  have hs' : s ∈ Ioo 0 b := by simpa only [uIoo_of_le hb.le] using hs
  exact heq ⟨hs'.1.le, hs'.2.le⟩

theorem reducedAction_backwardSurvivorFootprintMap
    (K : Set (H.event i).incoming.terminalRegularOpen) {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K) D)
    (hmetric : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      S.base.metric t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (T b : ℝ) (hb : 0 ≤ b)
    (hleft : H.time i.castSucc ≤ T - b ^ 2) (hright : T < H.time i.succ)
    (β : ℝ → H.backwardSurvivorFootprintInterior first i hle K)
    (hβ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 β) :
    reducedAction S.base.metric T (b ^ 2) (squareRootReparametrization β) =
      reducedAction (H.event i).incoming.flow.base.metric T (b ^ 2)
        (squareRootReparametrization
          (fun s => (H.backwardSurvivorFootprintMap first i hle K (β s)).val)) := by
  let p : H.backwardSurvivorFootprintInterior first i hle K → (H.stage i.castSucc).Carrier :=
    fun z => (H.backwardSurvivorFootprintMap first i hle K z).val
  have hp : IsLocalDiffeomorph ThreeModel ThreeModel ∞ p :=
    DifferentialGeometry.isLocalDiffeomorph_comp
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := ThreeModel)
        (H.event i).incoming.terminalRegularOpen)
      (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K)
  have hdp (z : H.backwardSurvivorFootprintInterior first i hle K) :
      mfderiv ThreeModel ThreeModel p z = ContinuousLinearMap.id ℝ ThreeSpace := by
    have h1 := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
      (H.backwardSurvivorFootprintMap first i hle K) z
    have h2 := mfderiv_comp z
      ((H.backwardSurvivorTerminalFaceMap_contMDiff first i hle).mdifferentiable (by simp) z.val)
      ((contMDiff_subtype_val : ContMDiff ThreeModel ThreeModel ∞
        (Subtype.val : H.backwardSurvivorFootprintInterior first i hle K →
          H.backwardSurvivorTerminalFace first i hle)).mdifferentiable (by simp) z)
    change mfderiv ThreeModel ThreeModel p z =
      mfderiv ThreeModel ThreeModel (H.backwardSurvivorFootprintMap first i hle K) z at h1
    rw [h1]
    change mfderiv ThreeModel ThreeModel
      (H.backwardSurvivorTerminalFaceMap first i hle ∘ Subtype.val) z = _
    rw [h2, H.backwardSurvivorTerminalFaceMap_mfderiv, DifferentialGeometry.mfderiv_subtype_val]
    rfl
  have hm (s : ℝ) (hs : s ∈ Icc 0 b) :
      S.base.metric (T - s ^ 2) =
        ((H.event i).incoming.flow.localPullback p hp).base.metric (T - s ^ 2) := by
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).mpr hs.2
    rw [hmetric _ ⟨by linarith, by linarith [sq_nonneg s]⟩,
      H.backwardSurvivorTerminalFaceMetric_before first i hle
        (by linarith [sq_nonneg s] : T - s ^ 2 < H.time i.succ)]
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [SolutionOn.localPullback_metric, localPullMetric_inner, hdp]
    rfl
  rw [reducedAction_eq_lLength, reducedAction_eq_lLength,
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ (sq_nonneg b),
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ (sq_nonneg b),
    Real.sqrt_sq hb]
  unfold lRegularizedAction
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc 0 b := by simpa only [uIcc_of_le hb] using hs
  calc
    _ = lRegularizedLagrangian ((H.event i).incoming.flow.localPullback p hp) T β s := by
      unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
      rw [hm s hs']
    _ = _ := lRegularizedLagrangian_localPullback (H.event i).incoming.flow p hp T
      (hβ.mdifferentiable one_ne_zero s)

theorem exists_backwardSurvivor_reducedAction_minimizer
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K) D)
    (hmetric : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      S.base.metric t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (C T b r : ℝ) (hb : 0 < b)
    (hleft : H.time i.castSucc < T - b ^ 2) (hright : T < H.time i.succ)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ x : (H.stage i.castSucc).Carrier,
      normSq0S ((H.event i).incoming.flow.base.metric t) x 4
        ((H.event i).incoming.flow.base.rm04 t x) ≤ C)
    (x y : (H.stage i.castSucc).Carrier)
    (α₀ : ℝ → (H.stage i.castSucc).Carrier)
    (hα₀ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₀) (h₀ : α₀ 0 = x) (h₁ : α₀ b = y)
    (hball : {z | riemannianEDistOf ((H.event i).incoming.flow.base.metric T) x z <
      ENNReal.ofReal r} ⊆ Subtype.val '' interior K)
    (hgap : Real.sqrt b * Real.sqrt
      (Real.exp (18 * Real.sqrt C * b ^ 2) *
        (Real.exp (18 * Real.sqrt C * b ^ 2) *
          curveEnergy ((H.event i).incoming.flow.base.metric T) α₀ 0 b +
          72 * b ^ 3 * Real.sqrt C)) < r) :
    ∃ β : ℝ → H.backwardSurvivorFootprintInterior first i hle K,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ β ∧
      (H.backwardSurvivorFootprintMap first i hle K (β 0)).val = x ∧
      (H.backwardSurvivorFootprintMap first i hle K (β b)).val = y ∧
      reducedAction S.base.metric T (b ^ 2) (squareRootReparametrization β) =
        reducedLength (H.event i).incoming.flow.base.metric T isRegularizedAdmissible
          x (b ^ 2) y := by
  obtain ⟨β, hβ, h0, h1, hmin⟩ :=
    H.exists_stage_reducedAction_minimizer_in_backwardSurvivorFootprint first i hle K htrace
      C T b r hb hleft hright hRm x y α₀ hα₀ h₀ h₁ hball hgap
  refine ⟨β, hβ, h0, h1, ?_⟩
  rw [H.reducedAction_backwardSurvivorFootprintMap first i hle K S hmetric T b hb.le
    hleft.le hright β (hβ.of_le (by simp))]
  exact hmin

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
