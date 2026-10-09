import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowCommonC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowContinuationLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowCapWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Congruence

/-!
# `hwin`, late branch "Birth" (C12X, S16G G3)

Design `docs/geometrization/chapter8/out/CH12X-S16-HWIN-design.md` §2 (L) / §4 group G2.  A young
window point outside the core is late (`θB < T = scale · (t − time j.succ)`) or far-early.  For a
late point the window solution of `exists_standard_comparison_of_cap_window_trace` (which already
crosses every event `j.succ … k`) is old in standard-solution age, so the endpoint oriented
witness (`exists_uniform_orientedWitness_of_standard_close_endpoint`, closed window, no time
margin) and the windowed buffered canonical pipeline give a `CanonicalWitness` of the window
solution with uniform constant `C(ε)`.  Its spatial projection, pushed by `Ξ` and rescaled, is the
witness at `(y, t)`; if it is a neck, its `StrongNeck` is transported by
`SurvivorNeckPackage_C12X.full_of_model` (start `first := j.succ`, depth `R (t − time j.succ) ≥ 1`)
to a full history neck.  The model solution is the `Ξ`-pullback of the survivor package flow; it
agrees with the comparison's window solution on `[0, T]` (`window_model_metric_eq_C12X`).

Main theorem: `RetainedCoreHistory.exists_birth_C12X` (`θB CB` depend on `ε` only).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped NNReal Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.exists_slab_of_mem_Icc from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortion

universe u

private local instance s16gWindowSigmaCompact (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

private theorem s16g_nonempty_window_tangentOrientation (D : ℝ) :
    Nonempty (TangentOrientationSection (standardCapWindow D)) := by
  let e := (finCongr (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)).symm
  let o := DifferentialGeometry.Topology.Manifold.euclideanSmoothOrientation
    (EuclideanSpace ℝ (Fin 3))
    (Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3)) e
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation))
  obtain ⟨O, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      (𝓡 3) o
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let O₃ : DifferentialGeometry.ManifoldOrientation (𝓡 3) (EuclideanSpace ℝ (Fin 3)) 3 :=
    cast (congrArg (fun n =>
      DifferentialGeometry.ManifoldOrientation (𝓡 3) (EuclideanSpace ℝ (Fin 3)) n) hdim) O
  let oE : TangentOrientationSection (EuclideanSpace ℝ (Fin 3)) :=
    { orientation := O₃.orientation, locally_constant := O₃.locally_constant }
  exact ⟨oE.restrictOpen (standardCapWindow D)⟩

/-- A spatial canonical witness that is not a neck has a preconnected frontier (cap: one sphere;
whole components: clopen, empty frontier). -/
theorem isPreconnected_frontier_of_forall_ne_neck_C12X {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I3 M} {eps C1 C2 : ℝ} {x : M}
    (W : SpatialCanonicalWitness g eps C1 C2 x) (h : ∀ n, W.alternative ≠ .neck n) :
    IsPreconnected (frontier W.domain.carrier) := by
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ThreeSpace M
  cases hW : W.alternative with
  | neck n => exact absurd hW (h n)
  | cap c d => exact W.isPreconnected_frontier_of_alternative_eq_cap hW
  | positive whole _ _ =>
    rw [whole, isClopen_connectedComponent.frontier_eq]
    exact isPreconnected_empty
  | round whole _ =>
    rw [whole, isClopen_connectedComponent.frontier_eq]
    exact isPreconnected_empty

/-- A canonical witness whose alternative is not a neck projects to a non-neck spatial witness. -/
theorem canonicalWitness_toSpatial_ne_neck_C12X {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (K : CanonicalWitness S eps C1 C2 x t) (hK : ¬ ∃ data, K.alternative = .neck data) :
    ∀ n, K.toSpatial.alternative ≠ .neck n := by
  intro n hn
  change K.alternative.toSpatial = SpatialCanonicalAlternative.neck n at hn
  cases halt : K.alternative with
  | neck data => exact hK ⟨data, halt⟩
  | cap data deep =>
    rw [halt] at hn
    cases hn
  | positive whole data sec =>
    rw [halt] at hn
    cases hn
  | round whole data =>
    rw [halt] at hn
    cases hn

namespace RetainedCoreHistory

section WindowModel

variable (H : RetainedCoreHistory.{u}) {k : Fin (H.eventCount + 1)} {s : ℝ}
  (Gk : (H.stage k).IncomingSlab (H.time k) s) {j : Fin H.eventCount} (hl : j.succ ≤ k)

/-- `Ξ` composed with the inclusion of the incoming domain is a local diffeomorphism. -/
theorem isLocalDiffeomorph_incoming_val_C12X {t : ℝ}
    {G : (H.stage k).IncomingSlab (H.time k) t} {D : ℝ}
    {Ξ : standardCapWindow D → H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G}
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞
      (fun w => (Ξ w).val : standardCapWindow D → H.toHistory.backwardSurvivorDomain j.succ k hl) :=
  isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hΞ

/-- Pulling a restricted metric back along `Ξ` is pulling back along the inclusion composite. -/
private theorem localPull_scale_restrict_C12X {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    {V : TopologicalSpace.Opens M} [T2Space V] {N : Type*} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N] [T2Space N]
    (m : SmoothRiemannianMetric ThreeModel M) {q : ℝ} (hq : 0 < q) (f : N → V)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (hvf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun w => (f w).val)) :
    localPullMetric (scaleMetric q hq (m.restrictOpen V)) f hf =
      localPullMetric (scaleMetric q hq m) (fun w => (f w).val) hvf := by
  rw [localPullMetric_scaleMetric, localPullMetric_scaleMetric, ← localPullMetric_subtype_val,
    localPullMetric_comp _ _ _ (isLocalDiffeomorph_subtype_val V) hf hvf]
  rfl

/-- The comparison's window solution and the `Ξ`-pullback of a survivor package flow (start
`j.succ`) agree at every window time `τ ∈ [0, q (t − time j.succ)]`. -/
theorem window_model_metric_eq_C12X
    (P : H.toHistory.SurvivorNeckPackage_C12X k Gk j.succ hl) {t : ℝ} (hts : t < s)
    {G : (H.stage k).IncomingSlab (H.time k) t} {L : G.TerminalLimitMetric}
    (hG : ∀ v, G.flow.base.metric v = Gk.flow.base.metric v)
    (hL : L.metric = (Gk.flow.base.metric t).restrictOpen G.terminalRegularOpen)
    {D : ℝ} {Ξ : standardCapWindow D → H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G}
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    {gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G)}
    (hslab : ∀ (i : Fin H.eventCount) (hf : j.succ ≤ i.castSucc) (hi : i.succ ≤ k),
      ∀ τ ∈ Icc (H.time i.castSucc) (H.time i.succ),
        gflow τ = (H.toHistory.backwardSurvivorSlabMetric j.succ k hl i hf hi τ).restrictOpen
          (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G))
    (hcur : ∀ τ ∈ Icc (H.time k) t,
      gflow τ = H.toHistory.backwardSurvivorIncomingMetric j.succ k hl G L τ)
    {q : ℝ} (hq : 0 < q) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτT : τ ≤ q * (t - H.time j.succ)) :
    localPullMetric (scaleMetric q hq (gflow (H.time j.succ + τ / q))) Ξ hΞ =
      localPullMetric (scaleMetric q hq (P.gflow (H.time j.succ + τ / q))) (fun w => (Ξ w).val)
        (H.isLocalDiffeomorph_incoming_val_C12X hl hΞ) := by
  set τ' := H.time j.succ + τ / q with hτ'
  have h0 : 0 ≤ τ / q := div_nonneg hτ0 hq.le
  have h1 : τ / q ≤ t - H.time j.succ := by
    rw [div_le_iff₀ hq]
    linarith
  have hτ't : τ' ≤ t := by linarith
  rcases lt_or_ge τ' (H.time k) with hlt | hge
  · have hjk : H.time j.succ < H.time k := by linarith
    have hjk' : j.succ < k := H.time_strictMono.lt_iff_lt.mp hjk
    obtain ⟨i, hf, hi, hτi⟩ :=
      ObservedHistory.exists_slab_of_mem_Icc H.toHistory hjk' ⟨by linarith, hlt.le⟩
    rw [hslab i hf hi τ' hτi, ← P.slab_eq i hf hi τ' hτi]
    exact localPull_scale_restrict_C12X _ hq Ξ hΞ _
  · rw [hcur τ' ⟨hge, hτ't⟩, H.toHistory.localPullMetric_scaleMetric_backwardSurvivorIncomingMetric
      j.succ k hl G L Gk.flow.base.metric hG hL hΞ hq hτ't,
      P.cur_eq τ' ⟨hge, hτ't.trans_lt hts⟩,
      localPull_scale_restrict_C12X _ hq (fun w => (Ξ w).val)
        (H.isLocalDiffeomorph_incoming_val_C12X hl hΞ)
        (H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G hΞ),
      localPullMetric_scaleMetric]

end WindowModel

/-- **Late branch ("Birth").**  Uniform `θB CB` (depending on `ε` only): every window point with
`θB < T` (standard time since the birth of its cap) gets a witness of constants
`(CB, max CB Cgrad)` whose neck alternative carries a full history neck. -/
theorem exists_birth_C12X {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ θB CB : ℝ, 0 < θB ∧ θB < 1 ∧ 1 ≤ CB ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Ctime Cgrad : ℝ≥0) (Dw θw : ℝ),
      0 < Dw → θw < 1 →
    ∃ (Rw : ℝ) (mw : ℕ), Dw + 1 < Rw ∧
    ∀ qcan : ℝ, 0 < qcan →
    ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rw ≤ p₀.modelRadius → mw ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k → Gk.DerivativeBoundBefore Ctime qcan s →
    ∀ (y : (H.stage k).Carrier) (t : ℝ), t ∈ Ioo (H.time k) s → qcan < Gk.flow.scalar t y →
    ∀ d : H.WindowDatum_C12X records k y t Dw θw, θB < d.scale * (t - H.time d.j.succ) →
      H.StronglyCanonicalAtFull_C12X k Gk ε ε CB (max CB (Cgrad : ℝ)) y t := by
  obtain ⟨C, δ0, hC, hδ0, hδ01, hpipe⟩ :=
    exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts.{0} hε hε' 1
  obtain ⟨τQ, hτQ, hL6⟩ := exists_uniform_orientedWitness_of_standard_close_endpoint hδ0 hδ01
  obtain ⟨c₀, hc₀, hQlow⟩ := exists_standard_scalar_lower_bound
  set τs := max τQ 1 with hτsdef
  have hτs : 0 < τs := lt_of_lt_of_le one_pos (le_max_right _ _)
  set θB := 2 * τs / (c₀ + 2 * τs) with hθBdef
  have hθB : 0 < θB := by positivity
  have hθB1 : θB < 1 := by rw [hθBdef, div_lt_one (by positivity)]; linarith
  refine ⟨θB, C, hθB, hθB1, hC, ?_⟩
  intro P₀ g₀ Ctime Cgrad Dw θw hDw hθw
  obtain ⟨a₀, ha₀, hHI⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  set Θ := max θw (1 / 2) with hΘdef
  have hΘ1 : Θ < 1 := max_lt hθw (by norm_num)
  have hΘ0 : 0 < Θ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨eta, heta, hlower⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison Θ hΘ0.le hΘ1
  obtain ⟨Λ, hΛ, hplace⟩ := StandardSolution.exists_window_ball_placement hΘ1
  set L := 4 * C + 1 with hLdef
  have hL0 : 0 ≤ L := by positivity
  obtain ⟨D, N, e, hrD, he, hwit⟩ := hL6 Θ (Dw + 1 + Λ * (L + 1)) hΘ1
  have hΛL : 0 ≤ Λ * (L + 1) := by positivity
  have hD : 0 < D := by linarith
  obtain ⟨Pb, Creset, Cb, -, -, hCb, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace.{u} Θ Ctime hΘ0 hΘ1
  obtain ⟨R, hR, m, -, ζ, δ₀, hζ, -, hδ₀, hbr⟩ := hbridge D e eta hD he heta N
  refine ⟨R, m, by linarith, ?_⟩
  intro qcan hqcan
  set ρmax := min (Real.sqrt (Cb / (4 * qcan))) (Real.sqrt (a₀ / 2)) with hρdef
  have hρmax : 0 < ρmax := lt_min (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr (by positivity))
  have hρ₁ : ρmax ^ 2 ≤ Cb / (4 * qcan) := by
    have h := pow_le_pow_left₀ hρmax.le (min_le_left _ _) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  have hρ₂ : ρmax ^ 2 ≤ a₀ / 2 := by
    have h := pow_le_pow_left₀ hρmax.le (min_le_right _ _) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  refine ⟨δ₀, ρmax, ζ, hδ₀, hρmax, hζ, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec k s Gk hGk hderiv
    hderG y t ht hRy d hlate
  rcases d with ⟨j, hl, A, b, x, hanchor, hxD, hage⟩
  change θB < ((records j).static b).neck.scale * (t - H.time j.succ) at hlate
  obtain ⟨hkt, hts⟩ := ht
  have hcur := Gk.derivativeBoundBefore_mono hts.le hderG
  obtain ⟨hHI1, hHI2⟩ := hHI H.toHistory hId.some
  set q := ((records j).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j).static b).neck.scale_pos
  obtain ⟨hbirth, haq⟩ := hrec.birth_scale_bounds hΛδ j b hqcan hCb ha₀ hρb hρ₁ hρ₂
  have hbirth1 : qcan ≤ Cb * q := by linarith
  have hba : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hl
  have hθΘ : θw ≤ Θ := le_max_left _ _
  have hxD' : ‖x.val‖ < D + 1 := by linarith
  obtain ⟨G, L', hG, -, hL, -, -, -, -, -, -, -, z, hzx, hy, Ξ, hΞs, -, hΞmark, hΞ, gflow, S,
      hS1, hS2, hS3, -, hS5, -, -, Q, -, hclose⟩ :=
    hbr H p₀ δbound ρbound records hrec hδb hrad hord hacc qcan a₀ θw hqcan hθΘ hHI1 hHI2 k s
      Gk hGk hderiv t hkt hts hcur j hl y A b x hanchor hage hxD' hbirth1 haq
  have hyz : (Ξ z).val.val = y := congrArg Subtype.val hΞmark
  set T := q * (t - H.time j.succ) with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTθ : T ≤ θw := by
    have h1 := mul_le_mul_of_nonneg_left hage hq.le
    rwa [mul_comm θw, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTΘ : T ∈ Icc 0 Θ := ⟨hT0, hTθ.trans hθΘ⟩
  have hTmem : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  have hT1 : T < 1 := hTθ.trans_lt hθw
  have htT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST := H.capWindow_flow_metric_eq Gk hl hΞ hq hG hL hS2 hS5 T hTmem
    (by rw [htT]; linarith)
  rw [htT] at hST
  have hΦ := H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G hΞ
  have hinj := H.toHistory.injective_backwardSurvivorIncomingDomain_val_val j.succ k hl G
    hΞs.isEmbedding.injective
  -- the model solution: `Ξ`-pullback of a survivor package flow started at `j.succ`
  obtain ⟨P⟩ := H.toHistory.nonempty_survivorNeckPackage_C12X Gk j.succ hl hGk
  have hΞ' := H.isLocalDiffeomorph_incoming_val_C12X hl hΞ
  have hinj' : Injective (fun w => (Ξ w).val :
      standardCapWindow D → H.toHistory.backwardSurvivorDomain j.succ k hl) :=
    fun w₁ w₂ h => hinj (congrArg Subtype.val h)
  let S' : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
      (RealTimeInterval.closed 0 T hT0) :=
    { base := { metric := fun τ => localPullMetric (scaleMetric q hq
        (P.gflow (H.time j.succ + τ / q))) (fun w => (Ξ w).val) hΞ' } }
  have hSS' : ∀ τ ∈ Icc 0 T, S.base.metric τ = S'.base.metric τ := fun τ hτ => by
    rw [hS5 τ]
    exact H.window_model_metric_eq_C12X Gk hl P hts hG hL hΞ hS1 hS2 hq hτ.1 hτ.2
  have hS'sol : IsSolutionOn S' := IsSolutionOn.congr_metric hS3 hSS'
  have hS'T : S'.base.metric T = S.base.metric T := (hSS' T hTmem).symm
  have hRS : S'.scalar T z = q⁻¹ * Gk.flow.scalar t y := by
    change metricScalarAt (S'.base.metric T) z = _
    rw [hS'T, hST, metricScalarAt_localPullMetric_scaleMetric, hyz]
    rfl
  have hRpos : 0 < Gk.flow.scalar t y := hqcan.trans hRy
  have hTRS : T * S'.scalar T z = Gk.flow.scalar t y * (t - H.time j.succ) := by
    rw [hRS, hTdef]
    field_simp
  -- standard-solution scalar lower bound ⇒ age `τs ≤ T R_S`
  have hlow := (hlower Q (standardCapWindow D) (S.base.metric T) T hTΘ z
    (fun i hi => ((hclose T hTmem).2 i hi z).le)).2
  rw [metricScalarAt_restrictOpen] at hlow
  have hτs' : τs ≤ T * S'.scalar T z := by
    have hS : 1 / 2 * metricScalarAt (Q.val.metric T) z.val ≤ S'.scalar T z := by
      change _ ≤ metricScalarAt (S'.base.metric T) z
      rw [hS'T]
      exact hlow
    exact le_mul_of_half_standard_scalar_lower hτs.le hc₀ hT1 (hQlow Q z.val T ⟨hT0, hT1⟩) hS
      (by rw [hTdef]; exact hlate.le)
  have hdepth : H.time j.succ ≤ t - (Gk.flow.scalar t y)⁻¹ := by
    have h1 : 1 ≤ Gk.flow.scalar t y * (t - H.time j.succ) := by
      rw [← hTRS]
      exact (le_max_right τQ 1).trans hτs'
    have h2 : (Gk.flow.scalar t y)⁻¹ ≤ t - H.time j.succ := by
      rw [inv_le_iff_one_le_mul₀ hRpos, mul_comm]
      exact h1
    linarith
  -- canonical witness of the model solution
  obtain ⟨o⟩ := s16g_nonempty_window_tangentOrientation D
  have hOW : OrientedWitness S' o δ0 standardModelKappa z T :=
    hwit Q T hT0 (hTθ.trans hθΘ) S' hS'sol
      (fun τ hτ' i hi v => by rw [← hSS' τ hτ']; exact (hclose τ hτ').1 i hi v) o z
      (by rw [hzx]; linarith) ((le_max_left τQ 1).trans hτs')
  have hreg : Ioo (T - (δ0 * S'.scalar T z)⁻¹) T ⊆ (RealTimeInterval.closed 0 T hT0).regular := by
    obtain ⟨Wm, -⟩ := hOW
    have hwin := Wm.window_mem
      ⟨le_rfl, sub_le_self _ (inv_nonneg.mpr (mul_pos hδ0 Wm.scalar_pos).le)⟩
    intro σ hσ
    exact ⟨hwin.1.trans_lt hσ.1, hσ.2⟩
  obtain ⟨B, hB⟩ := hpipe standardModelKappa (standardCapWindow D)
    (RealTimeInterval.closed 0 T hT0) S' hS'sol δ0 o z T le_rfl hreg hOW
  let K : CanonicalWitness S' ε C C z T := B.canonicalWitnessMono B.tolerance_lt.le hε'
  have hK : K.capTubeHasNeckChart ε := hB.mono_eps B.tolerance_lt.le hε'
  -- the full neck in the neck case
  have hfull : (∃ data, K.alternative = .neck data) →
      H.toHistory.HistoryStrongNeckFull_C12X k Gk ε y t := by
    rintro ⟨data, -⟩
    have hj : H.time j.succ ∈ Ico (H.time j.succ) s := ⟨le_rfl, by linarith⟩
    have h := P.full_of_model (fun w => (Ξ w).val) hΞ' hinj' hq hj S' (fun _ => rfl) data.strong
      (y := y) hyz (by rw [htT]; exact hkt.le) (by rw [htT]; exact hts)
      (by rw [htT]; exact hdepth)
    rwa [htT] at h
  -- spatial witness on the pulled-back metric, then pushed to `Gk` at `t`
  subst hyz
  have hinner : ∀ (v : standardCapWindow D) (w : TangentSpace I3 v),
      (1 / 2) * ((Q.val.metric T).restrictOpen (standardCapWindow D)).inner v w w ≤
        (S.base.metric T).inner v w w := fun v w =>
    (hlower Q (standardCapWindow D) (S.base.metric T) T hTΘ v
      (fun i hi => ((hclose T hTmem).2 i hi v).le)).1 w
  have hQ1 : 1 ≤ metricScalarAt (Q.val.metric T) z.val :=
    Q.val.one_le_scalar T (Q.mem_domain_of_mem_Icc hΘ1 hTΘ) z.val
  have hzr : ‖(z : EuclideanSpace ℝ (Fin 3))‖ + Λ * (L + 1) < D + 1 := by
    rw [hzx]
    linarith only [hxD, hrD]
  obtain ⟨hcpt, -⟩ := hplace D L z hL0 hzr Q T hTΘ (S.base.metric T) hinner
  have key : ∃ W : SpatialCanonicalWitness (localPullMetric (scaleMetric q hq
      (Gk.flow.base.metric t)) (fun w => (Ξ w).val.val) hΦ) ε C C z,
      W.capTubeHasNeckChart ε ∧ 2 * W.radius < L ∧
        ((∃ data, K.alternative = .neck data) ∨ IsPreconnected (frontier W.domain.carrier)) := by
    rw [← hST, ← hS'T]
    refine ⟨K.toSpatial, CanonicalWitness.capTubeHasNeckChart_toSpatial hK, ?_, ?_⟩
    · have hRS2 : 1 / 2 ≤ metricScalarAt (S'.base.metric T) z := by
        rw [hS'T]
        linarith only [hlow, hQ1]
      have hs : 1 / 2 ≤ Real.sqrt (metricScalarAt (S'.base.metric T) z) := by
        have h := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ^ 2 ≤ metricScalarAt (S'.base.metric T) z by
          linarith only [hRS2])
        rwa [Real.sqrt_sq (by norm_num)] at h
      have hr0 : 0 ≤ K.toSpatial.radius :=
        (inv_nonneg.mpr (Real.sqrt_nonneg _)).trans K.toSpatial.radius_lower
      have hup := K.toSpatial.radius_upper
      rw [le_div_iff₀ (Real.sqrt_pos.mpr (by linarith only [hRS2]))] at hup
      linarith only [mul_le_mul_of_nonneg_left hs hr0, hup, hLdef]
    · by_cases hKn : ∃ data, K.alternative = .neck data
      · exact Or.inl hKn
      · exact Or.inr (isPreconnected_frontier_of_forall_ne_neck_C12X _
          (canonicalWitness_toSpatial_ne_neck_C12X K hKn))
  obtain ⟨W, hW, hWr, hWalt⟩ := key
  rw [hST] at hcpt
  have hscale : scaleMetric q⁻¹ (inv_pos.mpr hq) (scaleMetric q hq (Gk.flow.base.metric t)) =
      Gk.flow.base.metric t :=
    SmoothRiemannianMetric.ext_inner fun v w₁ w₂ => by
      simp only [scaleMetric_inner]
      field_simp
  have hWit : ∃ W' : SpatialCanonicalWitness (Gk.flow.base.metric t) ε C C (Ξ z).val.val,
      W'.capTubeHasNeckChart ε ∧
        ((∃ data, K.alternative = .neck data) ∨ ∀ n, W'.alternative ≠ .neck n) := by
    rw [← hscale]
    refine ⟨(W.pushforwardOfInjectiveULift hΦ hinj hWr hcpt).scaleMetric q⁻¹ (inv_pos.mpr hq),
      SpatialCanonicalWitness.capTubeHasNeckChart.scaleMetric q⁻¹ (inv_pos.mpr hq)
        (hW.pushforwardOfInjectiveULift hΦ hinj hWr hcpt), ?_⟩
    rcases hWalt with hn | hWf
    · exact Or.inl hn
    · refine Or.inr fun n => ?_
      apply SpatialCanonicalWitness.alternative_ne_neck_of_isPreconnected_frontier
      rw [SpatialCanonicalWitness.domain_scaleMetric]
      exact W.isPreconnected_frontier_pushforwardOfInjectiveULift hΦ hinj hWr hcpt hWf
  obtain ⟨W', hW', hW'alt⟩ := hWit
  have hAt : H.StronglyCanonicalAtFull_C12X k Gk ε ε C C (Ξ z).val.val t := by
    refine ⟨W', hW', fun ⟨n, hn⟩ => ?_⟩
    rcases hW'alt with hKn | hne
    · exact hfull hKn
    · exact absurd hn (hne n)
  have hWhere : H.StronglyCanonicalWhereFull_C12X k Gk ε ε C C qcan
      (fun y' t' => y' = (Ξ z).val.val ∧ t' = t) := by
    rintro y' t' - - ⟨rfl, rfl⟩
    exact hAt
  exact (hWhere.mono_constants le_rfl (le_max_left _ _)) _ _ ⟨hkt, hts⟩ hRy ⟨rfl, rfl⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
