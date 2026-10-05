import DifferentialGeometry.Geometry.Fibration.ActualStageChain
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutputLocalityBLOC

/-!
# CFS24 on the actual stage outputs of the GAF02 chain

Blueprint `master207B.tex`, CFS24 (`lem:fibration-spectral-marker-locality`, B:3477–3520). The
"single smoothing construction CFS11–CFS14" of the row is, on the actual data, the native stage
output `O : Cfs15StageOutput` of an active slot of the chain `C : Gaf02Chain P …` (stage cloud
`S_st = gafCloud st`, radius `r = Σ_st ρ ∘ sel_st`, accuracy `ε = Ξ_st`, so `b = ε⁻¹`, planes
`C.plane st`); the stage projection is `P = π_{Q_st} ∘ a` with `a = O.ambient`, and the blended
adjustment is `adjustmentMap Q_st P ψ`, `z ↦ z + ψ z • (P(π_{Q_st} z) − π_{Q_st} z)` (the chain's
`Ψ_j` for `ψ = ψ_j`).

* `cfs24_kernel_CFSB`: the row on any native output whose cloud and planes lie in `Q`, for a
  continuous linear `J` with `J w = 0 ⇒ J (π_Q w) = 0` (true for coordinate projections).
* `cfs24_row_CFSB` (`J = π_T`, the orthogonal projection onto the coordinate subspace of a tag set
  `T`) and `cfs24_row_marker_CFSB` (`J = v_t`, a scalar marker projection — "in particular scalar
  marker projections are allowed"): under (ZL) for every selected centre of the whole contributor
  window at the core point `x`, `Jη = Jz` on `B(x, 8br_x)`, `J ≡ 0` on `W ∩ B(x, 3br_x)`,
  `JP = 0` on `B(x, r_x)`, and every blended adjustment keeps a zero `J` coordinate there.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

section Kernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k Kj : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}

/-- **CFS24 on one native output** (kernel form). If the cloud and the planes lie in `Q`, `J`
kills `π_Q w` whenever it kills `w`, and every selected centre `i` of the whole contributor window
at `x ∈ S` has `J i = 0`, `P i ≤ ker J` (ZL), then `J ∘ η = J` on `B(x, 8ε⁻¹r_x)`, `J ≡ 0` on
`W ∩ B(x, 3ε⁻¹r_x)`, `J (π_Q a z) = 0` on `B(x, r_x)`, and every blended adjustment
`z + ψ z • (π_Q a(π_Q z) − π_Q z)` keeps `J z = 0` when `π_Q z ∈ B(x, r_x)`. -/
theorem cfs24_kernel_CFSB (O : Cfs15StageOutput k Kj ε cw S T r P) (Q : Submodule ℝ H)
    (J : H →L[ℝ] F) (hJQ : ∀ w, J w = 0 → J (Q.starProjection w) = 0) {x : H} (hx : x ∈ S)
    (hZL : ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      J i = 0 ∧ P i ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) :
    (∀ z ∈ ball x (8 * ε⁻¹ * r x), J (cfs15Section_C15 ε r P O.hI z) = J z) ∧
    (∀ w ∈ O.Z ∩ ball x (3 * ε⁻¹ * r x), J w = 0) ∧
    (∀ z ∈ ball x (r x), J (Q.starProjection (O.ambient z)) = 0) ∧
    ∀ (ψ : H → ℝ) (z : H), Q.starProjection z ∈ ball x (r x) → J z = 0 →
      J (adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z) = 0 := by
  obtain ⟨h1, h2, h3, -, -⟩ := O.linear_kernel_BLOC hx J hZL
  have hrx := O.radius_pos x hx
  have hε := O.eps_pos
  have h38 : 3 * ε⁻¹ * r x ≤ 8 * ε⁻¹ * r x := by
    have : 0 < ε⁻¹ * r x := by positivity
    nlinarith
  have hP : ∀ z ∈ ball x (r x), J (Q.starProjection (O.ambient z)) = 0 :=
    fun z hz => hJQ _ (h3 z hz)
  refine ⟨h1, fun w hw => h2 ⟨hw.1, ball_subset_ball h38 hw.2⟩, hP, fun ψ z hz hJz => ?_⟩
  rw [adjustmentMap_apply, map_add, map_smul, map_sub, hP _ hz, hJQ z hJz, hJz]
  simp

end Kernel

section Row

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

open Classical in
/-- A coordinate projection `π_T` kills `π_{Q_st} w` whenever it kills `w`. -/
theorem blockRestrict_stageQ_CFSB (st : Fin 3) (Tg : Finset (CGPTag P.toLocalChartFamily P.zero))
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hw : blockRestrict Tg w = 0) :
    blockRestrict Tg ((gafStageQ P.toLocalChartFamily P.zero st).starProjection w) = 0 := by
  rw [gafStageQ_starProjection]
  have h1 := congrArg (fun A => A w) (blockRestrict_comp (V := fun _ : CGPTag
    P.toLocalChartFamily P.zero => ℝ²) (gafStageTags P.toLocalChartFamily P.zero st) Tg)
  have h2 := congrArg (fun A => A w) (blockRestrict_comp (V := fun _ : CGPTag
    P.toLocalChartFamily P.zero => ℝ²) Tg (gafStageTags P.toLocalChartFamily P.zero st))
  simp only [ContinuousLinearMap.comp_apply] at h1 h2
  rw [h1, Finset.inter_comm, ← h2, hw, map_zero]

open Classical in
/-- A scalar marker projection `v_t` kills `π_{Q_st} w` whenever it kills `w`. -/
theorem blockMarker_stageQ_CFSB (st : Fin 3) (t : CGPTag P.toLocalChartFamily P.zero)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hw : blockMarkerCLM t w = 0) :
    blockMarkerCLM t ((gafStageQ P.toLocalChartFamily P.zero st).starProjection w) = 0 := by
  rw [gafStageQ_starProjection, blockMarkerCLM_apply, blockRestrict_apply]
  rw [blockMarkerCLM_apply] at hw
  split_ifs
  · exact hw
  · rfl

open Classical in
/-- **CFS24** (`lem:fibration-spectral-marker-locality`) on the actual stage output of the chain,
`J = π_T` the orthogonal projection onto the coordinate subspace of the tags `T`. If the slot of
stage `st` is the native output `O` and EVERY selected centre `i` whose closed
`80b r_i` ball meets `B(x, 8b r_x)` (`b = Ξ_st⁻¹`, `r = Σ_st ρ ∘ sel_st`, `x ∈ S_st`) has
`π_T i = 0` and `L_i ⊆ ker π_T` (ZL), then the global section has `π_T η = π_T` on `B(x, 8br_x)`,
every `w ∈ W ∩ B(x, 3br_x)` has `π_T w = 0`, `π_T P(z) = 0` on `B(x, r_x)` for the stage
projection `P = π_{Q_st} ∘ a`, and every blended adjustment `adjustmentMap Q_st P ψ` (in
particular the chain's `Ψ_j`) preserves a zero `π_T` coordinate at every input with
`π_{Q_st} z ∈ B(x, r_x)`. -/
theorem cfs24_row_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3)
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
      (fun x => S st * ρ (C.sel st x)) (C.plane st))
    (hO : C.slot st = .active O) (Tg : Finset (CGPTag P.toLocalChartFamily P.zero))
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hZL : ∀ i ∈ O.I, (closedBall i (80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st i))) ∩
        ball x (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st x)))).Nonempty →
      blockRestrict Tg i = 0 ∧ C.plane st i ≤ LinearMap.ker
        ((blockRestrict (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) Tg :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ]
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ]
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) :
    (∀ z ∈ ball x (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st x))),
      blockRestrict Tg (cfs15Section_C15 (Ξ st) (fun x => S st * ρ (C.sel st x)) (C.plane st)
        O.hI z) = blockRestrict Tg z) ∧
    (∀ w ∈ O.Z ∩ ball x (3 * (Ξ st)⁻¹ * (S st * ρ (C.sel st x))), blockRestrict Tg w = 0) ∧
    (∀ z ∈ ball x (S st * ρ (C.sel st x)),
      blockRestrict Tg ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
        ((C.slot st).map z)) = 0) ∧
    ∀ (ψ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ)
      (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection z ∈
        ball x (S st * ρ (C.sel st x)) → blockRestrict Tg z = 0 →
      blockRestrict Tg (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero st)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection ((C.slot st).map y))
        ψ z) = 0 := by
  have hmap : (C.slot st).map = O.ambient := by rw [hO]; rfl
  rw [hmap]
  exact cfs24_kernel_CFSB O (gafStageQ P.toLocalChartFamily P.zero st) (blockRestrict Tg)
    (blockRestrict_stageQ_CFSB st Tg) hx hZL

open Classical in
/-- **CFS24 with a scalar marker projection** `J = v_t` (the second coordinate of the block `t`):
the same four conclusions under (ZL) for `v_t`. -/
theorem cfs24_row_marker_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (st : Fin 3)
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
      (fun x => S st * ρ (C.sel st x)) (C.plane st))
    (hO : C.slot st = .active O) (t : CGPTag P.toLocalChartFamily P.zero)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hZL : ∀ i ∈ O.I, (closedBall i (80 * (Ξ st)⁻¹ * (S st * ρ (C.sel st i))) ∩
        ball x (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st x)))).Nonempty →
      blockMarkerCLM t i = 0 ∧ C.plane st i ≤ LinearMap.ker
        ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) t :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) :
    (∀ z ∈ ball x (8 * (Ξ st)⁻¹ * (S st * ρ (C.sel st x))),
      blockMarkerCLM t (cfs15Section_C15 (Ξ st) (fun x => S st * ρ (C.sel st x)) (C.plane st)
        O.hI z) = blockMarkerCLM t z) ∧
    (∀ w ∈ O.Z ∩ ball x (3 * (Ξ st)⁻¹ * (S st * ρ (C.sel st x))), blockMarkerCLM t w = 0) ∧
    (∀ z ∈ ball x (S st * ρ (C.sel st x)),
      blockMarkerCLM t ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
        ((C.slot st).map z)) = 0) ∧
    ∀ (ψ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ)
      (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection z ∈
        ball x (S st * ρ (C.sel st x)) → blockMarkerCLM t z = 0 →
      blockMarkerCLM t (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero st)
        (fun y => (gafStageQ P.toLocalChartFamily P.zero st).starProjection ((C.slot st).map y))
        ψ z) = 0 := by
  have hmap : (C.slot st).map = O.ambient := by rw [hO]; rfl
  rw [hmap]
  exact cfs24_kernel_CFSB O (gafStageQ P.toLocalChartFamily P.zero st) (blockMarkerCLM t)
    (blockMarker_stageQ_CFSB st t) hx hZL

end Row

end DifferentialGeometry.Geometry.Collapse
