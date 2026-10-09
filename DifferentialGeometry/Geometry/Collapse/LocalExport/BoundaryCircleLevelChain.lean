import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleLevelConnected
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorEmbedding

/-!
# O-WF G2b: the whole adjusted circle level of the boundary chain is connected

`BoundarySupplyCore.circleY_OWF S j = {q ∈ B(j, 200ρ_j) | ‖η_j q‖ < 5}` (GAF07's `Y_j` on `W°`,
open: `isOpen_circleY_OWF`) and **`BoundaryGaf02ChainE.circle_level_connected_OWF`**: for
`‖a‖ < 4` the WHOLE adjusted level `{q ∈ Y_j | κ_j(f₀ q) = a}` is connected (closed twin
`Gaf02Chain.gaf07_circle_level_GAFC`; FC34a with the inputs of `BoundaryCircleLevelConnected`).
Register premises: `c₂ < 1/1000`, `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- GAF07's original circle domain on `W°`: `Y_j = {q ∈ B(j, 200ρ_j) | ‖η_j q‖ < 5}`. -/
def circleY_OWF (j : S.CircleIdx_BAUGD) : Set (W.pieceInterior ⊤) :=
  letI := inducedMetricSpace S.completion.metric
  {q | dist q j.1 < 200 * S.rho j.1 ∧ ‖S.circleEta_BIF j.1 q‖ < 5}

/-- `Y_j` lies in the chart ball `B(j, 200ρ_j)`. -/
theorem circleY_subset_ball_OWF (j : S.CircleIdx_BAUGD) :
    S.circleY_OWF j ⊆
      (letI := inducedMetricSpace S.completion.metric; ball j.1 (200 * S.rho j.1)) :=
  fun _ hq => hq.1

/-- `Y_j` is open. -/
theorem isOpen_circleY_OWF (j : S.CircleIdx_BAUGD) : IsOpen (S.circleY_OWF j) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hη : ContinuousOn (S.circleEta_BIF j.1) (ball j.1 (200 * S.rho j.1)) := by
    rw [S.circleEta_eq_cgpCircleCoord_BBP j]
    exact (cgpCircleCoord_contMDiffOn_BAUGP S.family.toLocalPacketsOnB hj).continuousOn
  have h := hη.isOpen_inter_preimage isOpen_ball
    (isOpen_lt continuous_norm (continuous_const (y := (5 : ℝ))))
  exact h

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The adjusted circle coordinate `g_j = κ_j ∘ f₀ ∘ val` is smooth on `W°`. -/
theorem circle_adjusted_contMDiff_OWF (j : S.CircleIdx_BAUGD) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ²) ∞
      (fun q : W.pieceInterior ⊤ => S.circleKappa_BBP j (C.toChain.stageMap 0 q.val)) :=
  ((S.circleKappa_BBP j).comp ((actualSlotsV2_BAUGD S).stageProj 0)).contDiff.comp_contMDiff
    ((C.stage_smooth_BAUGD 3).comp (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff)

/-- **The whole adjusted circle level is connected** (closed `gaf07_circle_level_GAFC`): for
`‖a‖ < 4`, `{q ∈ Y_j | κ_j(f₀ q) = a}` is connected. -/
theorem circle_level_connected_OWF (hc : c 2 < 1 / 1000) (hβ : β 2 ≤ 1 / 10000000)
    (hd : γ + β 2 < 1 / 10) (j : S.CircleIdx_BAUGD) {a : ℝ²} (ha : ‖a‖ < 4) :
    IsConnected {q | q ∈ S.circleY_OWF j ∧
      S.circleKappa_BBP j (C.toChain.stageMap 0 q.val) = a} := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hr := S.rho_pos j.1
  obtain ⟨H, hH0, hH1, hcoord⟩ := C.circle_final_coordinates_BAUGD hc
  have e := S.circleEta_eq_cgpCircleCoord_BBP j
  set η' := cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB j.1 hj with hη'
  have eq : ∀ q, S.circleEta_BIF j.1 q = η' q := fun q => congrFun e q
  have hU := S.isOpen_circleY_OWF j
  have hη : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ²) ∞ η' (S.circleY_OWF j) :=
    (cgpCircleCoord_contMDiffOn_BAUGP S.family.toLocalPacketsOnB hj).mono fun q hq => hq.1
  have hgη : ∀ y ∈ S.circleY_OWF j,
      ‖S.circleKappa_BBP j (C.toChain.stageMap 0 y.val) - η' y‖ < 1 / 800 := by
    intro y hy
    rw [← eq y]
    exact (hcoord j hy.1 (by linarith [hy.2])).1
  have hright : ∀ y ∈ S.circleY_OWF j, ∃ R : ℝ² →L[ℝ] E3,
      (show E3 →L[ℝ] ℝ² from mfderiv (𝓡 3) 𝓘(ℝ, ℝ²) η' y).comp R = ContinuousLinearMap.id ℝ ℝ² ∧
        ∀ w, (fun (q : W.pieceInterior ⊤) (v : E3) =>
          (S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q v v)) y (R w) ≤ 2 * ‖w‖ :=
    fun y hy => circle_gram_right_inverse_OWF S.family.toLocalPacketsOnB hβ hd hj hy.1
  have hDg : ∀ y ∈ S.circleY_OWF j, ∀ v : E3,
      ‖(show E3 →L[ℝ] ℝ² from mfderiv (𝓡 3) 𝓘(ℝ, ℝ²)
          (fun q : W.pieceInterior ⊤ => S.circleKappa_BBP j (C.toChain.stageMap 0 q.val)) y) v -
        (show E3 →L[ℝ] ℝ² from mfderiv (𝓡 3) 𝓘(ℝ, ℝ²) η' y) v‖ ≤
        H * (fun (q : W.pieceInterior ⊤) (v : E3) =>
          (S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q v v)) y v := by
    intro y hy v
    have hD' := (hcoord j hy.1 (by linarith [hy.2])).2 v
    have e4 : mvfderiv (𝓡 3) (S.circleEta_BIF j.1) y v = mvfderiv (𝓡 3) η' y v :=
      congrArg (fun f => mvfderiv (𝓡 3) f y v) e
    exact (congrArg (fun t => ‖mvfderiv (𝓡 3) (fun x : W.pieceInterior ⊤ =>
      S.circleKappa_BBP j (C.toChain.stageMap 0 x.val)) y v - t‖) e4).symm.trans_le hD'
  have hQ : IsCompact {y | y ∈ S.circleY_OWF j ∧ ‖η' y‖ ≤ 401 / 100 * 1} := by
    convert isCompact_circleSlab_OWF S.family.toLocalPacketsOnB hj (a := 401 / 100)
      (by norm_num) using 1
    ext x
    constructor
    · rintro ⟨⟨hx, -⟩, hxa⟩
      exact ⟨hx, by linarith⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨hx, lt_of_eq_of_lt (congrArg norm (eq x)) (by linarith)⟩, by linarith⟩
  have hconn : IsConnected {y | y ∈ S.circleY_OWF j ∧ η' y = a} := by
    convert isConnected_circleLevel_OWF S.family.toLocalPacketsOnB hj (a := a) (by linarith)
      using 1
    ext x
    constructor
    · rintro ⟨⟨hx, -⟩, hxa⟩
      exact ⟨hx, hxa⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨hx, lt_of_eq_of_lt (congrArg norm ((eq x).trans hxa)) (by linarith)⟩, hxa⟩
  have : LocallyCompactSpace (W.pieceInterior ⊤) :=
    Manifold.locallyCompact_of_finiteDimensional (𝓡 3)
  exact connected_adjusted_level_of_isotopy_BAUGD (by simp) hU hη
    (C.circle_adjusted_contMDiff_OWF j).contMDiffOn le_rfl (by linarith) hgη _ hH0
    (by linarith) hright hDg hQ hconn

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
