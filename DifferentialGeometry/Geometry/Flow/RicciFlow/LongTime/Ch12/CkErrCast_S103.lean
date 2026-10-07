import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.H0Defect_S103
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LiftBridge_S65

set_option autoImplicit false

/-!
# CH12-S103 / G4: transport of the `ckErr` closeness along the post-stage equality; `h0` defect half
for the `postStage` / `postMetric` data of the hWA statement

* `ckErr_S45_cast_stage_S103` : `ckErr_S45` of a metric / map is unchanged under `subst` of a stage
  equality `P = P'` (map `f` cast along `congrArg Carrier`, metrics `HEq`).
* `h0_defect_of_post_S103` : `h0_defect_S103` with the hypotheses in the shape of the frozen hWA (v3):
  `f : H.Carrier → (postStage O t).Carrier`, `ckErr_S45 H (postMetric O t) t⁻¹ f j p < δ`,
  `postStage O t = K.stage j0`, `HEq (postMetric O t) (K.stageMetric j0 t)` (`postData_eq_history_O3`),
  `J = cast f`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime TopologicalSpace
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem ckErr_S45_cast_stage_S103 (H : FiniteVolumeHyperbolicModel.{u}) {P P' : OrientedThreeStage.{u}}
    (hP : P = P') (g' : P.Metric) (g'' : P'.Metric) (hg : HEq g' g'') (c : ℝ)
    (f : H.Carrier → P.Carrier) (k : ℕ) (p : H.Carrier) :
    ckErr_S45 H g'' c (fun q => cast (congrArg OrientedThreeStage.Carrier hP) (f q)) k p =
      ckErr_S45 H g' c f k p := by
  subst hP
  have h := eq_of_heq hg
  subst h
  rfl

theorem isSmoothEmbedding_cast_stage_S103 {P P' : OrientedThreeStage.{u}} (hP : P = P') {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] (f : X → P.Carrier)
    (hf : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ f) :
    IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x => cast (congrArg OrientedThreeStage.Carrier hP) (f x)) := by
  subst hP
  exact hf

/-- **G4** : the defect half of `h0` in the `postStage` / `postMetric` shape of the frozen hWA. -/
theorem h0_defect_of_post_S103 {P : OrientedThreeStage.{u}} {g : P.Metric} (O : ObservationTower P g)
    (H : FiniteVolumeHyperbolicModel.{u}) (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1))
    {t : ℝ} (ht : 0 < t) (hact : actS_S70 K t = j0) (hP : postStage O t = K.stage j0)
    (hm : HEq (postMetric O t) (K.stageMetric j0 t)) (f : H.Carrier → (postStage O t).Carrier)
    (U : Opens H.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x))
    (B : Set H.Carrier) (hBU : B ⊆ U) {δ η : ℝ} (hδ : δ ≤ 1 / 2) (hδη : 2882 * δ ≤ η)
    (hck : ∀ j : ℕ, j ≤ 2 → ∀ p ∈ B, ckErr_S45 H (postMetric O t) t⁻¹ f j p < δ) :
    DefectAllAt_S85 K j0 (fun x => cast (congrArg OrientedThreeStage.Carrier hP) (f x)) B η t := by
  refine h0_defect_S103 H K j0 ht hact _ U (contMDiffOn_cast_S65 hP f U hF)
    (isSmoothEmbedding_cast_stage_S103 hP (fun x : U => f x) hemb) B hBU hδ hδη ?_
  intro j hj p hp
  rw [ckErr_S45_cast_stage_S103 H hP _ _ hm t⁻¹ f j p]
  exact hck j hj p hp

end GC.LongTime.Ch12
