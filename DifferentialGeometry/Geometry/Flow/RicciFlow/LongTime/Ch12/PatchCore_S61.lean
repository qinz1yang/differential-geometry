import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchPieces_S55
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.IsotopyBall_S49
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WindowSurvivor_S49

set_option autoImplicit false

/-! # CH12-S61 G1a: the local core of `persistentModelPatch_of_windows_S61`

Given a window index `j`, a time interval `(a, b)` meeting only the windows `j`, `j + 1`, a box
`U ⊆ B(m)` and two survivor lifts `φ₁` (window `j`) and `φ₂` (window `j+1`, only needed when it meets
`(a, b)`) *in one history and one stage range*, the CX5 constructor
`persistentModelPatch_of_dyadic_lifts_CX5` applies with `φ k := if k = j + 1 then φ₂ else φ₁`.
`hjoin` is derived from `hend` by `survivor_join_S49`, `himage` by `isotopy_mem_ball_S49`,
`hmetric` by the pointwise form of `hmetric_window_S55`. -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

theorem isOpen_riemannianBallOf_S61 (H : FiniteVolumeHyperbolicModel.{u}) (r : ℝ) :
    IsOpen (riemannianBallOf H.metric H.basepoint r) :=
  isOpen_lt (by
    unfold riemannianEDistOf
    exact Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const

/-- `hmetric_window_S55` at one time `t` (no window interval needed). -/
theorem hmetric_pt_S61 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (n : ℕ)
    (first last : Fin ((F.tower.history n).eventCount + 1)) (ordered : first ≤ last)
    (t : Icc (0 : ℝ) (F.tower.history n).horizon) (ht0 : 0 < (t : ℝ))
    (st : first ≤ (F.tower.history n).toHistory.activeStage t ∧
        (F.tower.history n).toHistory.activeStage t ≤ last)
    (A : Set H.Carrier) (hA : IsOpen A)
    (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered)
    (w : H.Carrier → (postStage F.observation t).Carrier)
    (hraw : ∀ p ∈ A, HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage t) st.1 st.2 (φ p)) (w p))
    (hck : ∀ p ∈ A, ckErr_S45 H (postMetric F.observation t) (t : ℝ)⁻¹ w 0 p < 1) :
    ∀ p ∈ A, ∀ v : TangentSpace (𝓡 3) p,
        let history := (F.tower.history n).toHistory;
        let ψ := history.backwardSurvivorMap first last ordered (history.activeStage t)
          st.1 st.2 ∘ φ;
        (history.stageMetric (history.activeStage t) t).inner (ψ p)
          (mfderiv (𝓡 3) (𝓡 3) ψ p v) (mfderiv (𝓡 3) (𝓡 3) ψ p v) ≤
            4 * (t : ℝ) * H.metric.inner p v v := by
  intro p hp v
  have hτn : (t : ℝ) ≤ ((n : ℕ) : ℝ) := by
    have := F.tower.horizon_eq n
    exact this ▸ t.2.2
  have hpd := postData_eq_history_O3 F.observation n t t.2.1 hτn
    ((F.tower.history n).toHistory.activeStage t) rfl
  have hf : ∀ q ∈ A, ∀ u : TangentSpace (𝓡 3) q,
      (t : ℝ)⁻¹ * (postMetric F.observation t).inner (w q) (mfderiv (𝓡 3) (𝓡 3) w q u)
        (mfderiv (𝓡 3) (𝓡 3) w q u) ≤ 2 * H.metric.inner q u u := by
    intro q hq u
    have := pullback_inner_le_of_ckErr_S49 H (postMetric F.observation t) (t : ℝ)⁻¹ w q
      (hck q hq) u
    simpa [one_add_one_eq_two] using this
  exact physical_metric_of_heq_S49 H hpd.1.symm _ _ hpd.2.symm _ w A hA hraw ht0 hf p hp v

end GC.LongTime.Ch12
