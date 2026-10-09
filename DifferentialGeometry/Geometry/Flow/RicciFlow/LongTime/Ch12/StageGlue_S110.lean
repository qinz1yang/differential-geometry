import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WBNLevel_S98
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrLocalPull_S98
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SurvivorFlowIdent_S107
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LiftBridge_S65

set_option autoImplicit false

/-!
# CH12-S110 / G1: stage-level glue for `hWB'`

* `gStage_S110` : the N-level metric family `r ↦ ψ_r^* (stageMetric (activeStage r) r)` on the survivor domain
  `N = backwardSurvivorDomain first last` (for `r ∈ Ico a b ∩ [0, horizon]`; fallback metric `g0` elsewhere).
* inner / Ricci identification (`gStage_inner_ricci_S110`), defect clause transfer (`defect_gStage_S110`).
* `ckErr` congruence for maps equal on an open set (`ckErr_congr_open_S110`), `ckErr` of `gStage` along `φ`
  = `ckErr` of the stage metric along `ψ_r ∘ φ` (`ckErr_gStage_S110`), and at the time `t` the `postStage` bridge
  (`ckErr_gStage_eq_post_S110`).
* `injective_mfderiv_of_heq_S110`: `d f` injective and `f = cast ∘ ψ ∘ φ` on an open set ⟹ `d φ` injective.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter TopologicalSpace
open Manifold GC.LongTime GC.LongTime.Ch12 GC.LongTime.CuspP1
open scoped Manifold ContDiff ENNReal Topology
universe u

namespace GC.LongTime.Ch12

section Generic

/-- `ckErr_S45` only depends on the germ of the map on an open set. -/
theorem ckErr_congr_open_S110 (H : FiniteVolumeHyperbolicModel.{u}) {M' : Type u}
    [TopologicalSpace M'] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M'] [IsManifold (𝓡 3) ∞ M']
    (m : SmoothRiemannianMetric (𝓡 3) M') (f f' : H.Carrier → M') (W : Opens H.Carrier)
    (hff : ∀ q ∈ W, f q = f' q) (c : ℝ) (j : ℕ) (p : H.Carrier) (hp : p ∈ W) :
    ckErr_S45 H m c f j p = ckErr_S45 H m c f' j p := by
  change ckErr_O19 H m c f j p = ckErr_O19 H m c f' j p
  unfold ckErr_O19
  congr 1
  refine iteratedMetricCovariantDerivative_congr_open_O19 H.metric _ _ W.isOpen ?_ j p hp
  intro q hq
  have hev : f =ᶠ[𝓝 q] f' :=
    Filter.eventually_of_mem (W.isOpen.mem_nhds hq) (fun z hz => hff z hz)
  have hd : mfderiv (𝓡 3) (𝓡 3) f q = mfderiv (𝓡 3) (𝓡 3) f' q := hev.mfderiv_eq
  have hq' := hff q hq
  have key : localPullInner (I := 𝓡 3) m f q = localPullInner (I := 𝓡 3) m f' q := by
    ext v w
    rw [localPullInner_apply, localPullInner_apply, hd, hq']
  rw [key]

/-- `d f` injective and `f = cast ∘ ψ ∘ φ` (as `HEq`) on an open set `W` ⟹ `d φ` injective on `W`. -/
theorem injective_mfderiv_of_heq_S110 (H : FiniteVolumeHyperbolicModel.{u}) {A B : OrientedThreeStage.{u}}
    (e : A = B) (W : Opens H.Carrier) {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (φ : H.Carrier → N) (ψ : N → B.Carrier) (hψ : ContMDiff (𝓡 3) (𝓡 3) ∞ ψ)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ W) (f : H.Carrier → A.Carrier)
    (hheq : ∀ p ∈ W, HEq (ψ (φ p)) (f p))
    (hinj : ∀ y ∈ W, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) :
    ∀ y ∈ W, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y) := by
  subst e
  intro y hy v w hvw
  have hinf : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hev : (fun z => ψ (φ z)) =ᶠ[𝓝 y] f :=
    Filter.eventually_of_mem (W.isOpen.mem_nhds hy) (fun z hz => eq_of_heq (hheq z hz))
  have hd : mfderiv (𝓡 3) (𝓡 3) (fun z => ψ (φ z)) y = mfderiv (𝓡 3) (𝓡 3) f y := hev.mfderiv_eq
  have hφy : MDifferentiableAt (𝓡 3) (𝓡 3) φ y :=
    (hφ.contMDiffAt (W.isOpen.mem_nhds hy)).mdifferentiableAt hinf
  have hcomp : ∀ a : TangentSpace (𝓡 3) y,
      mfderiv (𝓡 3) (𝓡 3) f y a = mfderiv (𝓡 3) (𝓡 3) ψ (φ y) (mfderiv (𝓡 3) (𝓡 3) φ y a) := by
    intro a
    rw [← hd]
    exact mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) y
      ((hψ (φ y)).mdifferentiableAt hinf) hφy (v := a)
  apply hinj y hy
  rw [hcomp v, hcomp w, hvw]

variable (K : ObservedHistory.{u}) (first last : Fin (K.eventCount + 1)) (ordered : first ≤ last)
  (a b : ℝ)
  (stages : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ico a b →
    first ≤ K.activeStage r ∧ K.activeStage r ≤ last)

/-- The stage metric family pulled back to the survivor domain along the survivor map of the active stage. -/
def gStage_S110
    (g0 : SmoothRiemannianMetric (𝓡 3) (K.backwardSurvivorDomain first last ordered)) (s : ℝ) :
    SmoothRiemannianMetric (𝓡 3) (K.backwardSurvivorDomain first last ordered) :=
  if h : s ∈ Ico a b ∧ s ∈ Icc (0 : ℝ) K.horizon then
    localPullMetric (K.stageMetric (K.activeStage ⟨s, h.2⟩) s)
      (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, h.2⟩)
        (stages ⟨s, h.2⟩ h.1).1 (stages ⟨s, h.2⟩ h.1).2)
      (K.backwardSurvivorMap_isLocalDiffeomorph first last ordered _ _ _)
  else g0

theorem gStage_apply_S110
    (g0 : SmoothRiemannianMetric (𝓡 3) (K.backwardSurvivorDomain first last ordered))
    {s : ℝ} (hs : s ∈ Ico a b) (hs0 : s ∈ Icc (0 : ℝ) K.horizon) :
    gStage_S110 K first last ordered a b stages g0 s =
      localPullMetric (K.stageMetric (K.activeStage ⟨s, hs0⟩) s)
        (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
          (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2)
        (K.backwardSurvivorMap_isLocalDiffeomorph first last ordered _ _ _) := by
  unfold gStage_S110
  split_ifs with h
  · rfl
  · exact absurd ⟨hs, hs0⟩ h

theorem gStage_inner_ricci_S110
    (g0 : SmoothRiemannianMetric (𝓡 3) (K.backwardSurvivorDomain first last ordered))
    {s : ℝ} (hs : s ∈ Ico a b) (hs0 : s ∈ Icc (0 : ℝ) K.horizon)
    (y : K.backwardSurvivorDomain first last ordered) (V : TangentSpace (𝓡 3) y) :
    (gStage_S110 K first last ordered a b stages g0 s).inner y V V =
        (K.stageMetric (K.activeStage ⟨s, hs0⟩) s).inner
          (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
            (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2 y)
          (mfderiv (𝓡 3) (𝓡 3) (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
            (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2) y V)
          (mfderiv (𝓡 3) (𝓡 3) (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
            (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2) y V) ∧
      ricciTensor (gStage_S110 K first last ordered a b stages g0 s) y V V =
        ricciTensor (K.stageMetric (K.activeStage ⟨s, hs0⟩) s)
          (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
            (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2 y)
          (mfderiv (𝓡 3) (𝓡 3) (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
            (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2) y V)
          (mfderiv (𝓡 3) (𝓡 3) (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
            (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2) y V) := by
  rw [gStage_apply_S110 K first last ordered a b stages g0 hs hs0,
    localPullMetric_inner, ricciTensor_localPullMetric]
  exact ⟨rfl, rfl⟩

/-- the stage Einstein-defect clause at the survivor point gives the N-level one. -/
theorem defect_gStage_S110
    (g0 : SmoothRiemannianMetric (𝓡 3) (K.backwardSurvivorDomain first last ordered))
    {s : ℝ} (hs : s ∈ Ico a b) (hs0 : s ∈ Icc (0 : ℝ) K.horizon) (η : ℝ)
    (y : K.backwardSurvivorDomain first last ordered)
    (hdef : ∀ V' : TangentSpace (𝓡 3)
        (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
          (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2 y),
      |2 * s * ricciTensor (K.stageMetric (K.activeStage ⟨s, hs0⟩) s)
          (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
            (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2 y) V' V' +
        (K.stageMetric (K.activeStage ⟨s, hs0⟩) s).inner
          (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
            (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2 y) V' V'| ≤
        η * (K.stageMetric (K.activeStage ⟨s, hs0⟩) s).inner
          (K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
            (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2 y) V' V')
    (V : TangentSpace (𝓡 3) y) :
    |2 * s * ricciTensor (gStage_S110 K first last ordered a b stages g0 s) y V V +
        (gStage_S110 K first last ordered a b stages g0 s).inner y V V| ≤
      η * (gStage_S110 K first last ordered a b stages g0 s).inner y V V := by
  obtain ⟨h1, h2⟩ := gStage_inner_ricci_S110 K first last ordered a b stages g0 hs hs0 y V
  rw [h1, h2]
  exact hdef _

theorem backwardSurvivorMap_contMDiff_S110 (j : Fin (K.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (K.backwardSurvivorMap first last ordered j hj hl) :=
  (K.backwardSurvivorMap_isSmoothEmbedding first last ordered j hj hl).contMDiff

/-- `ckErr` of `gStage r` along `φ` is `ckErr` of the stage metric along `ψ_r ∘ φ` (on an open `W` where `φ` is
smooth). -/
theorem ckErr_gStage_S110 (H : FiniteVolumeHyperbolicModel.{u})
    (g0 : SmoothRiemannianMetric (𝓡 3) (K.backwardSurvivorDomain first last ordered))
    {s : ℝ} (hs : s ∈ Ico a b) (hs0 : s ∈ Icc (0 : ℝ) K.horizon)
    (φ : H.Carrier → K.backwardSurvivorDomain first last ordered) (W : Opens H.Carrier)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ W) (c : ℝ) (j : ℕ) (p : H.Carrier) (hp : p ∈ W) :
    ckErr_S45 H (gStage_S110 K first last ordered a b stages g0 s) c φ j p =
      ckErr_S45 H (K.stageMetric (K.activeStage ⟨s, hs0⟩) s) c
        (fun q => K.backwardSurvivorMap first last ordered (K.activeStage ⟨s, hs0⟩)
          (stages ⟨s, hs0⟩ hs).1 (stages ⟨s, hs0⟩ hs).2 (φ q)) j p := by
  rw [gStage_apply_S110 K first last ordered a b stages g0 hs hs0]
  exact ckErr_localPull_S98 H _ _ _
    (backwardSurvivorMap_contMDiff_S110 K first last ordered _ _ _) φ W hφ c j p hp

end Generic

section Post

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- at the time `t` (with the `HEq` clause on `W`): `ckErr` of `gStage t` along `φ` is `ckErr` of `postMetric t`
along `f`. -/
theorem ckErr_gStage_eq_post_S110 (H : FiniteVolumeHyperbolicModel.{u}) (n : ℕ)
    (first last : Fin ((F.tower.history n).eventCount + 1)) (ordered : first ≤ last) (a b t : ℝ)
    (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
      first ≤ (F.tower.history n).toHistory.activeStage r ∧
        (F.tower.history n).toHistory.activeStage r ≤ last)
    (g0 : SmoothRiemannianMetric (𝓡 3)
      ((F.tower.history n).toHistory.backwardSurvivorDomain first last ordered))
    (ht0 : 0 ≤ t) (hth : t ≤ (F.tower.history n).horizon) (hat : a ≤ t) (htb : t < b)
    (f : H.Carrier → (postStage F.observation t).Carrier)
    (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered)
    (W : Opens H.Carrier) (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ W)
    (hheq : ∀ p ∈ W, HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage ⟨t, ht0, hth⟩)
        (stages ⟨t, ht0, hth⟩ ⟨hat, htb⟩).1 (stages ⟨t, ht0, hth⟩ ⟨hat, htb⟩).2 (φ p)) (f p))
    (j : ℕ) (p : H.Carrier) (hp : p ∈ W) :
    ckErr_S45 H (gStage_S110 (F.tower.history n).toHistory first last ordered a b stages g0 t)
        t⁻¹ φ j p = ckErr_S45 H (postMetric F.observation t) t⁻¹ f j p := by
  have hs : t ∈ Ico a b := ⟨hat, htb⟩
  have hs0 : t ∈ Icc (0 : ℝ) (F.tower.history n).toHistory.horizon := ⟨ht0, hth⟩
  rw [ckErr_gStage_S110 _ first last ordered a b stages H g0 hs hs0 φ W hφ _ j p hp]
  have h1 := ckErr_liftMap_S65 (F := F) H n first last ordered ⟨t, ht0, hth⟩
    (stages ⟨t, ht0, hth⟩ hs).1 (stages ⟨t, ht0, hth⟩ hs).2 φ t⁻¹ j p
  rw [← h1]
  refine (ckErr_congr_open_S110 H _ _ _ W ?_ _ j p hp).symm
  intro q hq
  exact eq_of_heq ((hheq q hq).symm.trans
    (liftMap_heq_S65 (F := F) n first last ordered ⟨t, ht0, hth⟩
      (stages ⟨t, ht0, hth⟩ hs).1 (stages ⟨t, ht0, hth⟩ hs).2 (φ q)))

/-- `d f` injective on `W` ⟹ `d φ` injective on `W` (through the `postStage`-cast of the active stage). -/
theorem injective_mfderiv_phi_S110 (H : FiniteVolumeHyperbolicModel.{u}) (n : ℕ)
    (first last : Fin ((F.tower.history n).eventCount + 1)) (ordered : first ≤ last) (a b t : ℝ)
    (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
      first ≤ (F.tower.history n).toHistory.activeStage r ∧
        (F.tower.history n).toHistory.activeStage r ≤ last)
    (ht0 : 0 ≤ t) (hth : t ≤ (F.tower.history n).horizon) (hat : a ≤ t) (htb : t < b)
    (f : H.Carrier → (postStage F.observation t).Carrier)
    (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered)
    (W : Opens H.Carrier) (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ W)
    (hheq : ∀ p ∈ W, HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage ⟨t, ht0, hth⟩)
        (stages ⟨t, ht0, hth⟩ ⟨hat, htb⟩).1 (stages ⟨t, ht0, hth⟩ ⟨hat, htb⟩).2 (φ p)) (f p))
    (hinj : ∀ y ∈ W, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) :
    ∀ y ∈ W, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y) :=
  injective_mfderiv_of_heq_S110 H (postStage_eq_stage_active_CPD2 F.observation n ⟨t, ht0, hth⟩) W φ
    _ (backwardSurvivorMap_contMDiff_S110 (F.tower.history n).toHistory first last ordered _
      (stages ⟨t, ht0, hth⟩ ⟨hat, htb⟩).1 (stages ⟨t, ht0, hth⟩ ⟨hat, htb⟩).2) hφ f hheq hinj

end Post

end GC.LongTime.Ch12

end
