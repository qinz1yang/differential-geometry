import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LiftBridge_S65
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StageGlue_S110
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoverCkErr_S90
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LocalCurve_S136

set_option autoImplicit false

/-! # CH12-S145 G2a: speed bound for the IFT curve of a `PersistentModelPatch`

`inner_mfderiv_transport_S145`: for `A = B` and `HEq` metrics / maps, the metric norm of `mfderiv` agrees (the one
`HEq` bridge).  `patch_speed_S145`: if `p.map (σ, c σ) = y` near `τ` (`c` the implicit curve), then
`d_x track (c') = - d_σ track` (differentiate the constant), so `(1-α) h(c',c') < α²/τ²` using the lower bound `hlow`
for `mold τ` and `p.speed`.  `patch_inj_S145`: `d_x map(τ,·)` is injective at `x` (needed for `local_curve_S136`). -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime GC.LongTime.Ch12 GC.LongTime.CuspP1
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem inner_mfderiv_transport_S145 {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    {A B : OrientedThreeStage.{u}} (h : A = B) (mA : A.Metric) (mB : B.Metric) (hm : HEq mA mB)
    (fA : X → A.Carrier) (fB : X → B.Carrier) (N : Set X) (hN : IsOpen N)
    (hf : ∀ x ∈ N, HEq (fA x) (fB x)) {x : X} (hx : x ∈ N) (u : TangentSpace (𝓡 3) x) :
    mA.inner (fA x) (mfderiv (𝓡 3) (𝓡 3) fA x u) (mfderiv (𝓡 3) (𝓡 3) fA x u) =
      mB.inner (fB x) (mfderiv (𝓡 3) (𝓡 3) fB x u) (mfderiv (𝓡 3) (𝓡 3) fB x u) := by
  subst h
  have hm' := eq_of_heq hm
  subst hm'
  have hev : fA =ᶠ[nhds x] fB :=
    Filter.eventually_of_mem (hN.mem_nhds hx) (fun y hy => eq_of_heq (hf y hy))
  have hfx : fA x = fB x := eq_of_heq (hf x hx)
  rw [hev.mfderiv_eq]
  exact congrArg (fun q => mA.inner q (mfderiv (𝓡 3) (𝓡 3) fB x u) (mfderiv (𝓡 3) (𝓡 3) fB x u)) hfx

section Patch

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hold : FiniteVolumeHyperbolicModel.{u}} {start : ℝ} {α : ℝ → ℝ}
  {Ω : TopologicalSpace.Opens (ℝ × Hold.Carrier)}
  {mold : ∀ t : ℝ, start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier}
  {t₀ : ℝ} {x₀ : Hold.Carrier}

/-- The survivor-map lift of `p.map` into the stage active at `τ` (the `track` of `PersistentModelPatch.speed`). -/
def trackS145 (p : PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t₀ x₀)
    (τ : Icc (0 : ℝ) (F.tower.history p.n).horizon) (hτ : (τ : ℝ) ∈ Ioo p.a p.b) :
    ℝ × Hold.Carrier → ((F.tower.history p.n).toHistory.stage
      ((F.tower.history p.n).toHistory.activeStage τ)).Carrier :=
  (F.tower.history p.n).toHistory.backwardSurvivorMap p.first p.last p.ordered
    ((F.tower.history p.n).toHistory.activeStage τ) (p.stages τ hτ).1 (p.stages τ hτ).2 ∘ p.map

theorem trackS145_contMDiffAt (p : PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t₀ x₀)
    (τ : Icc (0 : ℝ) (F.tower.history p.n).horizon) (hτ : (τ : ℝ) ∈ Ioo p.a p.b)
    {σ : ℝ} {x : Hold.Carrier} (hσ : σ ∈ Ioo p.a p.b) (hx : x ∈ p.neighborhood) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (trackS145 p τ hτ) (σ, x) :=
  (backwardSurvivorMap_contMDiff_S110 (F.tower.history p.n).toHistory p.first p.last p.ordered _ _ _
    ).contMDiffAt.comp (σ, x)
    (p.smooth.contMDiffAt ((isOpen_Ioo.prod p.neighborhood.isOpen).mem_nhds ⟨hσ, hx⟩))

theorem slice_inner_S145 (p : PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t₀ x₀)
    (τ : Icc (0 : ℝ) (F.tower.history p.n).horizon) (hτ : (τ : ℝ) ∈ Ioo p.a p.b)
    (hT : start ≤ (τ : ℝ)) {x : Hold.Carrier} (hx : x ∈ p.neighborhood) (u : TangentSpace (𝓡 3) x) :
    ((F.tower.history p.n).toHistory.stageMetric ((F.tower.history p.n).toHistory.activeStage τ) τ).inner
      (trackS145 p τ hτ (τ, x))
      (mfderiv (𝓡 3) (𝓡 3) (fun x' => trackS145 p τ hτ ((τ : ℝ), x')) x u)
      (mfderiv (𝓡 3) (𝓡 3) (fun x' => trackS145 p τ hτ ((τ : ℝ), x')) x u) =
    (postMetric F.observation τ).inner (mold τ hT x)
      (mfderiv (𝓡 3) (𝓡 3) (mold τ hT) x u) (mfderiv (𝓡 3) (𝓡 3) (mold τ hT) x u) :=
  inner_mfderiv_transport_S145 (postStage_eq_stage_active_CPD2 F.observation p.n τ).symm _ _
    (postMetric_heq_stageMetric_S65 F.observation p.n τ).symm _ _ (p.neighborhood : Set Hold.Carrier)
    p.neighborhood.isOpen (fun x' hx' => p.agrees τ hτ hT x' hx') hx u

theorem patch_inj_S145 (p : PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t₀ x₀)
    (τ : Icc (0 : ℝ) (F.tower.history p.n).horizon) (hτ : (τ : ℝ) ∈ Ioo p.a p.b)
    (hT : start ≤ (τ : ℝ)) {x : Hold.Carrier} (hx : x ∈ p.neighborhood) (hα : α τ < 1)
    (hlow : ∀ w : TangentSpace (𝓡 3) x, (1 - α τ) * Hold.metric.inner x w w ≤
      (τ : ℝ)⁻¹ * (postMetric F.observation τ).inner (mold τ hT x)
        (mfderiv (𝓡 3) (𝓡 3) (mold τ hT) x w) (mfderiv (𝓡 3) (𝓡 3) (mold τ hT) x w)) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun x' => p.map ((τ : ℝ), x')) x) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have hτ0 : 0 < (τ : ℝ) := lt_of_le_of_lt p.a_nonneg hτ.1
  have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ p.map ((τ : ℝ), x) :=
    p.smooth.contMDiffAt ((isOpen_Ioo.prod p.neighborhood.isOpen).mem_nhds ⟨hτ, hx⟩)
  have hD : MDifferentiableAt (𝓡 3) (𝓡 3) (fun x' => p.map ((τ : ℝ), x')) x :=
    (hmap.mdifferentiableAt (by simp)).comp x
      (f := fun x' : Hold.Carrier => ((τ : ℝ), x')) (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hbs : MDifferentiableAt (𝓡 3) (𝓡 3) ((F.tower.history p.n).toHistory.backwardSurvivorMap p.first p.last
      p.ordered ((F.tower.history p.n).toHistory.activeStage τ) (p.stages τ hτ).1 (p.stages τ hτ).2)
      (p.map ((τ : ℝ), x)) :=
    (backwardSurvivorMap_contMDiff_S110 (F.tower.history p.n).toHistory p.first p.last p.ordered _ _ _
      ).contMDiffAt.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp x hbs hD
  have h0 : mfderiv (𝓡 3) (𝓡 3) (fun x' => trackS145 p τ hτ ((τ : ℝ), x')) x u = 0 := by
    change mfderiv (𝓡 3) (𝓡 3) ((F.tower.history p.n).toHistory.backwardSurvivorMap p.first p.last
      p.ordered ((F.tower.history p.n).toHistory.activeStage τ) (p.stages τ hτ).1 (p.stages τ hτ).2 ∘
        fun x' => p.map ((τ : ℝ), x')) x u = 0
    rw [hcomp]
    change mfderiv (𝓡 3) (𝓡 3) _ (p.map ((τ : ℝ), x)) (mfderiv (𝓡 3) (𝓡 3) (fun x' => p.map ((τ : ℝ), x')) x u) = 0
    rw [hu]
    exact map_zero _
  have htr := slice_inner_S145 p τ hτ hT hx u
  rw [h0] at htr
  simp only [map_zero, ContinuousLinearMap.zero_apply] at htr
  have hl := hlow u
  by_contra hne
  have hpos := Hold.metric.pos x u hne
  have h1 : 0 < 1 - α τ := by linarith
  have := mul_pos h1 hpos
  rw [← htr] at hl
  simp at hl
  linarith

theorem patch_speed_S145 (p : PersistentModelPatch F Hold start α (sourceSlice_CX5 Ω) mold t₀ x₀)
    (τ : Icc (0 : ℝ) (F.tower.history p.n).horizon) (hτ : (τ : ℝ) ∈ Ioo p.a p.b)
    (hT : start ≤ (τ : ℝ)) (c : ℝ → Hold.Carrier) (hcN : c τ ∈ p.neighborhood)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) c τ)
    (y : (F.tower.history p.n).toHistory.backwardSurvivorDomain p.first p.last p.ordered)
    (hy : ∀ᶠ σ in nhds (τ : ℝ), p.map (σ, c σ) = y)
    (hlow : ∀ w : TangentSpace (𝓡 3) (c τ), (1 - α τ) * Hold.metric.inner (c τ) w w ≤
      (τ : ℝ)⁻¹ * (postMetric F.observation τ).inner (mold τ hT (c τ))
        (mfderiv (𝓡 3) (𝓡 3) (mold τ hT) (c τ) w) (mfderiv (𝓡 3) (𝓡 3) (mold τ hT) (c τ) w)) :
    (1 - α τ) * Hold.metric.inner (c τ) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c τ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c τ 1) <
      α τ ^ 2 / (τ : ℝ) ^ 2 := by
  have hτ0 : 0 < (τ : ℝ) := lt_of_le_of_lt p.a_nonneg hτ.1
  have hD : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) (trackS145 p τ hτ) ((τ : ℝ), c τ) :=
    (trackS145_contMDiffAt p τ hτ hτ hcN).mdifferentiableAt (by simp)
  have hpair : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun σ : ℝ => (σ, c σ)) (τ : ℝ) :=
    mdifferentiableAt_id.prodMk hc
  have hG : (fun σ : ℝ => trackS145 p τ hτ (σ, c σ)) =ᶠ[nhds (τ : ℝ)]
      fun _ => (F.tower.history p.n).toHistory.backwardSurvivorMap p.first p.last p.ordered
        ((F.tower.history p.n).toHistory.activeStage τ) (p.stages τ hτ).1 (p.stages τ hτ).2 y := by
    filter_upwards [hy] with σ hσ
    simp only [trackS145, Function.comp, hσ]
  have h0 : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun σ : ℝ => trackS145 p τ hτ (σ, c σ)) (τ : ℝ) = 0 := by
    rw [hG.mfderiv_eq, mfderiv_const]
    exact ContinuousLinearMap.comp_zero _
  have hcomp : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun σ : ℝ => trackS145 p τ hτ (σ, c σ)) (τ : ℝ) =
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) (trackS145 p τ hτ) ((τ : ℝ), c τ)).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun σ : ℝ => (σ, c σ)) (τ : ℝ)) :=
    mfderiv_comp (τ : ℝ) hD hpair
  set e : EuclideanSpace ℝ (Fin 3) := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c (τ : ℝ) 1 with he
  set dT := mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) (trackS145 p τ hτ) ((τ : ℝ), c τ) with hdT
  have hpd : mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun σ : ℝ => (σ, c σ)) (τ : ℝ) 1 = ((1 : ℝ), e) := by
    change mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun σ : ℝ => (id σ, c σ)) (τ : ℝ) 1 = _
    rw [mfderiv_prodMk mdifferentiableAt_id hc, mfderiv_id]
    rfl
  have hv0 : dT ((1 : ℝ), e) = 0 := by
    have h1 : (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun σ : ℝ => trackS145 p τ hτ (σ, c σ)) (τ : ℝ)) 1 = 0 := by
      rw [h0]; rfl
    rw [hcomp] at h1
    change dT (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun σ : ℝ => (σ, c σ)) (τ : ℝ) 1) = 0 at h1
    rw [hpd] at h1
    exact h1
  have hι : mfderiv (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun x' : Hold.Carrier => ((τ : ℝ), x')) (c τ) =
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)) := by
    change mfderiv (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun x : Hold.Carrier => ((τ : ℝ), id x)) (c τ) = _
    rw [mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_id, mfderiv_const, mfderiv_id]
    ext w
    · rfl
    · rfl
  have hsl : mfderiv (𝓡 3) (𝓡 3) (fun x' => trackS145 p τ hτ ((τ : ℝ), x')) (c τ) e =
      dT ((0 : ℝ), e) := by
    have hc2 := mfderiv_comp (I := 𝓡 3) (I' := 𝓘(ℝ, ℝ).prod (𝓡 3)) (I'' := 𝓡 3) (c τ) hD
      (f := fun x' : Hold.Carrier => ((τ : ℝ), x'))
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    change mfderiv (𝓡 3) (𝓡 3) (trackS145 p τ hτ ∘ fun x' : Hold.Carrier => ((τ : ℝ), x')) (c τ) e = _
    rw [hc2, hι]
    rfl
  have hv : ((1 : ℝ), e) = (((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) + ((0 : ℝ), e) : ℝ × EuclideanSpace ℝ (Fin 3)) := by
    ext <;> simp
  have hsplit : dT ((1 : ℝ), e) = dT ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) + dT ((0 : ℝ), e) :=
    (congrArg (fun v => dT v) hv).trans (map_add _ _ _)
  have hneg : mfderiv (𝓡 3) (𝓡 3) (fun x' => trackS145 p τ hτ ((τ : ℝ), x')) (c τ) e =
      - dT ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) := by
    rw [hsl]
    exact eq_neg_of_add_eq_zero_right (by rw [← hsplit]; exact hv0)
  have hsp : ((F.tower.history p.n).toHistory.stageMetric ((F.tower.history p.n).toHistory.activeStage τ) τ).inner
      (trackS145 p τ hτ ((τ : ℝ), c τ))
      (dT ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))))
      (dT ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))) < α τ ^ 2 / (τ : ℝ) :=
    p.speed τ hτ hT (c τ) hcN
  have htr := slice_inner_S145 p τ hτ hT hcN e
  rw [hneg] at htr
  simp only [map_neg, neg_apply, neg_neg] at htr
  have hl := hlow e
  rw [← htr] at hl
  calc _ ≤ _ := hl
    _ < (τ : ℝ)⁻¹ * (α τ ^ 2 / (τ : ℝ)) := mul_lt_mul_of_pos_left hsp (inv_pos.mpr hτ0)
    _ = α τ ^ 2 / (τ : ℝ) ^ 2 := by field_simp

end Patch

end GC.LongTime.Ch12
