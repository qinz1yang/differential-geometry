import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollarFieldR7E
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.ConjugatingFlow.Properties
import DifferentialGeometry.Topology.Ehresmann.RelatedFlows
import DifferentialGeometry.Topology.Manifold.IntegralCurve.ScalarRate

/-!
# O-MY-R7E G3-b：紧支撑 flow 的微积分（level 等式、时间导数、Lie 导数 slot、tangential contraction）

`X` 为紧支撑光滑截面，`D t := compactSupportFlowDiffeomorph X`（整体 flow，联合光滑）。

* `hasMFDerivAt_collarFlow_time_R7E`：`∂ₛ D s x = X (D s x)`；
* `collarFlow_add_R7E`：`D (s + t) = D t ∘ D s`；
* `mfderiv_collarFlow_field_R7E`：`dD_t (X x) = X (D t x)`（flow 不变量）；
* `mfderiv_collarFlow_joint_R7E`：`R(y) = D (ρ y − c) y` 的微分 `dR ξ = dρ(ξ) X(R y) + dD_τ ξ`；
* `hasDerivAt_collarFlow_pairing_R7E`：`d/ds G(dD_s v, dD_s v) = L_X G(dD_s v, dD_s v)`
  （树里 `flow_slot_pos` 经时间平移，对**所有** `s` 成立）；
* level 等式 `rho_collarFlow_R7E`：`dρ(X) = −β(ρ)`、`0 ≤ β ≤ 1`、`[a, b]` 上 `β = 1` ⇒
  `ρ x ∈ [a, b]`、`s ∈ [0, ρ x − a]` 时 `ρ (D s x) = ρ x − s`（标量 ODE `h' = −β(h)`）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.ODE DifferentialGeometry.Topology.Ehresmann
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

/-- 紧支撑截面的整体 flow。 -/
def collarFlow_R7E (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
    (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x))) (t : ℝ) :
    N ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ N :=
  compactSupportFlowDiffeomorph (X : (x : N) → TangentSpace 𝓘(ℝ, E) x) X.contMDiff hXc t

section Flow

variable (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
  (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)))

theorem collarFlow_apply_R7E (t : ℝ) (x : N) :
    collarFlow_R7E X hXc t x =
      curveAt (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)
        (exists_globalIntegralCurve_of_compactSupport _ X.contMDiff hXc) x t := rfl

theorem collarFlow_zero_R7E (x : N) : collarFlow_R7E X hXc 0 x = x := by
  rw [collarFlow_apply_R7E]
  exact curveAt_zero _ _ x

theorem collarFlow_add_R7E (s t : ℝ) (x : N) :
    collarFlow_R7E X hXc (s + t) x = collarFlow_R7E X hXc t (collarFlow_R7E X hXc s x) := by
  have h := compactSupportFlowDiffeomorph_trans (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)
    X.contMDiff hXc s t
  exact (congrArg (fun F : N ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ N => F x) h).symm

theorem hasMFDerivAt_collarFlow_time_R7E (x : N) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => collarFlow_R7E X hXc s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (collarFlow_R7E X hXc t x))) :=
  curveAt_integralCurve (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)
    (exists_globalIntegralCurve_of_compactSupport _ X.contMDiff hXc) x t

theorem contMDiff_collarFlow_joint_R7E :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × N => collarFlow_R7E X hXc p.1 p.2) :=
  contMDiff_globalFlow_joint_of_compactSupport _ X.contMDiff hXc

theorem continuous_collarFlow_joint_R7E :
    Continuous (fun p : ℝ × N => collarFlow_R7E X hXc p.1 p.2) :=
  (contMDiff_collarFlow_joint_R7E X hXc).continuous

/-- flow 不变量：`dD_t (X x) = X (D t x)`。 -/
theorem mfderiv_collarFlow_field_R7E (t : ℝ) (x : N) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc t) x (X x) = X (collarFlow_R7E X hXc t x) := by
  have h0 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => collarFlow_R7E X hXc s x) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X x)) := by
    have h := hasMFDerivAt_collarFlow_time_R7E X hXc x 0
    rwa [collarFlow_zero_R7E] at h
  have hD : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc t) (collarFlow_R7E X hXc 0 x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc t) x) := by
    rw [collarFlow_zero_R7E]
    exact ((collarFlow_R7E X hXc t).contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (collarFlow_R7E X hXc t ∘ fun s => collarFlow_R7E X hXc s x) 0
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc t) x).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X x))) :=
    hD.comp 0 h0
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => collarFlow_R7E X hXc (s + t) x) 0
      (((1 : ℝ →L[ℝ] ℝ).smulRight (X (collarFlow_R7E X hXc t x))).comp
        (ContinuousLinearMap.id ℝ ℝ)) := by
    have h := hasMFDerivAt_collarFlow_time_R7E X hXc x (0 + t)
    have htr : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + t) 0
        (ContinuousLinearMap.id ℝ ℝ) :=
      ((hasFDerivAt_id (0 : ℝ)).add_const t).hasMFDerivAt
    have hc := h.comp 0 htr
    rw [zero_add] at hc
    exact hc
  have hfun : (collarFlow_R7E X hXc t ∘ fun s => collarFlow_R7E X hXc s x) =
      fun s => collarFlow_R7E X hXc (s + t) x := by
    funext s
    exact (collarFlow_add_R7E X hXc s t x).symm
  rw [hfun] at h1
  have huniq := h1.mfderiv.symm.trans hshift.mfderiv
  have happ := DFunLike.congr_fun huniq 1
  have e1 : ((1 : ℝ →L[ℝ] ℝ).smulRight (X x)) 1 = X x := by simp
  have e2 : ((1 : ℝ →L[ℝ] ℝ).smulRight (X (collarFlow_R7E X hXc t x))) 1 =
      X (collarFlow_R7E X hXc t x) := by simp
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc t) x
      (((1 : ℝ →L[ℝ] ℝ).smulRight (X x)) 1) =
    ((1 : ℝ →L[ℝ] ℝ).smulRight (X (collarFlow_R7E X hXc t x))) 1 at happ
  rwa [e1, e2] at happ

/-- 标量 `ρ` 沿 flow 的导数：`d/ds ρ (D s x) = dρ(X)(D s x)`。 -/
theorem hasDerivAt_rho_collarFlow_R7E {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    {β : ℝ → ℝ} (hdρ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y (X y) = -β (ρ y)) (x : N) (s : ℝ) :
    HasDerivAt (fun t => ρ (collarFlow_R7E X hXc t x)) (-β (ρ (collarFlow_R7E X hXc s x))) s := by
  have hcurve : IsMIntegralCurveOn (fun t => collarFlow_R7E X hXc t x)
      (X : (x : N) → TangentSpace 𝓘(ℝ, E) x) univ :=
    fun t _ => (hasMFDerivAt_collarFlow_time_R7E X hXc x t).hasMFDerivWithinAt
  have h := DifferentialGeometry.Manifold.hasDerivWithinAt_scalar_comp_integralCurve hcurve
    (mem_univ s) ((hρ (collarFlow_R7E X hXc s x)).mdifferentiableAt (by simp))
  rw [hdρ, hasDerivWithinAt_univ] at h
  exact h

section Level

variable {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ}
  (hdρ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y (X y) = -β (ρ y))
  (hβ0 : ∀ r, 0 ≤ β r) (hβ1 : ∀ r, β r ≤ 1)

include hρ hdρ hβ0 in
/-- `ρ` 沿 flow 不增。 -/
theorem rho_collarFlow_antitone_R7E (x : N) :
    Antitone (fun t => ρ (collarFlow_R7E X hXc t x)) :=
  antitone_of_hasDerivAt_nonpos (fun s => hasDerivAt_rho_collarFlow_R7E X hXc hρ hdρ x s)
    (fun s => by simpa using hβ0 (ρ (collarFlow_R7E X hXc s x)))

include hρ hdρ hβ1 in
/-- `ρ` 沿 flow 的下降速度 `≤ 1`：`t ↦ ρ (D t x) + t` 单调不减。 -/
theorem rho_collarFlow_add_monotone_R7E (x : N) :
    Monotone (fun t => ρ (collarFlow_R7E X hXc t x) + t) :=
  monotone_of_hasDerivAt_nonneg
    (fun s => (hasDerivAt_rho_collarFlow_R7E X hXc hρ hdρ x s).add (hasDerivAt_id s))
    (fun s => by
      change 0 ≤ -β (ρ (collarFlow_R7E X hXc s x)) + 1
      linarith [hβ1 (ρ (collarFlow_R7E X hXc s x))])

include hρ hdρ hβ0 hβ1 in
/-- level 等式：`[a, b]` 上 `β = 1`、`ρ x ∈ [a, b]`、`0 ≤ s ≤ ρ x − a` ⇒ `ρ (D s x) = ρ x − s`。 -/
theorem rho_collarFlow_R7E {a b : ℝ} (hβeq : ∀ r, a ≤ r → r ≤ b → β r = 1) {x : N}
    (hxb : ρ x ≤ b) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ ρ x - a) :
    ρ (collarFlow_R7E X hXc s x) = ρ x - s := by
  have hanti := rho_collarFlow_antitone_R7E X hXc hρ hdρ hβ0 x
  have hmono := rho_collarFlow_add_monotone_R7E X hXc hρ hdρ hβ1 x
  have h0 : ρ (collarFlow_R7E X hXc 0 x) = ρ x := by rw [collarFlow_zero_R7E]
  have hrange : ∀ t ∈ Icc (0 : ℝ) s, a ≤ ρ (collarFlow_R7E X hXc t x) ∧
      ρ (collarFlow_R7E X hXc t x) ≤ b := by
    intro t ht
    have h1 := hanti ht.1
    have h2 := hmono ht.1
    simp only at h1 h2
    rw [h0] at h1
    rw [h0, add_zero] at h2
    constructor <;> linarith [ht.2]
  have hcont : ContinuousOn (fun t => ρ (collarFlow_R7E X hXc t x) + t) (Icc 0 s) := fun t _ =>
    ((hasDerivAt_rho_collarFlow_R7E X hXc hρ hdρ x t).add
      (hasDerivAt_id t)).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero (f := fun t => ρ (collarFlow_R7E X hXc t x) + t)
    (a := 0) (b := s) hcont ?_ s ⟨hs0, le_rfl⟩
  · simp only [h0, add_zero] at hconst
    linarith
  · intro t ht
    have hd := (hasDerivAt_rho_collarFlow_R7E X hXc hρ hdρ x t).add (hasDerivAt_id t)
    rw [hβeq _ (hrange t (Ico_subset_Icc_self ht)).1 (hrange t (Ico_subset_Icc_self ht)).2] at hd
    have hz : (-1 : ℝ) + 1 = 0 := by norm_num
    rw [hz] at hd
    exact hd.hasDerivWithinAt

end Level

/-- `R(y) = D (ρ y − c) y` 的微分：`dR ξ = dρ(ξ) • X(R y) + dD_τ ξ`，`τ = ρ y − c`。 -/
theorem mfderiv_collarFlow_joint_R7E {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (c : ℝ) (y : N) (ξ : TangentSpace 𝓘(ℝ, E) y) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => collarFlow_R7E X hXc (ρ z - c) z) y ξ =
      mvfderiv 𝓘(ℝ, E) ρ y ξ • X (collarFlow_R7E X hXc (ρ y - c) y) +
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc (ρ y - c)) y ξ := by
  let F : ℝ × N → N := fun p => collarFlow_R7E X hXc (p.1 - c) p.2
  let P : N → ℝ × N := fun z => (ρ z, z)
  have hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) F (P y) := by
    have hshift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × N => (p.1 - c, p.2)) :=
      (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
    exact (((contMDiff_collarFlow_joint_R7E X hXc).comp hshift) (P y)).mdifferentiableAt
      (by simp)
  have hρd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y := (hρ y).mdifferentiableAt (by simp)
  have hP : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) P y :=
    hρd.prodMk mdifferentiableAt_id
  have hcomp := mfderiv_comp y hF hP
  have hfun : (fun z => collarFlow_R7E X hXc (ρ z - c) z) = F ∘ P := rfl
  have hPd : mfderiv 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) P y =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y).prod (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id y) :=
    mfderiv_prodMk hρd mdifferentiableAt_id
  rw [hfun, hcomp, ContinuousLinearMap.comp_apply, hPd, mfderiv_id,
    mfderiv_prod_eq_add_apply hF]
  have htime : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => F (t, (P y).2)) (P y).1 =
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (collarFlow_R7E X hXc (ρ y - c) y))).comp
        (ContinuousLinearMap.id ℝ ℝ) := by
    have h := hasMFDerivAt_collarFlow_time_R7E X hXc y (ρ y - c)
    have htr : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t - c) (ρ y)
        (ContinuousLinearMap.id ℝ ℝ) :=
      ((hasFDerivAt_id (ρ y)).sub_const c).hasMFDerivAt
    exact (h.comp (ρ y) htr).mfderiv
  rw [htime]
  rfl

theorem collarFlow_zero_eq_refl_R7E :
    collarFlow_R7E X hXc 0 = Diffeomorph.refl 𝓘(ℝ, E) N ∞ :=
  compactSupportFlowDiffeomorph_zero _ X.contMDiff hXc

/-- `d/ds G(dD_s v, dD_s v) = L_X G(dD_s v, dD_s v)`：树里 `flow_slot_pos`（`Ici 0` 上的单侧导数）
经时间平移 `s ↦ s − L`，对**所有** `s₀` 给出双侧导数。 -/
theorem hasDerivAt_collarFlow_pairing_R7E (G : SmoothRiemannianMetric 𝓘(ℝ, E) N) (x : N)
    (v : TangentSpace 𝓘(ℝ, E) x) (s₀ : ℝ) :
    HasDerivAt (fun s => G.inner (collarFlow_R7E X hXc s x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc s) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc s) x v))
      (PDE.DeTurck.lieDerivMetric G X (collarFlow_R7E X hXc s₀ x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc s₀) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc s₀) x v)) s₀ := by
  set L : ℝ := |s₀| + 1 with hL
  have hLpos : 0 < s₀ + L := by
    have := neg_abs_le s₀
    linarith
  let Φ : ℝ → N ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ N := fun s => collarFlow_R7E X hXc (s - L)
  have hode : ∀ y : N, ∀ t ∈ Ioo (0 : ℝ) (s₀ + L + 1),
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => (Φ s : N → N) y) (Ici 0) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X ((Φ t : N → N) y))) := by
    intro y t _
    have h := hasMFDerivAt_collarFlow_time_R7E X hXc y (t - L)
    have htr : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s - L) t
        (ContinuousLinearMap.id ℝ ℝ) :=
      ((hasFDerivAt_id t).sub_const L).hasMFDerivAt
    have hc : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => (Φ s : N → N) y) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X ((Φ t : N → N) y))) :=
      (h.comp t htr).congr_mfderiv (ContinuousLinearMap.ext fun r => rfl)
    exact hc.hasMFDerivWithinAt
  have hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × N => (Φ q.1 : N → N) q.2) (Ioo (0 : ℝ) (s₀ + L + 1) ×ˢ univ) := by
    have hshift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × N => (p.1 - L, p.2)) :=
      (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
    exact ((contMDiff_collarFlow_joint_R7E X hXc).comp hshift).contMDiffOn
  have hslot := PDE.RicciFlow.flow_slot_pos G (fun _ => X) (s₀ + L + 1) Φ hode hjoint (s₀ + L)
    ⟨hLpos, by linarith⟩ x v v
  have hat := (hslot.hasDerivAt (Ici_mem_nhds hLpos)).comp s₀
    ((hasDerivAt_id s₀).add_const L)
  simp only [Φ, Function.comp_def, id, mul_one] at hat
  convert hat using 1
  · funext s
    rw [add_sub_cancel_right]
    rfl
  · rw [add_sub_cancel_right]
    rfl

/-- tangential contraction：`[0, τ]` 上 `L_X G(dD_s v, dD_s v) ≤ 0` ⇒ `|dD_τ v|² ≤ |v|²`。 -/
theorem collarFlow_pairing_le_R7E (G : SmoothRiemannianMetric 𝓘(ℝ, E) N) (x : N)
    (v : TangentSpace 𝓘(ℝ, E) x) {τ : ℝ} (hτ : 0 ≤ τ)
    (hlie : ∀ s ∈ Icc (0 : ℝ) τ, PDE.DeTurck.lieDerivMetric G X (collarFlow_R7E X hXc s x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc s) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc s) x v) ≤ 0) :
    G.inner (collarFlow_R7E X hXc τ x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc τ) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc τ) x v) ≤ G.inner x v v := by
  set f : ℝ → ℝ := fun s => G.inner (collarFlow_R7E X hXc s x)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc s) x v)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc s) x v) with hf
  have hd := hasDerivAt_collarFlow_pairing_R7E X hXc G x v
  have hanti : AntitoneOn f (Icc 0 τ) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 τ)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    exact hlie s (Ioo_subset_Icc_self hs)
  have h := hanti ⟨le_rfl, hτ⟩ ⟨hτ, le_rfl⟩ hτ
  have h0 : f 0 = G.inner x v v := by
    rw [hf]
    change G.inner (collarFlow_R7E X hXc 0 x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc 0) x v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc 0) x v) = _
    rw [collarFlow_zero_eq_refl_R7E, Diffeomorph.coe_refl, mfderiv_id]
    rfl
  rw [h0] at h
  exact h

end Flow

end DifferentialGeometry.Geometry
