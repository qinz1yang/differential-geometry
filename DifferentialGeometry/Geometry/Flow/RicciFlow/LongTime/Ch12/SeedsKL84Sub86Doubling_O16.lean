import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalarEvolutionRate

/-!
# CH12-O16 G2b-(b1): backward scalar-curvature doubling from the P2 time-derivative bound

KL Sublemma 86.3, step (b1) (KL70.1-type): if `|∂ₜR| ≤ C R²` wherever `R > M`, and `R ≤ M` at the
top time `b`, then `R ≤ 2M` on the backward window `[b - (12 C M)⁻¹, b]`.

* `backward_doubling_O16`: the one-variable statement, with left derivatives (`derivWithin … Iic`),
  the form in which `P2_O2` is stated.  Proof: reflect time and compare with the barrier
  `B(σ) = (2/(3M) - 2Cσ)⁻¹`, which solves `B' = 2C B²` (mathlib's
  `image_le_of_deriv_right_lt_deriv_boundary'`).
* `event_scalar_backward_doubling_O16`: the same along a fixed point of the incoming flow of an
  event slab of `F.tower.history n`, with the bound supplied by the first clause of `P2_O2`
  (above the neck threshold `(neckRadius t)⁻²`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Topology NNReal

namespace GC.LongTime.Ch12

universe u

/-- One-variable backward doubling: the left-derivative bound `|f'| ≤ C f²` above level `M` and
`f b ≤ M` give `f ≤ 2M` on `[c, b]` when `b - c ≤ (12 C M)⁻¹`. -/
theorem backward_doubling_O16 {f : ℝ → ℝ} {c b M C : ℝ} (hC : 0 < C) (hM : 0 < M)
    (hcont : ContinuousOn f (Icc c b))
    (hdiff : ∀ t ∈ Ioc c b, DifferentiableWithinAt ℝ f (Iic t) t)
    (hP2 : ∀ t ∈ Ioc c b, M < f t → |derivWithin f (Iic t) t| ≤ C * f t ^ 2)
    (hb : f b ≤ M) (hwin : b - c ≤ (12 * C * M)⁻¹) :
    ∀ t ∈ Icc c b, f t ≤ 2 * M := by
  -- reflected function and barrier
  set β : ℝ := 2 / (3 * M) with hβ
  let h : ℝ → ℝ := fun σ => f (b - σ)
  let h' : ℝ → ℝ := fun σ => -derivWithin f (Iic (b - σ)) (b - σ)
  let den : ℝ → ℝ := fun σ => β - 2 * C * σ
  let B : ℝ → ℝ := fun σ => (den σ)⁻¹
  let B' : ℝ → ℝ := fun σ => 2 * C / den σ ^ 2
  have hwin' : (b - c) * (12 * C * M) ≤ 1 := by
    have hpos : 0 < 12 * C * M := by positivity
    calc (b - c) * (12 * C * M) ≤ (12 * C * M)⁻¹ * (12 * C * M) :=
          mul_le_mul_of_nonneg_right hwin hpos.le
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  -- on the window the denominator is at least `1/(2M)`
  have hden : ∀ σ, 0 ≤ σ → σ ≤ b - c → 1 / (2 * M) ≤ den σ := by
    intro σ hσ0 hσ
    have h1 : σ * (12 * C * M) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hσ (by positivity)) hwin'
    have h2 : 2 * C * σ ≤ 1 / (6 * M) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h3 : β = 1 / (2 * M) + 1 / (6 * M) := by
      rw [hβ]; field_simp; ring
    change 1 / (2 * M) ≤ β - 2 * C * σ
    linarith
  have hdenpos : ∀ σ, 0 ≤ σ → σ ≤ b - c → 0 < den σ := fun σ h0 h1 =>
    lt_of_lt_of_le (by positivity) (hden σ h0 h1)
  have hB_le : ∀ σ, 0 ≤ σ → σ ≤ b - c → B σ ≤ 2 * M := by
    intro σ h0 h1
    have hd := hden σ h0 h1
    have hp : 0 < 1 / (2 * M) := by positivity
    calc B σ = (den σ)⁻¹ := rfl
      _ ≤ (1 / (2 * M))⁻¹ := inv_anti₀ hp hd
      _ = 2 * M := by rw [one_div, inv_inv]
  have hB_ge : ∀ σ, 0 ≤ σ → σ ≤ b - c → 3 * M / 2 ≤ B σ := by
    intro σ h0 h1
    have hd := hdenpos σ h0 h1
    have hle : den σ ≤ β := by
      change β - 2 * C * σ ≤ β
      nlinarith
    calc 3 * M / 2 = β⁻¹ := by rw [hβ]; field_simp
      _ ≤ (den σ)⁻¹ := inv_anti₀ hd hle
  -- derivative of the reflected function
  have hh' : ∀ σ ∈ Ico (0 : ℝ) (b - c), HasDerivWithinAt h (h' σ) (Ici σ) σ := by
    intro σ hσ
    have ht : b - σ ∈ Ioc c b := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hf := (hdiff (b - σ) ht).hasDerivWithinAt
    have hlin : HasDerivWithinAt (fun σ : ℝ => b - σ) (-1) (Ici σ) σ :=
      ((hasDerivAt_id σ).const_sub b).hasDerivWithinAt
    have hmaps : MapsTo (fun σ : ℝ => b - σ) (Ici σ) (Iic (b - σ)) := by
      intro x hx; simp only [mem_Ici] at hx; simp only [mem_Iic]; linarith
    have hcomp := hf.comp σ hlin hmaps
    have heq : derivWithin f (Iic (b - σ)) (b - σ) * (-1) = h' σ := by
      simp only [h', mul_neg, mul_one]
    rw [heq] at hcomp
    exact hcomp
  have hhc : ContinuousOn h (Icc 0 (b - c)) := by
    have hmaps : MapsTo (fun σ : ℝ => b - σ) (Icc 0 (b - c)) (Icc c b) := by
      intro x hx; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    exact hcont.comp (continuousOn_const.sub continuousOn_id) hmaps
  have hBc : ContinuousOn B (Icc 0 (b - c)) := by
    refine ContinuousOn.inv₀ (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      ?_
    intro σ hσ; exact (hdenpos σ hσ.1 hσ.2).ne'
  have hB' : ∀ σ ∈ Ico (0 : ℝ) (b - c), HasDerivWithinAt B (B' σ) (Ici σ) σ := by
    intro σ hσ
    have hd : HasDerivAt den (-(2 * C)) σ := by
      have := ((hasDerivAt_id σ).const_mul (2 * C)).const_sub β
      simpa [den, mul_one] using this
    have hinv := hd.inv (hdenpos σ hσ.1 hσ.2.le).ne'
    have heq : -(-(2 * C)) / den σ ^ 2 = B' σ := by simp only [neg_neg, B']
    rw [heq] at hinv
    exact hinv.hasDerivWithinAt
  intro t0 ht0
  have hbc : 0 ≤ b - c := by linarith [ht0.1, ht0.2]
  have ha : h 0 ≤ B 0 := by
    have h0 := hB_ge 0 le_rfl hbc
    change f (b - 0) ≤ B 0
    rw [sub_zero]
    linarith
  have bound : ∀ σ ∈ Ico (0 : ℝ) (b - c), h σ = B σ → h' σ < B' σ := by
    intro σ hσ heq
    have ht : b - σ ∈ Ioc c b := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hge := hB_ge σ hσ.1 hσ.2.le
    have hd := hdenpos σ hσ.1 hσ.2.le
    have hfM : M < f (b - σ) := by
      change f (b - σ) = B σ at heq
      rw [heq]; linarith
    have hd2 := hP2 (b - σ) ht hfM
    have hfB : f (b - σ) = (den σ)⁻¹ := heq
    rw [hfB] at hd2
    have hneg : h' σ ≤ |derivWithin f (Iic (b - σ)) (b - σ)| := by
      simp only [h']; exact neg_le_abs _
    have hsq : C * ((den σ)⁻¹) ^ 2 < B' σ := by
      simp only [B', inv_pow, div_eq_mul_inv]
      have : 0 < (den σ ^ 2)⁻¹ := by positivity
      nlinarith
    linarith
  have hcmp := image_le_of_deriv_right_lt_deriv_boundary' hhc hh' ha hBc hB' bound
  have hσ : b - t0 ∈ Icc (0 : ℝ) (b - c) := ⟨by linarith [ht0.2], by linarith [ht0.1]⟩
  have h1 := hcmp hσ
  have h2 := hB_le (b - t0) hσ.1 hσ.2
  have : h (b - t0) = f t0 := by simp only [h, sub_sub_cancel]
  linarith

/-- Backward doubling along a fixed point of an incoming slab flow, from a P2-type left-derivative
bound above a time-dependent threshold `θ t ≤ M`. -/
theorem incoming_scalar_backward_doubling_O16 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (y : P.Carrier) {θ : ℝ → ℝ} {C : ℝ≥0}
    (hP2 : ∀ t ∈ Ioo a s, θ t < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    {c b M : ℝ} (hM : 0 < M) (hcb : Icc c b ⊆ Ioo a s) (hθ : ∀ t ∈ Icc c b, θ t ≤ M)
    (hb : G.flow.scalar b y ≤ M) (hwin : b - c ≤ (12 * ((C : ℝ) + 1) * M)⁻¹) :
    ∀ t ∈ Icc c b, G.flow.scalar t y ≤ 2 * M := by
  have hder : ∀ t ∈ Icc c b, HasDerivAt (fun v => G.flow.scalar v y)
      (scalarEvolutionRate (G.flow.base.metric t) y) t := fun t ht =>
    G.hasDerivAt_scalar_scalarEvolutionRate (hcb ht) y
  have hC1 : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  refine backward_doubling_O16 hC1 hM ?_ ?_ ?_ hb hwin
  · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hder t (Ioc_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
  · intro t ht hMt
    have ht' : t ∈ Icc c b := Ioc_subset_Icc_self ht
    have h1 := hP2 t (hcb ht') (lt_of_le_of_lt (hθ t ht') hMt)
    have h2 : (C : ℝ) * G.flow.scalar t y ^ 2 ≤ ((C : ℝ) + 1) * G.flow.scalar t y ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    exact h1.trans h2

section Profile

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **(b1), event slabs**: backward doubling of `R` at a fixed point of the incoming flow of an
event slab of `F.tower.history n`, from the first clause of `P2_O2` (threshold `(neckRadius t)⁻²`).
-/
theorem event_scalar_backward_doubling_O16 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime) (n : ℕ) (j : Fin (F.tower.history n).eventCount)
    (y : ((F.tower.history n).stage j.castSucc).Carrier) {c b M : ℝ} (hM : 0 < M)
    (hcb : Icc c b ⊆ Ioo ((F.tower.history n).time j.castSucc) ((F.tower.history n).time j.succ))
    (hneck : ∀ t ∈ Icc c b, (Hp.parameters.neckRadius t ^ 2)⁻¹ ≤ M)
    (hb : ((F.tower.history n).toHistory.event j).incoming.flow.scalar b y ≤ M)
    (hwin : b - c ≤ (12 * ((Ctime : ℝ) + 1) * M)⁻¹) :
    ∀ t ∈ Icc c b, ((F.tower.history n).toHistory.event j).incoming.flow.scalar t y ≤ 2 * M :=
  incoming_scalar_backward_doubling_O16 ((F.tower.history n).toHistory.event j).incoming y
    (θ := fun t => (Hp.parameters.neckRadius t ^ 2)⁻¹) (fun t ht hlt => hP2.1 n j y t ht hlt)
    hM hcb hneck hb hwin

end Profile

end GC.LongTime.Ch12
