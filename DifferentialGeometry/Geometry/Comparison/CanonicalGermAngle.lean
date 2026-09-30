import DifferentialGeometry.Geometry.Comparison.LocalGermAngle
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false

open Set Filter Topology Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

noncomputable def germComparisonAngle {X : Type*} [MetricSpace X]
    (κ : ℝ) (γ β : ℝ → X) : ℝ :=
  limsup (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
    (dist (γ z.1) (β z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))

theorem germComparisonAngle_eq_of_tendsto {X : Type*} [MetricSpace X]
    {κ α : ℝ} {γ β : ℝ → X}
    (h : Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
      (dist (γ z.1) (β z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 α)) :
    germComparisonAngle κ γ β = α := h.limsup_eq

theorem germComparisonAngle_congr {X : Type*} [MetricSpace X]
    {κ : ℝ} {γ β γ' β' : ℝ → X}
    (hγ : γ =ᶠ[𝓝[>] (0 : ℝ)] γ') (hβ : β =ᶠ[𝓝[>] (0 : ℝ)] β') :
    germComparisonAngle κ γ β = germComparisonAngle κ γ' β' := by
  apply limsup_congr
  filter_upwards [hγ.prod_inl _, hβ.prod_inr _] with z h₁ h₂
  rw [h₁, h₂]

theorem germComparisonAngle_congr_on {X : Type*} [MetricSpace X]
    {κ r s : ℝ} (hr : 0 < r) (hs : 0 < s) {γ β γ' β' : ℝ → X}
    (hγ : EqOn γ γ' (Ioc (0 : ℝ) r)) (hβ : EqOn β β' (Ioc (0 : ℝ) s)) :
    germComparisonAngle κ γ β = germComparisonAngle κ γ' β' := by
  apply germComparisonAngle_congr
  · filter_upwards [Ioc_mem_nhdsGT hr] with t ht using hγ ht
  · filter_upwards [Ioc_mem_nhdsGT hs] with t ht using hβ ht

theorem germComparisonAngle_mem_Icc {X : Type*} [MetricSpace X]
    (κ : ℝ) (γ β : ℝ → X) : germComparisonAngle κ γ β ∈ Icc (0 : ℝ) Real.pi := by
  let f := fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
    (dist (γ z.1) (β z.2))
  have hlo : ∀ᶠ z in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ), 0 ≤ f z :=
    Eventually.of_forall fun z => (comparisonAngleNegCurvature_mem_Icc _ _ _ _).1
  have hhi : ∀ᶠ z in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ), f z ≤ Real.pi :=
    Eventually.of_forall fun z => (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2
  exact ⟨le_limsup_of_frequently_le hlo.frequently (isBoundedUnder_of_eventually_le hhi),
    limsup_le_of_le (isBoundedUnder_of_eventually_ge hlo).isCobounded_flip hhi⟩

theorem germComparisonAngle_comm {X : Type*} [MetricSpace X]
    (κ : ℝ) (γ β : ℝ → X) :
    germComparisonAngle κ γ β = germComparisonAngle κ β γ := by
  unfold germComparisonAngle
  conv_lhs => rw [Filter.prod_comm]
  rw [← limsup_comp]
  apply limsup_congr
  exact Eventually.of_forall fun z => by
    dsimp only [Function.comp_def, Prod.swap]
    rw [comparisonAngleNegCurvature_comm, dist_comm]

theorem germComparisonAngle_self {X : Type*} [MetricSpace X]
    {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R) {γ : ℝ → X}
    (hmin : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ s) (γ t) = |s - t|) : germComparisonAngle κ γ γ = 0 := by
  change limsup _ _ = 0
  apply Eq.trans (b := limsup (fun _ : ℝ × ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))) _ (limsup_const 0)
  apply limsup_congr
  have he : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioc (0 : ℝ) R := Ioc_mem_nhdsGT hR
  filter_upwards [he.prod_inl _, he.prod_inr _]
    with z hs ht
  rw [hmin z.1 hs z.2 ht, comparisonAngleNegCurvature_abs_sub hκ hs.1 ht.1]

theorem germComparisonAngle_opposite {X : Type*} [MetricSpace X]
    {κ R S : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R) (hS : 0 < S) {γ β : ℝ → X}
    (hopp : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (γ s) (β t) = s + t) : germComparisonAngle κ γ β = Real.pi := by
  change limsup _ _ = Real.pi
  apply Eq.trans (b := limsup (fun _ : ℝ × ℝ => Real.pi) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))) _ (limsup_const Real.pi)
  apply limsup_congr
  have heR : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioc (0 : ℝ) R := Ioc_mem_nhdsGT hR
  have heS : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioc (0 : ℝ) S := Ioc_mem_nhdsGT hS
  filter_upwards [heR.prod_inl _, heS.prod_inr _]
    with z hs ht
  rw [hopp z.1 hs z.2 ht, comparisonAngleNegCurvature_add hκ hs.1 ht.1]

theorem germComparisonAngle_eq_limitingComparisonAngle
    {X : Type*} [MetricSpace X] {κ R S : ℝ} (hκ : 0 ≤ κ)
    (hR : 0 < R) (hS : 0 < S) {Ω : Set X}
    (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω) {γ β : ℝ → X}
    (hγrad : ∀ s ∈ Ioc (0 : ℝ) R, dist p (γ s) = s)
    (hβrad : ∀ t ∈ Ioc (0 : ℝ) S, dist p (β t) = t)
    (hγmin : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ s) (γ t) = |s - t|)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (β s) (β t) = |s - t|)
    (hγmem : ∀ s ∈ Ioc (0 : ℝ) R, γ s ∈ Ω)
    (hβmem : ∀ t ∈ Ioc (0 : ℝ) S, β t ∈ Ω) :
    germComparisonAngle κ γ β = limitingComparisonAngle κ R S γ β :=
  germComparisonAngle_eq_of_tendsto
    (tendsto_limitingComparisonAngle_of_fourPointComparison hκ hR hS hcomp hp
      hγrad hβrad hγmin hβmin hγmem hβmem)

end DifferentialGeometry.Geometry.Comparison.Toponogov
