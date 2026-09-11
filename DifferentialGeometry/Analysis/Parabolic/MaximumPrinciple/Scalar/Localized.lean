import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.FirstContact
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle ℝ E (TangentSpace I : M → Type _)]

private theorem parabolic_time_mul_at
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {T t : ℝ} {u : ℝ → M → ℝ} {x : M}
    (huniq : UniqueDiffWithinAt ℝ (Icc 0 T) t)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hu : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hgu : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X (fun s y => s * u s y) t x =
      u t x + t * parabolicOperatorWithDrift (I := I) G T X u t x := by
  unfold parabolicOperatorWithDrift heatOperatorWithDrift
  rw [derivWithin_fun_mul differentiableWithinAt_fun_id hu_time, derivWithin_id' (𝕜 := ℝ) (s := Icc 0 T) (x := t) huniq]
  change _ - (laplacianAt (I := I) G t (t • u t) x +
    driftTerm (I := I) G t (X t) (t • u t) x) = _
  rw [laplacianAt_smul_at (I := I) G t t hu hgu,
    driftTerm_const_smul (I := I) G t (X t) t hu.self_of_nhds]
  ring

private theorem parabolic_time_mul_nonpos_at_spacetime_min
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {t : ℝ} (ht : 0 < t) {x : M} (hx : I.IsInteriorPoint x)
    (q : ℝ → M → ℝ)
    (hq_time : DifferentiableWithinAt ℝ (fun s => q s x) (Icc 0 t) t)
    (hq : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (q t) y)
    (hgq : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (q t) y) x)
    (hmin : IsLocalMinOn (fun p : ℝ × M => p.1 * q p.1 p.2)
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x)) :
    q t x + t * parabolicOperatorWithDrift (I := I) G t X q t x ≤ 0 := by
  have hgtq : MDiffAt (T% fun y =>
      gradientFun (I := I) (G.metric t) (fun z => t * q t z) y) x := by
    refine (hgq.smul_const_section (a := t)).congr_of_eventuallyEq ?_
    filter_upwards [hq] with y hy
    exact congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      (gradientFun_const_smul (I := I) (G.metric t) t hy)
  have hL := derivWithin_sub_heatOperatorWithDrift_nonpos_at_spacetime_min
    (I := I) G X (psi := fun s y => s * q s y)
    ht hmin hx (hq.self_of_nhds.const_smul t)
    (hq.mono fun y hy => hy.const_smul t) hgtq
  change parabolicOperatorWithDrift (I := I) G t X (fun s y => s * q s y) t x ≤ 0 at hL
  rw [parabolic_time_mul_at G X ((uniqueDiffOn_Icc ht) t ⟨ht.le, le_rfl⟩)
    hq_time hq hgq] at hL
  exact hL

private theorem isLocalMin_of_time_mul_spacetime_min
    {t : ℝ} (ht : 0 < t) {x : M} {q : ℝ → M → ℝ}
    (hmin : IsLocalMinOn (fun p : ℝ × M => p.1 * q p.1 p.2)
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x)) :
    IsLocalMin (q t) x := by
  have hspace : IsLocalMin (fun y => t * q t y) x := by
    rw [← isLocalMinOn_univ_iff]
    exact hmin.comp_continuousOn
      (s := Set.univ) (g := fun y : M => (t, y))
      (by intro y hy; exact ⟨⟨ht.le, le_rfl⟩, hy⟩)
      (continuous_const.prodMk continuous_id).continuousOn (Set.mem_univ x)
  filter_upwards [hspace] with y hy
  exact (mul_le_mul_iff_right₀ ht).mp hy

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
private theorem gradient_inner_eq_at_product_min
    (g : SmoothRiemannianMetric I M) {φ u : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x)
    (hφ : MDifferentiableAt I 𝓘(ℝ, ℝ) φ x)
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x)
    (hmin : IsLocalMin (fun y => φ y * u y) x) :
    φ x * g.inner x (gradientFun (I := I) g φ x) (gradientFun (I := I) g u x) +
      u x * g.inner x (gradientFun (I := I) g φ x) (gradientFun (I := I) g φ x) = 0 := by
  have hzero := gradientFun_eq_zero_at_spatial_min_of_isInteriorPoint
    (I := I) g hmin hx (hφ.mul hu)
  rw [gradientFun_mul (I := I) g hφ hu] at hzero
  have hcross := congrArg (fun w => g.inner x (gradientFun (I := I) g φ x) w) hzero
  simpa only [map_add, map_smul, map_zero, smul_eq_mul] using hcross

private theorem cutoff_parabolic_inequality_at_spacetime_min
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {t : ℝ} (ht : 0 < t) {x : M} (hx : I.IsInteriorPoint x)
    (φ u : ℝ → M → ℝ)
    (hφ_time : DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 t) t)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 t) t)
    (hφ : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y)
    (hu : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hgφ : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (φ t) y) x)
    (hgu : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (u t) y) x)
    (hmin : IsLocalMinOn (fun p : ℝ × M => p.1 * (φ p.1 p.2 * u p.1 p.2))
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x))
    (hφnonneg : 0 ≤ φ t x) :
    φ t x ^ 2 * u t x + t * φ t x ^ 2 *
      parabolicOperatorWithDrift (I := I) G t X u t x +
      t * φ t x * u t x * parabolicOperatorWithDrift (I := I) G t X φ t x +
      2 * t * u t x * (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
        (gradientAt (I := I) G t (φ t) x) ≤ 0 := by
  let q : ℝ → M → ℝ := fun s y => φ s y * u s y
  have hq : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (q t) y := by
    filter_upwards [hφ, hu] with y hφy huy
    exact hφy.mul huy
  have hgq := mdifferentiableAt_gradientFun_mul (G.metric t) hφ hu hgφ hgu
  have hL := parabolic_time_mul_nonpos_at_spacetime_min G X ht hx q
    (hφ_time.mul hu_time) hq hgq hmin
  have hminq := isLocalMin_of_time_mul_spacetime_min (q := q) (x := x) ht hmin
  have hcross := gradient_inner_eq_at_product_min (G.metric t) hx
    hφ.self_of_nhds hu.self_of_nhds hminq
  change φ t x * (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
    (gradientAt (I := I) G t (u t) x) +
    u t x * (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
      (gradientAt (I := I) G t (φ t) x) = 0 at hcross
  have hproduct := parabolic_mul_nhds (I := I) (G := G) t X φ u t x
    hφ_time hu_time hφ hu hgφ hgu
  change parabolicOperatorWithDrift (I := I) G t X q t x = _ at hproduct
  rw [hproduct] at hL
  dsimp only [q] at hL
  have hscaled := mul_le_mul_of_nonneg_left hL hφnonneg
  linear_combination hscaled + 2 * t * hcross

private theorem cutoff_quadratic_bound
    {t φ u c δ ε Pu Pφ B : ℝ}
    (ht : 0 < t) (hφpos : 0 < φ) (hφle : φ ≤ 1) (huneg : u < 0)
    (hc : 0 < c) (hPu : c * u ^ 2 ≤ Pu) (hPφ : Pφ ≤ δ)
    (hgrad : B ≤ ε * φ)
    (hL : φ ^ 2 * u + t * φ ^ 2 * Pu + t * φ * u * Pφ + 2 * t * u * B ≤ 0) :
    -(1 + t * (δ + 2 * ε)) / c ≤ t * (φ * u) := by
  have hscaled := mul_le_mul_of_nonneg_left hL ht.le
  have hreac := mul_le_mul_of_nonneg_left hPu (sq_nonneg (t * φ))
  have hcut := mul_le_mul_of_nonpos_left hPφ
    (show t ^ 2 * φ * u ≤ 0 from
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg t) hφpos.le) huneg.le)
  have hgradient := mul_le_mul_of_nonpos_left hgrad
    (show 2 * t ^ 2 * u ≤ 0 from
      mul_nonpos_of_nonneg_of_nonpos (by positivity) huneg.le)
  have hbound : c * (t * (φ * u)) ^ 2 +
      (t * (φ * u)) * φ + t * (t * (φ * u)) * (δ + 2 * ε) ≤ 0 := by
    nlinarith only [hscaled, hreac, hcut, hgradient]
  have hvneg : t * (φ * u) < 0 :=
    mul_neg_of_pos_of_neg ht (mul_neg_of_pos_of_neg hφpos huneg)
  have hplateau := mul_le_mul_of_nonpos_left hφle hvneg.le
  have hfactor : (t * (φ * u)) * (c * (t * (φ * u)) + 1 + t * (δ + 2 * ε)) ≤ 0 := by
    nlinarith only [hbound, hplateau]
  have hnonneg := nonneg_of_mul_nonpos_right hfactor hvneg
  apply (div_le_iff₀ hc).2
  nlinarith only [hnonneg]

theorem cutoff_quadratic_lower_bound_at_spacetime_min
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {t : ℝ} (ht : 0 < t) {x : M} (hx : I.IsInteriorPoint x)
    (φ u : ℝ → M → ℝ)
    (hφ_time : DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 t) t)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 t) t)
    (hφ : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y)
    (hu : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hgφ : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (φ t) y) x)
    (hgu : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (u t) y) x)
    (hmin : IsLocalMinOn (fun p : ℝ × M => p.1 * (φ p.1 p.2 * u p.1 p.2))
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x))
    (hφpos : 0 < φ t x) (hφle : φ t x ≤ 1) (huneg : u t x < 0)
    {c δ ε : ℝ} (hc : 0 < c)
    (hPu : c * u t x ^ 2 ≤ parabolicOperatorWithDrift (I := I) G t X u t x)
    (hPφ : parabolicOperatorWithDrift (I := I) G t X φ t x ≤ δ)
    (hgrad : (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
      (gradientAt (I := I) G t (φ t) x) ≤ ε * φ t x) :
    -(1 + t * (δ + 2 * ε)) / c ≤ t * (φ t x * u t x) := by
  exact cutoff_quadratic_bound ht hφpos hφle huneg hc hPu hPφ hgrad
    (cutoff_parabolic_inequality_at_spacetime_min G X ht hx φ u
      hφ_time hu_time hφ hu hgφ hgu hmin hφpos.le)


theorem cutoff_quadratic_lower_bound_of_lower_support_at_spacetime_min
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {t : ℝ} (ht : 0 < t) {x : M} (hx : I.IsInteriorPoint x)
    (χ φ u : ℝ → M → ℝ)
    (hφ_time : DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 t) t)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 t) t)
    (hφ : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y)
    (hu : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hgφ : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (φ t) y) x)
    (hgu : MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_cont : ContinuousWithinAt (fun p : ℝ × M => u p.1 p.2)
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x))
    (hφχ : ∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x), φ p.1 p.2 ≤ χ p.1 p.2)
    (hφeq : φ t x = χ t x)
    (hχpos : 0 < χ t x) (hχle : χ t x ≤ 1) (huneg : u t x < 0)
    (hmin : IsLocalMinOn (fun p : ℝ × M => p.1 * (χ p.1 p.2 * u p.1 p.2))
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x))
    {c δ ε : ℝ} (hc : 0 < c)
    (hPu : c * u t x ^ 2 ≤ parabolicOperatorWithDrift (I := I) G t X u t x)
    (hPφ : parabolicOperatorWithDrift (I := I) G t X φ t x ≤ δ)
    (hgrad : (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
      (gradientAt (I := I) G t (φ t) x) ≤ ε * φ t x) :
    -(1 + t * (δ + 2 * ε)) / c ≤ t * (χ t x * u t x) := by
  have hminφ : IsLocalMinOn (fun p : ℝ × M => p.1 * (φ p.1 p.2 * u p.1 p.2))
      (Icc 0 t ×ˢ (Set.univ : Set M)) (t, x) := by
    have hunear : ∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x), u p.1 p.2 < 0 :=
      hu_cont.preimage_mem_nhdsWithin (Iio_mem_nhds huneg)
    filter_upwards [hmin, hφχ, hunear, self_mem_nhdsWithin] with p hminp hφχp hunegp hp
    rw [hφeq]
    exact hminp.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonpos_right hφχp hunegp.le) hp.1.1)
  rw [← hφeq]
  exact cutoff_quadratic_lower_bound_at_spacetime_min G X ht hx φ u
    hφ_time hu_time hφ hu hgφ hgu hminφ (hφeq.symm ▸ hχpos)
    (hφeq.symm ▸ hχle) huneg hc hPu hPφ hgrad


theorem cutoff_quadratic_lower_bound_on_compact_support
    [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {T c δ ε : ℝ} (hT : 0 ≤ T) (hc : 0 < c) (herror : 0 ≤ δ + 2 * ε)
    (χ u : ℝ → M → ℝ)
    (K : Set M) (hK : IsCompact K)
    (hχ : ∀ t ∈ Icc 0 T, ∀ x, χ t x ∈ Icc 0 1)
    (hsupport : ∀ t ∈ Icc 0 T, ∀ x ∉ K, χ t x = 0)
    (hcont : ContinuousOn (fun p : ℝ × M => p.1 * (χ p.1 p.2 * u p.1 p.2))
      (Icc 0 T ×ˢ K))
    (hu_cont : ContinuousOn (fun p : ℝ × M => u p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hu_time : ∀ t ∈ Ioc 0 T, ∀ x,
      DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 t) t)
    (hu_space : ∀ t ∈ Ioc 0 T, ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) x)
    (hu_grad : ∀ t ∈ Ioc 0 T, ∀ x,
      MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (u t) y) x)
    (hPu : ∀ t ∈ Ioc 0 T, ∀ x,
      c * u t x ^ 2 ≤ parabolicOperatorWithDrift (I := I) G t X u t x)
    (hcut : ∀ t ∈ Ioc 0 T, ∀ x, 0 < χ t x → u t x < 0 →
      ∃ φ : ℝ → M → ℝ,
        φ t x = χ t x ∧
        (∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x), φ p.1 p.2 ≤ χ p.1 p.2) ∧
        DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 t) t ∧
        (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y) ∧
        MDiffAt (T% fun y => gradientFun (I := I) (G.metric t) (φ t) y) x ∧
        parabolicOperatorWithDrift (I := I) G t X φ t x ≤ δ ∧
        (G.metric t).inner x (gradientAt (I := I) G t (φ t) x)
          (gradientAt (I := I) G t (φ t) x) ≤ ε * φ t x) :
    ∀ t ∈ Icc 0 T, ∀ x, -(1 + T * (δ + 2 * ε)) / c ≤ t * (χ t x * u t x) := by
  classical
  let w : ℝ × M → ℝ := fun p => p.1 * (χ p.1 p.2 * u p.1 p.2)
  have hboundneg : -(1 + T * (δ + 2 * ε)) / c < 0 := by
    exact div_neg_of_neg_of_pos (by nlinarith [mul_nonneg hT herror]) hc
  intro t ht x
  by_contra hnot
  have hbad : w (t, x) < -(1 + T * (δ + 2 * ε)) / c := lt_of_not_ge hnot
  have hbadneg : w (t, x) < 0 := hbad.trans hboundneg
  have hxK : x ∈ K := by
    by_contra hx
    have hzero := hsupport t ht x hx
    simp only [w, hzero, zero_mul, mul_zero] at hbadneg
    exact (lt_irrefl 0 hbadneg)
  obtain ⟨p, hp, hpmin⟩ := (isCompact_Icc.prod hK).exists_isMinOn
    (show (Icc 0 T ×ˢ K).Nonempty from ⟨(t, x), ht, hxK⟩) hcont
  have hpbad : w p < -(1 + T * (δ + 2 * ε)) / c :=
    (hpmin (show (t, x) ∈ Icc 0 T ×ˢ K from ⟨ht, hxK⟩)).trans_lt hbad
  have hpneg : w p < 0 := hpbad.trans hboundneg
  have hptime : 0 < p.1 := by
    have hpne : p.1 ≠ 0 := by
      intro heq
      simp only [w, heq, zero_mul] at hpneg
      exact (lt_irrefl 0 hpneg)
    exact lt_of_le_of_ne hp.1.1 (Ne.symm hpne)
  have hpreg : p.1 ∈ Ioc 0 T := ⟨hptime, hp.1.2⟩
  have hχp := hχ p.1 hp.1 p.2
  have hχpos : 0 < χ p.1 p.2 := by
    have hχne : χ p.1 p.2 ≠ 0 := by
      intro heq
      simp only [w, heq, zero_mul, mul_zero] at hpneg
      exact (lt_irrefl 0 hpneg)
    exact lt_of_le_of_ne hχp.1 (Ne.symm hχne)
  have huneg : u p.1 p.2 < 0 := by
    have hmul : χ p.1 p.2 * u p.1 p.2 < 0 :=
      (neg_of_mul_neg_right hpneg hptime.le)
    exact (neg_of_mul_neg_right hmul hχpos.le)
  have hmin : IsMinOn w (Icc 0 p.1 ×ˢ (Set.univ : Set M)) p := by
    intro q hq
    have hqT : q.1 ∈ Icc 0 T := ⟨hq.1.1, hq.1.2.trans hp.1.2⟩
    by_cases hqK : q.2 ∈ K
    · exact hpmin ⟨hqT, hqK⟩
    · have hzero : w q = 0 := by simp only [w, hsupport q.1 hqT q.2 hqK, zero_mul, mul_zero]
      exact hpneg.le.trans_eq hzero.symm
  obtain ⟨φ, hφeq, hφχ, hφtime, hφspace, hφgrad, hφP, hφg⟩ :=
    hcut p.1 hpreg p.2 hχpos huneg
  have hucont : ContinuousWithinAt (fun q : ℝ × M => u q.1 q.2)
      (Icc 0 p.1 ×ˢ (Set.univ : Set M)) p := by
    apply (hu_cont p (show p ∈ Icc 0 T ×ˢ (Set.univ : Set M) from ⟨hp.1, mem_univ _⟩)).mono
    intro q hq
    exact ⟨⟨hq.1.1, hq.1.2.trans hp.1.2⟩, hq.2⟩
  have hlocal := cutoff_quadratic_lower_bound_of_lower_support_at_spacetime_min
    G X hptime BoundarylessManifold.isInteriorPoint χ φ u hφtime
    (hu_time p.1 hpreg p.2) hφspace (Eventually.of_forall (hu_space p.1 hpreg))
    hφgrad (hu_grad p.1 hpreg p.2) hucont hφχ hφeq hχpos hχp.2 huneg
    hmin.localize hc (hPu p.1 hpreg p.2) hφP hφg
  have hmono : -(1 + T * (δ + 2 * ε)) / c ≤ -(1 + p.1 * (δ + 2 * ε)) / c := by
    apply div_le_div_of_nonneg_right _ hc.le
    linarith [mul_le_mul_of_nonneg_right hp.1.2 herror]
  exact not_lt_of_ge (hmono.trans hlocal) hpbad

end DifferentialGeometry.Analysis.Parabolic
