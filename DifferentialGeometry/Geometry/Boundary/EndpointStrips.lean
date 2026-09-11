import DifferentialGeometry.Geometry.Boundary.UniformGradientFlow
import DifferentialGeometry.Topology.Manifold.FlowInjectivity
import DifferentialGeometry.Topology.Manifold.BoundaryExtrema
import Mathlib.Topology.Order.Compact

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Gradient DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {I : ModelWithCorners ℝ E H} [HasSmoothBoundary E H I]
  [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
private theorem closedEmbedding_restrict_flow {K U : Set M} {Φ : M × ℝ → M} {δ ε : ℝ}
    (hK : IsCompact K) (hKU : K ⊆ U) (hδε : δ < ε)
    (hΦ : ContinuousOn Φ (U ×ˢ Ico 0 ε)) (hinj : InjOn Φ (K ×ˢ Ico 0 ε)) :
    IsClosedEmbedding (fun z : K × Icc (0 : ℝ) δ ↦ Φ (z.1.1, z.2.1)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun z : K × Icc (0 : ℝ) δ ↦ Φ (z.1.1, z.2.1)) :=
    hΦ.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
      (fun z ↦ ⟨hKU z.1.2, z.2.2.1, z.2.2.2.trans_lt hδε⟩)
  apply hc.isClosedEmbedding
  intro z w heq
  have h := hinj ⟨z.1.2, z.2.2.1, z.2.2.2.trans_lt hδε⟩
    ⟨w.1.2, w.2.2.1, w.2.2.2.trans_lt hδε⟩ heq
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

theorem exists_disjoint_adapted_endpoint_strips [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    ∃ ε > 0, 2 * ε < b - a ∧
      ∃ U₁ U₂ : Set M, IsOpen U₁ ∧ IsOpen U₂ ∧
        u ⁻¹' {a} ⊆ U₁ ∧ u ⁻¹' {b} ⊆ U₂ ∧
      ∃ Φ₁ Φ₂ : M × ℝ → M,
        (∀ x ∈ U₁, Φ₁ (x, 0) = x) ∧ (∀ x ∈ U₂, Φ₂ (x, 0) = x) ∧
        ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ₁ (U₁ ×ˢ Icc 0 ε) ∧
        ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ₂ (U₂ ×ˢ Icc 0 ε) ∧
        (∀ x ∈ U₁, IsMIntegralCurveOn (fun t ↦ Φ₁ (x, t)) (normalizedGradient g u) (Icc 0 ε)) ∧
        (∀ x ∈ U₂, IsMIntegralCurveOn (fun t ↦ Φ₂ (x, t)) (-normalizedGradient g u) (Icc 0 ε)) ∧
        (∀ x ∈ u ⁻¹' {a}, ∀ t ∈ Icc 0 ε, u (Φ₁ (x, t)) = a + t) ∧
        (∀ x ∈ u ⁻¹' {b}, ∀ t ∈ Icc 0 ε, u (Φ₂ (x, t)) = b - t) ∧
        IsClosedEmbedding (fun z : (u ⁻¹' {a}) × Icc (0 : ℝ) ε ↦ Φ₁ (z.1.1, z.2.1)) ∧
        IsClosedEmbedding (fun z : (u ⁻¹' {b}) × Icc (0 : ℝ) ε ↦ Φ₂ (z.1.1, z.2.1)) ∧
        Disjoint (Φ₁ '' ((u ⁻¹' {a}) ×ˢ Icc 0 ε)) (Φ₂ '' ((u ⁻¹' {b}) ×ˢ Icc 0 ε)) ∧
        (∀ x ∈ U₁, ∀ t ∈ Ioc 0 ε, I.IsInteriorPoint (Φ₁ (x, t))) ∧
        ∀ x ∈ U₂, ∀ t ∈ Ioc 0 ε, I.IsInteriorPoint (Φ₂ (x, t)) := by
  have hb := fun x ↦ range_subset_Icc_of_boundary_values hab.le hreg hboundary (mem_range_self x)
  have hmin : ∀ x ∈ u ⁻¹' {a}, IsLocalMin u x := by
    intro x hx
    exact Eventually.of_forall (fun y ↦ by simpa only [show u x = a from hx] using (hb y).1)
  have hmax : ∀ x ∈ u ⁻¹' {b}, IsLocalMax u x := by
    intro x hx
    exact Eventually.of_forall (fun y ↦ by simpa only [show u x = b from hx] using (hb y).2)
  have hKa : IsCompact (u ⁻¹' {a}) := (isClosed_singleton.preimage hu.continuous).isCompact
  have hKb : IsCompact (u ⁻¹' {b}) := (isClosed_singleton.preimage hu.continuous).isCompact
  have hBa : u ⁻¹' {a} ⊆ I.boundary M := fun x hx ↦
    isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero (hmin x hx) (hreg x)
  have hBb : u ⁻¹' {b} ⊆ I.boundary M := fun x hx ↦
    isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero (hmax x hx) (hreg x)
  obtain ⟨ε₁, hε₁, U₁, hU₁, hKU₁, Φ₁, hzero₁, hΦ₁, hcurve₁, hheight₁, hinside₁⟩ :=
    exists_normalizedGradient_lower_uniformFlow g hu hreg hKa hBa hmin
  obtain ⟨ε₂, hε₂, U₂, hU₂, hKU₂, Φ₂, hzero₂, hΦ₂, hcurve₂, hheight₂, hinside₂⟩ :=
    exists_normalizedGradient_upper_uniformFlow g hu hreg hKb hBb hmax
  let ε := min (ε₁ / 2) (min (ε₂ / 2) ((b - a) / 3))
  have hε : 0 < ε := lt_min (half_pos hε₁) (lt_min (half_pos hε₂) (div_pos (sub_pos.mpr hab) (by norm_num)))
  have hεlo : ε < ε₁ := (min_le_left _ _).trans_lt (half_lt_self hε₁)
  have hεhi : ε < ε₂ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hε₂)
  have hgap : 2 * ε < b - a := by
    have hh : ε ≤ (b - a) / 3 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have htime₁ : Icc (0 : ℝ) ε ⊆ Ico 0 ε₁ := fun t ht ↦ ⟨ht.1, ht.2.trans_lt hεlo⟩
  have htime₂ : Icc (0 : ℝ) ε ⊆ Ico 0 ε₂ := fun t ht ↦ ⟨ht.1, ht.2.trans_lt hεhi⟩
  have hunit₁ := fun x ↦ mfderiv_normalizedGradient g u x (hreg x)
  have hunit₂ : ∀ x, mfderiv I 𝓘(ℝ) u x ((-normalizedGradient g u) x) = (-1 : ℝ) := by
    intro x
    rw [Pi.neg_apply, map_neg, mfderiv_normalizedGradient g u x (hreg x)]
    rfl
  have hv := contMDiff_normalizedGradient g u hu hreg
  have hinj₁ := injOn_integralCurveFamily_of_height hε₁ one_ne_zero (hu.mdifferentiable (by simp))
    (hv.of_le (by simp)) hunit₁ (fun x (hx : x ∈ u ⁻¹' {a}) ↦ (show u x = a from hx))
    (fun x hx ↦ hzero₁ x (hKU₁ hx)) (fun x hx ↦ hcurve₁ x (hKU₁ hx))
  have hinj₂ := injOn_integralCurveFamily_of_height hε₂ (neg_ne_zero.mpr one_ne_zero)
    (hu.mdifferentiable (by simp)) (hv.neg_section.of_le (by simp)) hunit₂
    (fun x (hx : x ∈ u ⁻¹' {b}) ↦ (show u x = b from hx))
    (fun x hx ↦ hzero₂ x (hKU₂ hx)) (fun x hx ↦ hcurve₂ x (hKU₂ hx))
  have hha : ∀ x ∈ u ⁻¹' {a}, ∀ t ∈ Icc 0 ε, u (Φ₁ (x, t)) = a + t := by
    intro x hx t ht
    simpa only [show u x = a from hx] using hheight₁ x (hKU₁ hx) t (htime₁ ht)
  have hhb : ∀ x ∈ u ⁻¹' {b}, ∀ t ∈ Icc 0 ε, u (Φ₂ (x, t)) = b - t := by
    intro x hx t ht
    simpa only [show u x = b from hx] using hheight₂ x (hKU₂ hx) t (htime₂ ht)
  refine ⟨ε, hε, hgap, U₁, U₂, hU₁, hU₂, hKU₁, hKU₂, Φ₁, Φ₂, hzero₁, hzero₂,
    hΦ₁.mono (prod_mono_right htime₁), hΦ₂.mono (prod_mono_right htime₂),
    (fun x hx ↦ (hcurve₁ x hx).mono htime₁), (fun x hx ↦ (hcurve₂ x hx).mono htime₂), hha, hhb,
    closedEmbedding_restrict_flow hKa hKU₁ hεlo hΦ₁.continuousOn hinj₁,
    closedEmbedding_restrict_flow hKb hKU₂ hεhi hΦ₂.continuousOn hinj₂, ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro q ⟨⟨x, t⟩, hx, rfl⟩ ⟨⟨y, s⟩, hy, heq⟩
    have hh := congrArg u heq
    rw [hha x hx.1 t hx.2, hhb y hy.1 s hy.2] at hh
    linarith [hx.2.2, hy.2.2]
  · exact fun x hx t ht ↦ hinside₁ x hx t ⟨ht.1, ht.2.trans_lt hεlo⟩
  · exact fun x hx t ht ↦ hinside₂ x hx t ⟨ht.1, ht.2.trans_lt hεhi⟩

end DifferentialGeometry.Geometry.Boundary
