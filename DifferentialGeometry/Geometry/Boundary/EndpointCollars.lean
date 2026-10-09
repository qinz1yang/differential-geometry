import DifferentialGeometry.Geometry.Boundary.UniformCollar
import DifferentialGeometry.Geometry.Boundary.EndpointStrips
import DifferentialGeometry.Geometry.Boundary.LevelComponents

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Gradient DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I]
  [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
omit [T2Space M] in
private theorem collar_of_embedded_flow
    {K : Set (BoundaryManifold I M)} {S U : Set M} {τ : ℝ} {Φ : M × ℝ → M}
    {v : (x : M) → TangentSpace I x}
    (hK : IsCompact K) (hKo : IsOpen K) (hKne : K.Nonempty) (hτ : 0 < τ)
    (hKS : ∀ x ∈ K, x.1 ∈ S) (hSU : S ⊆ U)
    (hzero : ∀ y ∈ U, Φ (y, 0) = y)
    (hΦ : ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (U ×ˢ Icc 0 τ))
    (hcurve : ∀ y ∈ U, IsMIntegralCurveOn (fun t ↦ Φ (y, t)) v (Icc 0 τ))
    (hembed : IsClosedEmbedding (fun z : S × Icc (0 : ℝ) τ ↦ Φ (z.1.1, z.2.1)))
    (hinward : ∀ x ∈ K, ∃ (w : TangentSpace hI.boundaryI x) (c : ℝ), 0 < c ∧
      v x.1 = boundaryInclusionMfderiv x w + c • inwardCoord x) :
    ∃ ε > 0, ε < τ ∧
      ∃ d : PartialDiffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I
          (BoundaryManifold I M × EuclideanHalfSpace 1) M ∞,
        d.source = K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ε} ∧
        (∀ z, d z = Φ (z.1.1, z.2.1 0)) ∧ (Subtype.val '' K) ⊆ d.target := by
  let φ : BoundaryManifold I M × ℝ → M := fun z ↦ Φ (z.1.1, z.2)
  have hφ : ContMDiffOn (hI.boundaryI.prod 𝓘(ℝ)) I ∞ φ (K ×ˢ Icc 0 τ) :=
    hΦ.comp ((boundaryInclusion_contMDiff.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
      (fun z hz ↦ ⟨hSU (hKS z.1 hz.1), hz.2⟩)
  apply exists_uniform_collar_of_one_sided hK hKo hKne hτ hφ
    (fun y hy ↦ hzero y.1 (hSU (hKS y hy)))
  · intro z hz w hw heq
    have hh := hembed.injective (a₁ := (⟨z.1.1, hKS z.1 hz.1⟩, ⟨z.2, hz.2⟩))
      (a₂ := (⟨w.1.1, hKS w.1 hw.1⟩, ⟨w.2, hw.2⟩)) heq
    exact Prod.ext (Subtype.ext (congrArg (fun q : S × Icc (0 : ℝ) τ ↦ q.1.1) hh))
      (congrArg (fun q : S × Icc (0 : ℝ) τ ↦ q.2.1) hh)
  · intro x hx
    refine ⟨v x.1, ?_, hinward x hx⟩
    have hh := hcurve x.1 (hSU (hKS x hx)) 0 ⟨le_rfl, hτ.le⟩
    apply hh.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change ℝ at a
    change a • v (Φ (x.1, 0)) = a • v x.1
    rw [hzero x.1 (hSU (hKS x hx))]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem restrict_collar
    {K : Set (BoundaryManifold I M)} {δ ε : ℝ}
    (hKo : IsOpen K) (hKne : K.Nonempty) (hεδ : ε ≤ δ)
    (d : PartialDiffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I
      (BoundaryManifold I M × EuclideanHalfSpace 1) M ∞)
    (hd : d.source = K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < δ}) :
    ∃ c : PartialDiffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I
        (BoundaryManifold I M × EuclideanHalfSpace 1) M ∞,
      c.source = K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ε} ∧
      (c : BoundaryManifold I M × EuclideanHalfSpace 1 → M) = d := by
  let A := K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ε}
  have hA : IsOpen A := hKo.prod
    (isOpen_lt ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val) continuous_const)
  have hAd : A ⊆ d.source := by
    rw [hd]
    exact fun z hz ↦ ⟨hz.1, hz.2.trans_le hεδ⟩
  let : Nonempty (BoundaryManifold I M × EuclideanHalfSpace 1) := ⟨hKne.choose, 0⟩
  obtain ⟨c, hc, _, heq⟩ := exists_partialDiffeomorph_of_injOn hA
    (show IsLocalDiffeomorphOn (hI.boundaryI.prod (𝓡∂ 1)) I ∞ d A from
      fun z ↦ ⟨d, hAd z.2, eqOn_refl _ _⟩)
    (d.toOpenPartialHomeomorph.injOn.mono hAd)
  exact ⟨c, hc, heq⟩

set_option backward.isDefEq.respectTransparency false in
theorem exists_disjoint_adapted_endpoint_collars [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (ha : a ∈ range u) (hb : b ∈ range u) :
    ∃ ε > 0, 2 * ε < b - a ∧
      ∃ c₀ c₁ : PartialDiffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I
          (BoundaryManifold I M × EuclideanHalfSpace 1) M ∞,
        c₀.source = {x : BoundaryManifold I M | u x.1 = a} ×ˢ
          {t : EuclideanHalfSpace 1 | t.1 0 < ε} ∧
        c₁.source = {x : BoundaryManifold I M | u x.1 = b} ×ˢ
          {t : EuclideanHalfSpace 1 | t.1 0 < ε} ∧
        (∀ x : BoundaryManifold I M, u x.1 = a → c₀ (x, 0) = x.1) ∧
        (∀ x : BoundaryManifold I M, u x.1 = b → c₁ (x, 0) = x.1) ∧
        (∀ z ∈ c₀.source, u (c₀ z) = a + z.2.1 0) ∧
        (∀ z ∈ c₁.source, u (c₁ z) = b - z.2.1 0) ∧
        u ⁻¹' {a} ⊆ c₀.target ∧ u ⁻¹' {b} ⊆ c₁.target ∧
        Disjoint c₀.target c₁.target ∧
        (∀ z ∈ c₀.source, 0 < z.2.1 0 → I.IsInteriorPoint (c₀ z)) ∧
        ∀ z ∈ c₁.source, 0 < z.2.1 0 → I.IsInteriorPoint (c₁ z) := by
  have hbounds := fun x ↦ range_subset_Icc_of_boundary_values hab.le hreg hboundary (mem_range_self x)
  have hmin : ∀ x, u x = a → IsLocalMin u x := fun x hx ↦
    Eventually.of_forall (fun y ↦ by simpa only [hx] using (hbounds y).1)
  have hmax : ∀ x, u x = b → IsLocalMax u x := fun x hx ↦
    Eventually.of_forall (fun y ↦ by simpa only [hx] using (hbounds y).2)
  let K₀ := {x : BoundaryManifold I M | u x.1 = a}
  let K₁ := {x : BoundaryManifold I M | u x.1 = b}
  have hK₀cl := isClopen_boundary_level_of_two_values (I := I) hab.ne hu.continuous hboundary
  have hK₁cl := isClopen_boundary_level_of_two_values (I := I) hab.ne.symm hu.continuous
    (fun x hx ↦ (hboundary x hx).symm)
  let : CompactSpace (BoundaryManifold I M) :=
    isCompact_iff_compactSpace.mp ((I.isClosed_boundary (M := M) (n := ∞) (by simp)).isCompact)
  have hK₀ne : K₀.Nonempty := by
    obtain ⟨x, hx⟩ := ha
    exact ⟨⟨x, isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero (hmin x hx) (hreg x)⟩, hx⟩
  have hK₁ne : K₁.Nonempty := by
    obtain ⟨x, hx⟩ := hb
    exact ⟨⟨x, isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero (hmax x hx) (hreg x)⟩, hx⟩
  obtain ⟨τ, hτ, hgap, U₀, U₁, _, _, hSU₀, hSU₁, Φ₀, Φ₁, hzero₀, hzero₁,
    hΦ₀, hΦ₁, hcurve₀, hcurve₁, hheight₀, hheight₁, hembed₀, hembed₁, _, hinside₀, hinside₁⟩ :=
    exists_disjoint_adapted_endpoint_strips g hab hu hreg hboundary
  have hin₀ : ∀ x ∈ K₀, ∃ (w : TangentSpace hI.boundaryI x) (c : ℝ), 0 < c ∧
      normalizedGradient g u x.1 = boundaryInclusionMfderiv x w + c • inwardCoord x := by
    intro x hx
    apply (exists_pos_inward_decomposition_iff g x _).2
    exact normalizedGradient_inner_outwardNormal_neg_of_isLocalMin g (hmin x.1 hx)
      (hu.mdifferentiableAt (by simp)) (hreg x.1)
  have hin₁ : ∀ x ∈ K₁, ∃ (w : TangentSpace hI.boundaryI x) (c : ℝ), 0 < c ∧
      (-normalizedGradient g u) x.1 = boundaryInclusionMfderiv x w + c • inwardCoord x := by
    intro x hx
    apply (exists_pos_inward_decomposition_iff g x _).2
    rw [Pi.neg_apply, map_neg, neg_apply]
    exact neg_neg_of_pos (normalizedGradient_inner_outwardNormal_pos_of_isLocalMax g (hmax x.1 hx)
      (hu.mdifferentiableAt (by simp)) (hreg x.1))
  obtain ⟨δ₀, hδ₀, hδ₀τ, d₀, hd₀, heq₀, _⟩ := collar_of_embedded_flow
    hK₀cl.isClosed.isCompact hK₀cl.isOpen hK₀ne hτ (fun _ hx ↦ hx) hSU₀
    hzero₀ hΦ₀ hcurve₀ hembed₀ hin₀
  obtain ⟨δ₁, hδ₁, hδ₁τ, d₁, hd₁, heq₁, _⟩ := collar_of_embedded_flow
    hK₁cl.isClosed.isCompact hK₁cl.isOpen hK₁ne hτ (fun _ hx ↦ hx) hSU₁
    hzero₁ hΦ₁ hcurve₁ hembed₁ hin₁
  let ε := min δ₀ δ₁
  have hε : 0 < ε := lt_min hδ₀ hδ₁
  have hετ : ε < τ := (min_le_left _ _).trans_lt hδ₀τ
  obtain ⟨c₀, hc₀, hcd₀⟩ := restrict_collar hK₀cl.isOpen hK₀ne (min_le_left δ₀ δ₁) d₀ hd₀
  obtain ⟨c₁, hc₁, hcd₁⟩ := restrict_collar hK₁cl.isOpen hK₁ne (min_le_right δ₀ δ₁) d₁ hd₁
  have hcΦ₀ : ∀ z, c₀ z = Φ₀ (z.1.1, z.2.1 0) := fun z ↦ (congrFun hcd₀ z).trans (heq₀ z)
  have hcΦ₁ : ∀ z, c₁ z = Φ₁ (z.1.1, z.2.1 0) := fun z ↦ (congrFun hcd₁ z).trans (heq₁ z)
  have ht₀ : ∀ z ∈ c₀.source, u z.1.1 = a ∧ z.2.1 0 ∈ Icc 0 τ := by
    intro z hz
    rw [hc₀] at hz
    exact ⟨hz.1, z.2.2, hz.2.le.trans hετ.le⟩
  have ht₁ : ∀ z ∈ c₁.source, u z.1.1 = b ∧ z.2.1 0 ∈ Icc 0 τ := by
    intro z hz
    rw [hc₁] at hz
    exact ⟨hz.1, z.2.2, hz.2.le.trans hετ.le⟩
  have hz₀ : ∀ x : BoundaryManifold I M, u x.1 = a → c₀ (x, 0) = x.1 := by
    intro x hx
    rw [hcΦ₀]
    exact hzero₀ x.1 (hSU₀ hx)
  have hz₁ : ∀ x : BoundaryManifold I M, u x.1 = b → c₁ (x, 0) = x.1 := by
    intro x hx
    rw [hcΦ₁]
    exact hzero₁ x.1 (hSU₁ hx)
  have hh₀ : ∀ z ∈ c₀.source, u (c₀ z) = a + z.2.1 0 := by
    intro z hz
    rw [hcΦ₀]
    exact hheight₀ z.1.1 (ht₀ z hz).1 _ (ht₀ z hz).2
  have hh₁ : ∀ z ∈ c₁.source, u (c₁ z) = b - z.2.1 0 := by
    intro z hz
    rw [hcΦ₁]
    exact hheight₁ z.1.1 (ht₁ z hz).1 _ (ht₁ z hz).2
  refine ⟨ε, hε, (by linarith), c₀, c₁, hc₀, hc₁, hz₀, hz₁, hh₀, hh₁, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    let y : BoundaryManifold I M :=
      ⟨x, isBoundaryPoint_of_isLocalMin_of_mfderiv_ne_zero (hmin x hx) (hreg x)⟩
    have hy : (y, (0 : EuclideanHalfSpace 1)) ∈ c₀.source := by rw [hc₀]; exact ⟨hx, hε⟩
    have hh := c₀.toOpenPartialHomeomorph.map_source hy
    change c₀ (y, 0) ∈ c₀.target at hh
    rwa [hz₀ y hx] at hh
  · intro x hx
    let y : BoundaryManifold I M :=
      ⟨x, isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero (hmax x hx) (hreg x)⟩
    have hy : (y, (0 : EuclideanHalfSpace 1)) ∈ c₁.source := by rw [hc₁]; exact ⟨hx, hε⟩
    have hh := c₁.toOpenPartialHomeomorph.map_source hy
    change c₁ (y, 0) ∈ c₁.target at hh
    rwa [hz₁ y hx] at hh
  · apply disjoint_left.mpr
    intro y hy₀ hy₁
    have hs₀ := c₀.toOpenPartialHomeomorph.map_target hy₀
    have hs₁ := c₁.toOpenPartialHomeomorph.map_target hy₁
    have hh0 := hh₀ (c₀.symm y) hs₀
    have hh1 := hh₁ (c₁.symm y) hs₁
    have hright₀ : c₀ (c₀.symm y) = y := c₀.toOpenPartialHomeomorph.right_inv hy₀
    have hright₁ : c₁ (c₁.symm y) = y := c₁.toOpenPartialHomeomorph.right_inv hy₁
    rw [hright₀] at hh0
    rw [hright₁] at hh1
    have htime₀ := (ht₀ _ hs₀).2.2
    have htime₁ := (ht₁ _ hs₁).2.2
    change (c₀.symm y).2.1 0 ≤ τ at htime₀
    change (c₁.symm y).2.1 0 ≤ τ at htime₁
    linarith
  · intro z hz ht
    rw [hcΦ₀]
    exact hinside₀ z.1.1 (hSU₀ (ht₀ z hz).1) _ ⟨ht, (ht₀ z hz).2.2⟩
  · intro z hz ht
    rw [hcΦ₁]
    exact hinside₁ z.1.1 (hSU₁ (ht₁ z hz).1) _ ⟨ht, (ht₁ z hz).2.2⟩

end DifferentialGeometry.Geometry.Boundary
