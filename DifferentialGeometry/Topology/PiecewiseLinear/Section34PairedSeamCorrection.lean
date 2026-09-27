import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionComposition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RegularCircleCylinder

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCylindricalDiagram.exists_paired_seam_volume_correction
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {A B : Set E} {δ ε : ℝ → E}
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) A) (hε : IsPLHomeomorphOn ε (Icc 0 1) B)
    (hεzero : ε 0 = δ 0) (hεone : ε 1 = δ 1)
    (hcover : A ∪ B = (boundaryComplex 2 K).space) (hAB : A ∩ B = {δ 0, δ 1})
    {g : E × ℝ → F} {R : Set F} (hg : IsCylindricalDiagram g K.space R)
    (hends : ∀ p ∈ K.space, g (p, 0) = g (p, 1))
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hboundary : g '' ((boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) = L.space)
    {d₀ d₁ : ℝ} (hd₀ : 0 < d₀) (hd₁ : 0 < d₁)
    {ρ₀ ρ₁ : (Fin 3 → ℝ) × ℝ → F} {W₀ W₁ : Set F}
    (hρ₀ : IsPLHomeomorphOn ρ₀ (stdSimplexBoundary 2 ×ˢ Icc (-d₀) d₀) W₀)
    (hρ₁ : IsPLHomeomorphOn ρ₁ (stdSimplexBoundary 2 ×ˢ Icc (-d₁) d₁) W₁)
    (hW₀ : W₀ ⊆ L.space) (hW₁ : W₁ ⊆ L.space)
    (hzero₀ : ∀ t ∈ Icc (0 : ℝ) 1, ρ₀ (stdTriangleLoop t, 0) = g (δ 0, t))
    (hzero₁ : ∀ t ∈ Icc (0 : ℝ) 1, ρ₁ (stdTriangleLoop t, 0) = g (δ 1, t))
    (hpos₀ : ρ₀ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) d₀) ⊆
      g '' (A ×ˢ Icc (0 : ℝ) 1))
    (hneg₀ : ρ₀ '' (stdSimplexBoundary 2 ×ˢ Icc (-d₀) 0) ⊆
      g '' (B ×ˢ Icc (0 : ℝ) 1))
    (hpos₁ : ρ₁ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) d₁) ⊆
      g '' (A ×ˢ Icc (0 : ℝ) 1))
    (hneg₁ : ρ₁ '' (stdSimplexBoundary 2 ×ˢ Icc (-d₁) 0) ⊆
      g '' (B ×ˢ Icc (0 : ℝ) 1)) :
    ∃ (H : F → F) (κ : (Fin 3 → ℝ) × E → F) (θ₀ θ₁ : ℝ × ℝ → E)
      (e₀ e₁ : ℝ) (ν₀ ν₁ : (Fin 3 → ℝ) → (Fin 3 → ℝ)),
      IsPLHomeomorphOn H R R ∧ IsCylindricalDiagram (H ∘ g) K.space R ∧
      H '' (g '' (A ×ˢ Icc (0 : ℝ) 1)) = g '' (A ×ˢ Icc (0 : ℝ) 1) ∧
      H '' (g '' (B ×ˢ Icc (0 : ℝ) 1)) = g '' (B ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ p ∈ K.space, ∀ t ∈ Icc (0 : ℝ) 1, κ (stdTriangleLoop t, p) = g (p, t)) ∧
      IsPLHomeomorphOn θ₀ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) K.space ∧
      IsPLHomeomorphOn θ₁ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) K.space ∧
      θ₀ (1 / 2, 0) = δ 0 ∧ θ₁ (1 / 2, 0) = δ 1 ∧
      0 < e₀ ∧ e₀ ≤ d₀ ∧ e₀ ≤ 1 ∧ 0 < e₁ ∧ e₁ ≤ d₁ ∧ e₁ ≤ 1 ∧
      IsPLHomeomorphOn ν₀ (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
      IsPLHomeomorphOn ν₁ (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
      (∀ z ∈ stdSimplexBoundary 2, ∀ t ∈ Icc (-e₀) e₀,
        H (κ (z, θ₀ (t / 2 + 1 / 2, 0))) = ρ₀ (ν₀ z, t)) ∧
      ∀ z ∈ stdSimplexBoundary 2, ∀ t ∈ Icc (-e₁) e₁,
        H (κ (z, θ₁ (t / 2 + 1 / 2, 0))) = ρ₁ (ν₁ z, t) := by
  obtain ⟨θ₀, r₀, s₀, c₀, H₀, κ₀, μ₀, hθ₀, hθ₀zero, hr₀, hs₀, hθ₀one, -, hc₀,
    hc₀d, hc₀1, hH₀, hH₀A, hH₀B, hκ₀, hmatch₀, hμ₀, hact₀⟩ :=
    hg.exists_one_seam_volume_correction K hK hδ hε hεzero hεone hcover hAB hends L hL
      hboundary hd₀ hρ₀ hW₀ hzero₀ hpos₀ hneg₀
  have hδK (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : δ t ∈ K.space :=
    boundaryComplex_space_subset 2 K
      (hcover.subset (Or.inl (hδ.bijOn.mapsTo ht)))
  have hother : δ 1 ∈ θ₀ '' ({r₀} ×ˢ Icc (s₀ / 2) ((s₀ + 1) / 2)) := by
    refine ⟨(r₀, s₀), ⟨rfl, ?_⟩, hθ₀one⟩
    constructor <;> linarith [hs₀.1, hs₀.2]
  have hρ₁core (z : Fin 3 → ℝ) (hz : z ∈ stdSimplexBoundary 2) :
      ρ₁ (z, 0) = κ₀ (z, δ 1) := by
    obtain ⟨t, ht, rfl⟩ := stdTriangleLoop_image.symm.subset hz
    rw [hzero₁ t ht, hκ₀ (δ 1) (hδK 1 (by norm_num)) t ht]
  let g₁ := H₀ ∘ g
  let ρ₁' := ρ₁ ∘ Prod.map μ₀ id
  let δ' := fun t : ℝ => δ (1 - t)
  let ε' := fun t : ℝ => ε (1 - t)
  have hg₁ : IsCylindricalDiagram g₁ K.space R := hg.postcomp_equivalence hH₀
  have hends₁ (p) (hp : p ∈ K.space) : g₁ (p, 0) = g₁ (p, 1) :=
    congrArg H₀ (hends p hp)
  have hfaces : L.space = g '' (A ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (B ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hboundary, ← hcover, union_prod, image_union]
  have hH₀L : H₀ '' L.space = L.space := by rw [hfaces, image_union, hH₀A, hH₀B]
  have hboundary₁ : g₁ '' ((boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) = L.space := by
    rw [show g₁ = H₀ ∘ g from rfl, image_comp, hboundary, hH₀L]
  have hρ₁' : IsPLHomeomorphOn ρ₁' (stdSimplexBoundary 2 ×ˢ Icc (-d₁) d₁) W₁ :=
    (hμ₀.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hρ₁
  have hzero₁' (t) (ht : t ∈ Icc (0 : ℝ) 1) :
      ρ₁' (stdTriangleLoop t, 0) = g₁ (δ' 0, t) := by
    have hz := stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop ht)
    change ρ₁ (μ₀ (stdTriangleLoop t), 0) = H₀ (g (δ (1 - 0), t))
    rw [sub_zero, hρ₁core _ (hμ₀.bijOn.mapsTo hz), ← hact₀ _ hz _ hother,
      hκ₀ (δ 1) (hδK 1 (by norm_num)) t ht]
  have hstrip (I : Set ℝ) : ρ₁' '' (stdSimplexBoundary 2 ×ˢ I) =
      ρ₁ '' (stdSimplexBoundary 2 ×ˢ I) := by
    rw [show ρ₁' = ρ₁ ∘ Prod.map μ₀ id from rfl, image_comp, prodMap_image_prod,
      hμ₀.image_eq, image_id]
  have hpos₁' : ρ₁' '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) d₁) ⊆
      g₁ '' (A ×ˢ Icc (0 : ℝ) 1) := by
    rw [hstrip, show g₁ = H₀ ∘ g from rfl, image_comp, hH₀A]
    exact hpos₁
  have hneg₁' : ρ₁' '' (stdSimplexBoundary 2 ×ˢ Icc (-d₁) 0) ⊆
      g₁ '' (B ×ˢ Icc (0 : ℝ) 1) := by
    rw [hstrip, show g₁ = H₀ ∘ g from rfl, image_comp, hH₀B]
    exact hneg₁
  have hεzero' : ε' 0 = δ' 0 := by simpa only [ε', δ', sub_zero] using hεone
  have hεone' : ε' 1 = δ' 1 := by simpa only [ε', δ', sub_self] using hεzero
  have hAB' : A ∩ B = {δ' 0, δ' 1} := by
    simpa only [δ', sub_zero, sub_self, pair_comm] using hAB
  obtain ⟨θ₁, r₁, s₁, c₁, H₁, κ₁, μ₁, hθ₁, hθ₁zero, -, -, -, hN₁, hc₁,
    hc₁d, hc₁1, hH₁, hH₁A, hH₁B, hκ₁, hmatch₁, hμ₁, hact₁⟩ :=
    hg₁.exists_one_seam_volume_correction K hK (isPLHomeomorphOn_comp_one_sub hδ)
      (isPLHomeomorphOn_comp_one_sub hε) hεzero' hεone' hcover hAB' hends₁ L hL
      hboundary₁ hd₁ hρ₁' hW₁ hzero₁' hpos₁' hneg₁'
  have hκeq (z) (hz : z ∈ stdSimplexBoundary 2) (p) (hp : p ∈ K.space) :
      κ₁ (z, p) = H₀ (κ₀ (z, p)) := by
    obtain ⟨t, ht, rfl⟩ := stdTriangleLoop_image.symm.subset hz
    rw [hκ₁ p hp t ht, hκ₀ p hp t ht]
    rfl
  let γ := fun t : ℝ => θ₀ (t / 2 + 1 / 2, 0)
  have hpath (t) (ht : t ∈ Icc (-c₀) c₀) :
      (t / 2 + 1 / 2, (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    refine ⟨?_, by norm_num⟩
    constructor <;> linarith [ht.1, ht.2]
  have hγcont : ContinuousOn γ (Icc (-c₀) c₀) :=
    hθ₀.isPiecewiseAffineOn.continuousOn.comp (by fun_prop) hpath
  have hθ₀bd : θ₀ '' frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) =
      (boundaryComplex 2 K).space := by
    obtain ⟨q, hq⟩ := isPLBall_unit_square
    rw [← hq.image_stdSimplexBoundary_eq_frontier_real_prod, ← image_comp]
    exact (hq.trans hθ₀).image_stdSimplexBoundary_eq_boundaryComplex K rfl
  have hγB : MapsTo γ (Icc (-c₀) c₀) (boundaryComplex 2 K).space := by
    intro t ht
    apply hθ₀bd.subset
    refine ⟨(t / 2 + 1 / 2, 0), ?_, rfl⟩
    rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc (zero_le_one' ℝ)]
    exact Or.inl ⟨(hpath t ht).1, by simp⟩
  let N := θ₁ '' ({r₁} ×ˢ Icc (s₁ / 2) ((s₁ + 1) / 2)) ∩ (boundaryComplex 2 K).space
  have hN : N ∈ 𝓝[(boundaryComplex 2 K).space] (γ 0) := by
    have hcore : γ 0 = δ 0 := by simpa only [γ, zero_div, zero_add] using hθ₀zero
    rw [hcore]
    exact Filter.inter_mem (by simpa only [δ', sub_self] using hN₁) self_mem_nhdsWithin
  have hρ₀short := hρ₀.restrict
    (isPolyhedron_stdSimplexBoundary_two.prod isHPolytope_Icc.isPolyhedron)
    (prod_mono_right (Icc_subset_Icc (neg_le_neg hc₀d) hc₀d))
  obtain ⟨e₀, he₀, he₀c, hH, -, hmatch, -⟩ :=
    exists_short_seam_matching_after_uniform_circle_correction hc₀
      (hγcont 0 (by constructor <;> linarith)) hγB hN hH₀ hH₁ hμ₁ hρ₀short hmatch₀
      (by
        intro z hz p hp
        have hpK := boundaryComplex_space_subset 2 K hp.2
        rw [← hκeq z hz p hpK, hact₁ z hz p hp.1,
          hκeq (μ₁ z) (hμ₁.bijOn.mapsTo hz) p hpK])
  have hθ₁core : θ₁ (1 / 2, 0) = δ 1 := by
    simpa only [δ', sub_zero] using hθ₁zero
  refine ⟨H₁ ∘ H₀, κ₀, θ₀, θ₁, e₀, c₁, μ₁, μ₀, hH,
    hg.postcomp_equivalence hH, ?_, ?_, hκ₀, hθ₀, hθ₁, hθ₀zero, hθ₁core,
    he₀, he₀c.trans hc₀d, he₀c.trans hc₀1, hc₁, hc₁d, hc₁1, hμ₁, hμ₀, hmatch, ?_⟩
  · rw [image_comp, hH₀A]
    simpa only [g₁, image_comp, hH₀A] using hH₁A
  · rw [image_comp, hH₀B]
    simpa only [g₁, image_comp, hH₀B] using hH₁B
  · intro z hz t ht
    have htQ : (t / 2 + 1 / 2, (0 : ℝ)) ∈
        Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
      refine ⟨?_, by norm_num⟩
      constructor <;> linarith [ht.1, ht.2]
    change H₁ (H₀ (κ₀ (z, θ₁ (t / 2 + 1 / 2, 0)))) = ρ₁ (μ₀ z, t)
    rw [← hκeq z hz _ (hθ₁.bijOn.mapsTo htQ)]
    exact hmatch₁ z hz t ht

end DifferentialGeometry.Topology.PiecewiseLinear
