import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionFromSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionBaseSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionFacePreservation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionConjugacy
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionFaceCoordinates

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCylindricalDiagram.exists_one_seam_volume_correction
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
    {d : ℝ} (hd : 0 < d) {ρ : (Fin 3 → ℝ) × ℝ → F} {W : Set F}
    (hρ : IsPLHomeomorphOn ρ (stdSimplexBoundary 2 ×ˢ Icc (-d) d) W)
    (hWL : W ⊆ L.space)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ρ (stdTriangleLoop t, 0) = g (δ 0, t))
    (hpos : ρ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) d) ⊆
      g '' (A ×ˢ Icc (0 : ℝ) 1))
    (hneg : ρ '' (stdSimplexBoundary 2 ×ˢ Icc (-d) 0) ⊆
      g '' (B ×ˢ Icc (0 : ℝ) 1)) :
    ∃ (θ : ℝ × ℝ → E) (r s e : ℝ) (H : F → F)
      (κ : (Fin 3 → ℝ) × E → F) (ν : (Fin 3 → ℝ) → (Fin 3 → ℝ)),
      IsPLHomeomorphOn θ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) K.space ∧
      θ (1 / 2, 0) = δ 0 ∧ r ∈ ({0, 1} : Set ℝ) ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      θ (r, s) = δ 1 ∧
      θ '' ({r} ×ˢ Icc (s / 2) ((s + 1) / 2)) ∈
        𝓝[(boundaryComplex 2 K).space] (δ 1) ∧
      0 < e ∧ e ≤ d ∧ e ≤ 1 ∧ IsPLHomeomorphOn H R R ∧
      H '' (g '' (A ×ˢ Icc (0 : ℝ) 1)) = g '' (A ×ˢ Icc (0 : ℝ) 1) ∧
      H '' (g '' (B ×ˢ Icc (0 : ℝ) 1)) = g '' (B ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ p ∈ K.space, ∀ t ∈ Icc (0 : ℝ) 1, κ (stdTriangleLoop t, p) = g (p, t)) ∧
      (∀ z ∈ stdSimplexBoundary 2, ∀ t ∈ Icc (-e) e,
        H (κ (z, θ (t / 2 + 1 / 2, 0))) = ρ (z, t)) ∧
      IsPLHomeomorphOn ν (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
      ∀ z ∈ stdSimplexBoundary 2,
        ∀ p ∈ θ '' ({r} ×ˢ Icc (s / 2) ((s + 1) / 2)),
          H (κ (z, p)) = κ (ν z, p) := by
  obtain ⟨θ, r, s, hθ, hθcore, hθbot, hθneg, hθpos, hθtop, -, -, hr, hs,
    hθother, hotherN⟩ := exists_seam_correction_rectangle K hK hδ hε hεzero hεone
      hcover hAB
  let Q := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hθbd : θ '' frontier Q = (boundaryComplex 2 K).space := by
    obtain ⟨q, hq⟩ := isPLBall_unit_square
    rw [← hq.image_stdSimplexBoundary_eq_frontier_real_prod, ← image_comp]
    exact (hq.trans hθ).image_stdSimplexBoundary_eq_boundaryComplex K rfl
  have hAbd : A ⊆ (boundaryComplex 2 K).space := hcover ▸ subset_union_left
  have hBbd : B ⊆ (boundaryComplex 2 K).space := hcover ▸ subset_union_right
  have hAK := hAbd.trans (boundaryComplex_space_subset 2 K)
  have hBK := hBbd.trans (boundaryComplex_space_subset 2 K)
  have hsmall : Icc (0 : ℝ) (1 / 4) ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hbotK : θ '' (Icc (0 : ℝ) 1 ×ˢ {0}) ⊆ K.space := by
    exact (image_mono (prod_mono_right (by norm_num : ({0} : Set ℝ) ⊆ Icc 0 1))).trans
      hθ.image_eq.subset
  have hbotbd : θ '' (Icc (0 : ℝ) 1 ×ˢ {0}) ⊆ (boundaryComplex 2 K).space := by
    rw [hθbot]
    exact union_subset ((image_mono hsmall).trans (hε.image_eq.subset.trans hBbd))
      ((image_mono hsmall).trans (hδ.image_eq.subset.trans hAbd))
  let f := g ∘ Prod.map θ id
  have hf : IsCylindricalDiagram f Q R := hg.precomp_base_equivalence hθ
  have hfends (p) (hp : p ∈ Q) : f (p, 0) = f (p, 1) :=
    hends (θ p) (hθ.bijOn.mapsTo hp)
  have himage (V : Set (ℝ × ℝ)) : f '' (V ×ˢ Icc (0 : ℝ) 1) =
      g '' ((θ '' V) ×ˢ Icc (0 : ℝ) 1) := by
    rw [show f = g ∘ Prod.map θ id from rfl, image_comp, prodMap_image_prod, image_id]
  have hAL : f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1) ⊆ L.space := by
    rw [himage]
    exact (image_mono (prod_mono_left hbotbd)).trans hboundary.subset
  obtain ⟨hbaseA, hbaseB, -⟩ := inter_initial_arcs_of_common_ends hδ hε
    hεzero hεone hAB
  have hAP : (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) ∩
      (g '' (A ×ˢ Icc (0 : ℝ) 1)) =
        f '' ((Icc (1 / 2 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1) := by
    rw [himage, himage, hg.inter_images_base_regions hends hbotK hAK,
      hθbot, hθpos, hbaseA]
  have hAN : (f '' ((Icc (0 : ℝ) 1 ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1)) ∩
      (g '' (B ×ˢ Icc (0 : ℝ) 1)) =
        f '' ((Icc (0 : ℝ) (1 / 2) ×ˢ {0}) ×ˢ Icc (0 : ℝ) 1) := by
    rw [himage, himage, hg.inter_images_base_regions hends hbotK hBK,
      hθbot, hθneg, hbaseB]
  obtain ⟨e, H, σ, ψ, ν, he, hed, he1, hH, hσ, hσf, hψ, hconj,
    hHneg, hHpos, hmatch, hν⟩ :=
    hf.exists_seam_volume_correction_of_surface_sides hfends L hL hAL hd hρ hWL
      (by
        intro t ht
        change ρ (stdTriangleLoop t, 0) = g (θ (1 / 2, 0), t)
        rw [hθcore]
        exact hzero t ht) hpos hneg hAP hAN
  have hleft : Icc (0 : ℝ) (1 / 2) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc le_rfl (by norm_num)
  have hright : Icc (1 / 2 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (by norm_num) le_rfl
  have hψneg := hσ.image_circle_region_of_preserved_bottom_annulus hσf hψ hconj
    hleft hHneg
  have hψpos := hσ.image_circle_region_of_preserved_bottom_annulus hσf hψ hconj
    hright hHpos
  have hψrim (q : ℝ) (hq : q ∈ ({0, 1} : Set ℝ)) :
      ψ '' (stdSimplexBoundary 2 ×ˢ {q}) = stdSimplexBoundary 2 ×ˢ {q} := by
    conv_lhs => rw [prod_singleton, image_image]
    calc
      (fun z => ψ (z, q)) '' stdSimplexBoundary 2 =
          (fun z => (ν q z, q)) '' stdSimplexBoundary 2 := image_congr (hν q hq).2.1
      _ = stdSimplexBoundary 2 ×ˢ {q} := by
        rw [show (fun z => (ν q z, q)) = (fun z => (z, q)) ∘ ν q from rfl,
          image_comp, (hν q hq).1.image_eq, ← prod_singleton]
  obtain ⟨hUA, hVB, hUbot, hVbot, hUtop, hVtop⟩ := hθ.seam_face_coordinates
    (hθbd.trans hcover.symm) hδ hε hεzero hεone hAB hθbot hθneg hθpos hθtop
  have hfaceA := image_square_face_eq_of_annulus_product_conjugacy hσf hconj
    hψ.image_eq hψrim hright hψpos inter_subset_left hUbot (Or.inl hUtop)
  have hfaceB := image_square_face_eq_of_annulus_product_conjugacy hσf hconj
    hψ.image_eq hψrim hleft hψneg inter_subset_left hVbot (Or.inr hVtop)
  rw [himage, hUA] at hfaceA
  rw [himage, hVB] at hfaceB
  let κ : (Fin 3 → ℝ) × E → F := fun z =>
    σ ((z.1, (Function.invFunOn θ Q z.2).1), (Function.invFunOn θ Q z.2).2)
  have hκθ (z : Fin 3 → ℝ) (p : ℝ × ℝ) (hp : p ∈ Q) :
      κ (z, θ p) = σ ((z, p.1), p.2) := by
    change σ ((z, (Function.invFunOn θ Q (θ p)).1),
      (Function.invFunOn θ Q (θ p)).2) = _
    rw [hθ.bijOn.invOn_invFunOn.1 hp]
  have hκg (p) (hp : p ∈ K.space) (t) (ht : t ∈ Icc (0 : ℝ) 1) :
      κ (stdTriangleLoop t, p) = g (p, t) := by
    obtain ⟨q, hq, rfl⟩ := hθ.bijOn.surjOn hp
    rw [hκθ _ q hq, hσf q.1 hq.1 q.2 hq.2 t ht]
    rfl
  refine ⟨θ, r, s, e, H, κ, ν r, hθ, hθcore, hr, hs, hθother, hotherN,
    he, hed, he1, hH, ?_, ?_, hκg, ?_, (hν r hr).1, ?_⟩
  · exact hfaceA
  · exact hfaceB
  · intro z hz t ht
    obtain ⟨q, hq, rfl⟩ := stdTriangleLoop_image.symm.subset hz
    have hp : (t / 2 + 1 / 2, (0 : ℝ)) ∈ Q := by
      constructor
      · constructor <;> linarith [ht.1, ht.2, he1]
      · norm_num
    rw [hκg _ (hθ.bijOn.mapsTo hp) q hq]
    exact hmatch t ht q hq
  · intro z hz p hp
    obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := hp
    have hur : u = r := hu
    subst u
    have hrI : r ∈ Icc (0 : ℝ) 1 := by rcases hr with rfl | rfl <;> norm_num
    have hvI : v ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hv.1, hv.2, hs.1, hs.2]
    rw [hκθ z (r, v) ⟨hrI, hvI⟩, hκθ (ν r z) (r, v) ⟨hrI, hvI⟩]
    exact (hν r hr).2.2 z hz v hvI

end DifferentialGeometry.Topology.PiecewiseLinear
