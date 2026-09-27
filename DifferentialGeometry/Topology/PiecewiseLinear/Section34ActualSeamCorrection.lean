import DifferentialGeometry.Topology.PiecewiseLinear.Section34PairedSeamCorrection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingCornerBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingFaceAnnuli

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_actual_paired_seam_correction
    {M : Type*} {P : Set (EuclideanSpace ℝ (Fin 3))}
    {u : EuclideanSpace ℝ (Fin 3) → M} (hu : InjOn u P)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hRP : R.space ⊆ P)
    {g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hg : IsCylindricalDiagram g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R.space)
    (hends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (p, 0) = g (p, 1))
    (hside : frontier R.space =
      g '' (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1))
    {As Bs F D : Set M} (hfirst : As ∩ u '' R.space = F)
    (hsecond : Bs ∩ u '' R.space = D)
    {a : Fin 2 → ℝ × ℝ} {A₀ A₁ : Set (ℝ × ℝ)} {δ₀ δ₁ : ℝ → ℝ × ℝ}
    (hδ₀ : IsPLHomeomorphOn δ₀ (Icc 0 1) A₀)
    (hδ₁ : IsPLHomeomorphOn δ₁ (Icc 0 1) A₁)
    (hδ₀₀ : δ₀ 0 = a 0) (hδ₀₁ : δ₀ 1 = a 1)
    (hδ₁₀ : δ₁ 0 = a 0) (hδ₁₁ : δ₁ 1 = a 1)
    (hcover : A₀ ∪ A₁ = frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hinter : A₀ ∩ A₁ = {a 0, a 1})
    (hface₀ : (u ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F)
    (hface₁ : (u ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D)
    {J : Fin 2 → Set M}
    (hPg : ∀ k, (u ∘ g) '' ({a k} ×ˢ Icc (0 : ℝ) 1) = J k)
    {C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3))}
    {f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hCP : ∀ k, C k ⊆ P) (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k))
    (hfends : ∀ k p, p ∈ spliceSquare → f k (p, 0) = f k (p, 1))
    (haxis : ∀ k, u '' (f k '' section34MarkedAxis) = J k)
    (hA : ∀ k, u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
      u '' C k ∩ As)
    (hB : ∀ k, u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
      u '' C k ∩ Bs)
    (α β : Fin 2 → Bool)
    (hquad : ∀ k, f k '' (section34CrossingQuadrant (α k) (β k) ×ˢ Icc (0 : ℝ) 1) =
      C k ∩ R.space) :
    ∃ (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (θ : Fin 2 → ℝ × ℝ → ℝ × ℝ) (e : Fin 2 → ℝ)
      (ν : Fin 2 → (Fin 3 → ℝ) → (Fin 3 → ℝ)),
      IsPLHomeomorphOn H R.space R.space ∧
      IsCylindricalDiagram (H ∘ g) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R.space ∧
      (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (H ∘ g) (p, 0) = (H ∘ g) (p, 1)) ∧
      (u ∘ H ∘ g) '' (A₀ ×ˢ Icc (0 : ℝ) 1) = F ∧
      (u ∘ H ∘ g) '' (A₁ ×ˢ Icc (0 : ℝ) 1) = D ∧
      (∀ k, (u ∘ H ∘ g) '' ({a k} ×ˢ Icc (0 : ℝ) 1) = J k) ∧
      ∀ k, IsPLHomeomorphOn (θ k) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
          (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧ θ k (1 / 2, 0) = a k ∧
        0 < e k ∧ e k ≤ 1 / 2 ∧
        IsPLHomeomorphOn (ν k) (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
          ν k (stdTriangleLoop s) = stdTriangleLoop q →
          ∀ t ∈ Icc (0 : ℝ) (e k), (H ∘ g) (θ k (t / 2 + 1 / 2, 0), s) =
            f k (t • fourSpokeModelLeaf (if α k then 0 else 2), q)) ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
          ν k (stdTriangleLoop s) = stdTriangleLoop q →
          ∀ t ∈ Icc (-e k) 0, (H ∘ g) (θ k (t / 2 + 1 / 2, 0), s) =
            f k ((-t) • fourSpokeModelLeaf (if β k then 1 else 3), q) := by
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  let Q := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hAfront : A₀ ⊆ frontier Q := hcover ▸ subset_union_left
  have hBfront : A₁ ⊆ frontier Q := hcover ▸ subset_union_right
  have hA₀Q := hAfront.trans isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  have hA₁Q := hBfront.trans isPLBall_unit_square.isPolyhedron.isClosed.frontier_subset
  have haQ (k : Fin 2) : a k ∈ Q := by
    fin_cases k
    · exact hδ₀₀ ▸ hA₀Q (hδ₀.bijOn.mapsTo (by norm_num : (0 : ℝ) ∈ Icc 0 1))
    · exact hδ₀₁ ▸ hA₀Q (hδ₀.bijOn.mapsTo (by norm_num : (1 : ℝ) ∈ Icc 0 1))
  have hgP {V : Set (ℝ × ℝ)} (hV : V ⊆ Q) : g '' (V ×ˢ Icc (0 : ℝ) 1) ⊆ P :=
    ((image_mono (prod_mono_left hV)).trans hg.image_eq.subset).trans hRP
  have hmodel {V Z : Set (EuclideanSpace ℝ (Fin 3))} {T : Set M}
      (hVP : V ⊆ P) (hZP : Z ⊆ P) (hh : u '' V = u '' Z ∩ T) :
      V = Z ∩ u ⁻¹' T := by
    apply (hu.image_eq_image_iff hVP (inter_subset_left.trans hZP)).mp
    rw [image_inter_preimage, hh]
  have hFmodel : u ⁻¹' As ∩ R.space = g '' (A₀ ×ˢ Icc (0 : ℝ) 1) := by
    symm
    have hh : u '' (g '' (A₀ ×ˢ Icc (0 : ℝ) 1)) = u '' R.space ∩ As := by
      rw [← image_comp, hface₀, inter_comm, hfirst]
    exact (hmodel (hgP hA₀Q) hRP hh).trans (inter_comm _ _)
  have hDmodel : u ⁻¹' Bs ∩ R.space = g '' (A₁ ×ˢ Icc (0 : ℝ) 1) := by
    symm
    have hh : u '' (g '' (A₁ ×ˢ Icc (0 : ℝ) 1)) = u '' R.space ∩ Bs := by
      rw [← image_comp, hface₁, inter_comm, hsecond]
    exact (hmodel (hgP hA₁Q) hRP hh).trans (inter_comm _ _)
  have hsheet (k : Fin 2) (i j : Fin 4) :
      f k '' (section34MarkedRibbon i ∪ section34MarkedRibbon j) ⊆ C k :=
    (image_mono (union_subset (section34_marked_ribbon_subset_cylinder i)
      (section34_marked_ribbon_subset_cylinder j))).trans (hf k).image_eq.subset
  have haxisModel (k : Fin 2) : f k '' section34MarkedAxis =
      g '' ({a k} ×ˢ Icc (0 : ℝ) 1) := by
    apply (hu.image_eq_image_iff
      (((image_mono ((section34_marked_axis_subset_ribbon 0).trans
        (section34_marked_ribbon_subset_cylinder 0))).trans (hf k).image_eq.subset).trans
          (hCP k)) (hgP (singleton_subset_iff.mpr (haQ k)))).mp
    rw [haxis k, ← image_comp, hPg k]
  let γ : Fin 2 → ℝ → ℝ × ℝ := ![δ₀, fun t => δ₀ (1 - t)]
  have hγ (k : Fin 2) : IsPLHomeomorphOn (γ k) (Icc 0 1) A₀ := by
    fin_cases k
    · exact hδ₀
    · exact isPLHomeomorphOn_comp_one_sub hδ₀
  have hγzero (k : Fin 2) : γ k 0 = a k := by
    fin_cases k
    · exact hδ₀₀
    · change δ₀ (1 - 0) = a 1
      simpa only [sub_zero] using hδ₀₁
  have hcharts (k : Fin 2) := (hf k).exists_filling_corner_chart_matching_core (hfends k)
    (hmodel ((hsheet k 0 2).trans (hCP k)) (hCP k) (hA k))
    (hmodel ((hsheet k 1 3).trans (hCP k)) (hCP k) (hB k)) (hquad k) hFmodel hDmodel
    hg hends (hγ k) hA₀Q (by rw [hγzero k]; exact haxisModel k)
  choose ρ μ W hρ hμ hW hρcore hρpos hρneg hρp hρn hρpI hρnI using hcharts
  obtain ⟨K, hKfin, hKspace⟩ := isPLBall_unit_square.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKspace.symm ▸ isPLBall_unit_square
  have hKbd := frontier_space_eq_boundaryComplex_space_of_finrank
    (by simp : Module.finrank ℝ (ℝ × ℝ) = 2) K hK.isCombinatorialManifoldWithBoundary
  rw [hKspace] at hKbd
  let L := boundaryComplex 3 R
  let _ : Finite L.faces := inferInstanceAs (Finite (boundaryComplex 3 R).faces)
  have hL : IsCombinatorialManifoldWithBoundary 2 L :=
    (isCombinatorialManifold_boundaryComplex R hR).isCombinatorialManifoldWithBoundary
  have hRbd := frontier_space_eq_boundaryComplex_space_of_finrank (by simp) R hR
  have hboundary : g '' ((boundaryComplex 2 K).space ×ˢ Icc (0 : ℝ) 1) = L.space := by
    rw [← hKbd, ← hside]
    exact hRbd
  have hWL (k : Fin 2) : W k ⊆ L.space := by
    apply (hW k).trans
    rw [← hRbd, hside, ← hcover, union_prod, image_union]
  obtain ⟨H, κ, θ₀, θ₁, e₀, e₁, ν₀, ν₁, hH, hg', hHA, hHB, hκ, hθ₀, hθ₁,
    hθ₀zero, hθ₁zero, he₀, he₀half, he₀1, he₁, he₁half, he₁1, hν₀, hν₁, hmatch₀,
    hmatch₁⟩ := (hKspace.symm ▸ hg).exists_paired_seam_volume_correction K hK hδ₀ hδ₁
      (hδ₁₀.trans hδ₀₀.symm) (hδ₁₁.trans hδ₀₁.symm) (hcover.trans hKbd)
      (by simpa only [hδ₀₀, hδ₀₁] using hinter) (by simpa only [hKspace] using hends)
      L hL hboundary (by norm_num) (by norm_num) (hρ 0) (hρ 1) (hWL 0) (hWL 1)
      (hρcore 0) (by simpa only [hγzero, hδ₀₁] using hρcore 1)
      (hρpos 0) (hρneg 0) (hρpos 1) (hρneg 1)
  let θ := ![θ₀, θ₁]
  let e := ![e₀, e₁]
  let ν := ![ν₀, ν₁]
  have hθ (k : Fin 2) : IsPLHomeomorphOn (θ k) Q Q := by
    fin_cases k <;> simpa only [θ, Matrix.cons_val_zero, Matrix.cons_val_one, hKspace]
      using (show IsPLHomeomorphOn _ Q K.space from by assumption)
  have hθzero (k : Fin 2) : θ k (1 / 2, 0) = a k := by
    fin_cases k
    · exact hθ₀zero.trans hδ₀₀
    · exact hθ₁zero.trans hδ₀₁
  have he (k : Fin 2) : 0 < e k ∧ e k ≤ 1 / 2 := by fin_cases k <;> exact ⟨by assumption,
    by assumption⟩
  have hν (k : Fin 2) : IsPLHomeomorphOn (ν k) (stdSimplexBoundary 2)
      (stdSimplexBoundary 2) := by fin_cases k <;> assumption
  have hmatch (k : Fin 2) (z) (hz : z ∈ stdSimplexBoundary 2) (t) (ht : t ∈ Icc (-e k) (e k)) :
      H (κ (z, θ k (t / 2 + 1 / 2, 0))) = ρ k (ν k z, t) := by
    fin_cases k
    · exact hmatch₀ z hz t ht
    · exact hmatch₁ z hz t ht
  have hκg (p) (hp : p ∈ Q) (t) (ht : t ∈ Icc (0 : ℝ) 1) :
      κ (stdTriangleLoop t, p) = g (p, t) := hκ p (hKspace.symm ▸ hp) t ht
  have hρzero (k) (s) (hs : s ∈ Icc (0 : ℝ) 1) :
      ρ k (stdTriangleLoop s, 0) = g (a k, s) := by rw [hρcore k s hs, hγzero k]
  have hκimage (p) (hp : p ∈ Q) :
      (fun z => κ (z, p)) '' stdSimplexBoundary 2 = g '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
    rw [← stdTriangleLoop_image, image_image]
    rw [show ({p} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1 =
      (fun t => (p, t)) '' Icc (0 : ℝ) 1 from singleton_prod]
    rw [image_image]
    exact image_congr (hκg p hp)
  have hHcore (k : Fin 2) : H '' (g '' ({a k} ×ˢ Icc (0 : ℝ) 1)) =
      g '' ({a k} ×ˢ Icc (0 : ℝ) 1) := by
    have heq : EqOn (fun z => H (κ (z, a k))) (fun z => ρ k (ν k z, 0))
        (stdSimplexBoundary 2) := by
      intro z hz
      have hh := hmatch k z hz 0 (by constructor <;> linarith [(he k).1])
      simpa only [zero_div, zero_add, hθzero] using hh
    conv_lhs => rw [← hκimage _ (haQ k), image_image, heq.image_eq]
    rw [show (fun z => ρ k (ν k z, 0)) = (fun z => ρ k (z, 0)) ∘ ν k from rfl,
      image_comp, (hν k).image_eq, ← stdTriangleLoop_image, image_image]
    have hh := image_congr (hρzero k)
    rw [singleton_prod, image_image]
    exact hh
  refine ⟨H, θ, e, fun k => μ k ∘ ν k, hH, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hKspace] using hg'
  · exact fun p hp => congrArg H (hends p hp)
  · rw [image_comp, image_comp, hHA, ← image_comp, hface₀]
  · rw [image_comp, image_comp, hHB, ← image_comp, hface₁]
  · intro k
    rw [image_comp, image_comp, hHcore k, ← image_comp, hPg k]
  · intro k
    refine ⟨hθ k, hθzero k, (he k).1, (he k).2, (hν k).trans (hμ k), ?_, ?_⟩
    all_goals
      intro s hs q hq heq t ht
      have hz := stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop hs)
      obtain ⟨v, hv, hvν⟩ := stdTriangleLoop_image.symm.subset ((hν k).bijOn.mapsTo hz)
      have htfull : t ∈ Icc (-e k) (e k) := by constructor <;> linarith [ht.1, ht.2, (he k).1]
      have hp : (t / 2 + 1 / 2, (0 : ℝ)) ∈ Q := by
        constructor
        · constructor <;> linarith [htfull.1, htfull.2, (he k).2]
        · norm_num
      have hh := hmatch k (stdTriangleLoop s) hz t htfull
      rw [hκg _ ((hθ k).bijOn.mapsTo hp) s hs, ← hvν] at hh
      have heq' : μ k (stdTriangleLoop v) = stdTriangleLoop q := by
        rw [hvν]
        exact heq
      change H (g (θ k (t / 2 + 1 / 2, 0), s)) = _
    · exact hh.trans (hρp k v q hq heq' t ⟨ht.1, ht.2.trans (he k).2⟩)
    · exact hh.trans (hρn k v q hq heq' t ⟨by linarith [ht.1, (he k).2], ht.2⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
