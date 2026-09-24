import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamAnnulusExtensionComplement
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionSupport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_annulus_complement_of_rim_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A W : Set E} {φ : (Fin 3 → ℝ) × ℝ → E}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) A)
    {c d : ℝ} (hcd : c < d) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ ((φ '' (stdSimplexBoundary 2 ×ˢ {0})) ×ˢ Icc c d) W)
    (hzero : ∀ z ∈ φ '' (stdSimplexBoundary 2 ×ˢ {0}), ρ (z, c) = z)
    (hWA : W ⊆ A) (hWtop : Disjoint W (φ '' (stdSimplexBoundary 2 ×ˢ {1}))) :
    ∃ η : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn η (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (closure (A \ W)) ∧
      η '' (stdSimplexBoundary 2 ×ˢ {0}) =
        ρ '' ((φ '' (stdSimplexBoundary 2 ×ˢ {0})) ×ˢ {d}) ∧
      η '' (stdSimplexBoundary 2 ×ˢ {1}) = φ '' (stdSimplexBoundary 2 ×ˢ {1}) ∧
      closure (A \ W) ∩ W = ρ '' ((φ '' (stdSimplexBoundary 2 ×ˢ {0})) ×ˢ {d}) ∧
      W ∪ closure (A \ W) = A := by
  let V := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1
  let B₀ := stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}
  let B₁ := stdSimplexBoundary 2 ×ˢ {(1 : ℝ)}
  let τ := Function.invFunOn φ V
  let W₀ := τ '' W
  have hbd : IsPolyhedron (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using
      (isPLSphere_simplexBoundary_std 1).isPolyhedron
  have hV : IsPolyhedron V := hbd.prod isHPolytope_Icc.isPolyhedron
  have hB₀ : IsPolyhedron B₀ := hbd.prod (isHPolytope_singleton _).isPolyhedron
  have hB₀V : B₀ ⊆ V := fun z hz => ⟨hz.1, hz.2.symm ▸ ⟨le_rfl, zero_le_one⟩⟩
  have hbase := hφ.restrict hB₀ hB₀V
  have hW : IsPolyhedron W := by
    rw [← hρ.image_eq]
    exact ((hB₀.image_of_isPiecewiseAffineOn hbase.isPiecewiseAffineOn hbase.bijOn.injOn).prod
      isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
        hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  have hτW : IsPLHomeomorphOn τ W W₀ := hφ.symm.restrict hW hWA
  have hW₀ : IsPolyhedron W₀ :=
    hW.image_of_isPiecewiseAffineOn hτW.isPiecewiseAffineOn hτW.bijOn.injOn
  have hW₀V : W₀ ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact hφ.symm.bijOn.mapsTo (hWA hz)
  have hback : φ '' W₀ = W := by
    rw [image_image]
    exact (image_congr fun z hz => hφ.bijOn.invOn_invFunOn.2 (hWA hz)).trans (image_id _)
  let ψ := τ ∘ ρ ∘ Prod.map φ id
  have hψ : IsPLHomeomorphOn ψ (B₀ ×ˢ Icc c d) W₀ :=
    ((hbase.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hρ).trans hτW
  have hψzero : ∀ z ∈ B₀, ψ (z, c) = z := by
    intro z hz
    change τ (ρ (φ z, c)) = z
    rw [hzero (φ z) (mem_image_of_mem φ hz)]
    exact hφ.bijOn.invOn_invFunOn.1 (hB₀V hz)
  have hdis : Disjoint W₀ B₁ := by
    apply disjoint_left.mpr
    intro z hzW hzB
    exact disjoint_left.mp hWtop (hback.subset (mem_image_of_mem φ hzW))
      (mem_image_of_mem φ hzB)
  have hid := (isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id
  obtain ⟨η, hη, hη₀, hη₁, hmeet, hcover⟩ :=
    hid.exists_lateral_complement_of_rim_collar (by norm_num : (0 : ℝ) < 1) hcd
      (by simpa only [image_id] using hψ) (by simpa only [image_id] using hψzero)
      (by simpa only [image_id] using hW₀V) (by simpa only [image_id] using hdis)
  simp only [image_id] at hη hη₀ hη₁ hmeet hcover
  let C := closure (V \ W₀)
  have hCV : C ⊆ V := closure_minimal sdiff_subset hV.isClosed
  have hC : IsPolyhedron C := hV.closure_sdiff hW₀
  have himage : φ '' C = closure (A \ W) := by
    rw [show C = closure (V \ W₀) from rfl,
      image_closure_of_isCompact (hV.isCompact.of_isClosed_subset isClosed_closure hCV)
        (hφ.isPiecewiseAffineOn.continuousOn.mono hCV),
      hφ.bijOn.injOn.image_sdiff_subset hW₀V, hφ.image_eq, hback]
  have hlevel : φ '' (ψ '' (B₀ ×ˢ {d})) = ρ '' ((φ '' B₀) ×ˢ {d}) := by
    rw [image_image]
    have heq : EqOn (φ ∘ ψ) (ρ ∘ Prod.map φ id) (B₀ ×ˢ {d}) := by
      intro z hz
      have hz' : z ∈ B₀ ×ˢ Icc c d := ⟨hz.1, hz.2.symm ▸ ⟨hcd.le, le_rfl⟩⟩
      exact hφ.bijOn.invOn_invFunOn.2 (hWA (hρ.bijOn.mapsTo
        ⟨mem_image_of_mem φ hz'.1, hz'.2⟩))
    change (φ ∘ ψ) '' (B₀ ×ˢ {d}) = _
    rw [heq.image_eq, image_comp, prodMap_image_prod, image_id]
  refine ⟨φ ∘ η, ?_, ?_, ?_, ?_, ?_⟩
  · exact himage ▸ hη.trans (hφ.restrict hC hCV)
  · rw [image_comp, hη₀]
    exact hlevel
  · rw [image_comp, hη₁]
  · rw [← himage, ← hback, ← hφ.bijOn.injOn.image_inter hCV hW₀V, hmeet, hlevel]
  · rw [← himage, ← hback, ← image_union, hcover, hφ.image_eq]


theorem IsPLHomeomorphOn.exists_short_rim_collar_annulus_complement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A W : Set E} {φ : (Fin 3 → ℝ) × ℝ → E}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) A)
    {c d : ℝ} (hcd : c < d) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ ((φ '' (stdSimplexBoundary 2 ×ˢ {0})) ×ˢ Icc c d) W)
    (hzero : ∀ z ∈ φ '' (stdSimplexBoundary 2 ×ˢ {0}), ρ (z, c) = z)
    (hWA : W ⊆ A) :
    ∃ e : ℝ, c < e ∧ e ≤ d ∧
      let W' := ρ '' ((φ '' (stdSimplexBoundary 2 ×ˢ {0})) ×ˢ Icc c e)
      ∃ η : (Fin 3 → ℝ) × ℝ → E,
        IsPLHomeomorphOn η (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (closure (A \ W')) ∧
        η '' (stdSimplexBoundary 2 ×ˢ {0}) =
          ρ '' ((φ '' (stdSimplexBoundary 2 ×ˢ {0})) ×ˢ {e}) ∧
        η '' (stdSimplexBoundary 2 ×ˢ {1}) = φ '' (stdSimplexBoundary 2 ×ˢ {1}) ∧
        closure (A \ W') ∩ W' = ρ '' ((φ '' (stdSimplexBoundary 2 ×ˢ {0})) ×ˢ {e}) ∧
        W' ∪ closure (A \ W') = A := by
  let J₀ := φ '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)})
  let J₁ := φ '' (stdSimplexBoundary 2 ×ˢ {(1 : ℝ)})
  have hbd : IsPolyhedron (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using
      (isPLSphere_simplexBoundary_std 1).isPolyhedron
  have hJ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      IsPolyhedron (φ '' (stdSimplexBoundary 2 ×ˢ {t})) := by
    have hpoly := hbd.prod (isHPolytope_singleton t).isPolyhedron
    have hsub : stdSimplexBoundary 2 ×ˢ {t} ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
      fun z hz => ⟨hz.1, hz.2.symm ▸ ht⟩
    exact hpoly.image_of_isPiecewiseAffineOn
      (hφ.isPiecewiseAffineOn.mono_of_isPolyhedron hpoly hsub) (hφ.bijOn.injOn.mono hsub)
  have hdis : Disjoint J₀ J₁ := by
    apply disjoint_left.mpr
    rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    have heq := hφ.bijOn.injOn
      (show x ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 from
        ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, zero_le_one⟩⟩)
      (show y ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 from
        ⟨hy.1, hy.2.symm ▸ ⟨zero_le_one, le_rfl⟩⟩) (hxz.trans hyz.symm)
    exact zero_ne_one (hx.2.symm.trans ((congrArg Prod.snd heq).trans hy.2))
  have hO : J₁ᶜ ∈ 𝓝ˢ[A] J₀ := mem_nhdsSetWithin.mpr
    ⟨J₁ᶜ, (hJ 1 (by norm_num)).isClosed.isOpen_compl,
      fun z hz => fun hz' => disjoint_left.mp hdis hz hz', inter_subset_left⟩
  obtain ⟨e, hce, hed, he⟩ := exists_short_product_image_subset_of_compact
    (hJ 0 (by norm_num)).isCompact hcd hρ.isPiecewiseAffineOn.continuousOn
    (hρ.bijOn.mapsTo.mono_right hWA) (fun z hz => by rw [hzero z hz]; exact hz) hO
  have hsub : J₀ ×ˢ Icc c e ⊆ J₀ ×ˢ Icc c d :=
    prod_mono_right (Icc_subset_Icc le_rfl hed)
  have hρ' := hρ.restrict ((hJ 0 (by norm_num)).prod isHPolytope_Icc.isPolyhedron) hsub
  refine ⟨e, hce, hed, hφ.exists_annulus_complement_of_rim_collar hce hρ' hzero
    ((image_mono hsub).trans hρ.image_eq.subset |>.trans hWA) ?_⟩
  exact disjoint_left.mpr fun z hz hz' => he hz hz'

end DifferentialGeometry.Topology.PiecewiseLinear
