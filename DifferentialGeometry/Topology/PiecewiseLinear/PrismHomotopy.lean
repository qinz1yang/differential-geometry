import DifferentialGeometry.Topology.PiecewiseLinear.PrismInterval
import DifferentialGeometry.Topology.PiecewiseLinear.BrokenLine
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_isPiecewiseAffineOn_prism {f g : ℝ → F}
    (hf : IsPiecewiseAffineOn f (Icc (0 : ℝ) 1)) (hg : IsPiecewiseAffineOn g (Icc (0 : ℝ) 1)) :
    ∃ (n : ℕ) (s : ℕ → ℝ) (Φ : ℝ × ℝ → F), s 0 = 0 ∧ s n = 1 ∧ (∀ i < n, s i < s (i + 1)) ∧
      IsPiecewiseAffineOn Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 0) = f x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 1) = g x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (0, t) = f 0 + t • (g 0 - f 0)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (1, t) = f 1 + t • (g 1 - f 1)) ∧
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∃ i, i < n ∧
        Φ z ∈ convexHull ℝ ({f (s i), f (s (i + 1)), g (s i), g (s (i + 1))} : Set F)) := by
  obtain ⟨n, s, hs0, hsn, hmono, -, -, -, hfaff, hgaff⟩ :=
    exists_partition_affineOn_two hf hg (δ := 1) one_pos ∅ (by simp)
  obtain ⟨Φ, hPA, hbot, htop, hleft, hright, himg⟩ :=
    exists_isPiecewiseAffineOn_prism_of_partition hs0 hsn hmono hfaff hgaff
  exact ⟨n, s, Φ, hs0, hsn, hmono, hPA, hbot, htop, hleft, hright, himg⟩

theorem exists_isPiecewiseAffineOn_prism_mapsTo {f g : ℝ → F} {S : Set F} (hS : Convex ℝ S)
    (hf : IsPiecewiseAffineOn f (Icc (0 : ℝ) 1)) (hg : IsPiecewiseAffineOn g (Icc (0 : ℝ) 1))
    (hfS : MapsTo f (Icc (0 : ℝ) 1) S) (hgS : MapsTo g (Icc (0 : ℝ) 1) S) :
    ∃ Φ : ℝ × ℝ → F, IsPiecewiseAffineOn Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) S ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 0) = f x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 1) = g x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (0, t) = f 0 + t • (g 0 - f 0)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (1, t) = f 1 + t • (g 1 - f 1)) := by
  obtain ⟨n, s, Φ, hs0, hsn, hmono, hPA, hbot, htop, hleft, hright, himg⟩ :=
    exists_isPiecewiseAffineOn_prism hf hg
  have hsmem : ∀ i, i ≤ n → s i ∈ Icc (0 : ℝ) 1 :=
    fun i hi => mem_Icc_of_forall_lt_succ hmono hs0 hsn hi
  refine ⟨Φ, hPA, ?_, hbot, htop, hleft, hright⟩
  refine mapsTo_of_forall_mem_convexHull_cell hS himg (fun i hi => ⟨?_, ?_, ?_, ?_⟩)
  · exact hfS (hsmem i (by omega))
  · exact hfS (hsmem (i + 1) (by omega))
  · exact hgS (hsmem i (by omega))
  · exact hgS (hsmem (i + 1) (by omega))

theorem exists_isPiecewiseAffineOn_annulus_of_partition (L : Geometry.SimplicialComplex ℝ F)
    {f g : ℝ → F} {n : ℕ} {s : ℕ → ℝ}
    (hs0 : s 0 = 0) (hsn : s n = 1) (hmono : ∀ i < n, s i < s (i + 1))
    (hfaff : ∀ i < n, ∀ x ∈ Icc (s i) (s (i + 1)),
      f x = f (s i) + ((x - s i) / (s (i + 1) - s i)) • (f (s (i + 1)) - f (s i)))
    (hgaff : ∀ i < n, ∀ x ∈ Icc (s i) (s (i + 1)),
      g x = g (s i) + ((x - s i) / (s (i + 1) - s i)) • (g (s (i + 1)) - g (s i)))
    (hfloop : f 0 = f 1) (hgloop : g 0 = g 1)
    (hface : ∀ i < n, ∃ u ∈ L.faces,
      ({f (s i), f (s (i + 1)), g (s i), g (s (i + 1))} : Set F) ⊆ convexHull ℝ (u : Set F)) :
    ∃ Φ : ℝ × ℝ → F, IsPiecewiseAffineOn Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 0) = f x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 1) = g x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (0, t) = Φ (1, t)) := by
  obtain ⟨Φ, hPA, hbot, htop, hsides, himg⟩ :=
    exists_isPiecewiseAffineOn_prism_of_partition_of_loop hs0 hsn hmono hfaff hgaff hfloop hgloop
  refine ⟨Φ, hPA, ?_, hbot, htop, hsides⟩
  intro z hz
  obtain ⟨i, hi, hmem⟩ := himg z hz
  obtain ⟨u, hu, hsub⟩ := hface i hi
  exact L.convexHull_subset_space hu
    ((convex_convexHull ℝ (u : Set F)).convexHull_subset_iff.mpr hsub hmem)

theorem exists_face_of_cell_of_mem_convexHull_carrierFace (L : Geometry.SimplicialComplex ℝ F)
    {f g : ℝ → F} {n : ℕ} {s : ℕ → ℝ}
    (hcell : ∀ i < n, ∃ u ∈ L.faces, ∀ x ∈ Icc (s i) (s (i + 1)), f x ∈ convexHull ℝ (u : Set F))
    (happrox : ∀ i < n, ∀ x ∈ Icc (s i) (s (i + 1)),
      g x ∈ convexHull ℝ ((carrierFace L (f x) : Finset F) : Set F))
    (hmono : ∀ i < n, s i < s (i + 1)) :
    ∀ i < n, ∃ u ∈ L.faces,
      ({f (s i), f (s (i + 1)), g (s i), g (s (i + 1))} : Set F) ⊆ convexHull ℝ (u : Set F) := by
  intro i hi
  obtain ⟨u, hu, hfu⟩ := hcell i hi
  have hle := (hmono i hi).le
  have hfi : f (s i) ∈ convexHull ℝ (u : Set F) := hfu _ ⟨le_rfl, hle⟩
  have hfi1 : f (s (i + 1)) ∈ convexHull ℝ (u : Set F) := hfu _ ⟨hle, le_rfl⟩
  have hcarrier : ∀ x ∈ Icc (s i) (s (i + 1)),
      g x ∈ convexHull ℝ (u : Set F) := by
    intro x hx
    have hfx : f x ∈ L.space := L.convexHull_subset_space hu (hfu x hx)
    have hsub : carrierFace L (f x) ⊆ u := carrierFace_subset hfx hu (hfu x hx)
    exact convexHull_mono (Finset.coe_subset.mpr hsub) (happrox i hi x hx)
  refine ⟨u, hu, ?_⟩
  rintro y (rfl | rfl | rfl | rfl)
  · exact hfi
  · exact hfi1
  · exact hcarrier _ ⟨le_rfl, hle⟩
  · exact hcarrier _ ⟨hle, le_rfl⟩

theorem exists_isPiecewiseAffineOn_prism_mapsTo_space (L : Geometry.SimplicialComplex ℝ F)
    {f g : ℝ → F} (hf : IsPiecewiseAffineOn f (Icc (0 : ℝ) 1))
    (hg : IsPiecewiseAffineOn g (Icc (0 : ℝ) 1)) {δ : ℝ} (hδ : 0 < δ)
    (T : Finset ℝ) (hT : ∀ x ∈ T, x ∈ Icc (0 : ℝ) 1)
    (hface : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f a, f b, g a, g b} : Set F) ⊆ convexHull ℝ (u : Set F)) :
    ∃ Φ : ℝ × ℝ → F, IsPiecewiseAffineOn Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 0) = f x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 1) = g x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (0, t) = f 0 + t • (g 0 - f 0)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (1, t) = f 1 + t • (g 1 - f 1)) := by
  obtain ⟨n, s, hs0, hsn, hmono, hmesh, -, hgap, hfaff, hgaff⟩ :=
    exists_partition_affineOn_two hf hg hδ T hT
  obtain ⟨Φ, hPA, hbot, htop, hleft, hright, himg⟩ :=
    exists_isPiecewiseAffineOn_prism_of_partition hs0 hsn hmono hfaff hgaff
  refine ⟨Φ, hPA, ?_, hbot, htop, hleft, hright⟩
  intro z hz
  obtain ⟨i, hi, hmem⟩ := himg z hz
  obtain ⟨u, hu, hsub⟩ := hface (s i) (mem_Icc_of_forall_lt_succ hmono hs0 hsn (by omega))
    (s (i + 1)) (mem_Icc_of_forall_lt_succ hmono hs0 hsn (by omega)) (hmesh i hi) (hgap i hi)
  exact L.convexHull_subset_space hu
    ((convex_convexHull ℝ (u : Set F)).convexHull_subset_iff.mpr hsub hmem)

theorem exists_isPiecewiseAffineOn_annulus_mapsTo_space (L : Geometry.SimplicialComplex ℝ F)
    {f g : ℝ → F} (hf : IsPiecewiseAffineOn f (Icc (0 : ℝ) 1))
    (hg : IsPiecewiseAffineOn g (Icc (0 : ℝ) 1)) (hfloop : f 0 = f 1) (hgloop : g 0 = g 1)
    {δ : ℝ} (hδ : 0 < δ) (T : Finset ℝ) (hT : ∀ x ∈ T, x ∈ Icc (0 : ℝ) 1)
    (hface : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f a, f b, g a, g b} : Set F) ⊆ convexHull ℝ (u : Set F)) :
    ∃ Φ : ℝ × ℝ → F, IsPiecewiseAffineOn Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 0) = f x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 1) = g x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Φ (0, t) = Φ (1, t)) := by
  obtain ⟨Φ, hPA, hmaps, hbot, htop, hleft, hright⟩ :=
    exists_isPiecewiseAffineOn_prism_mapsTo_space L hf hg hδ T hT hface
  refine ⟨Φ, hPA, hmaps, hbot, htop, fun t ht => ?_⟩
  rw [hleft t ht, hright t ht, hfloop, hgloop]

noncomputable def heightRescale (h : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  (LinearMap.prod (LinearMap.fst ℝ ℝ ℝ) (h⁻¹ • LinearMap.snd ℝ ℝ ℝ)).toAffineMap

theorem heightRescale_apply (h : ℝ) (z : ℝ × ℝ) : heightRescale h z = (z.1, z.2 / h) := by
  simp [heightRescale, div_eq_inv_mul]

theorem preimage_heightRescale {h : ℝ} (hh : 0 < h) :
    heightRescale h ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) h := by
  ext z
  rw [mem_preimage, heightRescale_apply]
  simp only [Set.mem_prod, mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [le_div_iff₀ hh] at h2
    rw [div_le_one hh] at h3
    exact ⟨h1, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [le_div_iff₀ hh]; linarith
    · rw [div_le_one hh]; linarith

theorem exists_isPiecewiseAffineOn_prism_height_mapsTo_space
    (L : Geometry.SimplicialComplex ℝ F) {f g : ℝ → F}
    (hf : IsPiecewiseAffineOn f (Icc (0 : ℝ) 1)) (hg : IsPiecewiseAffineOn g (Icc (0 : ℝ) 1))
    {δ : ℝ} (hδ : 0 < δ) (T : Finset ℝ) (hT : ∀ x ∈ T, x ∈ Icc (0 : ℝ) 1)
    (hface : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f a, f b, g a, g b} : Set F) ⊆ convexHull ℝ (u : Set F))
    {h : ℝ} (hh : 0 < h) :
    ∃ Φ : ℝ × ℝ → F, IsPiecewiseAffineOn Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) h) ∧
      MapsTo Φ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) h) L.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, 0) = f x) ∧ (∀ x ∈ Icc (0 : ℝ) 1, Φ (x, h) = g x) := by
  obtain ⟨Φ₀, hPA, hmaps, hbot, htop, -, -⟩ :=
    exists_isPiecewiseAffineOn_prism_mapsTo_space L hf hg hδ T hT hface
  refine ⟨Φ₀ ∘ heightRescale h, ?_, ?_, ?_, ?_⟩
  · have hc := hPA.comp (isPiecewiseAffineOn_of_affine (heightRescale h) isOpen_univ)
    rwa [univ_inter, preimage_heightRescale hh] at hc
  · intro z hz
    refine hmaps ?_
    rw [← preimage_heightRescale hh] at hz
    exact hz
  · intro x hx
    have hz : heightRescale h (x, 0) = (x, 0) := by rw [heightRescale_apply]; simp
    rw [Function.comp_apply, hz]
    exact hbot x hx
  · intro x hx
    have hz : heightRescale h (x, h) = (x, 1) := by
      rw [heightRescale_apply]
      simp [div_self (ne_of_gt hh)]
    rw [Function.comp_apply, hz]
    exact htop x hx

open Classical in
theorem exists_isPiecewiseAffineOn_glue_prism_collar (L : Geometry.SimplicialComplex ℝ F)
    {G : ℝ × ℝ → F} (hG : IsPiecewiseAffineOn G (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hGL : MapsTo G (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space)
    {f : ℝ → F} (hf : IsPiecewiseAffineOn f (Icc (0 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (T : Finset ℝ) (hT : ∀ x ∈ T, x ∈ Icc (0 : ℝ) 1)
    (hface : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces,
        ({f a, f b, G (a, ε), G (b, ε)} : Set F) ⊆ convexHull ℝ (u : Set F)) :
    ∃ g : ℝ × ℝ → F, IsPiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1, g (x, 0) = f x) ∧
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc ε 1, g z = G z) := by
  classical
  have hslice : IsPiecewiseAffineOn (fun x : ℝ => G (x, ε)) (Icc (0 : ℝ) 1) := by
    have haff : IsPiecewiseAffineOn
        (fun x : ℝ => ((x, ε) : ℝ × ℝ)) (univ : Set ℝ) :=
      (isPiecewiseAffineOn_of_affine
        (AffineMap.const ℝ ℝ ((0 : ℝ), ε) + ((LinearMap.id).prod 0).toAffineMap)
        isOpen_univ).congr (fun x _ => by simp)
    have hc := hG.comp haff
    have hset : (univ : Set ℝ) ∩ (fun x : ℝ => ((x, ε) : ℝ × ℝ)) ⁻¹'
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = Icc (0 : ℝ) 1 := by
      ext x
      simp only [univ_inter, mem_preimage, Set.mem_prod, mem_Icc]
      exact ⟨fun h => h.1, fun h => ⟨h, hε.le, hε1⟩⟩
    rwa [hset] at hc
  obtain ⟨Φ, hPAΦ, hmapsΦ, hbotΦ, htopΦ⟩ :=
    exists_isPiecewiseAffineOn_prism_height_mapsTo_space L hf hslice hδ T hT hface hε
  have hGupper : IsPiecewiseAffineOn G (Icc (0 : ℝ) 1 ×ˢ Icc ε 1) :=
    hG.mono_of_isPolyhedron (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
      (prod_mono_right (Icc_subset_Icc hε.le le_rfl))
  have hunion : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) ε ∪ Icc (0 : ℝ) 1 ×ˢ Icc ε 1
      = Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    rw [← prod_union, Icc_union_Icc_eq_Icc hε.le hε1]
  have heq : EqOn Φ G (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) ε ∩ Icc (0 : ℝ) 1 ×ˢ Icc ε 1) := by
    rintro ⟨x, t⟩ ⟨⟨hx, -, ht2⟩, -, ht3, -⟩
    have hte : t = ε := le_antisymm ht2 ht3
    subst hte
    exact htopΦ x hx
  set g : ℝ × ℝ → F :=
    @Set.piecewise (ℝ × ℝ) (fun _ => F) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) ε) Φ G
      (fun j => Classical.propDecidable _) with hgdef
  have hgmem : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) ε, g z = Φ z := by
    intro z hz
    rw [hgdef]
    exact if_pos hz
  have hgnot : ∀ z ∉ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) ε, g z = G z := by
    intro z hz
    rw [hgdef]
    exact if_neg hz
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [← hunion]
    exact hPAΦ.piecewise_of_isClosed hGupper (isClosed_Icc.prod isClosed_Icc)
      (isClosed_Icc.prod isClosed_Icc) heq
  · intro z hz
    by_cases hzc : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) ε
    · rw [hgmem _ hzc]
      exact hmapsΦ hzc
    · rw [hgnot _ hzc]
      exact hGL hz
  · intro x hx
    rw [hgmem _ ⟨hx, le_rfl, hε.le⟩]
    exact hbotΦ x hx
  · rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    by_cases hzc : ((x, t) : ℝ × ℝ) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) ε
    · rw [hgmem _ hzc]
      have hte : t = ε := le_antisymm hzc.2.2 ht1
      subst hte
      exact htopΦ x hx
    · rw [hgnot _ hzc]

end DifferentialGeometry.Topology.PiecewiseLinear
