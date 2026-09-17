import DifferentialGeometry.Topology.PiecewiseLinear.PrismHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialApproximation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def collarReparam (ε t : ℝ) : ℝ := max 0 ((t - ε) / (1 - ε))

theorem collarReparam_eq_zero {ε t : ℝ} (hε1 : ε < 1) (ht : t ≤ ε) : collarReparam ε t = 0 := by
  rw [collarReparam, max_eq_left]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem collarReparam_mem {ε t : ℝ} (hε1 : ε < 1) (ht : t ≤ 1) :
    collarReparam ε t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
  rw [div_le_one (by linarith)]
  linarith

theorem continuous_collarReparam (ε : ℝ) : Continuous (collarReparam ε) := by
  refine continuous_const.max ?_
  exact (continuous_id.sub continuous_const).div_const _

theorem exists_isPiecewiseAffineOn_square_eqOn_bottom
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {f : ℝ × ℝ → F} (hf : ContinuousOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hfL : MapsTo f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space)
    (hbot : IsPiecewiseAffineOn (fun x : ℝ => f (x, 0)) (Icc (0 : ℝ) 1))
    {δ : ℝ} (hδ : 0 < δ) (T : Finset ℝ) (hT : ∀ x ∈ T, x ∈ Icc (0 : ℝ) 1)
    (hbotface : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f (a, 0), f (b, 0)} : Set F) ⊆ convexHull ℝ (u : Set F)) :
    ∃ g : ℝ × ℝ → F, IsPiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space ∧
      (∀ x ∈ Icc (0 : ℝ) 1, g (x, 0) = f (x, 0)) := by
  classical
  have hε : (0 : ℝ) < 1 / 2 := by norm_num
  have hε1 : (1 : ℝ) / 2 < 1 := by norm_num
  set ρ : ℝ × ℝ → ℝ × ℝ := fun z => (z.1, collarReparam (1 / 2) z.2) with hρdef
  have hρcont : Continuous ρ :=
    continuous_fst.prodMk ((continuous_collarReparam _).comp continuous_snd)
  have hρmaps : MapsTo ρ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    fun z hz => ⟨hz.1, collarReparam_mem hε1 hz.2.2⟩
  have hf' : ContinuousOn (f ∘ ρ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    hf.comp hρcont.continuousOn hρmaps
  have hf'L : MapsTo (f ∘ ρ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space :=
    fun z hz => hfL (hρmaps hz)
  obtain ⟨K, hKfin, hKspace⟩ := IsPolyhedron.exists_simplicialComplex
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨K', φ, hK', hK'fin, hφ, hclose⟩ :=
    exists_isSubdivision_simplicialApproximation K L (by rw [hKspace]; exact hf')
      (by rw [hKspace]; exact hf'L)
  let _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by rw [hK'.space_eq, hKspace]
  have hG : IsPiecewiseAffineOn (simplicialMap K' φ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hK'space]
    exact isPiecewiseAffineOn_simplicialMap K' φ
  have hGL : MapsTo (simplicialMap K' φ) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) L.space := by
    rw [← hK'space]
    exact simplicialMap_mapsTo K' L φ hφ
  have hslice : ∀ a : ℝ, (f ∘ ρ) (a, 1 / 2) = f (a, 0) := by
    intro a
    rw [Function.comp_apply, hρdef]
    simp only
    rw [collarReparam_eq_zero hε1 le_rfl]
  have hface : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, b - a < δ →
      (∀ x ∈ T, ¬(a < x ∧ x < b)) →
      ∃ u ∈ L.faces, ({f (a, 0), f (b, 0), simplicialMap K' φ (a, 1 / 2),
        simplicialMap K' φ (b, 1 / 2)} : Set F) ⊆ convexHull ℝ (u : Set F) := by
    intro a ha b hb hab hgap
    obtain ⟨u, hu, hsub⟩ := hbotface a ha b hb hab hgap
    have hmemu : ∀ c : ℝ, c ∈ Icc (0 : ℝ) 1 → f (c, 0) ∈ convexHull ℝ (u : Set F) →
        simplicialMap K' φ (c, 1 / 2) ∈ convexHull ℝ (u : Set F) := by
      intro c hc hfc
      have hcK : ((c, (1 : ℝ) / 2) : ℝ × ℝ) ∈ K.space := by
        rw [hKspace]
        exact ⟨hc, hε.le, hε1.le⟩
      have h1 := hclose _ hcK
      rw [hslice c] at h1
      have h2 : carrierFace L (f (c, 0)) ⊆ u :=
        carrierFace_subset (L.convexHull_subset_space hu hfc) hu hfc
      exact convexHull_mono (Finset.coe_subset.mpr h2) h1
    refine ⟨u, hu, ?_⟩
    rintro y (rfl | rfl | rfl | rfl)
    · exact hsub (mem_insert _ _)
    · exact hsub (mem_insert_of_mem _ rfl)
    · exact hmemu a ha (hsub (mem_insert _ _))
    · exact hmemu b hb (hsub (mem_insert_of_mem _ rfl))
  obtain ⟨g, hgPA, hgL, hgbot, -⟩ :=
    exists_isPiecewiseAffineOn_glue_prism_collar L hG hGL hbot hε hε1.le hδ T hT hface
  exact ⟨g, hgPA, hgL, hgbot⟩

end DifferentialGeometry.Topology.PiecewiseLinear
