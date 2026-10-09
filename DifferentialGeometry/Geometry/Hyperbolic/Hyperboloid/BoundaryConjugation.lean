import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryPlane

noncomputable section

namespace DifferentialGeometry.Hyperboloid

private theorem isometry_distortion {X : Type*} [PseudoMetricSpace X] (A : X ≃ᵢ X) :
    ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : X,
      L⁻¹ * dist x y - C ≤ dist (A x) (A y) ∧ dist (A x) (A y) ≤ L * dist x y + C := by
  refine ⟨1, 0, le_rfl, le_rfl, ?_⟩
  intro x y
  simp only [A.dist_eq, inv_one, one_mul, sub_zero, add_zero, le_refl, and_self]

private theorem prepost_distortion {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : C(X, Y)) (A : Y ≃ᵢ Y) (B : X ≃ᵢ X)
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : X,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C) :
    ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : X,
      L⁻¹ * dist x y - C ≤ dist (A (f (B x))) (A (f (B y))) ∧
        dist (A (f (B x))) (A (f (B y))) ≤ L * dist x y + C := by
  obtain ⟨L, C, hL, hC, hxy⟩ := hf
  refine ⟨L, C, hL, hC, ?_⟩
  intro x y
  simpa only [A.dist_eq, B.dist_eq] using hxy (B x) (B y)

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

private theorem boundaryMap_prepost
    (f : C(Hyperboloid E, Hyperboloid E'))
    (A : Hyperboloid E' ≃ᵢ Hyperboloid E') (B : Hyperboloid E ≃ᵢ Hyperboloid E)
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hfAB : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (A (f (B x))) (A (f (B y))) ∧
        dist (A (f (B x))) (A (f (B y))) ≤ L * dist x y + C)
    (ξ : Metric.sphere (0 : E) 1) :
    boundaryMap ((A : C(Hyperboloid E', Hyperboloid E')).comp
      (f.comp (B : C(Hyperboloid E, Hyperboloid E)))) hfAB ξ =
        boundaryHomeomorph A (boundaryMap f hf (boundaryHomeomorph B ξ)) := by
  have hfB : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist ((f.comp (B : C(Hyperboloid E, Hyperboloid E))) x)
        ((f.comp (B : C(Hyperboloid E, Hyperboloid E))) y) ∧
      dist ((f.comp (B : C(Hyperboloid E, Hyperboloid E))) x)
        ((f.comp (B : C(Hyperboloid E, Hyperboloid E))) y) ≤ L * dist x y + C := by
    obtain ⟨L, C, hL, hC, hxy⟩ := hf
    exact ⟨L, C, hL, hC, fun x y => by simpa only [ContinuousMap.comp_apply,
      ContinuousMap.coe_apply, B.dist_eq] using hxy (B x) (B y)⟩
  rw [boundaryMap_comp (f.comp (B : C(Hyperboloid E, Hyperboloid E)))
      (A : C(Hyperboloid E', Hyperboloid E')) hfB (isometry_distortion A),
    boundaryMap_comp (B : C(Hyperboloid E, Hyperboloid E)) f (isometry_distortion B) hf]
  simp only [ContinuousMap.comp_apply, boundaryMap_isometryEquiv, ContinuousMap.coe_apply]

theorem exists_boundaryHomeomorphOfCoarseInverse_isometry_conjugate
    (f : C(Hyperboloid E, Hyperboloid E')) (g : C(Hyperboloid E', Hyperboloid E))
    (A : Hyperboloid E' ≃ᵢ Hyperboloid E') (B : Hyperboloid E ≃ᵢ Hyperboloid E)
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E',
      L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C)
    (hgf : ∃ C : ℝ, ∀ x : Hyperboloid E, dist (g (f x)) x ≤ C)
    (hfg : ∃ C : ℝ, ∀ x : Hyperboloid E', dist (f (g x)) x ≤ C) :
    let fAB := (A : C(Hyperboloid E', Hyperboloid E')).comp
      (f.comp (B : C(Hyperboloid E, Hyperboloid E)))
    let gAB := (B.symm : C(Hyperboloid E, Hyperboloid E)).comp
      (g.comp (A.symm : C(Hyperboloid E', Hyperboloid E')))
    ∃ (hfAB : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E,
        L⁻¹ * dist x y - C ≤ dist (fAB x) (fAB y) ∧ dist (fAB x) (fAB y) ≤ L * dist x y + C)
      (hgAB : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : Hyperboloid E',
        L⁻¹ * dist x y - C ≤ dist (gAB x) (gAB y) ∧ dist (gAB x) (gAB y) ≤ L * dist x y + C)
      (hgfAB : ∃ C : ℝ, ∀ x : Hyperboloid E, dist (gAB (fAB x)) x ≤ C)
      (hfgAB : ∃ C : ℝ, ∀ x : Hyperboloid E', dist (fAB (gAB x)) x ≤ C),
      boundaryHomeomorphOfCoarseInverse fAB gAB hfAB hgAB hgfAB hfgAB =
        (boundaryHomeomorph B).trans
          ((boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg).trans (boundaryHomeomorph A)) := by
  dsimp only
  let fAB := (A : C(Hyperboloid E', Hyperboloid E')).comp
    (f.comp (B : C(Hyperboloid E, Hyperboloid E)))
  let gAB := (B.symm : C(Hyperboloid E, Hyperboloid E)).comp
    (g.comp (A.symm : C(Hyperboloid E', Hyperboloid E')))
  have hfAB := prepost_distortion f A B hf
  have hgAB := prepost_distortion g B.symm A.symm hg
  have hgfAB : ∃ C : ℝ, ∀ x : Hyperboloid E, dist (gAB (fAB x)) x ≤ C := by
    obtain ⟨C, hC⟩ := hgf
    refine ⟨C, ?_⟩
    intro x
    change dist (B.symm (g (A.symm (A (f (B x)))))) x ≤ C
    rw [A.symm_apply_apply, ← B.dist_eq, B.apply_symm_apply]
    exact hC (B x)
  have hfgAB : ∃ C : ℝ, ∀ x : Hyperboloid E', dist (fAB (gAB x)) x ≤ C := by
    obtain ⟨C, hC⟩ := hfg
    refine ⟨C, ?_⟩
    intro x
    change dist (A (f (B (B.symm (g (A.symm x)))))) x ≤ C
    rw [B.apply_symm_apply, ← A.symm.dist_eq, A.symm_apply_apply]
    exact hC (A.symm x)
  refine ⟨hfAB, hgAB, hgfAB, hfgAB, ?_⟩
  apply Homeomorph.ext
  intro ξ
  exact boundaryMap_prepost f A B hf hfAB ξ

local notation "H3" => Hyperboloid (EuclideanSpace ℝ (Fin 3))

theorem exists_boundaryPlaneHomeomorph_isometry_conjugate
    (f g : C(H3, H3)) (A B : H3 ≃ᵢ H3)
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C)
    (hgf : ∃ C : ℝ, ∀ x : H3, dist (g (f x)) x ≤ C)
    (hfg : ∃ C : ℝ, ∀ x : H3, dist (f (g x)) x ≤ C)
    (hnorth : boundaryHomeomorph A
      (boundaryMap f hf (boundaryHomeomorph B sphereNorthPole)) = sphereNorthPole) :
    let fAB := (A : C(H3, H3)).comp (f.comp (B : C(H3, H3)))
    let gAB := (B.symm : C(H3, H3)).comp (g.comp (A.symm : C(H3, H3)))
    ∃ (hfAB : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
        L⁻¹ * dist x y - C ≤ dist (fAB x) (fAB y) ∧ dist (fAB x) (fAB y) ≤ L * dist x y + C)
      (hgAB : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
        L⁻¹ * dist x y - C ≤ dist (gAB x) (gAB y) ∧ dist (gAB x) (gAB y) ≤ L * dist x y + C)
      (hgfAB : ∃ C : ℝ, ∀ x : H3, dist (gAB (fAB x)) x ≤ C)
      (hfgAB : ∃ C : ℝ, ∀ x : H3, dist (fAB (gAB x)) x ≤ C)
      (hnorthAB : boundaryMap fAB hfAB sphereNorthPole = sphereNorthPole),
      ∀ z : ℂ,
        (stereographicComplex.symm
          (boundaryPlaneHomeomorph fAB gAB hfAB hgAB hgfAB hfgAB hnorthAB z)).val =
          boundaryHomeomorph A
            (boundaryMap f hf (boundaryHomeomorph B (stereographicComplex.symm z).val)) := by
  dsimp only
  obtain ⟨hfAB, hgAB, hgfAB, hfgAB, hboundary⟩ :=
    exists_boundaryHomeomorphOfCoarseInverse_isometry_conjugate f g A B hf hg hgf hfg
  have hmap (ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      boundaryMap ((A : C(H3, H3)).comp (f.comp (B : C(H3, H3)))) hfAB ξ =
        boundaryHomeomorph A (boundaryMap f hf (boundaryHomeomorph B ξ)) :=
    congrArg (fun H => H ξ) hboundary
  have hN := (hmap sphereNorthPole).trans hnorth
  refine ⟨hfAB, hgAB, hgfAB, hfgAB, hN, ?_⟩
  intro z
  rw [stereographicComplex_symm_boundaryPlaneHomeomorph, hmap]

end DifferentialGeometry.Hyperboloid
