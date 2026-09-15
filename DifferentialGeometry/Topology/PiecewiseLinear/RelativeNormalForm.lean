import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem simplicialMap_eqOn_convexHull_of_eqOn_vertices
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    {φ ψ : E → F} (hfix : EqOn ψ φ (s : Set E)) :
    EqOn (simplicialMap K ψ) (simplicialMap K φ) (convexHull ℝ (s : Set E)) := by
  intro x hx
  rw [simplicialMap_eq_of_mem K ψ hs hx, simplicialMap_eq_of_mem K φ hs hx]
  exact Finset.sum_congr rfl fun v hv => by rw [hfix hv]

theorem doublePointSet_simplicialMap_subset_of_eqOn_subcomplex
    (K B : Geometry.SimplicialComplex ℝ E) (hBK : B.faces ⊆ K.faces)
    {φ ψ : E → F} (hfix : EqOn ψ φ B.vertices) :
    doublePointSet (simplicialMap K φ) B.space ⊆
      doublePointSet (simplicialMap K ψ) K.space := by
  have heq := simplicialMap_eqOn_subcomplex_of_eqOn_vertices K B hBK hfix
  have hspace := space_mono_of_faces_subset hBK
  rintro y ⟨a, ha, b, hb, hab, hay, hby⟩
  exact ⟨a, hspace ha, b, hspace hb, hab, (heq ha).trans hay, (heq hb).trans hby⟩

theorem mem_doublePointSet_simplicialMap_of_fixed_faces
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) {φ ψ : E → F}
    (hfix : EqOn ψ φ ((s : Set E) ∪ (t : Set E)))
    {a b : E} {y : F} (ha : a ∈ convexHull ℝ (s : Set E))
    (hb : b ∈ convexHull ℝ (t : Set E)) (hab : a ≠ b)
    (hay : simplicialMap K φ a = y) (hby : simplicialMap K φ b = y) :
    y ∈ doublePointSet (simplicialMap K ψ) K.space := by
  have heqs := simplicialMap_eqOn_convexHull_of_eqOn_vertices K hs (hfix.mono subset_union_left)
  have heqt := simplicialMap_eqOn_convexHull_of_eqOn_vertices K ht (hfix.mono subset_union_right)
  exact ⟨a, K.convexHull_subset_space hs ha, b, K.convexHull_subset_space ht hb,
    hab, (heqs ha).trans hay, (heqt hb).trans hby⟩

open Classical in
theorem exists_small_relative_vertexMap_with_coincident_edges [FiniteDimensional ℝ F]
    (φ₀ : Fin 2 → Fin 4 → F) (hind : ∀ i, AffineIndependent ℝ (φ₀ i))
    (hcommon : ∀ j ∈ ({0, 1} : Finset (Fin 4)), φ₀ 0 j = φ₀ 1 j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Fin 2 × Fin 4 → F,
      (∀ i : Fin 2, ∀ j ∈ ({0, 1} : Finset (Fin 4)), ψ (i, j) = φ₀ i j) ∧
      (∀ j ∈ ({0, 1} : Finset (Fin 4)), ψ (0, j) = ψ (1, j)) ∧
      (∀ v, dist (ψ v) (φ₀ v.1 v.2) < ε) ∧
      (∀ i : Fin 2, AffineIndependent ℝ (fun j : Fin 4 => ψ (i, j))) ∧
      ∀ s : Finset (Fin 2 × Fin 4), s.card ≤ Module.finrank ℝ F + 1 →
        AffineIndependent ℝ (fun v : (s ∩ Finset.univ.product ({0, 1} : Finset (Fin 4)) :
            Finset (Fin 2 × Fin 4)) =>
          φ₀ (v : Fin 2 × Fin 4).1 (v : Fin 2 × Fin 4).2) →
            AffineIndependent ℝ (fun v : s => ψ (v : Fin 2 × Fin 4)) := by
  let B : Finset (Fin 2 × Fin 4) := Finset.univ.product {0, 1}
  let V : Finset (Fin 2 × Fin 4) := Finset.univ \ B
  have hVB : Disjoint V B := by
    exact Finset.disjoint_left.mpr fun _ hv hb => (Finset.mem_sdiff.mp hv).2 hb
  obtain ⟨ψ, _, hfix, hclose, hgood⟩ :=
    exists_small_affineIndependent_subsets_relative V B hVB (fun v => φ₀ v.1 v.2) hε
  have hdec : (fun a b : Fin 2 × Fin 4 => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq (Fin 2 × Fin 4)) := Subsingleton.elim _ _
  rw [hdec] at hgood
  have hcover : V ∪ B = Finset.univ := by ext v; simp [V]
  have hcard : 4 ≤ Module.finrank ℝ F + 1 := by
    have h := (hind 0).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le (vectorSpan ℝ (range (φ₀ 0)))) 1)
    simpa only [Fintype.card_fin] using h
  have hfixed : ∀ i : Fin 2, ∀ j ∈ ({0, 1} : Finset (Fin 4)), ψ (i, j) = φ₀ i j := by
    intro i j hj
    exact hfix (Finset.mem_product.mpr ⟨Finset.mem_univ i, hj⟩)
  refine ⟨ψ, hfixed, ?_, hclose, ?_, fun s hs hAI => ?_⟩
  · intro j hj
    exact (hfixed 0 j hj).trans ((hcommon j hj).trans (hfixed 1 j hj).symm)
  · intro i
    let I : Finset (Fin 2 × Fin 4) := ({i} : Finset (Fin 2)).product Finset.univ
    have hfst : ∀ v ∈ I, v.1 = i := by
      intro v hv
      exact Finset.mem_singleton.mp (Finset.mem_product.mp hv).1
    let e : (I ∩ B : Finset (Fin 2 × Fin 4)) ↪ Fin 4 :=
      ⟨fun v => (v : Fin 2 × Fin 4).2, fun a b hab => Subtype.ext
        (Prod.ext ((hfst _ (Finset.mem_inter.mp a.property).1).trans
          (hfst _ (Finset.mem_inter.mp b.property).1).symm) hab)⟩
    have hIB : AffineIndependent ℝ (fun v : (I ∩ B : Finset (Fin 2 × Fin 4)) =>
        φ₀ (v : Fin 2 × Fin 4).1 (v : Fin 2 × Fin 4).2) := by
      have heq : (fun v : (I ∩ B : Finset (Fin 2 × Fin 4)) =>
          φ₀ (v : Fin 2 × Fin 4).1 (v : Fin 2 × Fin 4).2) =
            fun v : (I ∩ B : Finset (Fin 2 × Fin 4)) => φ₀ i (v : Fin 2 × Fin 4).2 := by
        funext v
        rw [hfst _ (Finset.mem_inter.mp v.property).1]
      rw [heq]
      exact (hind i).comp_embedding e
    have hIcard : I.card ≤ Module.finrank ℝ F + 1 := by
      simpa [I] using hcard
    have hI : AffineIndependent ℝ (fun v : I => ψ (v : Fin 2 × Fin 4)) :=
      hgood I (by rw [hcover]; exact Finset.subset_univ I) hIcard hIB
    let eI : Fin 4 ↪ I := ⟨fun j => ⟨(i, j), by simp [I]⟩,
      fun _ _ hab => congrArg (fun v : I => (v : Fin 2 × Fin 4).2) hab⟩
    exact hI.comp_embedding eI
  · exact hgood s (by rw [hcover]; exact Finset.subset_univ s) hs hAI

end DifferentialGeometry.Topology.PiecewiseLinear
