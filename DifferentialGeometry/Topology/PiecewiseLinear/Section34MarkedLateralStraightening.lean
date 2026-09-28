import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SpanningArcBoundaryMap
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PlanarDiskBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PeriodicLateralExtension
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LateralFaceCover

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_rectangle_param_with_rim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : Set E} {δ : ℝ → E} (hδ : IsPLHomeomorphOn δ (Icc 0 1) A) :
    ∃ r : (Fin 3 → ℝ) → E × ℝ,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (A ×ˢ Icc (0 : ℝ) 1) ∧
      r '' stdSimplexBoundary 2 =
        ({δ 0, δ 1} ×ˢ Icc (0 : ℝ) 1) ∪ (A ×ˢ ({0, 1} : Set ℝ)) := by
  obtain ⟨r, hr⟩ := isPLBall_unit_square
  have hprod : IsPLHomeomorphOn (Prod.map δ id)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (A ×ˢ Icc (0 : ℝ) 1) :=
    hδ.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  refine ⟨Prod.map δ id ∘ r, hr.trans hprod, ?_⟩
  rw [image_comp, hr.image_stdSimplexBoundary_eq_frontier_real_prod, frontier_prod_eq,
    frontier_Icc zero_le_one, isClosed_Icc.closure_eq, image_union,
    prodMap_image_prod, prodMap_image_prod]
  simp only [image_pair, hδ.image_eq, id_eq, image_id']
  exact union_comm _ _

theorem exists_lateral_straightening_of_two_disk_faces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {A : Fin 2 → Set E} {δ : Fin 2 → ℝ → E} {a : Fin 2 → E}
    (hδ : ∀ i, IsPLHomeomorphOn (δ i) (Icc 0 1) (A i))
    (hδ₀ : ∀ i, δ i 0 = a 0) (hδ₁ : ∀ i, δ i 1 = a 1)
    (hAcover : A 0 ∪ A 1 = P) (hAmeet : A 0 ∩ A 1 = {a 0, a 1})
    {T F : Fin 2 → Set (E × ℝ)} {γ : Fin 2 → ℝ → E × ℝ}
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1) (T i))
    (hγ₀ : ∀ i, γ i 0 = (a i, 0)) (hγ₁ : ∀ i, γ i 1 = (a i, 1))
    (hTdis : Disjoint (T 0) (T 1))
    (hTrim : ∀ i, T i ∩ (P ×ˢ ({0, 1} : Set ℝ)) = {(a i, 0), (a i, 1)})
    {s : Fin 2 → (Fin 3 → ℝ) → E × ℝ}
    (hs : ∀ i, IsPLHomeomorphOn (s i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (F i))
    (hsrim : ∀ i, s i '' stdSimplexBoundary 2 =
      (T 0 ∪ T 1) ∪ (A i ×ˢ ({0, 1} : Set ℝ)))
    (hFcover : F 0 ∪ F 1 = P ×ˢ Icc (0 : ℝ) 1)
    (hFmeet : F 0 ∩ F 1 = T 0 ∪ T 1) :
    ∃ H : E × ℝ → E × ℝ,
      IsPLHomeomorphOn H (P ×ˢ Icc (0 : ℝ) 1) (P ×ˢ Icc (0 : ℝ) 1) ∧
      EqOn H id (P ×ˢ ({0, 1} : Set ℝ)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → H (a i, t) = γ i t) ∧
      ∀ i, H '' (A i ×ˢ Icc (0 : ℝ) 1) = F i := by
  classical
  have hunion (B : Fin 2 → Set (E × ℝ)) : (⋃ i, B i) = B 0 ∪ B 1 := by
    ext x
    simp only [mem_iUnion, Fin.exists_fin_two, mem_union]
  have hApoly (i : Fin 2) : IsPolyhedron (A i) :=
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn (hδ i)).isPolyhedron
  have hP : IsPolyhedron P := hAcover ▸ (hApoly 0).union (hApoly 1)
  have hAP (i : Fin 2) : A i ⊆ P := by
    fin_cases i
    · exact hAcover ▸ subset_union_left
    · exact hAcover ▸ subset_union_right
  have ha (i : Fin 2) : a i ∈ P := by
    fin_cases i
    · exact hAP 0 (hδ₀ 0 ▸ (hδ 0).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩)
    · exact hAP 0 (hδ₁ 0 ▸ (hδ 0).bijOn.mapsTo ⟨zero_le_one, le_rfl⟩)
  have hdis : Pairwise fun i j => Disjoint (T i) (T j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hTdis
    · exact hTdis.symm
    · exact (hij rfl).elim
  obtain ⟨φ, hφ, hφfix, hφγ⟩ :=
    exists_isPLHomeomorphOn_rims_and_spanning_arcs hP ha hγ hγ₀ hγ₁ hdis hTrim
  choose r hr hrim using fun i => exists_rectangle_param_with_rim (hδ i)
  have hrim' (i : Fin 2) : r i '' stdSimplexBoundary 2 =
      ({a 0, a 1} ×ˢ Icc (0 : ℝ) 1) ∪ (A i ×ˢ ({0, 1} : Set ℝ)) := by
    rw [hrim i, hδ₀ i, hδ₁ i]
  have hsource : (⋃ i, r i '' stdSimplexBoundary 2) =
      (P ×ˢ ({0, 1} : Set ℝ)) ∪ ⋃ i, ({a i} ×ˢ Icc (0 : ℝ) 1) := by
    rw [hunion, hrim', hrim', hunion, ← hAcover]
    ext x
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  have htarget : (⋃ i, s i '' stdSimplexBoundary 2) =
      (P ×ˢ ({0, 1} : Set ℝ)) ∪ ⋃ i, T i := by
    rw [hunion, hsrim, hsrim, hunion, ← hAcover]
    ext x
    simp only [mem_union, mem_prod]
    tauto
  have hφV (i : Fin 2) : φ '' ({a i} ×ˢ Icc (0 : ℝ) 1) = T i := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hx' : x = (a i, x.2) := Prod.ext hx.1 rfl
      rw [hx', hφγ i x.2 hx.2]
      exact (hγ i).bijOn.mapsTo hx.2
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := (hγ i).bijOn.surjOn hy
      exact ⟨(a i, t), ⟨rfl, ht⟩, hφγ i t ht⟩
  have hφr (i : Fin 2) : φ '' (r i '' stdSimplexBoundary 2) =
      s i '' stdSimplexBoundary 2 := by
    have hv : ({a 0, a 1} ×ˢ Icc (0 : ℝ) 1) =
        ({a 0} ×ˢ Icc (0 : ℝ) 1) ∪ ({a 1} ×ˢ Icc (0 : ℝ) 1) := by
      ext x
      simp only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_union]
      tauto
    rw [hrim', hsrim, hv, image_union, image_union, hφV, hφV,
      (hφfix.mono (prod_mono_left (hAP i))).image_eq, image_id]
  have hRmeet (i j : Fin 2) (hij : i ≠ j) :
      (A i ×ˢ Icc (0 : ℝ) 1) ∩ (A j ×ˢ Icc (0 : ℝ) 1) ⊆
        r i '' stdSimplexBoundary 2 := by
    have hmeet : A i ∩ A j = {a 0, a 1} := by
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hAmeet
      · exact inter_comm _ _ |>.trans hAmeet
      · exact (hij rfl).elim
    rw [hrim']
    exact fun x hx => Or.inl ⟨hmeet ▸ ⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
  have hSmeet (i j : Fin 2) (hij : i ≠ j) :
      F i ∩ F j ⊆ s i '' stdSimplexBoundary 2 := by
    have hmeet : F i ∩ F j = T 0 ∪ T 1 := by
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hFmeet
      · exact inter_comm _ _ |>.trans hFmeet
      · exact (hij rfl).elim
    rw [hmeet, hsrim]
    exact subset_union_left
  obtain ⟨H, hH, hHφ, hHi⟩ :=
    exists_isPLHomeomorphOn_finite_ball_union_of_boundary_maps hr hs hRmeet hSmeet
      (hsource.symm ▸ htarget.symm ▸ hφ) hφr
  have hcover : (⋃ i, A i ×ˢ Icc (0 : ℝ) 1) = P ×ˢ Icc (0 : ℝ) 1 := by
    rw [hunion, ← union_prod, hAcover]
  rw [hcover, hunion, hFcover] at hH
  rw [hsource] at hHφ
  refine ⟨H, hH, fun x hx => (hHφ (Or.inl hx)).trans (hφfix hx), ?_, hHi⟩
  intro i t ht
  have hmem : (a i, t) ∈ ⋃ i, {a i} ×ˢ Icc (0 : ℝ) 1 := mem_iUnion.mpr ⟨i, rfl, ht⟩
  exact (hHφ (Or.inr hmem)).trans (hφγ i t ht)

theorem exists_lateral_straightening_of_spanning_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    {Z : (r '' stdSimplexBoundary 2) → Set (E × ℝ)}
    (hZ : ∀ z, IsPreconnected (Z z))
    (hZside : ∀ z, Z z ⊆ (r '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1)
    (hZ₀ : ∀ z, Z z ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({0} : Set ℝ)) = {((z : E), 0)})
    (hZ₁ : ∀ z, Z z ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ)) = {((z : E), 1)})
    (hdis : Pairwise fun z w => Disjoint (Z z) (Z w))
    (hcover : ⋃ z, Z z = (r '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1)
    {x y : r '' stdSimplexBoundary 2} (hxy : x ≠ y) {α β : ℝ → E × ℝ}
    (hα : IsPLHomeomorphOn α (Icc 0 1) (Z x))
    (hβ : IsPLHomeomorphOn β (Icc 0 1) (Z y))
    (hα₀ : α 0 = ((x : E), 0)) (hα₁ : α 1 = ((x : E), 1))
    (hβ₀ : β 0 = ((y : E), 0)) (hβ₁ : β 1 = ((y : E), 1)) :
    ∃ H : E × ℝ → E × ℝ,
      IsPLHomeomorphOn H ((r '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1)
        ((r '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) ∧
      EqOn H id ((r '' stdSimplexBoundary 2) ×ˢ ({0, 1} : Set ℝ)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, H ((x : E), t) = α t ∧ H ((y : E), t) = β t := by
  obtain ⟨A₀, A₁, δ₀, δ₁, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hAcover, hAmeet⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hr.isPLSphere_image_stdSimplexBoundary x.2 y.2
      (fun h => hxy (Subtype.ext h))
  obtain ⟨F₀, F₁, q₀, q₁, hq₀, hq₁, hFcover, hFmeet, hrim₀, hrim₁, -⟩ :=
    exists_complementary_lateral_disks hr zero_lt_one hZ hZside hZ₀ hZ₁ hdis hcover
      hα hβ hδ₀ hδ₁ hα₀ hα₁ hβ₀ hβ₁ hδ₀₀ hδ₀₁ hδ₁₀ hδ₁₁ hAcover hAmeet
  have hTrim (z : r '' stdSimplexBoundary 2) :
      Z z ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({0, 1} : Set ℝ)) =
        {((z : E), 0), ((z : E), 1)} := by
    rw [← singleton_union, prod_union, inter_union_distrib_left, hZ₀, hZ₁, singleton_union]
  have hrim (A : Set E) (q : (Fin 3 → ℝ) → E × ℝ)
      (hq : q '' stdSimplexBoundary 2 =
        ((Z x ∪ (A ×ˢ ({0} : Set ℝ))) ∪ Z y) ∪ (A ×ˢ ({1} : Set ℝ))) :
      q '' stdSimplexBoundary 2 = (Z x ∪ Z y) ∪ (A ×ˢ ({0, 1} : Set ℝ)) := by
    rw [hq]
    ext z
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  obtain ⟨H, hH, hfix, hγ, -⟩ := exists_lateral_straightening_of_two_disk_faces
    (A := ![A₀, A₁]) (δ := ![δ₀, δ₁]) (a := ![(x : E), (y : E)])
    (T := ![Z x, Z y]) (F := ![F₀, F₁]) (γ := ![α, β]) (s := ![q₀, q₁])
    (Fin.forall_fin_two.mpr ⟨hδ₀, hδ₁⟩)
    (Fin.forall_fin_two.mpr ⟨hδ₀₀, hδ₁₀⟩)
    (Fin.forall_fin_two.mpr ⟨hδ₀₁, hδ₁₁⟩) hAcover hAmeet
    (Fin.forall_fin_two.mpr ⟨hα, hβ⟩)
    (Fin.forall_fin_two.mpr ⟨hα₀, hβ₀⟩)
    (Fin.forall_fin_two.mpr ⟨hα₁, hβ₁⟩) (hdis hxy)
    (Fin.forall_fin_two.mpr ⟨hTrim x, hTrim y⟩)
    (Fin.forall_fin_two.mpr ⟨hq₀, hq₁⟩)
    (Fin.forall_fin_two.mpr ⟨hrim A₀ q₀ hrim₀, hrim A₁ q₁ hrim₁⟩)
    hFcover hFmeet
  exact ⟨H, hH, hfix, fun t ht => ⟨hγ 0 t ht, hγ 1 t ht⟩⟩

open Classical in
theorem exists_prism_extension_fixed_caps_of_lateral_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {φ : E × ℝ → E × ℝ}
    (hφ : IsPLHomeomorphOn φ ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)
      ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))
    (hfix : EqOn φ id ((boundaryComplex 2 D).space ×ˢ ({0, 1} : Set ℝ))) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ (D.space ×ˢ Icc (0 : ℝ) 1) (D.space ×ˢ Icc (0 : ℝ) 1) ∧
      EqOn Φ φ ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1) ∧
      EqOn Φ id (D.space ×ˢ ({0, 1} : Set ℝ)) := by
  classical
  let _ : Finite (boundaryComplex 2 D).faces := (boundaryComplex_faces_finite 2 D).to_subtype
  have hends : IsPolyhedron ({0, 1} : Set ℝ) := by
    rw [← singleton_union]
    exact (isHPolytope_singleton (0 : ℝ)).isPolyhedron.union
      (isHPolytope_singleton (1 : ℝ)).isPolyhedron
  have hcaps := hD.isPolyhedron.prod hends
  have hside := (isPolyhedron_space (boundaryComplex 2 D)).prod
    (show IsPolyhedron (Icc (0 : ℝ) 1) from isHPolytope_Icc.isPolyhedron)
  have heq : EqOn id φ
      ((D.space ×ˢ {0, 1}) ∩ ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)) :=
    fun x hx => (hfix ⟨hx.2.1, hx.1.2⟩).symm
  obtain ⟨b, hb, hbcap, hbside⟩ := exists_isPLHomeomorphOn_union hcaps hside
    hcaps.isPLHomeomorphOn_id hφ heq (surjOn_id _)
  have hprism := isPLBall_three_prod hD (isPLBall_Icc (zero_lt_one' ℝ))
  obtain ⟨K, hKfin, hKspace⟩ := hprism.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 3 K.space := hKspace.symm ▸ hprism
  have hbd := boundaryComplex_space_prism D hD (zero_lt_one' ℝ) K hKspace
  have hbb : IsPLHomeomorphOn b (boundaryComplex 3 K).space
      (boundaryComplex 3 K).space := by rw [hbd]; exact hb
  obtain ⟨Φ, hΦ, hΦb⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K K hK hK hbb
  rw [hKspace] at hΦ
  rw [hbd] at hΦb
  exact ⟨Φ, hΦ, fun x hx => (hΦb (Or.inr hx)).trans (hbside hx),
    fun x hx => (hΦb (Or.inl hx)).trans (hbcap hx)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
