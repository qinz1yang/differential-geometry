import DifferentialGeometry.Topology.PiecewiseLinear.DiskPseudoIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Homogeneity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isPolyhedron_zero_one_pair : IsPolyhedron ({0, 1} : Set ℝ) := by
  have h : ({0, 1} : Set ℝ) = Icc (0 : ℝ) 0 ∪ Icc (1 : ℝ) 1 := by
    rw [Icc_self, Icc_self, singleton_union]
  rw [h]
  exact isHPolytope_Icc.isPolyhedron.union isHPolytope_Icc.isPolyhedron

theorem IsPLPseudoIsotopicToId.comp [FiniteDimensional ℝ E] {P : Set E} {u v : E → E}
    (hu : IsPLPseudoIsotopicToId u P) (hv : IsPLPseudoIsotopicToId v P)
    (hvP : ∀ x ∈ P, v x ∈ P) : IsPLPseudoIsotopicToId (u ∘ v) P := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ := hu
  obtain ⟨Ξ, hΞ, hΞ0, hΞ1⟩ := hv
  refine ⟨Φ ∘ Ξ, hΞ.trans hΦ, fun x hx => ?_, fun x hx => ?_⟩
  · change Φ (Ξ (x, 0)) = (x, 0)
    rw [hΞ0 x hx, hΦ0 x hx]
  · change Φ (Ξ (x, 1)) = ((u ∘ v) x, 1)
    rw [hΞ1 x hx, hΦ1 (v x) (hvP x hx)]
    rfl

theorem IsPLPseudoIsotopicToId.of_leftInverse [FiniteDimensional ℝ E] {P : Set E} {u v : E → E}
    (hu : IsPLPseudoIsotopicToId u P)
    (hvP : ∀ x ∈ P, v x ∈ P) (hvu : ∀ x ∈ P, u (v x) = x) :
    IsPLPseudoIsotopicToId v P := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ := hu
  refine ⟨Function.invFunOn Φ (P ×ˢ Icc 0 1), hΦ.symm, fun x hx => ?_, fun x hx => ?_⟩
  · have hmem : (x, (0 : ℝ)) ∈ P ×ˢ Icc (0 : ℝ) 1 := ⟨hx, by norm_num⟩
    have := hΦ.bijOn.invOn_invFunOn.1 hmem
    rwa [hΦ0 x hx] at this
  · have hmem : (v x, (1 : ℝ)) ∈ P ×ˢ Icc (0 : ℝ) 1 := ⟨hvP x hx, by norm_num⟩
    have := hΦ.bijOn.invOn_invFunOn.1 hmem
    rwa [hΦ1 (v x) (hvP x hx), hvu x hx] at this

theorem exists_isPLHomeomorphOn_unitSquare_of_fixed_endpoints
    {w : ℝ → ℝ} (hw : IsPLHomeomorphOn w (Icc 0 1) (Icc 0 1)) (hw0 : w 0 = 0) (hw1 : w 1 = 1) :
    ∃ Ψ : ℝ × ℝ → ℝ × ℝ,
      IsPLHomeomorphOn Ψ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
        (∀ x ∈ Icc (0 : ℝ) 1, Ψ (x, 0) = (x, 0)) ∧
        (∀ x ∈ Icc (0 : ℝ) 1, Ψ (x, 1) = (w x, 1)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Ψ (0, t) = (0, t)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Ψ (1, t) = (1, t)) := by
  classical
  have hQ : IsPLBall 2 (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isPLBall_unit_square
  obtain ⟨A, hAfin, hAspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hAball : IsPLBall 2 A.space := hAspace ▸ hQ
  have hfront : frontier A.space = (boundaryComplex 2 A).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank
      (by simp [Module.finrank_prod] : Module.finrank ℝ (ℝ × ℝ) = 1 + 1) A
      hAball.isCombinatorialManifoldWithBoundary
  have hbd : (boundaryComplex 2 A).space =
      Icc (0 : ℝ) 1 ×ˢ ({1} : Set ℝ) ∪
        (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) ∪ ({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hfront, hAspace, frontier_prod_eq, isClosed_Icc.closure_eq,
      frontier_Icc (zero_le_one : (0 : ℝ) ≤ 1)]
    ext z
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  set θ : ℝ × ℝ → ℝ × ℝ := fun z => if z.2 = 1 then (w z.1, z.2) else z with hθdef
  have hsing : IsPolyhedron ({1} : Set ℝ) := by
    rw [← Icc_self (1 : ℝ)]
    exact isHPolytope_Icc.isPolyhedron
  have hW1poly : IsPolyhedron (Icc (0 : ℝ) 1 ×ˢ ({1} : Set ℝ)) :=
    isPolyhedron_prod_singleton isHPolytope_Icc.isPolyhedron 1
  have hW0poly : IsPolyhedron
      (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) ∪ ({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1) :=
    (isPolyhedron_prod_singleton isHPolytope_Icc.isPolyhedron 0).union
      (isPolyhedron_zero_one_pair.prod isHPolytope_Icc.isPolyhedron)
  have hθ1 : IsPLHomeomorphOn θ (Icc (0 : ℝ) 1 ×ˢ ({1} : Set ℝ))
      (Icc (0 : ℝ) 1 ×ˢ ({1} : Set ℝ)) := by
    refine (hw.prodMap hsing.isPLHomeomorphOn_id).congr ?_
    rintro z ⟨-, hz2⟩
    have hz2' : z.2 = 1 := hz2
    simp only [hθdef, if_pos hz2']
    rfl
  have hθid : EqOn θ id
      (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) ∪ ({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1) := by
    rintro z hz
    by_cases hz2 : z.2 = 1
    · simp only [hθdef, if_pos hz2]
      rcases hz with ⟨-, hzbot⟩ | ⟨hz1, -⟩
      · have hzbot' : z.2 = 0 := hzbot
        exact absurd (hz2.symm.trans hzbot') (by norm_num)
      · rcases hz1 with hz1 | hz1
        · have hz1' : z.1 = 0 := hz1
          rw [hz1', hw0]
          exact Prod.ext hz1'.symm rfl
        · have hz1' : z.1 = 1 := hz1
          rw [hz1', hw1]
          exact Prod.ext hz1'.symm rfl
    · simp only [hθdef, if_neg hz2]
      rfl
  have hθ0 : IsPLHomeomorphOn θ
      (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) ∪ ({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1)
      (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) ∪ ({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1) :=
    hW0poly.isPLHomeomorphOn_id.congr hθid
  have hmeet : θ '' (Icc (0 : ℝ) 1 ×ˢ ({1} : Set ℝ) ∩
      (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) ∪ ({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1)) =
      Icc (0 : ℝ) 1 ×ˢ ({1} : Set ℝ) ∩
        (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) ∪ ({0, 1} : Set ℝ) ×ˢ Icc (0 : ℝ) 1) :=
    ((hθid.mono inter_subset_right).image_eq).trans (image_id _)
  have hθbd := hθ1.union hθ0 hW1poly hW0poly hmeet
  rw [← hbd] at hθbd
  obtain ⟨Ψ, hΨ, hΨbd⟩ :=
    exists_isPLHomeomorphOn_of_boundaryComplex (n := 1) A A hAball hAball hθbd
  refine ⟨Ψ, hAspace ▸ hΨ, fun x hx => ?_, fun x hx => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have hmem : (x, (0 : ℝ)) ∈ (boundaryComplex 2 A).space := by
      rw [hbd]
      exact Or.inr (Or.inl ⟨hx, rfl⟩)
    rw [hΨbd hmem]
    exact if_neg (by norm_num)
  · have hmem : (x, (1 : ℝ)) ∈ (boundaryComplex 2 A).space := by
      rw [hbd]
      exact Or.inl ⟨hx, rfl⟩
    rw [hΨbd hmem]
    exact if_pos rfl
  · have hmem : ((0 : ℝ), t) ∈ (boundaryComplex 2 A).space := by
      rw [hbd]
      exact Or.inr (Or.inr ⟨Or.inl rfl, ht⟩)
    rw [hΨbd hmem]
    by_cases ht1 : t = 1
    · simp only [hθdef, if_pos ht1, hw0]
    · exact if_neg ht1
  · have hmem : ((1 : ℝ), t) ∈ (boundaryComplex 2 A).space := by
      rw [hbd]
      exact Or.inr (Or.inr ⟨Or.inr rfl, ht⟩)
    rw [hΨbd hmem]
    by_cases ht1 : t = 1
    · simp only [hθdef, if_pos ht1, hw1]
    · exact if_neg ht1

theorem exists_isPLHomeomorphOn_arc_prod_of_fixed_endpoints [FiniteDimensional ℝ E]
    {A : Set E} {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    {v : E → E} (hv : IsPLHomeomorphOn v A A) (hv0 : v (γ 0) = γ 0) (hv1 : v (γ 1) = γ 1) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ (A ×ˢ Icc (0 : ℝ) 1) (A ×ˢ Icc (0 : ℝ) 1) ∧
        (∀ x ∈ A, Φ (x, 0) = (x, 0)) ∧ (∀ x ∈ A, Φ (x, 1) = (v x, 1)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Φ (γ 0, t) = (γ 0, t)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Φ (γ 1, t) = (γ 1, t)) := by
  classical
  set g : E → ℝ := Function.invFunOn γ (Icc 0 1) with hgdef
  have hg : IsPLHomeomorphOn g A (Icc (0 : ℝ) 1) := hγ.symm
  have hgγ : ∀ t ∈ Icc (0 : ℝ) 1, g (γ t) = t := fun t ht => hγ.bijOn.invOn_invFunOn.1 ht
  have hγg : ∀ x ∈ A, γ (g x) = x := fun x hx => hγ.bijOn.invOn_invFunOn.2 hx
  have hw : IsPLHomeomorphOn (g ∘ (v ∘ γ)) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
    (hγ.trans hv).trans hg
  have hw0 : (g ∘ (v ∘ γ)) 0 = 0 := by
    change g (v (γ 0)) = 0
    rw [hv0, hgγ 0 (by norm_num)]
  have hw1 : (g ∘ (v ∘ γ)) 1 = 1 := by
    change g (v (γ 1)) = 1
    rw [hv1, hgγ 1 (by norm_num)]
  obtain ⟨Ψ, hΨ, hΨ0, hΨ1, hΨleft, hΨright⟩ :=
    exists_isPLHomeomorphOn_unitSquare_of_fixed_endpoints hw hw0 hw1
  have hprod : IsPLHomeomorphOn (Prod.map γ (id : ℝ → ℝ))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (A ×ˢ Icc (0 : ℝ) 1) :=
    hγ.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  have hinv : ∀ x ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
      Function.invFunOn (Prod.map γ (id : ℝ → ℝ)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (x, t)
        = (g x, t) := by
    intro x hx t ht
    have hmem : (g x, t) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := ⟨hg.bijOn.mapsTo hx, ht⟩
    have hmap : Prod.map γ (id : ℝ → ℝ) (g x, t) = (x, t) := Prod.ext (hγg x hx) rfl
    have := hprod.bijOn.invOn_invFunOn.1 hmem
    rwa [hmap] at this
  refine ⟨Prod.map γ (id : ℝ → ℝ) ∘ (Ψ ∘ Function.invFunOn (Prod.map γ (id : ℝ → ℝ))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)), (hprod.symm.trans hΨ).trans hprod,
    fun x hx => ?_, fun x hx => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · change Prod.map γ (id : ℝ → ℝ)
      (Ψ (Function.invFunOn (Prod.map γ (id : ℝ → ℝ)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (x, 0))) = _
    rw [hinv x hx 0 (by norm_num), hΨ0 (g x) (hg.bijOn.mapsTo hx)]
    exact Prod.ext (hγg x hx) rfl
  · change Prod.map γ (id : ℝ → ℝ)
      (Ψ (Function.invFunOn (Prod.map γ (id : ℝ → ℝ)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (x, 1))) = _
    rw [hinv x hx 1 (by norm_num), hΨ1 (g x) (hg.bijOn.mapsTo hx)]
    refine Prod.ext ?_ rfl
    change γ ((g ∘ (v ∘ γ)) (g x)) = v x
    change γ (g (v (γ (g x)))) = v x
    rw [hγg x hx]
    exact hγg (v x) (hv.bijOn.mapsTo hx)
  · have hγ0A : γ 0 ∈ A := hγ.bijOn.mapsTo (by norm_num)
    change Prod.map γ (id : ℝ → ℝ)
      (Ψ (Function.invFunOn (Prod.map γ (id : ℝ → ℝ)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
        (γ 0, t))) = _
    rw [hinv (γ 0) hγ0A t ht, hgγ 0 (by norm_num), hΨleft t ht]
    rfl
  · have hγ1A : γ 1 ∈ A := hγ.bijOn.mapsTo (by norm_num)
    change Prod.map γ (id : ℝ → ℝ)
      (Ψ (Function.invFunOn (Prod.map γ (id : ℝ → ℝ)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
        (γ 1, t))) = _
    rw [hinv (γ 1) hγ1A t ht, hgγ 1 (by norm_num), hΨright t ht]
    rfl

theorem isPLPseudoIsotopicToId_of_arc_decomposition [FiniteDimensional ℝ E]
    {S A B : Set E} {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) B) (hδ0 : δ 0 = γ 0) (hδ1 : δ 1 = γ 1)
    (hunion : A ∪ B = S) (hinter : A ∩ B = {γ 0, γ 1})
    {u : E → E} (hu : IsPLHomeomorphOn u S S) (hIA : u '' A = A) (hIB : u '' B = B)
    (hu0 : u (γ 0) = γ 0) (hu1 : u (γ 1) = γ 1) :
    IsPLPseudoIsotopicToId u S := by
  classical
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ
  have hB : IsPLBall 1 B := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hδ
  have hAS : A ⊆ S := hunion ▸ subset_union_left
  have hBS : B ⊆ S := hunion ▸ subset_union_right
  have huA : IsPLHomeomorphOn u A A := by
    have h := hu.restrict hA.isPolyhedron hAS
    rwa [hIA] at h
  have huB : IsPLHomeomorphOn u B B := by
    have h := hu.restrict hB.isPolyhedron hBS
    rwa [hIB] at h
  obtain ⟨ΦA, hΦA, hΦA0, hΦA1, hΦAl, hΦAr⟩ :=
    exists_isPLHomeomorphOn_arc_prod_of_fixed_endpoints hγ huA hu0 hu1
  obtain ⟨ΦB, hΦB, hΦB0, hΦB1, hΦBl, hΦBr⟩ :=
    exists_isPLHomeomorphOn_arc_prod_of_fixed_endpoints hδ huB (hδ0 ▸ hu0) (hδ1 ▸ hu1)
  rw [hδ0] at hΦBl
  rw [hδ1] at hΦBr
  have hPQ : A ×ˢ Icc (0 : ℝ) 1 ∩ B ×ˢ Icc (0 : ℝ) 1 = ({γ 0, γ 1} : Set E) ×ˢ Icc (0 : ℝ) 1 := by
    rw [prod_inter_prod, inter_self, hinter]
  have heq : EqOn ΦA ΦB (A ×ˢ Icc (0 : ℝ) 1 ∩ B ×ˢ Icc (0 : ℝ) 1) := by
    rw [hPQ]
    rintro z ⟨hz1, hz2⟩
    rcases hz1 with hz1 | hz1
    · have hz1' : z.1 = γ 0 := hz1
      have hz : z = (γ 0, z.2) := Prod.ext hz1' rfl
      rw [hz, hΦAl z.2 hz2, hΦBl z.2 hz2]
    · have hz1' : z.1 = γ 1 := hz1
      have hz : z = (γ 1, z.2) := Prod.ext hz1' rfl
      rw [hz, hΦAr z.2 hz2, hΦBr z.2 hz2]
  have hsurj : SurjOn ΦA (A ×ˢ Icc (0 : ℝ) 1 ∩ B ×ˢ Icc (0 : ℝ) 1)
      (A ×ˢ Icc (0 : ℝ) 1 ∩ B ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz
    refine ⟨z, hz, ?_⟩
    rw [hPQ] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rcases hz1 with hz1 | hz1
    · have hz1' : z.1 = γ 0 := hz1
      have hz : z = (γ 0, z.2) := Prod.ext hz1' rfl
      rw [hz, hΦAl z.2 hz2]
    · have hz1' : z.1 = γ 1 := hz1
      have hz : z = (γ 1, z.2) := Prod.ext hz1' rfl
      rw [hz, hΦAr z.2 hz2]
  obtain ⟨Φ, hΦ, hΦfA, hΦfB⟩ := exists_isPLHomeomorphOn_union
    (hA.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
    (hB.isPolyhedron.prod isHPolytope_Icc.isPolyhedron) hΦA hΦB heq hsurj
  rw [← union_prod, hunion] at hΦ
  refine ⟨Φ, hΦ, fun x hx => ?_, fun x hx => ?_⟩
  · rcases hunion ▸ hx with hx | hx
    · rw [hΦfA ⟨hx, by norm_num⟩, hΦA0 x hx]
    · rw [hΦfB ⟨hx, by norm_num⟩, hΦB0 x hx]
  · rcases hunion ▸ hx with hx | hx
    · rw [hΦfA ⟨hx, by norm_num⟩, hΦA1 x hx]
    · rw [hΦfB ⟨hx, by norm_num⟩, hΦB1 x hx]

theorem image_arc_eq_self_or_eq_other [FiniteDimensional ℝ E]
    {S A B : Set E} {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) B) (hδ0 : δ 0 = γ 0) (hδ1 : δ 1 = γ 1)
    (hunion : A ∪ B = S) (hinter : A ∩ B = {γ 0, γ 1})
    {u : E → E} (hu : IsPLHomeomorphOn u S S) (hu0 : u (γ 0) = γ 0) (hu1 : u (γ 1) = γ 1) :
    (u '' A = A ∧ u '' B = B) ∨ u '' A = B := by
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ
  have hB : IsPLBall 1 B := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hδ
  have hAcl : IsClosed A := hA.isPolyhedron.isClosed
  have hBcl : IsClosed B := hB.isPolyhedron.isClosed
  have hAS : A ⊆ S := hunion ▸ subset_union_left
  have hBS : B ⊆ S := hunion ▸ subset_union_right
  have hpairA : ({γ 0, γ 1} : Set E) ⊆ A := by
    refine pair_subset (hγ.bijOn.mapsTo (by norm_num)) (hγ.bijOn.mapsTo (by norm_num))
  have hpairB : ({γ 0, γ 1} : Set E) ⊆ B := by
    refine pair_subset ?_ ?_
    · exact hδ0 ▸ hδ.bijOn.mapsTo (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    · exact hδ1 ▸ hδ.bijOn.mapsTo (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have hA0 : IsConnected (A \ ({γ 0, γ 1} : Set E)) := hγ.isConnected_sdiff_endpoints zero_lt_one
  have hB0 : IsConnected (B \ ({γ 0, γ 1} : Set E)) := by
    have h := hδ.isConnected_sdiff_endpoints zero_lt_one
    rwa [hδ0, hδ1] at h
  have hdisj : (A \ ({γ 0, γ 1} : Set E)) ∩ (B \ ({γ 0, γ 1} : Set E)) = ∅ :=
    eq_empty_iff_forall_notMem.mpr fun x hx => hx.1.2 (hinter ▸ mem_inter hx.1.1 hx.2.1)
  have hends : ∀ x ∈ S, u x ∈ ({γ 0, γ 1} : Set E) → x ∈ ({γ 0, γ 1} : Set E) := by
    intro x hx hux
    rcases hux with h | h
    · exact Or.inl (hu.bijOn.injOn hx (hAS (hpairA (by norm_num))) (h.trans hu0.symm))
    · have h' : u x = γ 1 := h
      exact Or.inr (hu.bijOn.injOn hx (hAS (hpairA (by norm_num))) (h'.trans hu1.symm))
  have hSfix : u '' (S \ ({γ 0, γ 1} : Set E)) = S \ ({γ 0, γ 1} : Set E) := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, ⟨hxS, hxn⟩, rfl⟩
      exact ⟨hu.bijOn.mapsTo hxS, fun h => hxn (hends x hxS h)⟩
    · rintro y ⟨hyS, hyn⟩
      obtain ⟨x, hxS, rfl⟩ := hu.bijOn.surjOn hyS
      refine ⟨x, ⟨hxS, ?_⟩, rfl⟩
      rintro (h | h)
      · exact hyn (Or.inl (by rw [h]; exact hu0))
      · have h' : x = γ 1 := h
        exact hyn (Or.inr (by rw [h']; exact hu1))
  have hsplit : ∀ C : Set E, C ⊆ S → IsConnected (C \ ({γ 0, γ 1} : Set E)) →
      u '' (C \ ({γ 0, γ 1} : Set E)) ⊆ A \ ({γ 0, γ 1} : Set E) ∨
        u '' (C \ ({γ 0, γ 1} : Set E)) ⊆ B \ ({γ 0, γ 1} : Set E) := by
    intro C hCS hC0
    have havoid : ∀ y ∈ u '' (C \ ({γ 0, γ 1} : Set E)), y ∉ ({γ 0, γ 1} : Set E) := by
      rintro _ ⟨x, hx, rfl⟩ h
      exact hx.2 (hends x (hCS hx.1) h)
    have hsAB : u '' (C \ ({γ 0, γ 1} : Set E)) ⊆ A ∪ B := by
      rintro _ ⟨x, hx, rfl⟩
      have h : u x ∈ S := hu.bijOn.mapsTo (hCS hx.1)
      rwa [← hunion] at h
    have hconn : IsConnected (u '' (C \ ({γ 0, γ 1} : Set E))) :=
      hC0.image u (hu.isPiecewiseAffineOn.continuousOn.mono fun x hx => hCS hx.1)
    have hmain : u '' (C \ ({γ 0, γ 1} : Set E)) ⊆ A ∨ u '' (C \ ({γ 0, γ 1} : Set E)) ⊆ B := by
      by_cases hmA : (u '' (C \ ({γ 0, γ 1} : Set E)) ∩ A).Nonempty
      · by_cases hmB : (u '' (C \ ({γ 0, γ 1} : Set E)) ∩ B).Nonempty
        · obtain ⟨y, hy⟩ := isPreconnected_closed_iff.mp hconn.isPreconnected A B hAcl hBcl
            hsAB hmA hmB
          exact absurd (hinter ▸ hy.2) (havoid y hy.1)
        · refine Or.inl fun y hy => ?_
          rcases hsAB hy with h | h
          · exact h
          · exact absurd ⟨y, hy, h⟩ hmB
      · refine Or.inr fun y hy => ?_
        rcases hsAB hy with h | h
        · exact absurd ⟨y, hy, h⟩ hmA
        · exact h
    exact hmain.imp (fun h y hy => ⟨h hy, havoid y hy⟩) fun h y hy => ⟨h hy, havoid y hy⟩
  have hcover : u '' (A \ ({γ 0, γ 1} : Set E)) ∪ u '' (B \ ({γ 0, γ 1} : Set E)) =
      (A \ ({γ 0, γ 1} : Set E)) ∪ (B \ ({γ 0, γ 1} : Set E)) := by
    rw [← image_union, ← union_sdiff_distrib, hunion, hSfix]
  have hkey : ∀ X Y X' Y' : Set E, X ⊆ X' → Y ⊆ Y' → X ∪ Y = X' ∪ Y' → X' ∩ Y' = ∅ →
      X = X' ∧ Y = Y' := by
    intro X Y X' Y' hX hY hXY hXY'
    refine ⟨Subset.antisymm hX fun x hx => ?_, Subset.antisymm hY fun y hy => ?_⟩
    · rcases hXY.symm.subset (Or.inl hx) with h | h
      · exact h
      · exact absurd (hXY' ▸ mem_inter hx (hY h)) (notMem_empty x)
    · rcases hXY.symm.subset (Or.inr hy) with h | h
      · exact absurd (hXY' ▸ mem_inter (hX h) hy) (notMem_empty y)
      · exact h
  have himagepair : u '' ({γ 0, γ 1} : Set E) = {γ 0, γ 1} := by
    rw [image_pair, hu0, hu1]
  have hAeq : (A \ ({γ 0, γ 1} : Set E)) ∪ {γ 0, γ 1} = A := sdiff_union_of_subset hpairA
  have hBeq : (B \ ({γ 0, γ 1} : Set E)) ∪ {γ 0, γ 1} = B := sdiff_union_of_subset hpairB
  have hrestore : ∀ C D : Set E, ({γ 0, γ 1} : Set E) ⊆ C →
      u '' (C \ ({γ 0, γ 1} : Set E)) = D \ ({γ 0, γ 1} : Set E) →
      (D \ ({γ 0, γ 1} : Set E)) ∪ {γ 0, γ 1} = D → u '' C = D := by
    intro C D hCp hCD hDeq
    rw [← sdiff_union_of_subset hCp, image_union, hCD, himagepair, hDeq]
  rcases hsplit A hAS hA0 with hAa | hAb
  · rcases hsplit B hBS hB0 with hBa | hBb
    · exfalso
      have hsub : (A \ ({γ 0, γ 1} : Set E)) ∪ (B \ ({γ 0, γ 1} : Set E)) ⊆
          A \ ({γ 0, γ 1} : Set E) := hcover ▸ union_subset hAa hBa
      obtain ⟨y, hy⟩ := hB0.nonempty
      exact absurd (hdisj ▸ mem_inter (hsub (Or.inr hy)) hy) (notMem_empty y)
    · obtain ⟨hA', hB'⟩ := hkey _ _ _ _ hAa hBb hcover hdisj
      exact Or.inl ⟨hrestore A A hpairA hA' hAeq, hrestore B B hpairB hB' hBeq⟩
  · rcases hsplit B hBS hB0 with hBa | hBb
    · obtain ⟨hB', hA'⟩ := hkey _ _ _ _ hBa hAb ((union_comm _ _).trans hcover) hdisj
      exact Or.inr (hrestore A B hpairA hA' hBeq)
    · exfalso
      have hsub : (A \ ({γ 0, γ 1} : Set E)) ∪ (B \ ({γ 0, γ 1} : Set E)) ⊆
          B \ ({γ 0, γ 1} : Set E) := hcover ▸ union_subset hAb hBb
      obtain ⟨y, hy⟩ := hA0.nonempty
      exact absurd (hdisj ▸ mem_inter hy (hsub (Or.inl hy))) (notMem_empty y)

theorem isPLPseudoIsotopicToId_of_arc_decomposition_of_ne [FiniteDimensional ℝ E]
    {S A B : Set E} {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) B) (hδ0 : δ 0 = γ 0) (hδ1 : δ 1 = γ 1)
    (hunion : A ∪ B = S) (hinter : A ∩ B = {γ 0, γ 1})
    {u : E → E} (hu : IsPLHomeomorphOn u S S) (hu0 : u (γ 0) = γ 0) (hu1 : u (γ 1) = γ 1)
    (hswap : u '' A ≠ B) : IsPLPseudoIsotopicToId u S := by
  rcases image_arc_eq_self_or_eq_other hγ hδ hδ0 hδ1 hunion hinter hu hu0 hu1 with ⟨hIA, hIB⟩ | h
  · exact isPLPseudoIsotopicToId_of_arc_decomposition hγ hδ hδ0 hδ1 hunion hinter hu hIA hIB
      hu0 hu1
  · exact absurd h hswap

theorem IsPLPseudoIsotopicToId.congr {P : Set E} {u v : E → E}
    (hu : IsPLPseudoIsotopicToId u P) (huv : EqOn v u P) : IsPLPseudoIsotopicToId v P := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ := hu
  exact ⟨Φ, hΦ, hΦ0, fun x hx => by rw [hΦ1 x hx, huv hx]⟩

theorem exists_isPLHomeomorphOn_arc_fixing_endpoints_of_parametrization [FiniteDimensional ℝ E]
    {A : Set E} {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    {p q : E} (hp : p ∈ A \ ({γ 0, γ 1} : Set E)) (hq : q ∈ A \ ({γ 0, γ 1} : Set E)) :
    ∃ f : E → E, IsPLHomeomorphOn f A A ∧ f (γ 0) = γ 0 ∧ f (γ 1) = γ 1 ∧ f p = q := by
  obtain ⟨s, hs, hγs⟩ := hγ.bijOn.surjOn hp.1
  obtain ⟨t, ht, hγt⟩ := hγ.bijOn.surjOn hq.1
  have hinterior : ∀ {a : ℝ}, a ∈ Icc (0 : ℝ) 1 → ∀ {x : E}, γ a = x →
      x ∉ ({γ 0, γ 1} : Set E) → a ∈ Ioo (0 : ℝ) 1 := by
    intro a ha x hγa hx
    refine ⟨lt_of_le_of_ne ha.1 ?_, lt_of_le_of_ne ha.2 ?_⟩
    · intro h
      exact hx (Or.inl (hγa.symm.trans (congrArg γ h.symm)))
    · intro h
      exact hx (Or.inr (hγa.symm.trans (congrArg γ h)))
  obtain ⟨g, hg, hg0, hg1, hgs⟩ :=
    exists_isPLHomeomorphOn_Icc_fixing_endpoints (hinterior hs hγs hp.2) (hinterior ht hγt hq.2)
  refine ⟨γ ∘ (g ∘ Function.invFunOn γ (Icc 0 1)), hγ.symm.trans (hg.trans hγ), ?_, ?_, ?_⟩
  · change γ (g (Function.invFunOn γ (Icc 0 1) (γ 0))) = γ 0
    rw [hγ.bijOn.invOn_invFunOn.1 (show (0 : ℝ) ∈ Icc 0 1 by norm_num), hg0]
  · change γ (g (Function.invFunOn γ (Icc 0 1) (γ 1))) = γ 1
    rw [hγ.bijOn.invOn_invFunOn.1 (show (1 : ℝ) ∈ Icc 0 1 by norm_num), hg1]
  · change γ (g (Function.invFunOn γ (Icc 0 1) p)) = q
    rw [← hγs, hγ.bijOn.invOn_invFunOn.1 hs, hgs, hγt]

theorem isPLPseudoIsotopicToId_of_arc_support [FiniteDimensional ℝ E]
    {S A B : Set E} {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hBpoly : IsPolyhedron B) (hunion : A ∪ B = S) (hinter : A ∩ B = {γ 0, γ 1})
    {u : E → E} (huA : IsPLHomeomorphOn u A A) (hu0 : u (γ 0) = γ 0) (hu1 : u (γ 1) = γ 1)
    (huB : EqOn u id B) : IsPLPseudoIsotopicToId u S := by
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ
  obtain ⟨ΦA, hΦA, hΦA0, hΦA1, hΦAl, hΦAr⟩ :=
    exists_isPLHomeomorphOn_arc_prod_of_fixed_endpoints hγ huA hu0 hu1
  have hΦB : IsPLHomeomorphOn (id : E × ℝ → E × ℝ) (B ×ˢ Icc (0 : ℝ) 1) (B ×ˢ Icc (0 : ℝ) 1) :=
    (hBpoly.prod isHPolytope_Icc.isPolyhedron).isPLHomeomorphOn_id
  have hPQ : A ×ˢ Icc (0 : ℝ) 1 ∩ B ×ˢ Icc (0 : ℝ) 1 = ({γ 0, γ 1} : Set E) ×ˢ Icc (0 : ℝ) 1 := by
    rw [prod_inter_prod, inter_self, hinter]
  have hfix : ∀ z ∈ ({γ 0, γ 1} : Set E) ×ˢ Icc (0 : ℝ) 1, ΦA z = z := by
    rintro z ⟨hz1, hz2⟩
    rcases hz1 with hz1 | hz1
    · have hz : z = (γ 0, z.2) := Prod.ext hz1 rfl
      rw [hz, hΦAl z.2 hz2]
    · have hz1' : z.1 = γ 1 := hz1
      have hz : z = (γ 1, z.2) := Prod.ext hz1' rfl
      rw [hz, hΦAr z.2 hz2]
  have heq : EqOn ΦA id (A ×ˢ Icc (0 : ℝ) 1 ∩ B ×ˢ Icc (0 : ℝ) 1) := by
    rw [hPQ]
    exact fun z hz => hfix z hz
  have hsurj : SurjOn ΦA (A ×ˢ Icc (0 : ℝ) 1 ∩ B ×ˢ Icc (0 : ℝ) 1)
      (A ×ˢ Icc (0 : ℝ) 1 ∩ B ×ˢ Icc (0 : ℝ) 1) := fun z hz => ⟨z, hz, heq hz⟩
  obtain ⟨Φ, hΦ, hΦfA, hΦfB⟩ := exists_isPLHomeomorphOn_union
    (hA.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
    (hBpoly.prod isHPolytope_Icc.isPolyhedron) hΦA hΦB heq hsurj
  rw [← union_prod, hunion] at hΦ
  refine ⟨Φ, hΦ, fun x hx => ?_, fun x hx => ?_⟩
  · rcases hunion ▸ hx with hx | hx
    · rw [hΦfA ⟨hx, by norm_num⟩, hΦA0 x hx]
    · exact hΦfB ⟨hx, by norm_num⟩
  · rcases hunion ▸ hx with hx | hx
    · rw [hΦfA ⟨hx, by norm_num⟩, hΦA1 x hx]
    · rw [hΦfB ⟨hx, by norm_num⟩, huB hx]
      rfl

theorem exists_isPLPseudoIsotopicToId_map_eq_of_arc [FiniteDimensional ℝ E]
    {S A B : Set E} {ε : ℝ → E} (hε : IsPLHomeomorphOn ε (Icc 0 1) A)
    (hBpoly : IsPolyhedron B) (hunion : A ∪ B = S) (hinter : A ∩ B = {ε 0, ε 1})
    {p p' : E} (hp : p ∈ A \ ({ε 0, ε 1} : Set E)) (hp' : p' ∈ A \ ({ε 0, ε 1} : Set E)) :
    ∃ r : E → E, IsPLHomeomorphOn r S S ∧ IsPLPseudoIsotopicToId r S ∧ r p' = p := by
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hε
  obtain ⟨f, hf, hf0, hf1, hfp⟩ :=
    exists_isPLHomeomorphOn_arc_fixing_endpoints_of_parametrization hε hp' hp
  have heq : EqOn f id (A ∩ B) := by
    rw [hinter]
    rintro x hx
    rcases hx with hx | hx
    · rw [show x = ε 0 from hx]
      exact hf0
    · have hx' : x = ε 1 := hx
      rw [hx']
      exact hf1
  have hsurj : SurjOn f (A ∩ B) (A ∩ B) := fun x hx => ⟨x, hx, heq hx⟩
  obtain ⟨r, hr, hrA, hrB⟩ := exists_isPLHomeomorphOn_union hA.isPolyhedron hBpoly hf
    hBpoly.isPLHomeomorphOn_id heq hsurj
  rw [hunion] at hr
  have hrAA : IsPLHomeomorphOn r A A := hf.congr hrA
  refine ⟨r, hr, ?_, ?_⟩
  · refine isPLPseudoIsotopicToId_of_arc_support hε hBpoly hunion hinter hrAA ?_ ?_ hrB
    · rw [hrA (hε.bijOn.mapsTo (show (0 : ℝ) ∈ Icc 0 1 by norm_num))]
      exact hf0
    · rw [hrA (hε.bijOn.mapsTo (show (1 : ℝ) ∈ Icc 0 1 by norm_num))]
      exact hf1
  · rw [hrA hp'.1]
    exact hfp

theorem exists_arc_pair_interior_of_isPLSphere_one [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) {p p' : E} (hp : p ∈ S) (hp' : p' ∈ S) (hne : p ≠ p') :
    ∃ (A B : Set E) (ε : ℝ → E), IsPLHomeomorphOn ε (Icc 0 1) A ∧ IsPolyhedron B ∧
      A ∪ B = S ∧ A ∩ B = {ε 0, ε 1} ∧ p ∈ A \ ({ε 0, ε 1} : Set E) ∧
        p' ∈ A \ ({ε 0, ε 1} : Set E) := by
  obtain ⟨A₀, B₀, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hun, hin⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hp hp' hne
  have hquarter : (1 / 4 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hthree : (3 / 4 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hz₁S : δ (1 / 4) ∈ S := hun ▸ Or.inr (hδ.bijOn.mapsTo hquarter)
  have hz₂S : δ (3 / 4) ∈ S := hun ▸ Or.inr (hδ.bijOn.mapsTo hthree)
  have hzne : δ (1 / 4) ≠ δ (3 / 4) := fun h => by
    have hq := hδ.bijOn.injOn hquarter hthree h
    norm_num at hq
  have hnotA : ∀ a ∈ Icc (0 : ℝ) 1, a ≠ 0 → a ≠ 1 → δ a ∉ A₀ := by
    intro a ha ha0 ha1 hmem
    have hmeet : δ a ∈ ({p, p'} : Set E) := hin ▸ mem_inter hmem (hδ.bijOn.mapsTo ha)
    rcases hmeet with h | h
    · exact ha0 (hδ.bijOn.injOn ha (by norm_num) (h.trans hδ0.symm))
    · have h' : δ a = p' := h
      exact ha1 (hδ.bijOn.injOn ha (by norm_num) (h'.trans hδ1.symm))
  have hz₁A : δ (1 / 4) ∉ A₀ := hnotA _ hquarter (by norm_num) (by norm_num)
  have hz₂A : δ (3 / 4) ∉ A₀ := hnotA _ hthree (by norm_num) (by norm_num)
  obtain ⟨A₁, B₁, ε, ζ, hε, hζ, hε0, hε1, hζ0, hζ1, hun1, hin1⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hz₁S hz₂S hzne
  have hA₁ : IsPLBall 1 A₁ := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hε
  have hB₁ : IsPLBall 1 B₁ := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hζ
  have hA₀conn : IsConnected A₀ := by
    have h := (isConnected_Icc (zero_le_one : (0 : ℝ) ≤ 1)).image γ
      hγ.isPiecewiseAffineOn.continuousOn
    rwa [hγ.image_eq] at h
  have hA₀sub : A₀ ⊆ A₁ ∪ B₁ := by
    rw [hun1, ← hun]
    exact subset_union_left
  have hsplit : A₀ ⊆ A₁ ∨ A₀ ⊆ B₁ := by
    by_cases hmA : (A₀ ∩ A₁).Nonempty
    · by_cases hmB : (A₀ ∩ B₁).Nonempty
      · obtain ⟨y, hy⟩ := isPreconnected_closed_iff.mp hA₀conn.isPreconnected A₁ B₁
          hA₁.isPolyhedron.isClosed hB₁.isPolyhedron.isClosed hA₀sub hmA hmB
        rcases hin1 ▸ hy.2 with h | h
        · exact absurd (h ▸ hy.1) hz₁A
        · have h' : y = δ (3 / 4) := h
          exact absurd (h' ▸ hy.1) hz₂A
      · refine Or.inl fun y hy => ?_
        rcases hA₀sub hy with h | h
        · exact h
        · exact absurd ⟨y, hy, h⟩ hmB
    · refine Or.inr fun y hy => ?_
      rcases hA₀sub hy with h | h
      · exact absurd ⟨y, hy, h⟩ hmA
      · exact h
  have hpA₀ : p ∈ A₀ := hγ0 ▸ hγ.bijOn.mapsTo (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have hp'A₀ : p' ∈ A₀ := hγ1 ▸ hγ.bijOn.mapsTo (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have hout : ∀ x ∈ A₀, x ∉ ({δ (1 / 4), δ (3 / 4)} : Set E) := by
    intro x hx hmem
    rcases hmem with h | h
    · exact hz₁A (h ▸ hx)
    · have h' : x = δ (3 / 4) := h
      exact hz₂A (h' ▸ hx)
  rcases hsplit with hcase | hcase
  · refine ⟨A₁, B₁, ε, hε, hB₁.isPolyhedron, hun1, ?_, ⟨hcase hpA₀, ?_⟩, ⟨hcase hp'A₀, ?_⟩⟩
    · rw [hin1, hε0, hε1]
    · rw [hε0, hε1]
      exact hout p hpA₀
    · rw [hε0, hε1]
      exact hout p' hp'A₀
  · refine ⟨B₁, A₁, ζ, hζ, hA₁.isPolyhedron, ?_, ?_, ⟨hcase hpA₀, ?_⟩, ⟨hcase hp'A₀, ?_⟩⟩
    · rw [union_comm]
      exact hun1
    · rw [inter_comm, hin1, hζ0, hζ1]
    · rw [hζ0, hζ1]
      exact hout p hpA₀
    · rw [hζ0, hζ1]
      exact hout p' hp'A₀

theorem exists_isPLPseudoIsotopicToId_map_eq_of_isPLSphere_one [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) {p p' : E} (hp : p ∈ S) (hp' : p' ∈ S) :
    ∃ r : E → E, IsPLHomeomorphOn r S S ∧ IsPLPseudoIsotopicToId r S ∧ r p' = p := by
  by_cases hpp : p = p'
  · exact ⟨id, hS.isPolyhedron.isPLHomeomorphOn_id,
      isPLPseudoIsotopicToId_id hS.isPolyhedron, hpp.symm⟩
  · obtain ⟨A, B, ε, hε, hBpoly, hunion, hinter, hpA, hp'A⟩ :=
      exists_arc_pair_interior_of_isPLSphere_one hS hp hp' hpp
    exact exists_isPLPseudoIsotopicToId_map_eq_of_arc hε hBpoly hunion hinter hpA hp'A

theorem isPLPseudoIsotopicToId_of_comp_left [FiniteDimensional ℝ E] {S : Set E} {u r : E → E}
    (hu : IsPLHomeomorphOn u S S) (hr : IsPLHomeomorphOn r S S)
    (hrid : IsPLPseudoIsotopicToId r S) (hcomp : IsPLPseudoIsotopicToId (r ∘ u) S) :
    IsPLPseudoIsotopicToId u S := by
  have hinv : IsPLPseudoIsotopicToId (Function.invFunOn r S) S :=
    hrid.of_leftInverse (fun x hx => hr.bijOn.surjOn.mapsTo_invFunOn hx)
      fun x hx => hr.bijOn.invOn_invFunOn.2 hx
  refine (hinv.comp hcomp fun x hx => hr.bijOn.mapsTo (hu.bijOn.mapsTo hx)).congr ?_
  intro x hx
  exact (hr.bijOn.invOn_invFunOn.1 (hu.bijOn.mapsTo hx)).symm

end DifferentialGeometry.Topology.PiecewiseLinear
