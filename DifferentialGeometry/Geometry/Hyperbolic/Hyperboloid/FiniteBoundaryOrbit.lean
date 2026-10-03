import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryOrbit
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Nilpotent
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Margulis
import DifferentialGeometry.Topology.Algebra.Group.FiniteOrbit

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem exists_finite_boundary_orbit_of_isNilpotent_of_finiteIndex
    (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E))
    (H : Subgroup Γ) [H.FiniteIndex] [Group.IsNilpotent H]
    (hfree : ∀ h : H, h ≠ 1 → ∀ x : Hyperboloid E,
      ((h : Γ) : Hyperboloid E ≃ᵢ Hyperboloid E) x ≠ x) :
    ∃ ξ : Metric.sphere (0 : E) 1,
      (Set.range (fun γ : Γ => boundaryHomeomorph
        (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ)).Finite := by
  let K := H.map Γ.subtype
  let e : H ≃* K := H.equivMapOfInjective Γ.subtype Γ.subtype_injective
  let _ : Group.IsNilpotent K := (Group.isNilpotent_congr e).mp inferInstance
  have hfreeK (k : K) (hk : k ≠ 1) (x : Hyperboloid E) :
      (k : Hyperboloid E ≃ᵢ Hyperboloid E) x ≠ x := by
    have hne : e.symm k ≠ 1 := by
      intro heq
      apply hk
      calc
        k = e (e.symm k) := (e.apply_symm_apply k).symm
        _ = 1 := by rw [heq, map_one]
    have hcoe : ((e.symm k : Γ) : Hyperboloid E ≃ᵢ Hyperboloid E) =
        (k : Hyperboloid E ≃ᵢ Hyperboloid E) :=
      congrArg Subtype.val (e.apply_symm_apply k)
    rw [← hcoe]
    exact hfree (e.symm k) hne x
  obtain ⟨ξ, hξ⟩ := exists_boundary_orbit_encard_le_two_of_isNilpotent K hfreeK
  let _ : MulAction Γ (Metric.sphere (0 : E) 1) :=
    { smul := fun γ ξ => boundaryHomeomorph (γ : Hyperboloid E ≃ᵢ Hyperboloid E) ξ
      one_smul := fun ξ => by
        change boundaryHomeomorph (IsometryEquiv.refl (Hyperboloid E)) ξ = ξ
        rw [boundaryHomeomorph_refl]
        rfl
      mul_smul := fun γ δ ξ => by
        change boundaryHomeomorph ((δ : Hyperboloid E ≃ᵢ Hyperboloid E).trans
          (γ : Hyperboloid E ≃ᵢ Hyperboloid E)) ξ = _
        rw [boundaryHomeomorph_trans]
        rfl }
  have hfinite : (MulAction.orbit H ξ).Finite := by
    apply (Set.finite_of_encard_le_coe hξ).subset
    rintro y ⟨h, rfl⟩
    exact ⟨e h, rfl⟩
  exact ⟨ξ, MulAction.finite_orbit_of_finiteIndex H ξ hfinite⟩

theorem exists_pos_forall_exists_finite_boundary_orbit_small_displacement :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E)) [DiscreteTopology Γ],
        (∀ γ : Γ, γ ≠ 1 → ∀ y : Hyperboloid E,
          (γ : Hyperboloid E ≃ᵢ Hyperboloid E) y ≠ y) →
        ∀ x : Hyperboloid E,
          let L := Subgroup.closure
            {g : Γ | dist ((g : Hyperboloid E ≃ᵢ Hyperboloid E) x) x < ε}
          ∃ ξ : Metric.sphere (0 : E) 1,
            (Set.range (fun g : L => boundaryHomeomorph
              ((g : Γ) : Hyperboloid E ≃ᵢ Hyperboloid E) ξ)).Finite := by
  obtain ⟨ε, hε, N, hN⟩ := margulis_lemma (E := E)
  refine ⟨ε, hε, ?_⟩
  intro Γ _ hfree x
  let L := Subgroup.closure
    {g : Γ | dist ((g : Hyperboloid E ≃ᵢ Hyperboloid E) x) x < ε}
  obtain ⟨H, hnil, hcard⟩ := hN Γ x
  let _ : Group.IsNilpotent H := hnil
  let _ : Finite (L ⧸ H) := ENat.card_lt_top.mp (hcard.trans_lt (ENat.natCast_lt_top N))
  let _ : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let K := L.map Γ.subtype
  let e : L ≃* K := L.equivMapOfInjective Γ.subtype Γ.subtype_injective
  let J := H.map e.toMonoidHom
  let _ : Group.IsNilpotent J :=
    (Group.isNilpotent_congr (e.subgroupMap H)).mp hnil
  let _ : J.FiniteIndex := Subgroup.FiniteIndex.map_of_surjective H e.surjective
  have hfreeK (k : K) (hk : k ≠ 1) (y : Hyperboloid E) :
      (k : Hyperboloid E ≃ᵢ Hyperboloid E) y ≠ y := by
    let g : L := e.symm k
    have hg : (g : Γ) ≠ 1 := by
      intro heq
      have hg1 : g = 1 := Subtype.ext heq
      apply hk
      calc
        k = e g := (e.apply_symm_apply k).symm
        _ = 1 := by rw [hg1, map_one]
    have hcoe : ((g : Γ) : Hyperboloid E ≃ᵢ Hyperboloid E) =
        (k : Hyperboloid E ≃ᵢ Hyperboloid E) :=
      congrArg Subtype.val (e.apply_symm_apply k)
    rw [← hcoe]
    exact hfree (g : Γ) hg y
  obtain ⟨ξ, hξ⟩ := exists_finite_boundary_orbit_of_isNilpotent_of_finiteIndex K J
    (fun h hh => hfreeK h (fun heq => hh (Subtype.ext heq)))
  refine ⟨ξ, hξ.subset ?_⟩
  rintro y ⟨g, rfl⟩
  exact ⟨e g, rfl⟩

theorem exists_pos_forall_exists_boundary_fixedPoint_small_displacement :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E)) [DiscreteTopology Γ],
        (∀ γ : Γ, γ ≠ 1 → ∀ y : Hyperboloid E,
          (γ : Hyperboloid E ≃ᵢ Hyperboloid E) y ≠ y) →
        ∀ x : Hyperboloid E,
          let L := Subgroup.closure
            {g : Γ | dist ((g : Hyperboloid E ≃ᵢ Hyperboloid E) x) x < ε}
          ∃ ξ : Metric.sphere (0 : E) 1,
            ∀ g : L, boundaryHomeomorph
              ((g : Γ) : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ := by
  obtain ⟨ε, hε, h⟩ := exists_pos_forall_exists_finite_boundary_orbit_small_displacement (E := E)
  refine ⟨ε, hε, ?_⟩
  intro Γ _ hfree x
  let L := Subgroup.closure
    {g : Γ | dist ((g : Hyperboloid E ≃ᵢ Hyperboloid E) x) x < ε}
  obtain ⟨ξ, hξ⟩ := h Γ hfree x
  let K := L.map Γ.subtype
  let e : L ≃* K := L.equivMapOfInjective Γ.subtype Γ.subtype_injective
  let i : K →* Γ := Subgroup.inclusion (Subgroup.map_subtype_le L)
  have hfreeK (k : K) (hk : k ≠ 1) (y : Hyperboloid E) :
      (k : Hyperboloid E ≃ᵢ Hyperboloid E) y ≠ y := by
    apply hfree (i k) ?_ y
    intro hi
    apply hk
    apply Subgroup.inclusion_injective (Subgroup.map_subtype_le L)
    simpa only [map_one] using hi
  have hfiniteK : (Set.range (fun k : K => boundaryHomeomorph
      (k : Hyperboloid E ≃ᵢ Hyperboloid E) ξ)).Finite := by
    apply hξ.subset
    rintro y ⟨k, rfl⟩
    refine ⟨e.symm k, ?_⟩
    have hcoe : ((e.symm k : Γ) : Hyperboloid E ≃ᵢ Hyperboloid E) =
        (k : Hyperboloid E ≃ᵢ Hyperboloid E) :=
      congrArg Subtype.val (e.apply_symm_apply k)
    exact congrArg (fun f : Hyperboloid E ≃ᵢ Hyperboloid E => boundaryHomeomorph f ξ) hcoe
  refine ⟨ξ, ?_⟩
  intro g
  exact boundaryHomeomorph_eq_self_of_finite_orbit K hfreeK ξ hfiniteK (e g)

end DifferentialGeometry.Hyperboloid
