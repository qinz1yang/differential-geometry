import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSupportedModification
import Mathlib.Data.Set.Card

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem supported_second_trace_motion_comp
    {M ι : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {A B S O Z K₀ K₁ : Set M} {Γ : ι → Set M}
    (Ψ Φ : M ≃ₜ M) (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hK₀S : K₀ ⊆ S) (hK₁S : K₁ ⊆ S) (hSO : S ⊆ O)
    (hfix₀ : EqOn Ψ id K₀ᶜ) (hfix₁ : EqOn Φ id K₁ᶜ)
    (hΨ : IsPLOn n n Ψ O) (hΦ : IsPLOn n n Φ O)
    (hZ₀ : Disjoint K₀ Z) (hZ₁ : Disjoint K₁ Z)
    (I : Set ι) (J : Set I)
    (hkeep₀ : ∀ i : I, Disjoint K₀ (Γ i.1))
    (hkeep₁ : ∀ j : J, Disjoint K₁ (Γ j.1.1))
    (htrace : A ∩ Φ '' (Ψ '' B) = ⋃ j : J, Γ j.1.1) :
    let I' : Set ι := Subtype.val '' J
    let H := Ψ.trans Φ
    I' ⊆ I ∧ Nat.card I' = Nat.card J ∧
      IsCompact (K₀ ∪ K₁) ∧ K₀ ∪ K₁ ⊆ S ∧ EqOn H id (K₀ ∪ K₁)ᶜ ∧
      IsPLOn n n H O ∧ Disjoint (K₀ ∪ K₁) Z ∧ EqOn H id Z ∧
      (∀ i : I', Disjoint (K₀ ∪ K₁) (Γ i.1)) ∧
      (∀ i : I', ∀ x ∈ Γ i.1, H =ᶠ[𝓝 x] id) ∧
      A ∩ H '' B = ⋃ i : I', Γ i.1 := by
  let I' : Set ι := Subtype.val '' J
  let H := Ψ.trans Φ
  have hI : I' ⊆ I := by
    rintro i ⟨j, hj, rfl⟩
    exact j.2
  have hfix : EqOn H id (K₀ ∪ K₁)ᶜ := by
    intro x hx
    change Φ (Ψ x) = x
    calc
      Φ (Ψ x) = Φ x := congrArg Φ (hfix₀ (fun h => hx (Or.inl h)))
      _ = x := hfix₁ (fun h => hx (Or.inr h))
  have hZ : Disjoint (K₀ ∪ K₁) Z := disjoint_union_left.mpr ⟨hZ₀, hZ₁⟩
  have hkeep (i : I') : Disjoint (K₀ ∪ K₁) (Γ i.1) := by
    obtain ⟨j, hj, hji⟩ := i.2
    exact disjoint_union_left.mpr ⟨hkeep₀ ⟨i.1, hI i.2⟩, hji ▸ hkeep₁ ⟨j, hj⟩⟩
  have hO : Ψ '' O = O :=
    image_eq_of_homeomorph_eqOn_compl_of_subset Ψ hfix₀ (hK₀S.trans hSO)
  have hPL : IsPLOn n n H O := hΦ.comp_of_mapsTo hΨ
    (fun x hx => hO.subset (mem_image_of_mem Ψ hx))
  have hunion : (⋃ j : J, Γ j.1.1) = ⋃ i : I', Γ i.1 := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨⟨j.1.1, ⟨j.1, j.2, rfl⟩⟩, hxj⟩
    · intro x hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      obtain ⟨j, hj, hji⟩ := i.2
      exact mem_iUnion.mpr ⟨⟨j, hj⟩, hji.symm ▸ hxi⟩
  refine ⟨hI, Nat.card_image_of_injective Subtype.val_injective J,
    hK₀.union hK₁, union_subset hK₀S hK₁S, hfix, hPL, hZ,
    fun x hx => hfix (disjoint_right.mp hZ hx), hkeep, ?_, ?_⟩
  · intro i x hx
    filter_upwards [(hK₀.union hK₁).isClosed.isOpen_compl.mem_nhds
      (disjoint_right.mp (hkeep i) hx)] with y hy
    exact hfix hy
  · change A ∩ (Φ ∘ Ψ) '' B = _
    rw [image_comp, htrace, hunion]

end DifferentialGeometry.Topology.PiecewiseLinear
