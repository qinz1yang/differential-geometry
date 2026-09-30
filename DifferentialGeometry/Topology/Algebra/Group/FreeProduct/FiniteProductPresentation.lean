import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteFreeFactors
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w
namespace GC.Group

abbrev sumGroupFamily {ι : Type v} {κ : Type w}
    (A : ι → Type u) (B : κ → Type u) : ι ⊕ κ → Type u
  | .inl i => A i
  | .inr j => B j
@[reducible] instance sumGroupFamily_group {ι : Type v} {κ : Type w}
    (A : ι → Type u) (B : κ → Type u) [∀ i, Group (A i)] [∀ j, Group (B j)] :
    ∀ k, Group (sumGroupFamily A B k)
  | .inl i => inferInstanceAs (Group (A i))
  | .inr j => inferInstanceAs (Group (B j))

def coprodISumEquiv {ι : Type v} {κ : Type w}
    (A : ι → Type u) (B : κ → Type u) [∀ i, Group (A i)] [∀ j, Group (B j)] :
    Monoid.CoprodI (sumGroupFamily A B) ≃*
      Monoid.Coprod (Monoid.CoprodI A) (Monoid.CoprodI B) := by
  let f : Monoid.CoprodI (sumGroupFamily A B) →*
      Monoid.Coprod (Monoid.CoprodI A) (Monoid.CoprodI B) :=
    Monoid.CoprodI.lift (fun k => match k with
      | .inl i => Monoid.Coprod.inl.comp (Monoid.CoprodI.of (M := A) (i := i))
      | .inr j => Monoid.Coprod.inr.comp (Monoid.CoprodI.of (M := B) (i := j)))
  let l : Monoid.CoprodI A →* Monoid.CoprodI (sumGroupFamily A B) :=
    Monoid.CoprodI.lift fun i => Monoid.CoprodI.of (M := sumGroupFamily A B) (i := Sum.inl i)
  let r : Monoid.CoprodI B →* Monoid.CoprodI (sumGroupFamily A B) :=
    Monoid.CoprodI.lift fun j => Monoid.CoprodI.of (M := sumGroupFamily A B) (i := Sum.inr j)
  let g := Monoid.Coprod.lift l r
  refine MonoidHom.toMulEquiv f g ?_ ?_
  · apply Monoid.CoprodI.ext_hom
    intro k
    cases k <;> ext x <;>
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, f,
        Monoid.CoprodI.lift_of] <;> simp [g, l, r]
  · apply Monoid.Coprod.hom_ext
    · apply Monoid.CoprodI.ext_hom
      intro i
      ext x
      simp [f, g, l, r]
    · apply Monoid.CoprodI.ext_hom
      intro j
      ext x
      simp [f, g, l, r]

def HasFiniteIndecomposablePresentation (G : Type u) [Group G] : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (F : ι → Type u) (_ : ∀ i, Group (F i)),
    (∀ i, Nontrivial (F i) ∧ Group.FG (F i) ∧ FreelyIndecomposable (F i)) ∧
      Nonempty (G ≃* Monoid.CoprodI F)

theorem finiteIndecomposablePresentation_of_subsingleton (G : Type u)
    [Group G] [Subsingleton G] : HasFiniteIndecomposablePresentation G := by
  let F : Empty → Type u := fun _ => PUnit
  let : Unique G := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  exact ⟨Empty, inferInstance, F, fun _ => inferInstance, fun i => i.elim,
    ⟨(MulEquiv.ofUnique : G ≃* PUnit.{u+1}).trans
      (DifferentialGeometry.Algebra.Group.coprodIEmptyEquivPUnit F).symm⟩⟩

theorem finiteIndecomposablePresentation_single (G : Type u)
    [Group G] [Nontrivial G] [Group.FG G] (h : FreelyIndecomposable G) :
    HasFiniteIndecomposablePresentation G :=
  ⟨PUnit, inferInstance, fun _ => G, fun _ => inferInstance,
    fun _ => ⟨inferInstance, inferInstance, h⟩,
    ⟨(DifferentialGeometry.Algebra.Group.coprodISingletonEquiv G).symm⟩⟩

theorem finiteIndecomposablePresentation_combine {G A B : Type u}
    [Group G] [Group A] [Group B]
    (e : G ≃* Monoid.Coprod A B)
    (ha : HasFiniteIndecomposablePresentation A)
    (hb : HasFiniteIndecomposablePresentation B) :
    HasFiniteIndecomposablePresentation G := by
  obtain ⟨ι, hi, F, hF, hf, ⟨ea⟩⟩ := ha
  obtain ⟨κ, hk, J, hJ, hj, ⟨eb⟩⟩ := hb
  refine ⟨ι ⊕ κ, inferInstance, sumGroupFamily F J, inferInstance, ?_,
    ⟨e.trans ((ea.coprodCongr eb).trans (coprodISumEquiv F J).symm)⟩⟩
  intro k
  cases k with
  | inl i => exact hf i
  | inr j => exact hj j

end GC.Group
