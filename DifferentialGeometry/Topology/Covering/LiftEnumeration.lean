import DifferentialGeometry.Topology.Covering.Lifting

namespace DifferentialGeometry.Topology.Covering

variable {E B Z W : Type*} [TopologicalSpace E] [TopologicalSpace B]
  [TopologicalSpace Z] [TopologicalSpace W] {p : E → B}

noncomputable def continuousMapLiftsEquivFiber (hp : IsCoveringMap p)
    [SimplyConnectedSpace Z] [LocallyPathConnectedSpace Z] (f : C(Z, B)) (z₀ : Z) :
    {g : C(Z, E) // p ∘ g = f} ≃ (p ⁻¹' {f z₀}) :=
  Equiv.ofBijective (fun g => ⟨g.val z₀, congrFun g.property z₀⟩) (by
    constructor
    · intro g h he
      apply Subtype.ext
      exact lifts_unique hp (g.property.trans h.property.symm) z₀ (congrArg Subtype.val he)
    · intro e
      obtain ⟨g, hg, _⟩ := hp.existsUnique_continuousMap_lifts f z₀ e.val e.property
      exact ⟨⟨g, hg.2⟩, Subtype.ext hg.1⟩)

@[simp]
theorem continuousMapLiftsEquivFiber_apply (hp : IsCoveringMap p)
    [SimplyConnectedSpace Z] [LocallyPathConnectedSpace Z] (f : C(Z, B)) (z₀ : Z)
    (g : {g : C(Z, E) // p ∘ g = f}) :
    (continuousMapLiftsEquivFiber hp f z₀ g : E) = g.val z₀ := rfl

def liftPrecomp (f : C(Z, B)) (u : C(W, Z)) :
    {g : C(Z, E) // p ∘ g = f} → {g : C(W, E) // p ∘ g = f.comp u} :=
  fun g => ⟨g.val.comp u, funext (fun w => congrFun g.property (u w))⟩

@[simp]
theorem liftPrecomp_apply (f : C(Z, B)) (u : C(W, Z))
    (g : {g : C(Z, E) // p ∘ g = f}) (w : W) :
    (liftPrecomp f u g).val w = g.val (u w) := rfl

theorem liftPrecomp_bijective (hp : IsCoveringMap p)
    [SimplyConnectedSpace Z] [LocallyPathConnectedSpace Z] [PreconnectedSpace W] [Nonempty W]
    (f : C(Z, B)) (u : C(W, Z)) : Function.Bijective (liftPrecomp (p := p) f u) := by
  obtain ⟨w₀⟩ := ‹Nonempty W›
  constructor
  · intro g h he
    apply Subtype.ext
    exact lifts_unique hp (g.property.trans h.property.symm) (u w₀)
      (congrArg (fun g => g.val w₀) he)
  · intro g
    obtain ⟨h, hh, _⟩ := hp.existsUnique_continuousMap_lifts f (u w₀) (g.val w₀)
      (congrFun g.property w₀)
    refine ⟨⟨h, hh.2⟩, Subtype.ext ?_⟩
    exact lifts_unique hp ((liftPrecomp f u ⟨h, hh.2⟩).property.trans g.property.symm) w₀ hh.1

noncomputable def liftPrecompEquiv (hp : IsCoveringMap p)
    [SimplyConnectedSpace Z] [LocallyPathConnectedSpace Z] [PreconnectedSpace W] [Nonempty W]
    (f : C(Z, B)) (u : C(W, Z)) :
    {g : C(Z, E) // p ∘ g = f} ≃ {g : C(W, E) // p ∘ g = f.comp u} :=
  Equiv.ofBijective (liftPrecomp f u) (liftPrecomp_bijective hp f u)

@[simp]
theorem liftPrecompEquiv_apply (hp : IsCoveringMap p)
    [SimplyConnectedSpace Z] [LocallyPathConnectedSpace Z] [PreconnectedSpace W] [Nonempty W]
    (f : C(Z, B)) (u : C(W, Z)) (g : {g : C(Z, E) // p ∘ g = f}) :
    liftPrecompEquiv hp f u g = liftPrecomp f u g := rfl

end DifferentialGeometry.Topology.Covering
