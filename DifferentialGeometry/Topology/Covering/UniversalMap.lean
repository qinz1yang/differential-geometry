import DifferentialGeometry.Topology.Covering.DeckAction

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private def mapFun (u : C(X, Y)) (x₀ : X) :
    @UniversalCover X _ ⟨x₀⟩ → @UniversalCover Y _ ⟨u x₀⟩ :=
  fun p => ⟨u p.1, p.2.map u⟩

private theorem mapFun_mem_basicOpen (u : C(X, Y)) (x₀ : X)
    (p q : @UniversalCover X _ ⟨x₀⟩) (U : Set Y)
    (hq : q ∈ @basicOpen X _ ⟨x₀⟩ p (u ⁻¹' U)) :
    mapFun u x₀ q ∈ @basicOpen Y _ ⟨u x₀⟩ (mapFun u x₀ p) U := by
  obtain ⟨γ, hγ, hq⟩ := hq
  refine ⟨γ.map u.continuous, hγ, ?_⟩
  change q.2.map u = (p.2.map u).trans
    (Path.Homotopic.Quotient.mk (γ.map u.continuous))
  rw [hq, Path.Homotopic.Quotient.mk_map]
  exact (FundamentalGroupoid.map u).map_comp
    (X := ⟨x₀⟩) (Y := ⟨p.1⟩) (Z := ⟨q.1⟩) p.2 (Path.Homotopic.Quotient.mk γ)

private theorem mapFun_continuous (u : C(X, Y)) (x₀ : X) :
    Continuous (mapFun u x₀) := by
  let : Inhabited X := ⟨x₀⟩
  let : Inhabited Y := ⟨u x₀⟩
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨q, U, hU, hq, rfl⟩
  apply isOpen_iff_forall_mem_open.mpr
  intro p hp
  change mapFun u x₀ p ∈ @basicOpen Y _ ⟨u x₀⟩ q U at hp
  have hpU : u p.1 ∈ U := by
    obtain ⟨γ, hγ, _⟩ := hp
    have ht : γ 1 = u p.1 := γ.target
    rw [← ht]
    exact hγ 1
  refine ⟨basicOpen p (u ⁻¹' U), ?_, ?_, ?_⟩
  · intro r hr
    exact basis_trans_shift (Set.Subset.refl U) hp
      (mapFun_mem_basicOpen u x₀ p r U hr)
  · exact TopologicalSpace.GenerateOpen.basic _
      ⟨p, u ⁻¹' U, hU.preimage u.continuous, hpU, rfl⟩
  · refine ⟨Path.refl p.1, fun _ => hpU, ?_⟩
    exact (Path.Homotopic.Quotient.trans_refl p.2).symm

def map (u : C(X, Y)) (x₀ : X) :
    C(@UniversalCover X _ ⟨x₀⟩, @UniversalCover Y _ ⟨u x₀⟩) :=
  ⟨mapFun u x₀, mapFun_continuous u x₀⟩

theorem map_apply (u : C(X, Y)) (x₀ : X) (p : @UniversalCover X _ ⟨x₀⟩) :
    map u x₀ p = ⟨u p.1, p.2.map u⟩ := rfl

@[simp]
theorem proj_map (u : C(X, Y)) (x₀ : X) (p : @UniversalCover X _ ⟨x₀⟩) :
    @proj Y _ ⟨u x₀⟩ (map u x₀ p) = u (@proj X _ ⟨x₀⟩ p) := rfl

@[simp]
theorem map_basePoint (u : C(X, Y)) (x₀ : X) :
    map u x₀ (@basePoint X _ ⟨x₀⟩) = @basePoint Y _ ⟨u x₀⟩ := by
  apply Sigma.ext rfl
  apply heq_of_eq
  rfl

theorem map_smul (u : C(X, Y)) (x₀ : X)
    (g : FundamentalGroup X x₀) (p : @UniversalCover X _ ⟨x₀⟩) :
    letI : MulAction (FundamentalGroup X x₀) (@UniversalCover X _ ⟨x₀⟩) :=
      @deckMulAction X _ ⟨x₀⟩
    letI : MulAction (FundamentalGroup Y (u x₀)) (@UniversalCover Y _ ⟨u x₀⟩) :=
      @deckMulAction Y _ ⟨u x₀⟩
    map u x₀ (g • p) = FundamentalGroup.map u x₀ g • map u x₀ p := by
  change (⟨u p.1, ((FundamentalGroup.toPath g⁻¹).trans p.2).map u⟩ :
      @UniversalCover Y _ ⟨u x₀⟩) =
    ⟨u p.1, (FundamentalGroup.toPath (FundamentalGroup.map u x₀ g)⁻¹).trans (p.2.map u)⟩
  apply congrArg (fun q : Path.Homotopic.Quotient (u x₀) (u p.1) =>
    (⟨u p.1, q⟩ : @UniversalCover Y _ ⟨u x₀⟩))
  rw [← map_inv]
  exact (FundamentalGroupoid.map u).map_comp
    (X := ⟨x₀⟩) (Y := ⟨x₀⟩) (Z := ⟨p.1⟩) (FundamentalGroup.toPath g⁻¹) p.2

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
