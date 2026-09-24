import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingLongitudes
import DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization
import DifferentialGeometry.Topology.FundamentalGroup.Product

open Set DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def IsPLSphere.fundamentalGroupEquivInt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J : Set E} (hJ : IsPLSphere 1 J) (x : J) :
    FundamentalGroup J x ≃* Multiplicative ℤ := by
  let e := (Classical.choice (nonempty_homeomorph_loopCircle_of_isPLSphere_one hJ)).symm.trans
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)
  let q : Path (e x) (1 : Circle) := PathConnectedSpace.somePath _ _
  exact (fundamentalGroupMulEquivOfHomotopyEquiv e.toHomotopyEquiv x (e x) rfl).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath q).trans fundamentalGroupCircleEquivInt)

private theorem exists_cyclic_generator {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) :
    ∃ g : G, g ≠ 1 ∧ ∀ a : G, ∃ n : ℤ, g ^ n = a := by
  let g := e.symm (Multiplicative.ofAdd (1 : ℤ))
  refine ⟨g, ?_, fun a => ⟨(e a).toAdd, e.injective ?_⟩⟩
  · intro h
    have hbad := congrArg (fun a => (e a).toAdd) h
    simp [g] at hbad
  · rw [map_zpow]
    apply Multiplicative.toAdd.injective
    simp [g]

private theorem fundamentalGroup_map_first_factor
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (a : FundamentalGroup X x) :
    FundamentalGroup.map
      (⟨fun z => (z, y), continuous_id.prodMk continuous_const⟩ : C(X, X × Y)) x a =
      (fundamentalGroupProdEquiv x y).symm (a, 1) := by
  rw [fundamentalGroupProdEquiv_symm_apply]
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
    change Path.Homotopic.Quotient.mk (p.map (continuous_id.prodMk continuous_const)) =
      Path.Homotopic.prod (Path.Homotopic.Quotient.mk p)
        (Path.Homotopic.Quotient.mk (Path.refl y))
    rw [Path.Homotopic.prod_lift]
    rfl

theorem exists_meridian_class_of_surjective_longitude
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace X]
    {J : Set E} {Q : Set F} (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    (f : C(J × Q, X)) (x : J) (y : Q)
    (hsurj : Function.Surjective (FundamentalGroup.map
      (f.comp (⟨fun z => (z, y), continuous_id.prodMk continuous_const⟩ : C(J, J × Q))) x)) :
    ∃ (l : FundamentalGroup J x) (m : FundamentalGroup Q y) (k : ℤ),
      (∀ a : FundamentalGroup J x, ∃ n : ℤ, l ^ n = a) ∧
      (∀ b : FundamentalGroup Q y, ∃ n : ℤ, m ^ n = b) ∧
      let long := (fundamentalGroupProdEquiv x y).symm (l, 1)
      let transverse := (fundamentalGroupProdEquiv x y).symm (1, m)
      (∀ a : FundamentalGroup X (f (x, y)),
        ∃ n : ℤ, (FundamentalGroup.map f (x, y) long) ^ n = a) ∧
      FundamentalGroup.map f (x, y) (transverse * long ^ k) = 1 ∧ transverse * long ^ k ≠ 1 := by
  obtain ⟨l, -, hl⟩ := exists_cyclic_generator (hJ.fundamentalGroupEquivInt x)
  obtain ⟨m, hm, hmgen⟩ := exists_cyclic_generator (hQ.fundamentalGroupEquivInt y)
  let long := (fundamentalGroupProdEquiv x y).symm (l, 1)
  let transverse := (fundamentalGroupProdEquiv x y).symm (1, m)
  have hgen : ∀ a : FundamentalGroup X (f (x, y)),
      ∃ n : ℤ, (FundamentalGroup.map f (x, y) long) ^ n = a := by
    intro a
    obtain ⟨b, hb⟩ := hsurj a
    obtain ⟨n, rfl⟩ := hl b
    refine ⟨n, ?_⟩
    rw [fundamentalGroup_map_continuousMap_comp, MonoidHom.comp_apply,
      map_zpow, map_zpow, fundamentalGroup_map_first_factor] at hb
    exact hb
  obtain ⟨k, hk⟩ := hgen ((FundamentalGroup.map f (x, y) transverse)⁻¹)
  refine ⟨l, m, k, hl, hmgen, hgen, ?_, ?_⟩
  · change FundamentalGroup.map f (x, y) (transverse * long ^ k) = 1
    rw [map_mul, map_zpow, hk, mul_inv_cancel]
  · intro h
    have hp := congrArg (fun a => ((fundamentalGroupProdEquiv x y) a).2) h
    apply hm
    simp only [map_mul, map_zpow, MulEquiv.apply_symm_apply, map_one] at hp
    change m * (1 : FundamentalGroup Q y) ^ k = 1 at hp
    rw [one_zpow, mul_one] at hp
    exact hp

theorem IsPLHomeomorphInto.exists_meridian_class_of_marked_boundary_product
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P C J Q : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hC : IsCombinatorialSolidTorus C) (hCP : C ⊆ P)
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    {f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : IsPLHomeomorphOn f (J ×ˢ Q) (frontier C)) (x : J) (y : Q)
    {S : Set M} (hS : IsTopologicalSolidTorus S) (hCS : u '' C ⊆ S)
    (hgen : CarriesFundamentalGroupOnto ((u ∘ f) '' (J ×ˢ {(y : EuclideanSpace ℝ (Fin 3))})) S) :
    ∃ F : C(J × Q, u '' C), (∀ z, (F z : M) = u (f (z.1, z.2))) ∧
      ∃ (l : FundamentalGroup J x) (m : FundamentalGroup Q y) (k : ℤ),
        (∀ a : FundamentalGroup J x, ∃ n : ℤ, l ^ n = a) ∧
        (∀ b : FundamentalGroup Q y, ∃ n : ℤ, m ^ n = b) ∧
        let long := (fundamentalGroupProdEquiv x y).symm (l, 1)
        let transverse := (fundamentalGroupProdEquiv x y).symm (1, m)
        (∀ a : FundamentalGroup (u '' C) (F (x, y)),
          ∃ n : ℤ, (FundamentalGroup.map F (x, y) long) ^ n = a) ∧
        FundamentalGroup.map F (x, y) (transverse * long ^ k) = 1 ∧ transverse * long ^ k ≠ 1 := by
  have hfront : frontier C ⊆ C := hC.isPolyhedron.isClosed.frontier_subset
  have hmap (z : J × Q) : f (z.1, z.2) ∈ C :=
    hfront (hf.bijOn.mapsTo ⟨z.1.2, z.2.2⟩)
  have hcont : Continuous (fun z : J × Q => u (f (z.1, z.2))) :=
    hu.continuousOn.comp_continuous
      (hf.isPiecewiseAffineOn.continuousOn.comp_continuous
        (continuous_subtype_val.prodMap continuous_subtype_val) fun z => ⟨z.1.2, z.2.2⟩)
      fun z => hCP (hmap z)
  let F : C(J × Q, u '' C) :=
    ⟨fun z => ⟨u (f (z.1, z.2)), ⟨f (z.1, z.2), hmap z, rfl⟩⟩, hcont.subtype_mk _⟩
  let L := (u ∘ f) '' (J ×ˢ {(y : EuclideanSpace ℝ (Fin 3))})
  have hLC : L ⊆ u '' C := by
    rintro _ ⟨⟨j, q⟩, ⟨hj, hq⟩, rfl⟩
    have hqy : q = y := hq
    subst q
    exact (F (⟨j, hj⟩, y)).2
  have hsolid := hC.1.image_of_continuousOn_injOn
    (hu.continuousOn.mono hCP) (hu.injOn.mono hCP)
  have hcarry := hgen.of_intermediate_solid_torus hsolid hS hLC hCS
  let g : J → L := fun j => ⟨u (f (j, y)), ⟨(j, y), ⟨j.2, rfl⟩, rfl⟩⟩
  have hgc : Continuous g :=
    (hcont.comp (continuous_id.prodMk continuous_const)).subtype_mk _
  have hgb : Function.Bijective g := by
    constructor
    · intro a b hab
      have heq := hu.injOn (hCP (hmap (a, y))) (hCP (hmap (b, y)))
        (congrArg Subtype.val hab)
      have hp := hf.bijOn.injOn ⟨a.2, y.2⟩ ⟨b.2, y.2⟩ heq
      exact Subtype.ext (congrArg Prod.fst hp)
    · rintro ⟨z, ⟨⟨j, q⟩, ⟨hj, hq⟩, rfl⟩⟩
      have hqy : q = y := hq
      subst q
      exact ⟨⟨j, hj⟩, rfl⟩
  let _ : CompactSpace J := isCompact_iff_compactSpace.mp hJ.isPolyhedron.isCompact
  let e₀ : J ≃ L := Equiv.ofBijective g hgb
  have he₀ : Continuous e₀ := hgc
  let e : J ≃ₜ L := he₀.homeoOfEquivCompactToT2
  let gc : C(J, L) := ⟨g, hgc⟩
  let iLC : C(L, u '' C) := ⟨inclusion hLC, continuous_inclusion hLC⟩
  have hgs : Function.Surjective (FundamentalGroup.map gc x) :=
    (bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e.symm.toHomotopyEquiv gc
      (fun a => e.symm_apply_apply a) x).2
  have hs : Function.Surjective (FundamentalGroup.map
      (F.comp (⟨fun z => (z, y), continuous_id.prodMk continuous_const⟩ : C(J, J × Q))) x) := by
    change Function.Surjective (FundamentalGroup.map (iLC.comp gc) x)
    rw [fundamentalGroup_map_continuousMap_comp]
    exact (hcarry.2 hLC (gc x)).comp hgs
  exact ⟨F, fun _ => rfl, exists_meridian_class_of_surjective_longitude hJ hQ F x y hs⟩

end DifferentialGeometry.Topology.PiecewiseLinear
