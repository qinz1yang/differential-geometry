import DifferentialGeometry.Topology.PiecewiseLinear.Section34PLMeridianGraph

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.exists_PL_meridian_inclusions_of_marked_boundary_product
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P C J Q : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hC : IsCombinatorialSolidTorus C) (hCP : C ⊆ P)
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    {f : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : IsPLHomeomorphOn f (J ×ˢ Q) (frontier C)) (x : J) (y : Q)
    {S : Set M} (hS : IsTopologicalSolidTorus S) (hCS : u '' C ⊆ S)
    (hgen : CarriesFundamentalGroupOnto ((u ∘ f) '' (J ×ˢ {(y : EuclideanSpace ℝ (Fin 3))})) S) :
    ∃ r : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn r Q (r '' Q) ∧ IsPLSphere 1 (r '' Q) ∧
      ∃ (hKC : r '' Q ⊆ C) (hKF : r '' Q ⊆ frontier C),
        (⟨inclusion hKC, continuous_inclusion hKC⟩ : C(r '' Q, C)).Nullhomotopic ∧
        ¬ (⟨inclusion hKF, continuous_inclusion hKF⟩ : C(r '' Q, frontier C)).Nullhomotopic ∧
        ∀ q ∈ Q, ∃ p ∈ J, (r '' Q) ∩ (f '' (J ×ˢ {q})) = {f (p, q)} := by
  classical
  obtain ⟨r, B, H, hr, hK, hKF, hB, hH, hnon, hnull, hmark⟩ :=
    hu.exists_PL_meridian_of_marked_boundary_product hC hCP hJ hQ hf x y hS hCS hgen
  have hKC : r '' Q ⊆ C := hKF.trans hC.isPolyhedron.isClosed.frontier_subset
  let _ : CompactSpace C := isCompact_iff_compactSpace.mp hC.isPolyhedron.isCompact
  let v : C → u '' C := fun z => ⟨u z, z, z.2, rfl⟩
  have hv : Continuous v :=
    ((hu.continuousOn.mono hCP).domRestrict).subtype_mk _
  have hvbij : Function.Bijective v := by
    constructor
    · intro a b hab
      exact Subtype.ext (hu.injOn (hCP a.2) (hCP b.2) (congrArg Subtype.val hab))
    · rintro ⟨z, p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  let V₀ : C ≃ u '' C := Equiv.ofBijective v hvbij
  have hV₀ : Continuous V₀ := hv
  let V : C ≃ₜ u '' C := hV₀.homeoOfEquivCompactToT2
  let e := hr.homeomorph
  let iC : C(r '' Q, C) := ⟨inclusion hKC, continuous_inclusion hKC⟩
  let iF : C(r '' Q, frontier C) := ⟨inclusion hKF, continuous_inclusion hKF⟩
  have hVeq : (V : C(C, u '' C)).comp (iC.comp (e : C(Q, r '' Q))) = H := by
    ext q
    change u (r q) = (H q : M)
    exact (hH q).symm
  have hmodel : ((V.symm : C(u '' C, C)).comp H).comp
      (e.symm : C(r '' Q, Q)) = iC := by
    rw [← hVeq]
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    change (V.symm (V (iC (e (e.symm z)))) : EuclideanSpace ℝ (Fin 3)) = (iC z : _)
    rw [e.apply_symm_apply, V.symm_apply_apply]
  have hBmodel : iF.comp (e : C(Q, r '' Q)) = B := by
    apply ContinuousMap.ext
    intro q
    apply Subtype.ext
    exact (hB q).symm
  refine ⟨r, hr, hK, hKC, hKF, ?_, ?_, hmark⟩
  · change iC.Nullhomotopic
    rw [← hmodel]
    exact (hnull.comp_right (V.symm : C(u '' C, C))).comp_left (e.symm : C(r '' Q, Q))
  · intro h
    apply hnon
    rw [← hBmodel]
    exact h.comp_left (e : C(Q, r '' Q))

end DifferentialGeometry.Topology.PiecewiseLinear
