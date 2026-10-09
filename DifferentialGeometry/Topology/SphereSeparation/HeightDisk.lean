import DifferentialGeometry.Topology.SphereSeparation.HeightSection
import DifferentialGeometry.Topology.PlanarJordan.InnermostSmoothDisk
import DifferentialGeometry.Topology.Handle.Embedding
import DifferentialGeometry.Topology.Embedding.Graph

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem exists_innermost_height_level_disk_coordinates {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    ∃ (η : AddCircle (1 : ℝ) → SphereTwo) (γ : AddCircle (1 : ℝ) → Schoenflies.Plane)
      (Φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane),
      IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
      (∀ z, e (η z) = (EuclideanSpace.equivProdLast 2).symm (γ z, a)) ∧
      IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
      Φ '' sphere (0 : Schoenflies.Plane) 1 = range γ ∧
      Φ '' ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (range γ) ∧
      Φ '' closedBall (0 : Schoenflies.Plane) 1 = closure (Schoenflies.inside (range γ)) ∧
      ∃ δ : ℝ, 0 < δ ∧
        (fun y : Schoenflies.Plane => (EuclideanSpace.equivProdLast 2).symm (y, a)) ⁻¹' range e ∩
          cthickening δ (Φ '' closedBall (0 : Schoenflies.Plane) 1) = range γ := by
  classical
  obtain ⟨hfinite, η, γ, hη, hγ, hcompat, hdisj, hcover⟩ :=
    exists_planar_height_level_circle_parametrizations he a hr
  let I := ConnectedComponents {x : SphereTwo // e x 2 = a}
  let : Finite I := hfinite
  let : Fintype I := Fintype.ofFinite I
  have hnonempty : Nonempty I := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨ConnectedComponents.mk (⟨x, hx⟩ : {x : SphereTwo // e x 2 = a})⟩
  let : Nonempty I := hnonempty
  obtain ⟨i, _, Φ, hΦ, hball, hclosed, δ, hδ, hclear⟩ :=
    PlanarJordan.exists_innermost_smooth_disk (Finset.univ : Finset I) Finset.univ_nonempty
      γ (fun i _ => hγ i) (fun i _ j _ hij => hdisj hij)
  refine ⟨η i, γ i, Φ, hη i, hcompat i, hγ i, hΦ, hball, hclosed, δ, hδ, ?_⟩
  rw [← hcover]
  ext y
  constructor
  · rintro ⟨hy, hyD⟩
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    by_cases hji : j = i
    · exact hji ▸ hyj
    · exact False.elim (disjoint_left.mp (hclear j (Finset.mem_univ j) hji) hyD hyj)
  · intro hy
    refine ⟨mem_iUnion.mpr ⟨i, hy⟩, self_subset_cthickening _ ?_⟩
    rw [← hΦ] at hy
    exact image_mono sphere_subset_closedBall hy

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_innermost_height_level_disk {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    ∃ (η : AddCircle (1 : ℝ) → SphereTwo) (γ : AddCircle (1 : ℝ) → Schoenflies.Plane)
      (Φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane) (b : ClosedCell 2 → EuclideanThree),
      IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
      (∀ z, e (η z) = (EuclideanSpace.equivProdLast 2).symm (γ z, a)) ∧
      IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
      IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ b ∧
      (∀ x, b x = (EuclideanSpace.equivProdLast 2).symm (Φ x.val, a)) ∧
      (∀ x, b x 2 = a) ∧
      Φ '' sphere (0 : Schoenflies.Plane) 1 = range γ ∧
      Φ '' ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (range γ) ∧
      Φ '' closedBall (0 : Schoenflies.Plane) 1 = closure (Schoenflies.inside (range γ)) ∧
      range (b ∘ cellBoundaryInclusion 2) =
        (fun y : Schoenflies.Plane => (EuclideanSpace.equivProdLast 2).symm (y, a)) '' range γ ∧
      range (b ∘ cellBoundaryInclusion 2) = e '' range η ∧
      range b ∩ range e = range (b ∘ cellBoundaryInclusion 2) ∧
      ∃ δ : ℝ, 0 < δ ∧ cthickening δ (range b) ∩ (range e ∩ {z | z 2 = a}) =
        range (b ∘ cellBoundaryInclusion 2) := by
  obtain ⟨η, γ, Φ, hη, hcompat, hγ, hΦ, hball, hclosed, δ, hδ, hclear⟩ :=
    exists_innermost_height_level_disk_coordinates he hne hr
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let lift : Schoenflies.Plane → EuclideanThree := fun y => L.symm (y, a)
  let b : ClosedCell 2 → EuclideanThree := fun x => lift (Φ x.val)
  have hb : IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ b := by
    have h := ((Handle.closedCellInclusion_isSmoothEmbedding 1).diffeomorph_comp Φ).graph
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Schoenflies.Plane => a))
    exact h.continuousLinearEquiv_comp L.symm
  have hlift : Isometry lift := EuclideanSpace.isometry_equivProdLast_symm_const 2 a
  have hheight (x : ClosedCell 2) : b x 2 = a :=
    EuclideanSpace.equivProdLast_symm_last 2 _
  have hbrange : range b = lift '' (Φ '' closedBall (0 : Schoenflies.Plane) 1) := by
    change range (lift ∘ Φ ∘ (Subtype.val : ClosedCell 2 → Schoenflies.Plane)) = _
    rw [range_comp, range_comp, range_closedCell]
  have hboundary : range (b ∘ cellBoundaryInclusion 2) = lift '' range γ := by
    have hh : b ∘ cellBoundaryInclusion 2 =
        lift ∘ Φ ∘ (Subtype.val : CellBoundary 2 → Schoenflies.Plane) := rfl
    rw [hh, range_comp, range_comp, range_cellBoundary, hΦ]
  have hclear' : cthickening δ (range b) ∩ (range e ∩ {z | z 2 = a}) =
      range (b ∘ cellBoundaryInclusion 2) := by
    rw [hbrange, hboundary]
    ext z
    constructor
    · rintro ⟨hzD, hze, hza⟩
      let y := (L z).1
      have hzy : lift y = z := by
        apply L.injective
        rw [L.apply_symm_apply]
        exact Prod.ext rfl hza.symm
      have hyD : y ∈ cthickening δ (Φ '' closedBall (0 : Schoenflies.Plane) 1) := by
        rw [← hzy, mem_cthickening_iff, Metric.infEDist_image hlift] at hzD
        exact hzD
      have hyγ : y ∈ range γ := hclear.subset ⟨by change lift y ∈ range e; rw [hzy]; exact hze, hyD⟩
      exact ⟨y, hyγ, hzy⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hye, hyD⟩ := hclear.symm.subset hy
      refine ⟨?_, hye, EuclideanSpace.equivProdLast_symm_last 2 _⟩
      rw [mem_cthickening_iff, Metric.infEDist_image hlift]
      exact hyD
  have hsection : range b ∩ range e = range (b ∘ cellBoundaryInclusion 2) := by
    apply Subset.antisymm
    · rintro z ⟨hz, hze⟩
      obtain ⟨x, rfl⟩ := hz
      exact hclear'.subset ⟨self_subset_cthickening _ (mem_range_self x), hze, hheight x⟩
    · rintro z ⟨x, rfl⟩
      exact ⟨mem_range_self _, (hclear'.symm.subset (mem_range_self x)).2.1⟩
  have hsource : range (b ∘ cellBoundaryInclusion 2) = e '' range η := by
    rw [hboundary, ← range_comp, ← range_comp]
    congr 1
    exact (funext hcompat).symm
  exact ⟨η, γ, Φ, b, hη, hcompat, hγ, hb, fun _ => rfl, hheight, hΦ, hball, hclosed,
    hboundary, hsource, hsection, δ, hδ, hclear'⟩

theorem exists_innermost_height_level_disk_family {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ Icc (a - ε) (a + ε) ⊆ W ∧
      ∃ (η : AddCircle (1 : ℝ) → SphereTwo) (γ : AddCircle (1 : ℝ) → Schoenflies.Plane)
        (Φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
        (D : EuclideanThree ≃ₘ[ℝ] EuclideanThree) (b : ℝ → ClosedCell 2 → EuclideanThree),
        IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        (∀ z, e (η z) = (EuclideanSpace.equivProdLast 2).symm (γ z, a)) ∧
        IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
        Φ '' sphere (0 : Schoenflies.Plane) 1 = range γ ∧
        Φ '' ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (range γ) ∧
        Φ '' closedBall (0 : Schoenflies.Plane) 1 = closure (Schoenflies.inside (range γ)) ∧
        (∀ z, D z 2 = z 2) ∧ (∀ z, z 2 = a → D z = z) ∧
        (∀ t x, b t x = D ((EuclideanSpace.equivProdLast 2).symm (Φ x.val, t))) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 2)) (𝓡 3) ∞
          (fun p : ℝ × ClosedCell 2 => b p.1 p.2) ∧
        (∀ t, IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ (b t)) ∧
        (∀ t x, b t x 2 = t) ∧
        range (b a ∘ cellBoundaryInclusion 2) = e '' range η ∧
        (∀ t ∈ Icc (a - ε) (a + ε),
          range (b t) ∩ range e = range (b t ∘ cellBoundaryInclusion 2)) ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (a - ε) (a + ε),
          (fun y : Schoenflies.Plane => D ((EuclideanSpace.equivProdLast 2).symm (y, t))) ⁻¹'
            range e ∩ cthickening δ (Φ '' closedBall (0 : Schoenflies.Plane) 1) = range γ) ∧
        ∃ K : Set EuclideanThree, IsCompact K ∧ K ⊆ {z | z 2 ∈ W} ∧ EqOn D id Kᶜ := by
  obtain ⟨η, γ, Φ, hη, hcompat, hγ, hΦ, hball, hclosed, δ, hδ, hclear⟩ :=
    exists_innermost_height_level_disk_coordinates he hne hr
  obtain ⟨ε, hε, hεW, D, hD, hDa, hlevels, K, hK, hKW, hfix⟩ :=
    exists_height_preserving_regular_level_diffeomorph he hr hW haW
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let lift : ℝ → Schoenflies.Plane → EuclideanThree := fun t y => D (L.symm (y, t))
  let b : ℝ → ClosedCell 2 → EuclideanThree := fun t x => lift t (Φ x.val)
  have hb (t : ℝ) : IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ (b t) := by
    have h := ((Handle.closedCellInclusion_isSmoothEmbedding 1).diffeomorph_comp Φ).graph
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Schoenflies.Plane => t))
    exact (h.continuousLinearEquiv_comp L.symm).diffeomorph_comp D
  have hbjoint : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 2)) (𝓡 3) ∞
      (fun p : ℝ × ClosedCell 2 => b p.1 p.2) := by
    exact D.contMDiff.comp (L.symm.contDiff.contMDiff.comp
      ((Φ.contMDiff.comp ((Handle.closedCellInclusion_isSmoothEmbedding 1).contMDiff.comp
        contMDiff_snd)).prodMk_space contMDiff_fst))
  have hboundary (t : ℝ) : range (b t ∘ cellBoundaryInclusion 2) = lift t '' range γ := by
    have hh : b t ∘ cellBoundaryInclusion 2 =
        lift t ∘ Φ ∘ (Subtype.val : CellBoundary 2 → Schoenflies.Plane) := rfl
    rw [hh, range_comp, range_comp, range_cellBoundary, hΦ]
  have hclear' (t : ℝ) (ht : t ∈ Icc (a - ε) (a + ε)) :
      lift t ⁻¹' range e ∩ cthickening δ (Φ '' closedBall (0 : Schoenflies.Plane) 1) =
        range γ := by
    rw [show lift t ⁻¹' range e =
      (fun y : Schoenflies.Plane => L.symm (y, a)) ⁻¹' range e from
        preimage_height_section_eq D.injective hD (hlevels t ht)]
    exact hclear
  have hsource : range (b a ∘ cellBoundaryInclusion 2) = e '' range η := by
    rw [hboundary, ← range_comp, ← range_comp]
    congr 1
    funext z
    change D (L.symm (γ z, a)) = e (η z)
    rw [hDa _ (EuclideanSpace.equivProdLast_symm_last 2 _)]
    exact (hcompat z).symm
  have hsection (t : ℝ) (ht : t ∈ Icc (a - ε) (a + ε)) :
      range (b t) ∩ range e = range (b t ∘ cellBoundaryInclusion 2) := by
    rw [hboundary]
    apply Subset.antisymm
    · rintro z ⟨⟨x, rfl⟩, hxe⟩
      exact ⟨Φ x.val, (hclear' t ht).subset ⟨hxe,
        self_subset_cthickening _ ⟨x.val, by simpa using x.property, rfl⟩⟩, rfl⟩
    · rintro z ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hΦ.symm.subset hy
      refine ⟨⟨⟨x, ?_⟩, rfl⟩, ((hclear' t ht).symm.subset hy).1⟩
      simpa using sphere_subset_closedBall hx
  refine ⟨ε, hε, hεW, η, γ, Φ, D, b, hη, hcompat, hγ, hΦ, hball, hclosed,
    hD, hDa, fun _ _ => rfl, hbjoint, hb, ?_, hsource, hsection,
    ⟨δ, hδ, hclear'⟩, K, hK, hKW, hfix⟩
  intro t x
  exact (hD _).trans (EuclideanSpace.equivProdLast_symm_last 2 _)

end DifferentialGeometry.Topology.SphereSeparation
