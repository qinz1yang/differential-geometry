import DifferentialGeometry.Topology.Ehresmann.BoundaryInterval

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Geometry.Boundary DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [CompactSpace M] [T2Space M] {I : ModelWithCorners ℝ E H}
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_boundary_endpoint_transport
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (ha : a ∈ range u) (hb : b ∈ range u) :
    let _ : Fact (a < b) := ⟨hab⟩
    let F₀ := boundaryLevel u a b hab.ne hu.continuous hboundary
    let F₁ := boundaryLevel u b a hab.ne.symm hu.continuous (fun x hx ↦ (hboundary x hx).symm)
    ∃ Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I (F₀ × Icc a b) M ∞,
      (∀ p, u (Θ p) = p.2.1) ∧
      (∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1) ∧
      ∃ P : Diffeomorph hI.boundaryI hI.boundaryI F₀ F₁ ∞,
        (∀ x, (P x).1.1 = Θ (x, ⟨b, hab.le, le_rfl⟩)) ∧
        ∀ y, P.symm y = (Θ.symm y.1.1).1 := by
  let _ : Fact (a < b) := ⟨hab⟩
  let F₀ := boundaryLevel u a b hab.ne hu.continuous hboundary
  let F₁ := boundaryLevel u b a hab.ne.symm hu.continuous (fun x hx ↦ (hboundary x hx).symm)
  let top : Icc a b := ⟨b, hab.le, le_rfl⟩
  obtain ⟨Θ, hh, hl⟩ := exists_boundary_interval_trivialization hab hu hreg hboundary ha hb
  have htopBoundary (x : F₀) : I.IsBoundaryPoint (Θ (x, top)) := by
    apply isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero _ (hreg _)
    apply Eventually.of_forall
    intro y
    rw [hh]
    exact (range_subset_Icc_of_boundary_values hab.le hreg hboundary (mem_range_self y)).2
  let forward : F₀ → F₁ := fun x ↦ ⟨⟨Θ (x, top), htopBoundary x⟩, hh (x, top)⟩
  let inverse : F₁ → F₀ := fun y ↦ (Θ.symm y.1.1).1
  have htop (y : F₁) : (Θ.symm y.1.1).2 = top := by
    apply Subtype.ext
    exact (hh (Θ.symm y.1.1)).symm.trans ((congrArg u (Θ.apply_symm_apply y.1.1)).trans y.2)
  have hleft (x : F₀) : inverse (forward x) = x :=
    congrArg Prod.fst (Θ.symm_apply_apply (x, top))
  have hright (y : F₁) : forward (inverse y) = y := by
    apply Subtype.ext
    apply Subtype.ext
    have hp : ((Θ.symm y.1.1).1, top) = Θ.symm y.1.1 := by
      apply Prod.ext
      · rfl
      · exact (htop y).symm
    exact (congrArg Θ hp).trans (Θ.apply_symm_apply y.1.1)
  have hfor : ContMDiff hI.boundaryI hI.boundaryI ∞ forward := by
    apply (contMDiff_boundaryLevelInclusion_comp_iff u b a hab.ne.symm hu.continuous
      (fun x hx ↦ (hboundary x hx).symm)).mp
    exact Θ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  have hback : ContMDiff hI.boundaryI hI.boundaryI ∞ inverse :=
    contMDiff_fst.comp (Θ.symm.contMDiff.comp (contMDiff_boundaryLevelInclusion u b a hab.ne.symm
      hu.continuous (fun x hx ↦ (hboundary x hx).symm)))
  exact ⟨Θ, hh, hl, ⟨⟨forward, inverse, hleft, hright⟩, hfor, hback⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

end DifferentialGeometry.Topology.Ehresmann
