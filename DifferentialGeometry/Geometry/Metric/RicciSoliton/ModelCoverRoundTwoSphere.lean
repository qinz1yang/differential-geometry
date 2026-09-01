import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.Sphere.FreeOrthogonalAction
import DifferentialGeometry.Geometry.Metric.Sphere.IsometryRepresentation
import DifferentialGeometry.Topology.ProjectiveSpace.Real

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Module Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

theorem solitonModelCovering_roundTwoSphere_deck_eq_one_or_antipodal
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → M}
    (hπ : solitonModelCovering roundTwoSphereShrinkerMetric
      roundTwoSphereShrinkerPotential g f cover)
    (gamma : coveringDeckGroup cover) :
    gamma.1 = 1 ∨ gamma.1 =
      (realProjectiveSpaceAntipodalHomeomorph
        (EuclideanSpace Real (Fin 3))).toEquiv := by
  let phi (delta : coveringDeckGroup cover) :=
    coveringDeckGroupDiffeomorph
      (solitonModelCovering_isLocalDiffeomorph hπ) delta
  have hphiMetric (delta : coveringDeckGroup cover) :
      Diffeomorph.pullbackMetricCross roundTwoSphereShrinkerMetric (phi delta) =
        roundTwoSphereShrinkerMetric :=
    (solitonModelCovering_deckGroup_preserves hπ delta).1
  have hphiOne (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
      phi 1 x = x := by
    rfl
  have hphiMul (delta eta : coveringDeckGroup cover)
      (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
      phi (delta * eta) x = phi delta (phi eta x) := by
    rfl
  have hphiIso (delta : coveringDeckGroup cover)
      (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (v w : TangentSpace (𝓡 2) x) :
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x v w =
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner
          (phi delta x)
          (mfderiv (𝓡 2) (𝓡 2) (phi delta) x v)
          (mfderiv (𝓡 2) (𝓡 2) (phi delta) x w) := by
    have h := Diffeomorph.pullbackMetricCross_inner
      roundTwoSphereShrinkerMetric (phi delta) x v w
    rw [hphiMetric delta] at h
    have hscaled := h
    simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric,
      scaleMetric_inner] at hscaled
    exact mul_left_cancel₀
      (ne_of_gt (sq_pos_of_pos
        (roundSphereShrinkerRadius_pos (n := 2) (by decide)))) hscaled
  have hphiFree : ∀ (delta : coveringDeckGroup cover)
      (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1),
      phi delta x = x → delta = 1 := by
    let _ : PreconnectedSpace
        (sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
      Subtype.preconnectedSpace
        (isPreconnected_sphere
          (Module.one_lt_rank_of_one_lt_finrank (by norm_num))
          (0 : EuclideanSpace Real (Fin 3)) 1)
    intro delta x hx
    exact coveringDeckGroup_eq_one_of_apply_eq
      (solitonModelCovering_isCoveringMap hπ) delta x hx
  obtain ⟨rho, hrho⟩ := orth_rep_of_iso
    (E := EuclideanSpace Real (Fin 3)) (n := 2)
    (Classical.choice (show Nonempty
      (sphere (0 : EuclideanSpace Real (Fin 3)) 1) from
        ⟨⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩⟩))
    phi (by norm_num) hphiOne hphiMul hphiIso
  have hfree : ∀ (delta : coveringDeckGroup cover)
      (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1),
      sphereDiffeo (n := 2) (rho delta) x = x → delta = 1 := by
    intro delta x hx
    apply hphiFree delta x
    rw [← hrho delta]
    exact hx
  rcases orth_rep_apply_eq_one_or_neg_of_free_sphere_action rho hfree gamma with
    hrhoGamma | hrhoGamma
  · left
    apply Equiv.ext
    intro x
    have h := congrArg
      (fun d : sphere (0 : EuclideanSpace Real (Fin 3)) 1
          ≃ₘ⟮𝓡 2, 𝓡 2⟯ sphere (0 : EuclideanSpace Real (Fin 3)) 1 => d x)
      (hrho gamma)
    rw [hrhoGamma] at h
    change x = gamma.1 x at h
    exact h.symm
  · right
    apply Equiv.ext
    intro x
    have h := congrArg
      (fun d : sphere (0 : EuclideanSpace Real (Fin 3)) 1
          ≃ₘ⟮𝓡 2, 𝓡 2⟯ sphere (0 : EuclideanSpace Real (Fin 3)) 1 => d x)
      (hrho gamma)
    rw [hrhoGamma] at h
    change -x = gamma.1 x at h
    exact h.symm

theorem solitonModelCovering_roundTwoSphere_deckGroup_eq_bot_or_antipodal
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → M}
    (hπ : solitonModelCovering roundTwoSphereShrinkerMetric
      roundTwoSphereShrinkerPotential g f cover) :
    coveringDeckGroup cover = ⊥ ∨
      coveringDeckGroup cover = realProjectivePlaneAntipodalGroup := by
  classical
  by_cases hanti : ∃ gamma : coveringDeckGroup cover,
      gamma.1 = (realProjectiveSpaceAntipodalHomeomorph
        (EuclideanSpace Real (Fin 3))).toEquiv
  · right
    apply le_antisymm
    · intro psi hpsi
      let gamma : coveringDeckGroup cover := ⟨psi, hpsi⟩
      rcases solitonModelCovering_roundTwoSphere_deck_eq_one_or_antipodal
          hπ gamma with hone | hgenerator
      · rw [show psi = 1 from hone]
        exact Subgroup.one_mem _
      · rw [show psi =
          (realProjectiveSpaceAntipodalHomeomorph
            (EuclideanSpace Real (Fin 3))).toEquiv from hgenerator]
        exact Subgroup.mem_zpowers _
    · change Subgroup.zpowers
        (realProjectiveSpaceAntipodalHomeomorph
          (EuclideanSpace Real (Fin 3))).toEquiv ≤ coveringDeckGroup cover
      apply Subgroup.zpowers_le.mpr
      obtain ⟨gamma, hgamma⟩ := hanti
      rw [← hgamma]
      exact gamma.property
  · left
    apply le_antisymm
    · intro psi hpsi
      simp only [Subgroup.mem_bot]
      let gamma : coveringDeckGroup cover := ⟨psi, hpsi⟩
      rcases solitonModelCovering_roundTwoSphere_deck_eq_one_or_antipodal
          hπ gamma with hone | hgenerator
      · exact hone
      · exact (hanti ⟨gamma, hgenerator⟩).elim
    · exact bot_le

end DifferentialGeometry.Geometry
