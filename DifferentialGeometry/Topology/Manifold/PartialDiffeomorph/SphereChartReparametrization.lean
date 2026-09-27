import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CylinderBoundary
import DifferentialGeometry.Topology.Diffeomorph.SphereExtension

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

variable {E H Z E' H' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace Z] [ChartedSpace H Z]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace P] [ChartedSpace H' P]

theorem exists_sphere_chart_reparametrization_of_cylinder_boundary
    (b : PartialDiffeomorph 𝓘(ℝ, E3) I E3 Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (T : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) J (S2 × ℝ) P ∞)
    (hb : Metric.sphere (0 : E3) 1 ⊆ b.source)
    (hF : b '' Metric.sphere (0 : E3) 1 ⊆ F.source)
    (hT : ∀ q : S2, (q, (0 : ℝ)) ∈ T.source)
    (hboundary : F '' (b '' Metric.sphere (0 : E3) 1) =
      range (fun q : S2 => T (q, 0))) :
    ∃ (D : E3 ≃ₘ[ℝ] E3) (b' : PartialDiffeomorph 𝓘(ℝ, E3) I E3 Z ∞),
      b' = D.toPartialDiffeomorph.trans b ∧
      (∀ x, ‖D x‖ = ‖x‖) ∧
      (∀ x, b' x = b (D x)) ∧
      (∀ r : ℝ, b' '' Metric.ball (0 : E3) r = b '' Metric.ball (0 : E3) r) ∧
      (∀ r : ℝ, Metric.closedBall (0 : E3) r ⊆ b.source →
        Metric.closedBall (0 : E3) r ⊆ b'.source) ∧
      ∀ q : S2, F (b' q) = T (q, 0) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  have hA : Metric.sphere (0 : E3) 1 ⊆ (b.trans F).source := by
    intro x hx
    exact ⟨hb hx, hF (mem_image_of_mem b hx)⟩
  have hboundary' : (b.trans F) '' Metric.sphere (0 : E3) 1 =
      range (fun q : S2 => T (q, 0)) := by
    change (F ∘ b) '' Metric.sphere (0 : E3) 1 = _
    rw [image_comp]
    exact hboundary
  obtain ⟨η, hη, _hηinv⟩ :=
    exists_sphere_diffeomorph_of_sphere_chart_and_cylinder_boundary
      (b.trans F) T hA hT hboundary'
  obtain ⟨D, hnorm, hD⟩ := exists_norm_preserving_diffeomorph_extension_sphere η
  let b' := D.toPartialDiffeomorph.trans b
  have hDinvnorm (x : E3) : ‖D.symm x‖ = ‖x‖ := by
    rw [← hnorm (D.symm x), D.apply_symm_apply]
  refine ⟨D, b', rfl, hnorm, fun _ => rfl, ?_, ?_, ?_⟩
  · intro r
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨D x, by simpa only [mem_ball_zero_iff, hnorm] using hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨D.symm x, ?_, ?_⟩
      · simpa only [mem_ball_zero_iff, hDinvnorm] using hx
      · change b (D (D.symm x)) = b x
        rw [D.apply_symm_apply]
  · intro r hr x hx
    change x ∈ (univ : Set E3) ∧ D x ∈ b.source
    exact ⟨mem_univ x, hr (by simpa only [mem_closedBall_zero_iff, hnorm] using hx)⟩
  · intro q
    change F (b (D q)) = T (q, 0)
    rw [hD]
    exact hη q

theorem exists_sphere_chart_reparametrization_of_cylinder_slice
    (b : PartialDiffeomorph 𝓘(ℝ, E3) I E3 Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (T : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) J (S2 × ℝ) P ∞)
    (θ : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (c : ℝ)
    (hb : Metric.sphere (0 : E3) 1 ⊆ b.source)
    (hF : b '' Metric.sphere (0 : E3) 1 ⊆ F.source)
    (hT : ∀ q : S2, (q, c) ∈ T.source)
    (hboundary : F '' (b '' Metric.sphere (0 : E3) 1) =
      range (fun q : S2 => T (q, c))) :
    ∃ (D : E3 ≃ₘ[ℝ] E3) (b' : PartialDiffeomorph 𝓘(ℝ, E3) I E3 Z ∞),
      b' = D.toPartialDiffeomorph.trans b ∧
      (∀ x, ‖D x‖ = ‖x‖) ∧
      (∀ x, b' x = b (D x)) ∧
      (∀ r : ℝ, b' '' Metric.ball (0 : E3) r = b '' Metric.ball (0 : E3) r) ∧
      (∀ r : ℝ, Metric.closedBall (0 : E3) r ⊆ b.source →
        Metric.closedBall (0 : E3) r ⊆ b'.source) ∧
      (∀ q : S2, F (b' q) = T (θ.symm q, c)) ∧
      ∀ q : S2, F (b' (θ q)) = T (q, c) := by
  let R : (S2 × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), (𝓡 2).prod 𝓘(ℝ)⟯ (S2 × ℝ) := {
    toFun := fun p => (θ.symm p.1, c - p.2)
    invFun := fun p => (θ p.1, c - p.2)
    left_inv := fun p => by simp
    right_inv := fun p => by simp
    contMDiff_toFun := (θ.symm.contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_const.sub contMDiff_snd)
    contMDiff_invFun := (θ.contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_const.sub contMDiff_snd) }
  let T' := R.toPartialDiffeomorph.trans T
  have hT' (q : S2) : (q, (0 : ℝ)) ∈ T'.source := by
    change (q, (0 : ℝ)) ∈ (univ : Set (S2 × ℝ)) ∧ R (q, 0) ∈ T.source
    refine ⟨mem_univ _, ?_⟩
    change (θ.symm q, c - 0) ∈ T.source
    simpa only [sub_zero] using hT (θ.symm q)
  have hrange : range (fun q : S2 => T' (q, 0)) =
      range (fun q : S2 => T (q, c)) := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨θ.symm q, by change T (θ.symm q, c) = T (θ.symm q, c - 0); rw [sub_zero]⟩
    · rintro ⟨q, rfl⟩
      refine ⟨θ q, ?_⟩
      change T (θ.symm (θ q), c - 0) = T (q, c)
      rw [θ.symm_apply_apply, sub_zero]
  obtain ⟨D, b', heq, hnorm, happly, hball, hclosed, hbd⟩ :=
    exists_sphere_chart_reparametrization_of_cylinder_boundary b F T' hb hF hT'
      (hboundary.trans hrange.symm)
  have hbd' (q : S2) : F (b' q) = T (θ.symm q, c) := by
    have h := hbd q
    change F (b' q) = T (θ.symm q, c - 0) at h
    simpa only [sub_zero] using h
  refine ⟨D, b', heq, hnorm, happly, hball, hclosed, hbd', ?_⟩
  intro q
  simpa only [θ.symm_apply_apply] using hbd' (θ q)

end DifferentialGeometry.Topology.Manifold
