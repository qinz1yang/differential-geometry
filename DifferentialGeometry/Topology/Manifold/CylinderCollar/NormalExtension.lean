import DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalDerivative

set_option autoImplicit false
noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem exists_supported_collar_extension_of_positive_axial_derivative
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = 1)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hzero : ∀ p : S2, A (p, 0) = (η p, 0))
    (hpos : ∀ p : S2, 0 < deriv (fun t => (A (p, t)).2) 0)
    (l u : ℝ) (hl : l < 0) (hu : 0 < u) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
      (∀ q : SphereCylinder, |q.2| ≤ r → q ∈ A.source ∧ F q = A q) ∧
      (∀ p : S2, F (p, 0) = (η p, 0)) ∧
      (∀ q : SphereCylinder, q.2 ≤ l ∨ u ≤ q.2 → F q = q ∧ F.symm q = q) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioo l u ∧
        EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  obtain ⟨R, hR, hRband, hRs, hRi, hRside⟩ :=
    exists_uniform_cylinder_width_of_positive_axial_derivative A hsource
      (fun p => congrArg Prod.snd (hzero p)) hpos l u hl hu
  let U : Set SphereCylinder := univ ×ˢ Ioo (-R) R
  let B := DifferentialGeometry.Topology.PartialDiffeomorph.restrict A U (isOpen_univ.prod isOpen_Ioo)
  have hBs : univ ×ˢ Icc (-(R / 2)) (R / 2) ⊆ B.source := by
    rintro q ⟨_, hq⟩
    have hqR : q ∈ univ ×ˢ Icc (-R) R := ⟨mem_univ _, by linarith [hq.1], by linarith [hq.2]⟩
    exact ⟨hRs hqR, mem_univ _, by linarith [hq.1], by linarith [hq.2]⟩
  have hBzero (p : S2) : B (p, 0) = (η p, 0) := hzero p
  have hBside : ∀ q ∈ B.source, q.2 ≤ 0 → (B q).2 ≤ 0 :=
    fun q hq hq0 => hRside q hq.2 hq0
  have hBi : B '' (univ ×ˢ Icc (-(R / 2)) (R / 2)) ⊆ univ ×ˢ Ioo l u := by
    rintro x ⟨q, hq, rfl⟩
    exact hRi q ⟨mem_univ _, by linarith [hq.2.1], by linarith [hq.2.2]⟩
  obtain ⟨F, hF, hFzero, K, hK, hKU, hfix, hfixi⟩ :=
    exists_supported_diffeomorph_eq_on_parametrized_cylinder_collar B η hη
      (r := R / 4) (R := R / 2) (by linarith) (by linarith)
      (by linarith [(lt_min_iff.mp hRband).1]) (by linarith [(lt_min_iff.mp hRband).2])
      hBs hBzero hBside hBi
  refine ⟨R / 4, by linarith, F, ?_, hFzero, ?_, K, hK, hKU, hfix, hfixi⟩
  · intro q hq
    refine ⟨hRs ⟨mem_univ _, ?_, ?_⟩, hF q hq⟩ <;>
      linarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  · intro q hq
    have hn : q ∉ K := by
      intro hqK
      rcases hq with hq | hq
      · exact (not_lt_of_ge hq) (hKU hqK).2.1
      · exact (not_lt_of_ge hq) (hKU hqK).2.2
    exact ⟨hfix hn, hfixi hn⟩

end DifferentialGeometry.Topology.Manifold
