import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_pullback_disk_of_not_bounding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Φ : E → E} (hΦ : IsPLHomeomorphOn Φ univ univ)
    {K U Q : Set E} {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q) (hQU : Q ⊆ Φ '' U)
    (htrace : Q ∩ Φ '' K = q '' stdSimplexBoundary 2)
    (hnot : ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ Φ '' K ∧
        r '' stdSimplexBoundary 2 = q '' stdSimplexBoundary 2) :
    ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ U ∧
      D ∩ K = r '' stdSimplexBoundary 2 ∧
      (¬ ∃ (A : Set E) (a : (Fin 3 → ℝ) → E),
        IsPLHomeomorphOn a (stdSimplex ℝ (Fin 3)) A ∧ A ⊆ K ∧
          a '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2) ∧
      Φ '' D = Q ∧ ∀ x, Φ (r x) = q x := by
  let ψ := Function.invFunOn Φ univ
  have hleft : Function.LeftInverse ψ Φ := fun x => hΦ.bijOn.invOn_invFunOn.1 (mem_univ x)
  have hright : Function.RightInverse ψ Φ := fun x => hΦ.bijOn.invOn_invFunOn.2 (mem_univ x)
  have hψ : IsPLHomeomorphOn ψ univ univ := hΦ.symm
  have hψi : Function.Injective ψ :=
    fun x y hxy => hψ.bijOn.injOn (mem_univ x) (mem_univ y) hxy
  have hback (S : Set E) : ψ '' (Φ '' S) = S := by
    rw [image_image, show (fun x => ψ (Φ x)) = id from funext hleft, image_id]
  have hforward (S : Set E) : Φ '' (ψ '' S) = S := by
    rw [image_image, show (fun x => Φ (ψ x)) = id from funext hright, image_id]
  have hQ : IsPLBall 2 Q := ⟨q, hq⟩
  have hr : IsPLHomeomorphOn (ψ ∘ q) (stdSimplex ℝ (Fin 3)) (ψ '' Q) :=
    hq.trans (hψ.restrict hQ.isPolyhedron (subset_univ _))
  have hsupport : ψ '' Q ⊆ U := by
    exact (image_mono hQU).trans (hback U).subset
  have hmeet : (ψ '' Q) ∩ K = (ψ ∘ q) '' stdSimplexBoundary 2 := by
    calc
      (ψ '' Q) ∩ K = (ψ '' Q) ∩ ψ '' (Φ '' K) := by rw [hback]
      _ = ψ '' (Q ∩ Φ '' K) := (image_inter hψi).symm
      _ = ψ '' (q '' stdSimplexBoundary 2) := by rw [htrace]
      _ = (ψ ∘ q) '' stdSimplexBoundary 2 := (image_comp ψ q _).symm
  refine ⟨ψ '' Q, ψ ∘ q, hr, hsupport, hmeet, ?_, hforward Q, fun x => hright (q x)⟩
  rintro ⟨A, a, ha, hAK, hab⟩
  have hA : IsPLBall 2 A := ⟨a, ha⟩
  refine hnot ⟨Φ '' A, Φ ∘ a, ha.trans (hΦ.restrict hA.isPolyhedron (subset_univ _)),
    image_mono hAK, ?_⟩
  rw [image_comp, hab, image_comp, hforward]

end DifferentialGeometry.Topology.PiecewiseLinear
