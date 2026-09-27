import DifferentialGeometry.Topology.Manifold.Interval.StripHeight
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Conormal

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace DifferentialGeometry.Manifold.BoundaryCollar
variable {E H B M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  {J : ModelWithCorners ℝ E H}
  {n : ℕ} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  {ε : ℝ} [Fact ((0 : ℝ) < ε)]
  (S : TopologicalSpace.Opens (B × Icc (0 : ℝ) ε)) (Y : TopologicalSpace.Opens M)
  (e : Diffeomorph (J.prod (𝓡∂ 1)) (𝓡∂ (n + 1)) S Y ∞)

theorem collar_normal_eq_pos_mul_proj {q : S} (hq : q.val.2.val = 0)
    (hboundary : (𝓡∂ (n + 1)).IsBoundaryPoint (e q).val) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : TangentSpace (J.prod (𝓡∂ 1)) q,
      DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2 v.2 =
        c * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)))
          (mfderiv (J.prod (𝓡∂ 1)) (𝓡∂ (n + 1)) e q v) := by
  let f : Y → ℝ := fun y => (e.symm y).val.2.val
  have hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ f :=
    contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp (contMDiff_subtype_val.comp e.symm.contMDiff))
  have hcomp : f ∘ e = fun p : S => p.val.2.val := by
    funext p
    change (e.symm (e p)).val.2.val = p.val.2.val
    rw [e.symm_apply_apply]
  have hd := mfderiv_comp q (hf.mdifferentiableAt (by simp)) (e.contMDiff.mdifferentiableAt (by simp))
  rw [hcomp] at hd
  have hreg : mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f (e q) ≠ 0 := by
    intro hz
    apply DifferentialGeometry.Manifold.Interval.mfderiv_stripHeight_ne_zero (J := J) S q
    rw [hd, hz, ContinuousLinearMap.zero_comp]
    rfl
  obtain ⟨c, hc, hdf⟩ := mfderiv_eq_pos_smul_proj_of_nonneg
    (hf.mdifferentiableAt (by simp))
    ((𝓡∂ (n + 1)).isBoundaryPoint_iff_isBoundaryPoint_val.mpr hboundary)
    (by change (e.symm (e q)).val.2.val = 0; rw [e.symm_apply_apply]; exact hq)
    (Eventually.of_forall (fun y : Y => (e.symm y).val.2.property.1)) hreg
  refine ⟨c, hc, fun v => ?_⟩
  rw [← DifferentialGeometry.Manifold.Interval.mfderiv_stripHeight S q v, hd, hdf]
  rfl

theorem proj_collar_pushforward_neg {q : S} (hq : q.val.2.val = 0)
    (hboundary : (𝓡∂ (n + 1)).IsBoundaryPoint (e q).val)
    (v : TangentSpace (J.prod (𝓡∂ 1)) q)
    (hv : DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2 v.2 < 0) :
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)))
      (mfderiv (J.prod (𝓡∂ 1)) (𝓡∂ (n + 1)) e q v) < 0 := by
  obtain ⟨c, hc, he⟩ := collar_normal_eq_pos_mul_proj S Y e hq hboundary
  rw [he v] at hv
  nlinarith

end DifferentialGeometry.Manifold.BoundaryCollar
