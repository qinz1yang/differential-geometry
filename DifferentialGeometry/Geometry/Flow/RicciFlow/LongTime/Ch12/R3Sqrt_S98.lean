import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.R3Defect_S91

set_option autoImplicit false

/-!
# CH12-S98 / G1: R3 square-root lemma for the order-0 defect jet

`sqrt_normSq0S_defect0_le_S98`: if `|p(w,w) + 2 r Ric_p(w,w)| ≤ c h(w,w)` for all `w` (`p = S.base.metric r`),
then `√|defectJet 0|_h ≤ 3 c` (dimension 3; polarisation in an `h`-orthonormal basis).
-/

noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem sqrt_normSq0S_defect0_le_S98 {D : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := M) D)
    (h : SmoothRiemannianMetric (𝓡 3) M) (r : ℝ) (x : M) {c : ℝ} (hc : 0 ≤ c)
    (hq : ∀ w : TangentSpace (𝓡 3) x,
      |(S.base.metric r).inner x w w + 2 * r * ricciTensor (S.base.metric r) x w w| ≤
        c * h.inner x w w) :
    Real.sqrt (normSq0S h x 2 (defectJet_S57 S h 0 r x)) ≤ 3 * c := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := 𝓡 3) h x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := finrank_euclideanSpace_fin
  have hinv : MetricInverseInBasis (I := 𝓡 3) h x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  have hp := fun v w : TangentSpace (𝓡 3) x => (S.base.metric r).symm x v w
  have hR := fun v w : TangentSpace (𝓡 3) x => ricciTensor_symm (S.base.metric r) x v w
  have hh := fun v w : TangentSpace (𝓡 3) x => h.symm x v w
  have key := sqrt_normSq0S_le_card_of_component_bound (I := 𝓡 3) h x 2 basis hinv
    (defectJet_S57 S h 0 r x) c hc (fun slots => by
      rw [component0S_apply, defectJet0_apply_S91]
      by_cases hij : slots 0 = slots 1
      · have e := hq (basis (slots 0))
        have g1 : h.inner x (basis (slots 0)) (basis (slots 0)) = 1 := by simp [hON]
        rw [g1, mul_one] at e
        simpa [hij] using e
      · refine abs_basis_le_of_quad_S91
          (fun v w : TangentSpace (𝓡 3) x => (S.base.metric r).inner x v w +
            2 * r * ricciTensor (S.base.metric r) x v w) (fun v w : TangentSpace (𝓡 3) x => h.inner x v w) ?_ hh ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          hq _ _ (by simp [hON]) (by simp [hON]) (by simp [hON, hij])
        · intro v w; rw [hp v w, hR v w]
        · intro u v w; simp only [map_add, _root_.add_apply]; ring
        · intro u v w; simp only [map_add]; ring
        · intro u v w; simp only [map_sub, _root_.sub_apply]; ring
        · intro u v w; simp only [map_sub]; ring
        · intro u v w; simp only [map_add, _root_.add_apply]
        · intro u v w; simp only [map_add]
        · intro u v w; simp only [map_sub, _root_.sub_apply]
        · intro u v w; simp only [map_sub])
  have hcard : (Fintype.card (Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) : ℝ) = 9 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hdim]; norm_num
  rw [hcard] at key
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [h9] at key

end GC.LongTime.Ch12
