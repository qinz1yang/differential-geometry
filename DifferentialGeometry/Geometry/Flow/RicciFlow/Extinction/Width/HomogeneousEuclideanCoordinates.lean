import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.HomogeneousRegularityBridge
import DifferentialGeometry.Geometry.Metric.Conformal

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.PDE.RicciFlow.Extinction.Width

private def translateChart (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  (Homeomorph.addRight p).toOpenPartialHomeomorph

private lemma translateChart_coe (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) :
    (translateChart n p : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      = fun y => y + p := by
  funext y
  simp [translateChart]

private lemma translateChart_symm_coe (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) :
    ((translateChart n p).symm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      = fun y => y + (-p) := by
  funext y
  simp [translateChart, Homeomorph.addRight_symm, Homeomorph.coe_addRight]

private lemma translateChart_source (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) :
    (translateChart n p).source = Set.univ := by
  simp [translateChart]

private lemma contMDiffOn_translateChart (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (translateChart n p) (translateChart n p).source := by
  rw [contMDiffOn_iff_contDiffOn, translateChart_coe, translateChart_source, contDiffOn_univ]
  fun_prop

private lemma contMDiffOn_translateChart_symm (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (translateChart n p).symm (translateChart n p).target := by
  rw [contMDiffOn_iff_contDiffOn, translateChart_symm_coe]
  have htarget : (translateChart n p).target = Set.univ := by
    simp [translateChart]
  rw [htarget, contDiffOn_univ]
  fun_prop

private def translateCubeChart (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) :
    CubeChart (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Q := EuclideanSpace ℝ (Fin n)) n where
  chart := translateChart n p
  closedCube_subset_source := fun _ _ => Set.mem_univ _
  smooth := contMDiffOn_translateChart n p
  smooth_inverse := contMDiffOn_translateChart_symm n p

private lemma translateCubeChart_centered (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) :
    (translateCubeChart n p).chart 0 = p := by
  change translateChart n p 0 = p
  rw [translateChart_coe]
  simp

private lemma mfderiv_translate_apply {n : ℕ} (p y : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (fun z : EuclideanSpace ℝ (Fin n) => z + p) y v = v := by
  simp only [mfderiv_eq_fderiv, fderiv_add_const, fderiv_fun_id]
  rfl

private lemma translateCubeChart_pullMetric {n : ℕ} (p y v w : EuclideanSpace ℝ (Fin n)) :
    (translateCubeChart n p).pullMetric
        (euclideanMetric (EuclideanSpace ℝ (Fin n))) y v w = inner ℝ v w := by
  have h1 := mfderiv_translate_apply p y v
  have h2 := mfderiv_translate_apply p y w
  change (euclideanMetric (EuclideanSpace ℝ (Fin n))).inner (y + p)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun z : EuclideanSpace ℝ (Fin n) => z + p) y v)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (fun z : EuclideanSpace ℝ (Fin n) => z + p) y w) = inner ℝ v w
  rw [h1, h2]
  exact euclideanMetric_inner (EuclideanSpace ℝ (Fin n)) (y + p) v w

noncomputable def euclideanHomogeneousCoordinates (n : ℕ) :
    HomogeneousCoordinates (euclideanMetric (EuclideanSpace ℝ (Fin n))) n where
  atPoint p := translateCubeChart n p
  centered p := translateCubeChart_centered n p
  lowerBound := 1
  upperBound := 1
  lower_pos := one_pos
  lower_le_upper := le_rfl
  ellipticity := by
    intro p y _ v
    rw [translateCubeChart_pullMetric, real_inner_self_eq_norm_sq]
    constructor <;> simp
  derivative_bounds := by
    intro k
    refine ⟨1, zero_le_one, fun p y _ i j => ?_⟩
    have hfun : (fun x : EuclideanSpace ℝ (Fin n) =>
        (translateCubeChart n p).pullMetric
          (euclideanMetric (EuclideanSpace ℝ (Fin n))) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
        = fun _ => inner ℝ (EuclideanSpace.single i (1 : ℝ))
            (EuclideanSpace.single j (1 : ℝ)) := by
      funext x
      rw [translateCubeChart_pullMetric]
    rw [hfun]
    rcases k with _ | k
    · rw [norm_iteratedFDeriv_zero]
      have habs := abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ))
      rw [Real.norm_eq_abs]
      simpa using habs
    · rw [iteratedFDeriv_const_of_ne (by simp) _]
      simp

theorem nonempty_homogeneousCoordinates_euclideanMetric (n : ℕ) :
    Nonempty (HomogeneousCoordinates (euclideanMetric (EuclideanSpace ℝ (Fin n))) n) :=
  ⟨euclideanHomogeneousCoordinates n⟩

theorem homogeneouslyRegularMetric_euclideanMetric :
    HomogeneouslyRegularMetric (euclideanMetric (EuclideanSpace ℝ (Fin 3))) :=
  homogeneouslyRegularMetric_of_homogeneousCoordinates _
    (euclideanHomogeneousCoordinates 3)

end DifferentialGeometry.Geometry
