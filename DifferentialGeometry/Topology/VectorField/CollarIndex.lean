import DifferentialGeometry.Topology.VectorField.CollarLinearization
import DifferentialGeometry.Topology.LocalDegree.Product
import DifferentialGeometry.Topology.LocalDegree.TriangularCoordinateLinear
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.LocalDegree.DomainComposition

set_option autoImplicit false
open Set Metric
open scoped Manifold ContDiff Topology
noncomputable section
namespace DifferentialGeometry.VectorField
open DifferentialGeometry.LocalDegree
variable {d : ℕ}


def euclideanCollarExtension
    (T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) (ρ : ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin (d + 2))) : EuclideanSpace ℝ (Fin (d + 2)) :=
  (euclideanProductChart d).symm
    (collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))) T b ρ
      (euclideanProductChart d z))

theorem mpullback_collarExtension_productChart
    (T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) (ρ : ℝ → ℝ) :
    _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))).prod 𝓘(ℝ, ℝ)) (euclideanProductChart d)
      (collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))) T b ρ) =
      euclideanCollarExtension T b ρ := by
  funext z
  unfold _root_.VectorField.mpullback
  erw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, mfderiv_eq_fderiv, (euclideanProductChart d).hasFDerivAt.fderiv,
    ContinuousLinearMap.inverse_equiv]
  rfl

theorem euclideanCollarExtension_point
    (T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) (ρ : ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    euclideanCollarExtension T b ρ (euclideanProductPoint d x t) =
      euclideanProductPoint d (T x) ((1 - ρ t) * b x + ρ t) := by
  change (euclideanProductChart d).symm
    (collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))) T b ρ
      ((euclideanProductChart d) ((euclideanProductChart d).symm (x, t)))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem euclideanCollarExtension_eq_comp
    (T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) (ρ : ℝ → ℝ) :
    euclideanCollarExtension T b ρ =
      euclideanProductField T ∘ euclideanCollarExtension id b ρ := by
  funext z
  let C := euclideanProductChart d
  apply C.injective
  change C (C.symm (T (C z).1, (1 - ρ (C z).2) * b (C z).1 + ρ (C z).2)) =
    C (euclideanProductField T (C.symm ((C z).1,
      (1 - ρ (C z).2) * b (C z).1 + ρ (C z).2)))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (euclideanProductChart_field T ((C z).1,
    (1 - ρ (C z).2) * b (C z).1 + ρ (C z).2)).symm

private theorem contDiffAt_collarNormalCoordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E → ℝ} {ρ : ℝ → ℝ} {x : E} {t : ℝ}
    (hb : ContDiffAt ℝ 1 b x) (hρ : ContDiffAt ℝ 1 ρ t) :
    ContDiffAt ℝ 1 (collarExtension (I := 𝓘(ℝ, E)) id b ρ) (x, t) := by
  have hb' := hb.comp (x, t) contDiffAt_fst
  have hρ' := hρ.comp (x, t) contDiffAt_snd
  exact contDiffAt_fst.prodMk (((contDiffAt_const.sub hρ').mul hb').add hρ')

private theorem hasFDerivAt_collarNormalCoordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E → ℝ} {ρ : ℝ → ℝ} {x : E} {t : ℝ}
    (hb : DifferentiableAt ℝ b x) (hρ : DifferentiableAt ℝ ρ t)
    (hc : deriv ρ t * (1 - b x) ≠ 0) :
    HasFDerivAt (collarExtension (I := 𝓘(ℝ, E)) id b ρ)
      (triangularLinearEquiv ((1 - ρ t) • fderiv ℝ b x)
        (deriv ρ t * (1 - b x)) hc).toContinuousLinearMap (x, t) := by
  have h := hasFDerivAt_collarExtension (hasFDerivAt_id x) hb.hasFDerivAt hρ.hasDerivAt
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem hasFDerivAt_euclideanCollarNormalCoordinate
    {b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {ρ : ℝ → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ}
    (hb : DifferentiableAt ℝ b x) (hρ : DifferentiableAt ℝ ρ t)
    (hc : deriv ρ t * (1 - b x) ≠ 0) :
    HasFDerivAt (euclideanCollarExtension id b ρ)
      (triangularConjugate (euclideanProductChart d)
        ((1 - ρ t) • fderiv ℝ b x) (deriv ρ t * (1 - b x)) hc).toContinuousLinearMap
      (euclideanProductPoint d x t) := by
  let C := euclideanProductChart d
  have he : C (euclideanProductPoint d x t) = (x, t) := C.apply_symm_apply (x, t)
  have hD : HasFDerivAt
      (collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))) id b ρ)
      (triangularLinearEquiv ((1 - ρ t) • fderiv ℝ b x)
        (deriv ρ t * (1 - b x)) hc).toContinuousLinearMap
      (C (euclideanProductPoint d x t)) := by
    simpa only [he] using hasFDerivAt_collarNormalCoordinate hb hρ hc
  have h := C.symm.hasFDerivAt.comp (euclideanProductPoint d x t)
    (hD.comp (euclideanProductPoint d x t) C.hasFDerivAt)
  exact h

theorem exists_partialDiffeomorph_collarNormalCoordinate
    {b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {ρ : ℝ → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ}
    (hb : ContDiffAt ℝ 1 b x) (hρ : ContDiffAt ℝ 1 ρ t)
    (hc : deriv ρ t * (1 - b x) ≠ 0) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
      (EuclideanSpace ℝ (Fin (d + 2))) (EuclideanSpace ℝ (Fin (d + 2))) 1,
      euclideanProductPoint d x t ∈ Φ.source ∧
        (Φ : EuclideanSpace ℝ (Fin (d + 2)) → EuclideanSpace ℝ (Fin (d + 2))) =
          euclideanCollarExtension id b ρ := by
  let C := euclideanProductChart d
  have he : C (euclideanProductPoint d x t) = (x, t) := C.apply_symm_apply (x, t)
  have hD : ContDiffAt ℝ 1
      (collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))) id b ρ)
      (C (euclideanProductPoint d x t)) := by
    simpa only [he] using contDiffAt_collarNormalCoordinate hb hρ
  have hd : ContDiffAt ℝ 1 (euclideanCollarExtension id b ρ)
      (euclideanProductPoint d x t) :=
    C.symm.contDiff.contDiffAt.comp _ (hD.comp _ C.contDiff.contDiffAt)
  exact DifferentialGeometry.Manifold.exists_partialDiffeomorph_of_contDiffAt
    (triangularConjugate C ((1 - ρ t) • fderiv ℝ b x) (deriv ρ t * (1 - b x)) hc)
    hd (hasFDerivAt_euclideanCollarNormalCoordinate hb.differentiableAt_one hρ.differentiableAt_one hc)

private theorem collarNormalCoordinate_center
    {b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {ρ : ℝ → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ}
    (hg : (1 - ρ t) * b x + ρ t = 0) :
    euclideanCollarExtension id b ρ (euclideanProductPoint d x t) =
      euclideanProductPoint d x 0 := by
  rw [euclideanCollarExtension_point, hg]
  rfl

theorem isolatedZero_euclideanCollarExtension_of_pos
    {T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {ρ : ℝ → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ}
    (hT : isolatedZero T x) (hb : ContDiffAt ℝ 1 b x) (hρ : ContDiffAt ℝ 1 ρ t)
    (hg : (1 - ρ t) * b x + ρ t = 0) (hc : 0 < deriv ρ t * (1 - b x)) :
    isolatedZero (euclideanCollarExtension T b ρ) (euclideanProductPoint d x t) := by
  obtain ⟨Φ, hp, hΦ⟩ := exists_partialDiffeomorph_collarNormalCoordinate hb hρ hc.ne'
  let A := triangularConjugate (euclideanProductChart d)
    ((1 - ρ t) • fderiv ℝ b x) (deriv ρ t * (1 - b x)) hc.ne'
  have hA : A.toContinuousLinearMap = fderiv ℝ Φ (euclideanProductPoint d x t) := by
    rw [hΦ]
    exact (hasFDerivAt_euclideanCollarNormalCoordinate
      hb.differentiableAt_one hρ.differentiableAt_one hc.ne').fderiv.symm
  have hz : Φ (euclideanProductPoint d x t) = euclideanProductPoint d x 0 := by
    rw [hΦ]
    exact collarNormalCoordinate_center hg
  have hP : isolatedZero (euclideanProductField T) (Φ (euclideanProductPoint d x t)) :=
    hz.symm ▸ isolatedZero_euclideanProduct_at hT
  have hi := isolatedZero_comp_partialDiffeomorph Φ le_rfl hp A hA hP
  have heq : (fun y => euclideanProductField T (Φ y)) = euclideanCollarExtension T b ρ := by
    rw [hΦ]
    exact (euclideanCollarExtension_eq_comp T b ρ).symm
  simpa only [heq] using hi

theorem euclideanLocalDegree_collarExtension_of_pos
    {T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {ρ : ℝ → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ}
    (hT : isolatedZero T x) (hb : ContDiffAt ℝ 1 b x) (hρ : ContDiffAt ℝ 1 ρ t)
    (hg : (1 - ρ t) * b x + ρ t = 0) (hc : 0 < deriv ρ t * (1 - b x)) :
    euclideanLocalDegree (euclideanCollarExtension T b ρ) (euclideanProductPoint d x t)
        (isolatedZero_euclideanCollarExtension_of_pos hT hb hρ hg hc) =
      euclideanLocalDegree T x hT := by
  obtain ⟨Φ, hp, hΦ⟩ := exists_partialDiffeomorph_collarNormalCoordinate hb hρ hc.ne'
  let A := triangularConjugate (euclideanProductChart d)
    ((1 - ρ t) • fderiv ℝ b x) (deriv ρ t * (1 - b x)) hc.ne'
  have hA : A.toContinuousLinearMap = fderiv ℝ Φ (euclideanProductPoint d x t) := by
    rw [hΦ]
    exact (hasFDerivAt_euclideanCollarNormalCoordinate
      hb.differentiableAt_one hρ.differentiableAt_one hc.ne').fderiv.symm
  have hz : Φ (euclideanProductPoint d x t) = euclideanProductPoint d x 0 := by
    rw [hΦ]
    exact collarNormalCoordinate_center hg
  have hP : isolatedZero (euclideanProductField T) (Φ (euclideanProductPoint d x t)) :=
    hz.symm ▸ isolatedZero_euclideanProduct_at hT
  have hd := euclideanLocalDegree_comp_partialDiffeomorph Φ le_rfl hp A hA hP
  have hsign : euclideanSphereDegree (linearSphereMap A) = 1 :=
    euclideanSphereDegree_triangularConjugate (euclideanProductChart d) _ hc
  rw [hsign, one_mul] at hd
  have heq : (fun y => euclideanProductField T (Φ y)) = euclideanCollarExtension T b ρ := by
    rw [hΦ]
    exact (euclideanCollarExtension_eq_comp T b ρ).symm
  have hh : euclideanLocalDegree (euclideanCollarExtension T b ρ) (euclideanProductPoint d x t)
      (isolatedZero_euclideanCollarExtension_of_pos hT hb hρ hg hc) =
      euclideanLocalDegree (euclideanProductField T) (euclideanProductPoint d x 0)
        (isolatedZero_euclideanProduct_at hT) := by
    simpa only [heq, hz] using hd
  exact hh.trans (euclideanLocalDegree_product hT)

private theorem collar_created_normal_factor
    {T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ} (hb0 : b x ≠ 0)
    (hz : collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))))
      T b collarTransition (x, t) = 0) :
    (1 - collarTransition t) * b x + collarTransition t = 0 ∧
      0 < deriv collarTransition t * (1 - b x) := by
  have hρ := contDiff_collarTransition.differentiable (by simp) t
  have hpos := collarExtension_normal_deriv_pos (fun _ => hb0) hz
  rw [(hasDerivAt_collarExtension_normal (T := T) (b := b) hρ.hasDerivAt).deriv] at hpos
  exact ⟨congrArg Prod.snd hz, hpos⟩

theorem isolatedZero_euclideanCollarExtension
    {T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ}
    (hT : isolatedZero T x) (hb : ContDiffAt ℝ 1 b x) (hb0 : b x ≠ 0)
    (hz : collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))))
      T b collarTransition (x, t) = 0) :
    isolatedZero (euclideanCollarExtension T b collarTransition) (euclideanProductPoint d x t) :=
  isolatedZero_euclideanCollarExtension_of_pos hT hb
    (contDiff_collarTransition.of_le (by simp)).contDiffAt
    (collar_created_normal_factor hb0 hz).1 (collar_created_normal_factor hb0 hz).2

theorem euclideanLocalDegree_collarExtension
    {T : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {b : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {t : ℝ}
    (hT : isolatedZero T x) (hb : ContDiffAt ℝ 1 b x) (hb0 : b x ≠ 0)
    (hz : collarExtension (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))))
      T b collarTransition (x, t) = 0) :
    euclideanLocalDegree (euclideanCollarExtension T b collarTransition)
        (euclideanProductPoint d x t) (isolatedZero_euclideanCollarExtension hT hb hb0 hz) =
      euclideanLocalDegree T x hT :=
  euclideanLocalDegree_collarExtension_of_pos hT hb
    (contDiff_collarTransition.of_le (by simp)).contDiffAt
    (collar_created_normal_factor hb0 hz).1 (collar_created_normal_factor hb0 hz).2

end DifferentialGeometry.VectorField
