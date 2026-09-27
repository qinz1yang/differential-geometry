import DifferentialGeometry.Topology.VectorField.CollarIndex

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace DifferentialGeometry.VectorField
open DifferentialGeometry.LocalDegree
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)

private def productCoordinateDiffeomorph (d : ℕ) :
    Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (d + 2))) (EuclideanSpace ℝ (Fin (d + 1)) × ℝ) 1 where
  toEquiv := (euclideanProductChart d).toEquiv
  contMDiff_toFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (euclideanProductChart d).contDiff.contMDiff
  contMDiff_invFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (euclideanProductChart d).symm.contDiff.contMDiff

private def productWithIdentity
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1) :
    PartialDiffeomorph ((𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))).prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, ℝ)) (EuclideanSpace ℝ (Fin (d + 1)) × ℝ) (M × ℝ) 1 where
  toPartialEquiv := f.toPartialEquiv.prod (PartialEquiv.refl ℝ)
  open_source := f.open_source.prod isOpen_univ
  open_target := f.open_target.prod isOpen_univ
  contMDiffOn_toFun := f.contMDiffOn.prodMap contMDiffOn_id
  contMDiffOn_invFun := f.symm.contMDiffOn.prodMap contMDiffOn_id


def collarParametrization
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
      (I.prod 𝓘(ℝ, ℝ)) (EuclideanSpace ℝ (Fin (d + 2))) (M × ℝ) 1 :=
  (productCoordinateDiffeomorph d).toPartialDiffeomorph.trans (productWithIdentity I f)


theorem collarParametrization_apply
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1) (z : EuclideanSpace ℝ (Fin (d + 2))) :
    collarParametrization I f z = (f (euclideanProductChart d z).1, (euclideanProductChart d z).2) := rfl


theorem collarParametrization_symm_apply
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1) (p : M × ℝ) :
    (collarParametrization I f).symm p = euclideanProductPoint d (f.symm p.1) p.2 := rfl


theorem collarParametrization_mem_source
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1) (z : EuclideanSpace ℝ (Fin (d + 2))) :
    z ∈ (collarParametrization I f).source ↔ (euclideanProductChart d z).1 ∈ f.source := by
  change (z ∈ univ ∧ ((euclideanProductChart d z).1 ∈ f.source ∧
    (euclideanProductChart d z).2 ∈ univ)) ↔ _
  simp


theorem collarParametrization_mem_target
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1) (p : M × ℝ) :
    p ∈ (collarParametrization I f).target ↔ p.1 ∈ f.target := by
  change ((p.1 ∈ f.target ∧ p.2 ∈ univ) ∧ (f.symm p.1, p.2) ∈ univ) ↔ _
  simp


theorem collarParametrization_point
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1)
    (x : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    collarParametrization I f (euclideanProductPoint d x t) = (f x, t) := by
  rw [collarParametrization_apply]
  change (f ((euclideanProductChart d) ((euclideanProductChart d).symm (x, t))).1,
    ((euclideanProductChart d) ((euclideanProductChart d).symm (x, t))).2) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

private theorem mfderiv_collarParametrization
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1) {z : EuclideanSpace ℝ (Fin (d + 2))}
    (hz : (euclideanProductChart d z).1 ∈ f.source) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2))) (I.prod 𝓘(ℝ, ℝ))
        (collarParametrization I f) z =
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f (euclideanProductChart d z).1).prodMap
        (ContinuousLinearMap.id ℝ ℝ)).comp (euclideanProductChart d).toContinuousLinearMap := by
  have hf := f.mdifferentiableAt one_ne_zero hz
  have hp := hf.prodMap' (mdifferentiableAt_id (I := 𝓘(ℝ, ℝ))
    (x := (euclideanProductChart d z).2))
  have hC := (productCoordinateDiffeomorph d).contMDiff.mdifferentiable one_ne_zero z
  change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2))) (I.prod 𝓘(ℝ, ℝ))
    (Prod.map f id ∘ (productCoordinateDiffeomorph d)) z = _
  erw [mfderiv_comp z hp hC, mfderiv_prodMap hf mdifferentiableAt_id, mfderiv_id]
  have hCd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))).prod 𝓘(ℝ, ℝ))
      (productCoordinateDiffeomorph d) z = (euclideanProductChart d).toContinuousLinearMap := by
    change mfderiv _ _ (euclideanProductChart d) z = _
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, mfderiv_eq_fderiv,
      (euclideanProductChart d).hasFDerivAt.fderiv]
  exact congrArg (fun L : EuclideanSpace ℝ (Fin (d + 2)) →L[ℝ]
    (EuclideanSpace ℝ (Fin (d + 1)) × ℝ) =>
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f (euclideanProductChart d z).1).prodMap
        (ContinuousLinearMap.id ℝ ℝ)).comp L) hCd

theorem mpullback_collarExtension_collarParametrization
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1)
    (T : ∀ x : M, TangentSpace I x) (b : M → ℝ) (ρ : ℝ → ℝ)
    {z : EuclideanSpace ℝ (Fin (d + 2))} (hz : z ∈ (collarParametrization I f).source) :
    _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2)))
        (I.prod 𝓘(ℝ, ℝ)) (collarParametrization I f) (collarExtension T b ρ) z =
      euclideanCollarExtension (_root_.VectorField.mpullback
        𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f T) (b ∘ f) ρ z := by
  have hz' := (collarParametrization_mem_source I f z).mp hz
  obtain ⟨A, hA⟩ := isInvertible_mfderiv_partialDiffeomorph f one_ne_zero hz'
  let B := (euclideanProductChart d).trans (A.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  have hB : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 2))) (I.prod 𝓘(ℝ, ℝ))
      (collarParametrization I f) z = B.toContinuousLinearMap := by
    rw [mfderiv_collarParametrization I f hz', ← hA]
    rfl
  unfold _root_.VectorField.mpullback
  erw [hB, ContinuousLinearMap.inverse_equiv]
  have hAi : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f
      (euclideanProductChart d z).1).inverse (T (f (euclideanProductChart d z).1)) =
      A.symm (T (f (euclideanProductChart d z).1)) := by
    rw [← hA, ContinuousLinearMap.inverse_equiv]
    rfl
  change (euclideanProductChart d).symm
    (A.symm (T (f (euclideanProductChart d z).1)),
      (1 - ρ (euclideanProductChart d z).2) * b (f (euclideanProductChart d z).1) +
        ρ (euclideanProductChart d z).2) =
    (euclideanProductChart d).symm
    ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f
      (euclideanProductChart d z).1).inverse (T (f (euclideanProductChart d z).1)),
      (1 - ρ (euclideanProductChart d z).2) * b (f (euclideanProductChart d z).1) +
        ρ (euclideanProductChart d z).2)
  exact congrArg (euclideanProductChart d).symm (Prod.ext hAi.symm rfl)

end DifferentialGeometry.VectorField
