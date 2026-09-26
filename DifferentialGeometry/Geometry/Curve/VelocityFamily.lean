import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
namespace DifferentialGeometry.Geometry
open Set Bundle Filter
open scoped Manifold ContDiff Topology
variable {F E H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
 [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem contMDiffOn_curve_velocity_family
    {alpha : F × Real → M} {V : Set F} {K : Set Real}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, F).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K)) :
    ContMDiffOn (𝓘(Real, F).prod 𝓘(Real, Real)) I.tangent ∞
      (fun q : F × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I)
          (alpha q)
          (mfderiv 𝓘(ℝ, ℝ) I (fun s ↦ alpha (q.1, s)) q.2 (1 : ℝ)) :
            TangentBundle I M)) (V ×ˢ K) := by
  let J := 𝓘(Real, F).prod 𝓘(Real, Real)
  let U := V ×ˢ K
  have hUopen : IsOpen U := hVopen.prod hKopen
  have htm :=
    halpha.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hUopen.uniqueMDiffOn
  have hunit : ContMDiff J J.tangent ∞
      (fun q : F × Real ↦
        (TotalSpace.mk' (F × Real) q ((0 : F), (1 : Real)) :
          TangentBundle J (F × Real))) := by
    have hF : ContMDiff 𝓘(Real, F) 𝓘(Real, F).tangent ∞
        (fun z : F ↦ (TotalSpace.mk' F z (0 : F) : TangentBundle 𝓘(Real, F) F)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : F ↦ (0 : F))).mpr contDiff_const
    have hR : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent ∞
        (fun r : Real ↦
          (TotalSpace.mk' Real r (1 : Real) : TangentBundle 𝓘(Real, Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    have hpair := (hF.comp contMDiff_fst).prodMk (hR.comp contMDiff_snd)
    have hsymm : ContMDiff
        (𝓘(Real, F).tangent.prod 𝓘(Real, Real).tangent) J.tangent ∞
        ((equivTangentBundleProd 𝓘(Real, F) F
          𝓘(Real, Real) Real).symm) :=
      contMDiff_equivTangentBundleProd_symm
    change ContMDiff J J.tangent ∞
      ((equivTangentBundleProd 𝓘(Real, F) F
        𝓘(Real, Real) Real).symm ∘ fun q : F × Real ↦
          ((TotalSpace.mk' F q.1 (0 : F) : TangentBundle 𝓘(Real, F) F),
            (TotalSpace.mk' Real q.2 (1 : Real) :
              TangentBundle 𝓘(Real, Real) Real)))
    exact hsymm.comp hpair
  have hcomp : ContMDiffOn J I.tangent ∞
      (fun q : F × Real ↦ tangentMapWithin J I alpha U
        (TotalSpace.mk' (F × Real) q ((0 : F), (1 : Real)))) U :=
    htm.comp hunit.contMDiffOn (fun _ hq ↦ hq)
  refine hcomp.congr ?_
  intro q hq
  have hwithin : mfderivWithin J I alpha U q = mfderiv J I alpha q :=
    mfderivWithin_of_isOpen hUopen hq
  have hdiff : MDifferentiableAt J I alpha q :=
    ((halpha q hq).contMDiffAt (hUopen.mem_nhds hq)).mdifferentiableAt (by simp)
  have hsplit := mfderiv_prod_eq_add_apply
    (I := 𝓘(Real, F)) (I' := 𝓘(Real, Real)) (I'' := I)
    (f := alpha) (p := q) (v := ((0 : F), (1 : Real))) hdiff
  have hzero :
      mfderiv 𝓘(Real, F) I (fun z : F ↦ alpha (z, q.2)) q.1 (0 : F) = 0 :=
    (mfderiv 𝓘(Real, F) I (fun z : F ↦ alpha (z, q.2)) q.1).map_zero
  change TotalSpace.mk' E (E := TangentSpace I) (alpha q)
      (mfderiv 𝓘(ℝ, ℝ) I (fun s ↦ alpha (q.1, s)) q.2 (1 : ℝ)) =
    tangentMapWithin J I alpha U
      (TotalSpace.mk' (F × Real) q ((0 : F), (1 : Real)))
  simp only [tangentMapWithin, hwithin]
  refine TotalSpace.ext rfl ?_
  exact heq_of_eq (by
    simpa only [hzero, zero_add] using hsplit.symm)

end DifferentialGeometry.Geometry
