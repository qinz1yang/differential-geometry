import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Regularized

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegJacobi_smooth
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (V : TangentSpace I x) :
    ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I.tangent ∞
      (fun p : E × Real =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y)
          (lRegCurve S T x p.1 p.2)
          (lRegJacobiField S T x p.1 V p.2) : TangentBundle I M))
      (lRegJointDom S T x) := by
  let J := 𝓘(Real, E).prod 𝓘(Real, Real)
  let U := lRegJointDom S T x
  let F : E × Real → M := fun p => lRegCurve S T x p.1 p.2
  have hU : IsOpen U := lRegJointDom_open S hS T x
  have hF : ContMDiffOn J I ∞ F U := lRegCurve_smoothOn S hS T x
  have htm := hF.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hU.uniqueMDiffOn
  have hσ : ContMDiff J J.tangent ∞
      (fun p : E × Real =>
        (TotalSpace.mk' (E × Real) p ((V : E), (0 : Real)) :
          TangentBundle J (E × Real))) := by
    have hE : ContMDiff 𝓘(Real, E) 𝓘(Real, E).tangent ∞
        (fun z : E =>
          (TotalSpace.mk' E z (V : E) : TangentBundle 𝓘(Real, E) E)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : E => (V : E))).mpr contDiff_const
    have hR : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent ∞
        (fun r : Real =>
          (TotalSpace.mk' Real r (0 : Real) :
            TangentBundle 𝓘(Real, Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real => (0 : Real))).mpr contDiff_const
    have hpair := (hE.comp contMDiff_fst).prodMk (hR.comp contMDiff_snd)
    have hsymm : ContMDiff
        (𝓘(Real, E).tangent.prod 𝓘(Real, Real).tangent) J.tangent ∞
        ((equivTangentBundleProd 𝓘(Real, E) E
          𝓘(Real, Real) Real).symm) :=
      contMDiff_equivTangentBundleProd_symm
    have h := hsymm.comp hpair
    change ContMDiff J J.tangent ∞
      (fun p : E × Real =>
        (TotalSpace.mk' (E × Real) p ((V : E), (0 : Real)) :
          TangentBundle J (E × Real))) at h
    exact h
  have hcomp : ContMDiffOn J I.tangent ∞
      (fun p : E × Real =>
        tangentMapWithin J I F U
          (TotalSpace.mk' (E × Real) p ((V : E), (0 : Real)))) U :=
    htm.comp (hσ.contMDiffOn (s := U)) (fun p hp => hp)
  refine hcomp.congr ?_
  intro p hp
  have hwithin : mfderivWithin J I F U p = mfderiv J I F p :=
    mfderivWithin_of_isOpen hU hp
  have hdiff : MDifferentiableAt J I F p :=
    ((hF p hp).contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)
  have hsplit := mfderiv_prod_eq_add_apply
    (I := 𝓘(Real, E)) (I' := 𝓘(Real, Real)) (I'' := I)
    (f := F) (p := p) (v := ((V : E), (0 : Real))) hdiff
  have hjoint :
      mfderiv J I F p ((V : E), (0 : Real)) =
        lRegJacobiField S T x p.1 V p.2 := by
    have hzero : mfderiv 𝓘(Real, Real) I
        (fun z : Real => F (p.1, z)) p.2 (0 : Real) = 0 :=
      map_zero _
    rw [hzero, add_zero] at hsplit
    simpa only [F, lRegJacobiField] using hsplit
  change TotalSpace.mk' E (E := fun y : M => TangentSpace I y)
      (F p) (lRegJacobiField S T x p.1 V p.2) =
    tangentMapWithin J I F U
      (TotalSpace.mk' (E × Real) p ((V : E), (0 : Real)))
  simp only [tangentMapWithin, hwithin, hjoint]

end DifferentialGeometry.PDE.RicciFlow.Perelman
