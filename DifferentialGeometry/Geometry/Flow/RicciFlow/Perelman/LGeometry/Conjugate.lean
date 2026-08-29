import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private def lConjModelMFDerivAt (f : E → M) (u : E) : E →L[Real] E :=
  (tangentSpaceModelContinuousLinearEquiv (I := I) (f u)).toContinuousLinearMap.comp
    ((mfderiv 𝓘(Real, E) I f u).comp
      (tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) u).symm.toContinuousLinearMap)

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem lConj_hasFDerivAt_chart
    {f : E → M} {u : E}
    (hf : MDifferentiableAt 𝓘(Real, E) I f u) :
    HasFDerivAt ((extChartAt I (f u)) ∘ f)
      (lConjModelMFDerivAt (I := I) f u) u := by
  have hf' : HasMFDerivAt 𝓘(Real, E) I f u
      (mfderiv 𝓘(Real, E) I f u) := hf.hasMFDerivAt
  have hchart : HasMFDerivAt I 𝓘(Real, E) (extChartAt I (f u)) (f u)
      (ContinuousLinearMap.id Real E) := by
    have h := (mdifferentiableAt_extChartAt (I := I)
      (mem_chart_source H (f u))).hasMFDerivAt
    rw [mfderiv_extChartAt_self (I := I) (x := f u)] at h
    exact h
  have hcomp := hchart.comp u hf'
  have hcomp' := hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  exact hcomp'.congr_fderiv (by
    ext v
    with_unfolding_all rfl)

omit [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem written_fderiv_inv
    {f : E → M} {u : E}
    (hf : MDifferentiableAt 𝓘(Real, E) I f u)
    (hinv : (mfderiv 𝓘(Real, E) I f u).IsInvertible) :
    (fderiv Real
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (extChartAt 𝓘(Real, E) u u)).IsInvertible := by
  have hchart := lConj_hasFDerivAt_chart (I := I) hf
  have hwritten : HasFDerivAt
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (lConjModelMFDerivAt (I := I) f u)
      (extChartAt 𝓘(Real, E) u u) := by
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_id, id_eq] using hchart
  rw [hwritten.fderiv]
  simpa only [lConjModelMFDerivAt, ContinuousLinearMap.isInvertible_comp_equiv,
    ContinuousLinearMap.isInvertible_equiv_comp] using hinv

omit [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
def IsLConj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) : Prop :=
  (Z, tau) ∈ lExpPosDom S T x ∧
    ¬ Function.Injective fun V : E =>
      mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z V

omit [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem isLConj_iff
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    IsLConj S T x Z tau ↔
      (Z, tau) ∈ lExpPosDom S T x ∧
        ∃ V : E, V ≠ 0 ∧
          mfderiv 𝓘(Real, E) I
            (fun W : E => lExp S T x W tau) Z V = 0 := by
  unfold IsLConj
  let f : E →L[Real] E := mfderiv 𝓘(Real, E) I
    (fun W : E => lExp S T x W tau) Z
  refine and_congr_right fun _ => ?_
  have hker : Function.Injective (fun V : E => f V) ↔
      ∀ V : E, f V = 0 → V = 0 := by
    constructor
    · intro hinj V hV
      exact hinj (hV.trans (map_zero f).symm)
    · intro hzero V W hVW
      apply sub_eq_zero.mp
      apply hzero
      change f V = f W at hVW
      calc
        f (V - W) = f V - f W := map_sub f V W
        _ = 0 := sub_eq_zero.mpr hVW
  change (¬ Function.Injective fun V : E => f V) ↔
    ∃ V : E, V ≠ 0 ∧ f V = 0
  rw [hker]
  push Not
  constructor
  · rintro ⟨V, hVzero, hVne⟩
    exact ⟨V, hVne, hVzero⟩
  · rintro ⟨V, hVne, hVzero⟩
    exact ⟨V, hVzero, hVne⟩

omit [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem isLConj_iff_jac
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    IsLConj S T x Z tau ↔
      (Z, tau) ∈ lExpPosDom S T x ∧
        ∃ V : E, V ≠ 0 ∧
          lRegJacobiField S T x Z V (Real.sqrt tau) = 0 := by
  rw [isLConj_iff]
  refine and_congr_right fun _ => ?_
  refine exists_congr fun V => and_congr_right fun _ => ?_
  have heq := lExpJacobi_eq (I := I) S T x Z V tau
  constructor
  · intro h
    exact heq.symm.trans h
  · intro h
    exact heq.trans h

omit [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lExpDeriv_inj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    Function.Injective fun V : E =>
      mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z V := by
  by_contra hinj
  exact hconj ⟨hdom, hinj⟩

omit [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lExpDeriv_surj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    Function.Surjective fun V : E =>
      mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z V := by
  let Q := tangentSpaceModelContinuousLinearEquiv
    (I := I) (lExp S T x Z tau)
  let L : E →L[Real] E := Q.toContinuousLinearMap.comp
    (mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z)
  have hinj : Function.Injective L := by
    intro V W hVW
    apply lExpDeriv_inj S T x Z tau hdom hconj
    exact Q.injective hVW
  have hsurj := LinearMap.surjective_of_injective hinj
  intro Y
  obtain ⟨V, hV⟩ := hsurj (Q Y)
  refine ⟨V, Q.injective ?_⟩
  exact hV

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExp_localDiffeo
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    IsLocalDiffeomorphAt 𝓘(Real, E) I ∞
      (fun W : E => lExp S T x W tau) Z := by
  let f : E → M := fun W => lExp S T x W tau
  let z : E := Z
  let U : Set E := (fun W : E => (W, tau)) ⁻¹' lExpPosDom S T x
  have hpair : ContMDiff 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      (fun W : E => (W, tau)) :=
    contMDiff_id.prodMk contMDiff_const
  have hUopen : IsOpen U :=
    (lExpPosDom_open S hS T x).preimage hpair.continuous
  have hZU : z ∈ U := by
    change (Z, tau) ∈ lExpPosDom S T x
    exact hdom
  have hfU : ContMDiffOn 𝓘(Real, E) I ∞ f U := by
    apply (lExp_smoothOn S hS T x).comp hpair.contMDiffOn
    intro W hW
    exact hW
  let L : E →L[Real] TangentSpace I (f z) :=
    mfderiv 𝓘(Real, E) I f z
  have hfinj : Function.Injective L := by
    intro V W hVW
    apply lExpDeriv_inj S T x Z tau hdom hconj
    change L V = L W
    exact hVW
  have hfsurj : Function.Surjective L := by
    intro Y
    obtain ⟨V, hV⟩ := lExpDeriv_surj S T x Z tau hdom hconj Y
    refine ⟨V, ?_⟩
    exact hV
  let Df : E ≃L[Real] TangentSpace I (f z) :=
    ContinuousLinearEquiv.ofBijective L
      (LinearMap.ker_eq_bot.mpr hfinj)
      (LinearMap.range_eq_top.mpr hfsurj)
  have hfZ : MDifferentiableAt 𝓘(Real, E) I f z :=
    (hfU.contMDiffAt (hUopen.mem_nhds hZU)).mdifferentiableAt
      (by simp)
  let Dmodel : E ≃L[Real] E := Df.trans
    (tangentSpaceModelContinuousLinearEquiv (I := I) (f z))
  have hmodel : lConjModelMFDerivAt (I := I) f z = Dmodel := by
    ext V
    with_unfolding_all rfl
  have hchart := lConj_hasFDerivAt_chart (I := I) hfZ
  have hwritten : HasFDerivAt
      (writtenInExtChartAt 𝓘(Real, E) I z f)
      (lConjModelMFDerivAt (I := I) f z)
      (extChartAt 𝓘(Real, E) z z) := by
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_id, id_eq] using hchart
  have hfdinv : (fderiv Real
      (writtenInExtChartAt 𝓘(Real, E) I z f)
      (extChartAt 𝓘(Real, E) z z)).IsInvertible := by
    rw [hwritten.fderiv]
    exact ⟨Dmodel, hmodel⟩
  obtain ⟨Psi, hZPsi, hPsiU, hEqPsi⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn
      (I := 𝓘(Real, E)) (J := I) (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hUopen hZU (hfU.of_le (by exact_mod_cast le_top)) hfdinv
  have hfPsi : ContMDiffOn 𝓘(Real, E) I ∞ f Psi.source :=
    hfU.mono hPsiU
  have hinvPsi : ∀ W ∈ Psi.source,
      (fderiv Real
        (writtenInExtChartAt 𝓘(Real, E) I W f)
        (extChartAt 𝓘(Real, E) W W)).IsInvertible := by
    intro W hW
    have hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I 1 f W :=
      ⟨Psi, hW, hEqPsi⟩
    have hmfdinv : (mfderiv 𝓘(Real, E) I f W).IsInvertible :=
      ⟨hloc.mfderivToContinuousLinearEquiv one_ne_zero,
        hloc.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
    have hfW : MDifferentiableAt 𝓘(Real, E) I f W :=
      (hfPsi.contMDiffAt (Psi.open_source.mem_nhds hW)).mdifferentiableAt
        (by simp)
    exact written_fderiv_inv (I := I) hfW hmfdinv
  obtain ⟨Phi, hZPhi, _hPhiPsi, hEqPhi⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
      (I := 𝓘(Real, E)) (J := I) Psi.open_source hZPsi hfPsi hinvPsi
  exact ⟨Phi, hZPhi, hEqPhi⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
