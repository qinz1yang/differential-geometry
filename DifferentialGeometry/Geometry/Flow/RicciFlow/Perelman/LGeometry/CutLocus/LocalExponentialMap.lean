import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ConjugatePoint

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
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

private theorem cut_hasFDerivAt_written
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    {G₀ : Type*} [TopologicalSpace G₀]
    {J₀ : ModelWithCorners Real F G₀} [J₀.Boundaryless]
    {N₀ : Type*} [TopologicalSpace N₀] [ChartedSpace G₀ N₀]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    {f : N₀ → N} {u : N₀}
    (hf : MDifferentiableAt J₀ J f u) :
    HasFDerivAt (writtenInExtChartAt J₀ J u f)
      ((tangentSpaceModelContinuousLinearEquiv
          (I := J) (f u)).toContinuousLinearMap.comp
        ((mfderiv J₀ J f u).comp
          (tangentSpaceModelContinuousLinearEquiv
            (I := J₀) u).symm.toContinuousLinearMap))
      (extChartAt J₀ u u) := by
  have h := hf.hasMFDerivAt.2
  rw [ModelWithCorners.Boundaryless.range_eq_univ] at h
  with_unfolding_all
    exact h.hasFDerivAt_of_univ.congr_fderiv (by ext v; rfl)

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [IsManifold I ∞ M] in
private theorem written_prod_inv
    {f : E × Real → M × Real} {u : E × Real}
    (hf : MDifferentiableAt
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Real)) f u)
    (hinv : (mfderiv
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Real)) f u).IsInvertible) :
    (fderiv Real
      (writtenInExtChartAt
        (𝓘(Real, E).prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Real)) u f)
      (extChartAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) u u)).IsInvertible := by
  rw [(cut_hasFDerivAt_written
    (J₀ := 𝓘(Real, E).prod 𝓘(Real, Real))
    (J := I.prod 𝓘(Real, Real)) hf).fderiv]
  simpa only [ContinuousLinearMap.isInvertible_comp_equiv,
    ContinuousLinearMap.isInvertible_equiv_comp] using hinv

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExpTime_local
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    IsLocalDiffeomorphAt
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Real)) ∞
      (fun p : E × Real => (lExp S T x p.1 p.2, p.2)) (Z, tau) := by
  let J := 𝓘(Real, E).prod 𝓘(Real, Real)
  let K := I.prod 𝓘(Real, Real)
  let f : E × Real → M := fun p => lExp S T x p.1 p.2
  let F : E × Real → M × Real := fun p => (f p, p.2)
  let U : Set (E × Real) := lExpPosDom S T x
  let z : E := Z
  have hUopen : IsOpen U := lExpPosDom_open S hS T x
  have hZU : (z, tau) ∈ U := by
    with_unfolding_all exact hdom
  have hfU : ContMDiffOn J I ∞ f U := by
    simpa only [J, f, U] using lExp_smoothOn S hS T x
  have hFU : ContMDiffOn J K ∞ F U := by
    exact hfU.prodMk contMDiffOn_snd
  have hFdiff : MDifferentiableAt J K F (z, tau) :=
    (hFU.contMDiffAt (hUopen.mem_nhds hZU)).mdifferentiableAt (by simp)
  have hfdiff : MDifferentiableAt J I f (z, tau) :=
    (hfU.contMDiffAt (hUopen.mem_nhds hZU)).mdifferentiableAt (by simp)
  have hsnddiff : MDifferentiableAt J 𝓘(Real, Real)
      (@Prod.snd E Real) (z, tau) :=
    (show ContMDiffAt J 𝓘(Real, Real) ∞
        (@Prod.snd E Real) (z, tau) from
      contMDiffAt_snd).mdifferentiableAt (by simp)
  have hFderiv := mfderiv_prodMk hfdiff hsnddiff
  have hDFinj : Function.Injective (mfderiv J K F (z, tau)) := by
    apply LinearMap.ker_eq_bot.mp
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hv
      have hpair :
          (mfderiv J I f (z, tau) v,
            mfderiv J 𝓘(Real, Real) (@Prod.snd E Real)
              (z, tau) v) = 0 := by
        have hv' : mfderiv J K (fun p : E × Real => (f p, p.2))
            (z, tau) v = 0 := by
          with_unfolding_all exact hv
        rw [hFderiv] at hv'
        exact hv'
      have hv2 : v.2 = 0 := by
        have := congrArg Prod.snd hpair
        have hsndEq :
            mfderiv J 𝓘(Real, Real) (@Prod.snd E Real) (z, tau) v =
              v.2 := by
          change (mfderiv
            (𝓘(Real, E).prod 𝓘(Real, Real)) 𝓘(Real, Real)
            (@Prod.snd E Real) (z, tau)) v = v.2
          rw [mfderiv_snd]
          rfl
        rw [hsndEq] at this
        with_unfolding_all exact this
      have hfirst : mfderiv J I f (z, tau) (v.1, 0) = 0 := by
        have := congrArg Prod.fst hpair
        have hvEq : v = (v.1, 0) := Prod.ext rfl hv2
        rw [hvEq] at this
        simpa only [Prod.fst_zero] using this
      let g : E → E × Real := fun W => (W, tau)
      have hidC : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
          (fun W : E => W) z := contMDiffAt_id
      have hconstC : ContMDiffAt 𝓘(Real, E) 𝓘(Real, Real) ∞
          (fun _ : E => tau) z := contMDiffAt_const
      have hidDiff : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E)
          (fun W : E => W) z := hidC.mdifferentiableAt (by simp)
      have hconstDiff : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (fun _ : E => tau) z := hconstC.mdifferentiableAt (by simp)
      have hgdiff : MDifferentiableAt 𝓘(Real, E) J g z :=
        (hidC.prodMk hconstC).mdifferentiableAt (by simp)
      have hcomp := mfderiv_comp z hfdiff hgdiff
      have hgderiv : mfderiv 𝓘(Real, E) J g z v.1 = (v.1, 0) := by
        have hprod := mfderiv_prodMk hidDiff hconstDiff
        rw [show (fun W : E => W) = id from rfl, mfderiv_id,
          mfderiv_const] at hprod
        change mfderiv 𝓘(Real, E) J (fun W : E => (W, tau)) z v.1 = _
        rw [hprod]
        rfl
      have hfix :
          mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) z v.1 =
            mfderiv J I f (z, tau) (v.1, 0) := by
        have hcompVal := congrArg (fun L => L v.1) hcomp
        have hfun : f ∘ g = fun W : E => lExp S T x W tau := by
          funext W
          rfl
        have hgz : g z = (z, tau) := rfl
        rw [hfun, hgz] at hcompVal
        change
          mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) z v.1 =
            ((mfderiv J I f (z, tau)).comp
              (mfderiv 𝓘(Real, E) J g z)) v.1 at hcompVal
        with_unfolding_all
          change mfderiv 𝓘(Real, E) I
              (fun W : E => lExp S T x W tau) z v.1 =
            mfderiv J I f (z, tau)
              (mfderiv 𝓘(Real, E) J g z v.1) at hcompVal
        rw [hgderiv] at hcompVal
        exact hcompVal
      have hzero :
          mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) z v.1 =
            0 := hfix.trans hfirst
      have hv1 : v.1 = 0 := by
        apply lExpDeriv_inj S T x z tau (by simpa only [z] using hdom)
          (by simpa only [z] using hconj)
        exact hzero.trans (map_zero _).symm
      exact Prod.ext hv1 hv2
    · rintro rfl
      exact map_zero _
  have hDFsurj : Function.Surjective (mfderiv J K F (z, tau)) :=
    LinearMap.surjective_of_injective hDFinj
  let DF : (E × Real) ≃L[Real] (E × Real) :=
    ContinuousLinearEquiv.ofBijective (mfderiv J K F (z, tau))
      (LinearMap.ker_eq_bot.mpr hDFinj)
      (LinearMap.range_eq_top.mpr hDFsurj)
  have hDinv : (mfderiv J K F (z, tau)).IsInvertible := by
    refine ⟨DF, ?_⟩
    rfl
  have hfdinv := written_prod_inv hFdiff hDinv
  obtain ⟨Psi, hZPsi, hPsiU, hEqPsi⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn
      (I := J) (J := K) (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hUopen hZU (hFU.of_le (by exact_mod_cast le_top)) hfdinv
  have hFPsi : ContMDiffOn J K ∞ F Psi.source :=
    hFU.mono hPsiU
  have hinvPsi : ∀ p ∈ Psi.source,
      (fderiv Real (writtenInExtChartAt J K p F)
        (extChartAt J p p)).IsInvertible := by
    intro p hp
    have hloc : IsLocalDiffeomorphAt J K 1 F p :=
      ⟨Psi, hp, hEqPsi⟩
    have hmfdinv : (mfderiv J K F p).IsInvertible :=
      ⟨hloc.mfderivToContinuousLinearEquiv one_ne_zero,
        hloc.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
    have hFp : MDifferentiableAt J K F p :=
      (hFPsi.contMDiffAt (Psi.open_source.mem_nhds hp)).mdifferentiableAt
        (by simp)
    exact written_prod_inv hFp hmfdinv
  obtain ⟨Phi, hZPhi, _hPhiPsi, hEqPhi⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
      (I := J) (J := K) Psi.open_source hZPsi hFPsi hinvPsi
  exact ⟨Phi, by simpa only [z] using hZPhi,
    by simpa only [F, f, z] using hEqPhi⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
