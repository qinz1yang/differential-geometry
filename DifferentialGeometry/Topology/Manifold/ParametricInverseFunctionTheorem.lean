import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem
import DifferentialGeometry.Bundle.TangentSpace

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Coordinates

open Set
open scoped ContDiff Manifold Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private def modelMFDerivAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    {G₀ : Type*} [TopologicalSpace G₀]
    {J₀ : ModelWithCorners Real F G₀}
    {N₀ : Type*} [TopologicalSpace N₀] [ChartedSpace G₀ N₀]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    (f : N₀ → N) (u : N₀) : F →L[Real] F :=
  (tangentSpaceModelContinuousLinearEquiv (I := J) (f u)).toContinuousLinearMap.comp
    ((mfderiv J₀ J f u).comp
      (tangentSpaceModelContinuousLinearEquiv
        (I := J₀) u).symm.toContinuousLinearMap)

private theorem hasFDerivAt_writtenInExtChartAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    {G₀ : Type*} [TopologicalSpace G₀]
    {J₀ : ModelWithCorners Real F G₀} [J₀.Boundaryless]
    {N₀ : Type*} [TopologicalSpace N₀] [ChartedSpace G₀ N₀]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    {f : N₀ → N} {u : N₀}
    (hf : MDifferentiableAt J₀ J f u) :
    HasFDerivAt (writtenInExtChartAt J₀ J u f)
      (modelMFDerivAt (J₀ := J₀) (J := J) f u)
      (extChartAt J₀ u u) := by
  have h := hf.hasMFDerivAt.2
  rw [ModelWithCorners.Boundaryless.range_eq_univ] at h
  with_unfolding_all
    exact h.hasFDerivAt_of_univ.congr_fderiv (by ext v; rfl)

private theorem writtenInExtChartAt_fderiv_isInvertible
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    {G₀ : Type*} [TopologicalSpace G₀]
    {J₀ : ModelWithCorners Real F G₀} [J₀.Boundaryless]
    {N₀ : Type*} [TopologicalSpace N₀] [ChartedSpace G₀ N₀]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    {f : N₀ → N} {u : N₀}
    (hf : MDifferentiableAt J₀ J f u)
    (hinv : (modelMFDerivAt (J₀ := J₀) (J := J) f u).IsInvertible) :
    (fderiv Real (writtenInExtChartAt J₀ J u f)
      (extChartAt J₀ u u)).IsInvertible := by
  rw [(hasFDerivAt_writtenInExtChartAt (J₀ := J₀) (J := J) hf).fderiv]
  exact hinv

theorem isLocalDiffeomorphAt_slice_of_mfderiv_injective
    {alpha : E × Real → M} {V : Set E} {K : Set Real}
    {A0 : E} {b : Real}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V) (hbK : b ∈ K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B) :
    IsLocalDiffeomorphAt 𝓘(Real, E) I ∞
      (fun A : E ↦ alpha (A, b)) A0 := by
  let f : E → M := fun A ↦ alpha (A, b)
  have hpair : ContMDiff 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      (fun A : E ↦ (A, b)) :=
    contMDiff_id.prodMk contMDiff_const
  have hfV : ContMDiffOn 𝓘(Real, E) I ∞ f V := by
    apply halpha.comp hpair.contMDiffOn
    intro A hAV
    exact ⟨hAV, hbK⟩
  let A : E →L[Real] E :=
    modelMFDerivAt (J₀ := 𝓘(Real, E)) (J := I) f A0
  have hAinj : Function.Injective A := by
    intro v w hvw
    apply hinj
    with_unfolding_all
      exact (tangentSpaceModelContinuousLinearEquiv
        (I := I) (f A0)).injective hvw
  have hAsurj : Function.Surjective A :=
    LinearMap.surjective_of_injective hAinj
  let Df : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hAinj)
      (LinearMap.range_eq_top.mpr hAsurj)
  have hAinv : A.IsInvertible := ⟨Df, rfl⟩
  have hfA0 : MDifferentiableAt 𝓘(Real, E) I f A0 :=
    (hfV.contMDiffAt (hVopen.mem_nhds hA0V)).mdifferentiableAt (by simp)
  have hfdinv := writtenInExtChartAt_fderiv_isInvertible (J := I) hfA0 hAinv
  obtain ⟨Psi, hA0Psi, hPsiV, hEqPsi⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn
      (I := 𝓘(Real, E)) (J := I) (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hVopen hA0V (hfV.of_le (by exact_mod_cast le_top)) hfdinv
  have hfPsi : ContMDiffOn 𝓘(Real, E) I ∞ f Psi.source :=
    hfV.mono hPsiV
  have hinvPsi : ∀ A ∈ Psi.source,
      (fderiv Real
        (writtenInExtChartAt 𝓘(Real, E) I A f)
        (extChartAt 𝓘(Real, E) A A)).IsInvertible := by
    intro A hA
    have hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I 1 f A :=
      ⟨Psi, hA, hEqPsi⟩
    have hmfdinv : (mfderiv 𝓘(Real, E) I f A).IsInvertible :=
      ⟨hloc.mfderivToContinuousLinearEquiv one_ne_zero,
        hloc.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
    have hfA : MDifferentiableAt 𝓘(Real, E) I f A :=
      (hfPsi.contMDiffAt (Psi.open_source.mem_nhds hA)).mdifferentiableAt
        (by simp)
    have hmodel : (modelMFDerivAt
        (J₀ := 𝓘(Real, E)) (J := I) f A).IsInvertible := by
      simpa only [modelMFDerivAt,
        ContinuousLinearMap.isInvertible_comp_equiv,
        ContinuousLinearMap.isInvertible_equiv_comp] using hmfdinv
    exact writtenInExtChartAt_fderiv_isInvertible (J := I) hfA hmodel
  obtain ⟨Phi, hA0Phi, _hPhiPsi, hEqPhi⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
      (I := 𝓘(Real, E)) (J := I) Psi.open_source hA0Psi hfPsi hinvPsi
  exact ⟨Phi, hA0Phi, hEqPhi⟩

theorem isLocalDiffeomorphAt_parameter_graph_of_slice_mfderiv_injective
    {alpha : E × Real → M} {V : Set E} {K : Set Real}
    {A0 : E} {b : Real}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hbK : b ∈ K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B) :
    IsLocalDiffeomorphAt
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Real)) ∞
      (fun p : E × Real ↦ (alpha p, p.2)) (A0, b) := by
  let J := 𝓘(Real, E).prod 𝓘(Real, Real)
  let L := I.prod 𝓘(Real, Real)
  let f : E × Real → M := alpha
  let F : E × Real → M × Real := fun p ↦ (f p, p.2)
  let U : Set (E × Real) := V ×ˢ K
  let z : E := A0
  have hUopen : IsOpen U := hVopen.prod hKopen
  have hzu : (z, b) ∈ U := ⟨hA0V, hbK⟩
  have hfU : ContMDiffOn J I ∞ f U := by
    simpa only [J, f, U] using halpha
  have hFU : ContMDiffOn J L ∞ F U := by
    exact hfU.prodMk contMDiffOn_snd
  have hFdiff : MDifferentiableAt J L F (z, b) :=
    (hFU.contMDiffAt (hUopen.mem_nhds hzu)).mdifferentiableAt (by simp)
  have hfdiff : MDifferentiableAt J I f (z, b) :=
    (hfU.contMDiffAt (hUopen.mem_nhds hzu)).mdifferentiableAt (by simp)
  have hsnddiff : MDifferentiableAt J 𝓘(Real, Real)
      (@Prod.snd E Real) (z, b) :=
    (show ContMDiffAt J 𝓘(Real, Real) ∞
        (@Prod.snd E Real) (z, b) from
      contMDiffAt_snd).mdifferentiableAt (by simp)
  have hFderiv := mfderiv_prodMk hfdiff hsnddiff
  have hDFinj : Function.Injective (mfderiv J L F (z, b)) := by
    apply LinearMap.ker_eq_bot.mp
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hv
      have hpair :
          (mfderiv J I f (z, b) v,
            mfderiv J 𝓘(Real, Real) (@Prod.snd E Real)
              (z, b) v) = 0 := by
        have hv' : mfderiv J L (fun p : E × Real ↦ (f p, p.2))
            (z, b) v = 0 := by
          with_unfolding_all exact hv
        rw [hFderiv] at hv'
        exact hv'
      have hv2 : v.2 = 0 := by
        have h := congrArg Prod.snd hpair
        have hsndEq :
            mfderiv J 𝓘(Real, Real) (@Prod.snd E Real) (z, b) v =
              v.2 := by
          change (mfderiv
            (𝓘(Real, E).prod 𝓘(Real, Real)) 𝓘(Real, Real)
            (@Prod.snd E Real) (z, b)) v = v.2
          rw [mfderiv_snd]
          rfl
        rw [hsndEq] at h
        with_unfolding_all exact h
      have hfirst : mfderiv J I f (z, b) (v.1, 0) = 0 := by
        have h := congrArg Prod.fst hpair
        have hvEq : v = (v.1, 0) := Prod.ext rfl hv2
        rw [hvEq] at h
        simpa only [Prod.fst_zero] using h
      let g : E → E × Real := fun W ↦ (W, b)
      have hidC : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
          (fun W : E ↦ W) z := contMDiffAt_id
      have hconstC : ContMDiffAt 𝓘(Real, E) 𝓘(Real, Real) ∞
          (fun _ : E ↦ b) z := contMDiffAt_const
      have hidDiff : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E)
          (fun W : E ↦ W) z := hidC.mdifferentiableAt (by simp)
      have hconstDiff : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (fun _ : E ↦ b) z := hconstC.mdifferentiableAt (by simp)
      have hgdiff : MDifferentiableAt 𝓘(Real, E) J g z :=
        (hidC.prodMk hconstC).mdifferentiableAt (by simp)
      have hcomp := mfderiv_comp z hfdiff hgdiff
      have hgderiv : mfderiv 𝓘(Real, E) J g z v.1 = (v.1, 0) := by
        have hprod := mfderiv_prodMk hidDiff hconstDiff
        rw [show (fun W : E ↦ W) = id from rfl, mfderiv_id,
          mfderiv_const] at hprod
        change mfderiv 𝓘(Real, E) J (fun W : E ↦ (W, b)) z v.1 = _
        rw [hprod]
        rfl
      have hfix :
          mfderiv 𝓘(Real, E) I (fun W : E ↦ alpha (W, b)) z v.1 =
            mfderiv J I f (z, b) (v.1, 0) := by
        have hcompVal := congrArg (fun Q ↦ Q v.1) hcomp
        have hfun : f ∘ g = fun W : E ↦ alpha (W, b) := by
          funext W
          rfl
        have hgz : g z = (z, b) := rfl
        rw [hfun, hgz] at hcompVal
        change
          mfderiv 𝓘(Real, E) I (fun W : E ↦ alpha (W, b)) z v.1 =
            ((mfderiv J I f (z, b)).comp
              (mfderiv 𝓘(Real, E) J g z)) v.1 at hcompVal
        with_unfolding_all
          exact hcompVal.trans
            (congrArg (mfderiv J I f (z, b)) hgderiv)
      have hzero :
          mfderiv 𝓘(Real, E) I (fun W : E ↦ alpha (W, b)) z v.1 =
            0 := hfix.trans hfirst
      have hv1 : v.1 = 0 := by
        apply hinj
        exact hzero.trans (map_zero _).symm
      exact Prod.ext hv1 hv2
    · rintro rfl
      exact map_zero _
  let A := modelMFDerivAt (J₀ := J) (J := L) F (z, b)
  have hAinj : Function.Injective A := by
    intro v w hvw
    apply (tangentSpaceModelContinuousLinearEquiv (I := J) (z, b)).symm.injective
    apply hDFinj
    apply (tangentSpaceModelContinuousLinearEquiv (I := L) (F (z, b))).injective
    with_unfolding_all
      exact hvw
  have hAsurj : Function.Surjective A :=
    LinearMap.surjective_of_injective hAinj
  let DA := ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hAinj)
      (LinearMap.range_eq_top.mpr hAsurj)
  have hAinv : A.IsInvertible := ⟨DA, rfl⟩
  have hfdinv :=
    writtenInExtChartAt_fderiv_isInvertible (J := L) hFdiff hAinv
  obtain ⟨Psi, hzuPsi, hPsiU, hEqPsi⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn
      (I := J) (J := L) (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hUopen hzu (hFU.of_le (by exact_mod_cast le_top)) hfdinv
  have hFPsi : ContMDiffOn J L ∞ F Psi.source :=
    hFU.mono hPsiU
  have hinvPsi : ∀ p ∈ Psi.source,
      (fderiv Real (writtenInExtChartAt J L p F)
        (extChartAt J p p)).IsInvertible := by
    intro p hp
    have hloc : IsLocalDiffeomorphAt J L 1 F p :=
      ⟨Psi, hp, hEqPsi⟩
    have hmfdinv : (mfderiv J L F p).IsInvertible :=
      ⟨hloc.mfderivToContinuousLinearEquiv one_ne_zero,
        hloc.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
    have hFp : MDifferentiableAt J L F p :=
      (hFPsi.contMDiffAt (Psi.open_source.mem_nhds hp)).mdifferentiableAt
        (by simp)
    exact writtenInExtChartAt_fderiv_isInvertible (J := L) hFp hmfdinv
  obtain ⟨Phi, hzuPhi, _hPhiPsi, hEqPhi⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
      (I := J) (J := L) Psi.open_source hzuPsi hFPsi hinvPsi
  exact ⟨Phi, by simpa only [z] using hzuPhi,
    by simpa only [F, f, z] using hEqPhi⟩

theorem eventuallyEq_fst_localInverse_parameter_graph_slice
    {alpha : E × Real → M} {V : Set E} {K : Set Real}
    {A0 : E} {b : Real}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hbK : b ∈ K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B) :
    let htime :=
      isLocalDiffeomorphAt_parameter_graph_of_slice_mfderiv_injective
        hVopen hA0V hKopen hbK halpha hinj
    let hfixed :=
      isLocalDiffeomorphAt_slice_of_mfderiv_injective
        hVopen hA0V hbK halpha hinj
    (fun y : M ↦ (htime.localInverse (y, b)).1) =ᶠ[nhds (alpha (A0, b))]
      hfixed.localInverse := by
  let F : E × Real → M × Real := fun p ↦ (alpha p, p.2)
  let endMap : E → M := fun A ↦ alpha (A, b)
  let q0 : M × Real := (alpha (A0, b), b)
  let htime :=
    isLocalDiffeomorphAt_parameter_graph_of_slice_mfderiv_injective
      hVopen hA0V hKopen hbK halpha hinj
  let hfixed :=
    isLocalDiffeomorphAt_slice_of_mfderiv_injective
      hVopen hA0V hbK halpha hinj
  have htime0 : htime.localInverse q0 = (A0, b) := by
    simpa only [htime, q0, F] using
      htime.localInverse_left_inv htime.localInverse_mem_target
  have hslice : ContinuousAt (fun y : M ↦ (y, b)) (alpha (A0, b)) :=
    continuousAt_id.prodMk continuousAt_const
  have hinv : ContinuousAt
      (fun y : M ↦ htime.localInverse (y, b)) (alpha (A0, b)) := by
    have htimeCont : ContinuousAt htime.localInverse
        (alpha (A0, b), b) := by
      simpa only [q0] using htime.localInverse_contMDiffAt.continuousAt
    exact ContinuousAt.comp'
      (f := fun y : M ↦ (y, b)) htimeCont hslice
  have hfirst : ContinuousAt
      (fun y : M ↦ (htime.localInverse (y, b)).1) (alpha (A0, b)) :=
    continuousAt_fst.comp hinv
  have htimeSrc :
      {y : M | (y, b) ∈ htime.localInverse.source} ∈
        nhds (alpha (A0, b)) := by
    apply hslice.preimage_mem_nhds
    exact htime.localInverse_open_source.mem_nhds
      htime.localInverse_mem_source
  have hfixedTgt :
      {y : M | (htime.localInverse (y, b)).1 ∈
        hfixed.localInverse.target} ∈ nhds (alpha (A0, b)) := by
    apply hfirst.preimage_mem_nhds
    rw [htime0]
    exact hfixed.localInverse.open_target.mem_nhds
      hfixed.localInverse_mem_target
  filter_upwards [htimeSrc, hfixedTgt] with y hyTime hyTarget
  let A : E := (htime.localInverse (y, b)).1
  have hright : F (htime.localInverse (y, b)) = (y, b) := by
    simpa only [F] using htime.localInverse_right_inv hyTime
  have htimeEq : (htime.localInverse (y, b)).2 = b :=
    congrArg Prod.snd hright
  have hend : endMap A = y := by
    have hfirstEq := congrArg Prod.fst hright
    have hpairEq : htime.localInverse (y, b) = (A, b) :=
      Prod.ext rfl htimeEq
    rw [hpairEq] at hfirstEq
    simpa only [F, endMap] using hfirstEq
  change A = hfixed.localInverse y
  rw [← hend]
  exact (hfixed.localInverse_left_inv hyTarget).symm

end DifferentialGeometry.Coordinates
