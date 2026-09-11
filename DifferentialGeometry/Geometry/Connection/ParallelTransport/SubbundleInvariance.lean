import DifferentialGeometry.Geometry.Connection.SubbundleRestriction
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Hom

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff
namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

theorem homBundleCovariantDerivativeGen_subtypeL_restrict
    (cov : CovariantDerivative I F V)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    let _ := S.contMDiffVectorBundle
    DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M (Fin S.rank → ℝ)
      (fun x => S.fiber x) F V (cov.restrict S hS) cov
      (fun x => (S.fiber x).subtypeL) = 0 := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Fin S.rank → ℝ) (V := fun x => S.fiber x) (n := (⊤ : ℕ∞)) x u
  have h := DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_apply
    I M (Fin S.rank → ℝ) (fun x => S.fiber x) F V
    (cov.restrict S hS) cov
    (⟨fun y => (S.fiber y).subtypeL,
      ContMDiff.clm_bundle_of_map (φ := fun y => (S.fiber y).subtypeL) S.contMDiff_subtypeVal⟩ :
      Cₛ^∞⟮I; (Fin S.rank → ℝ) →L[ℝ] F,
        (fun x => S.fiber x →L[ℝ] V x)⟯)
    σ x v
  rw [hσ] at h
  have hr := cov.restrict_subtypeVal S hS σ x v
  change (S.fiber x).subtypeL (cov.restrict S hS σ x v) =
    cov (fun y => (S.fiber y).subtypeL (σ y)) x v at hr
  change _ = 0
  have h' :
      ((DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M (Fin S.rank → ℝ)
          (fun x => S.fiber x) F V (cov.restrict S hS) cov
          (fun y => (S.fiber y).subtypeL) x v) u) =
        cov (fun y => (S.fiber y).subtypeL (σ y)) x v -
          (S.fiber x).subtypeL (cov.restrict S hS σ x v) := by
    convert h using 1 <;> rfl
  rw [h', hr, sub_self]

end CovariantDerivative

namespace ContMDiffVectorSubbundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

private theorem parallel_section_endpoint_mem_iff
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V)
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {a b : ℝ} {Z : ∀ t : ℝ, V (γ t)} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b))
    (hZpar : ∀ t ∈ Icc a b, cov.derivAlongWithin γ Z (Icc a b) t = 0) :
    Z b ∈ S.fiber (γ b) ↔ Z a ∈ S.fiber (γ a) := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  have hinc := (ContMDiff.clm_bundle_of_map
    (φ := fun x => (S.fiber x).subtypeL) S.contMDiff_subtypeVal).mdifferentiable (by simp)
  have hincpar := CovariantDerivative.homBundleCovariantDerivativeGen_subtypeL_restrict cov S hS
  have hlocal {c d t₀ : ℝ} (ht₀ : t₀ ∈ Icc c d) (hsub : Icc c d ⊆ Icc a b)
      (e : Trivialization (Fin S.rank → ℝ)
        (TotalSpace.proj : TotalSpace (Fin S.rank → ℝ) (fun x => S.fiber x) → M))
      [MemTrivializationAtlas e]
      (he : ∀ t ∈ Icc c d, γ t ∈ e.baseSet)
      (hi : Z t₀ ∈ S.fiber (γ t₀)) : ∀ t ∈ Icc c d, Z t ∈ S.fiber (γ t) := by
    obtain ⟨W, hW₀, hW, hpW⟩ :=
      (cov.restrict S hS).exists_parallel_section_in_trivialization_on_Icc
        (cov.contMDiff_restrict S hS hcov) e ht₀ (hγ.mono hsub) he ⟨Z t₀, hi⟩
    have hγd := (hγ.mono hsub).mdifferentiableOn (by simp)
    have hWambient : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun t => (⟨γ t, (W t : V (γ t))⟩ : TotalSpace F V)) (Icc c d) := by
      intro t ht
      exact ((hinc (γ t)).comp_mdifferentiableWithinAt t (hγd t ht)).clm_bundle_apply (hW t ht)
    have hWpar : ∀ t ∈ Icc c d,
        cov.derivAlongWithin γ (fun t => (W t : V (γ t))) (Icc c d) t = 0 := by
      intro t ht
      change cov.derivAlongWithin γ (fun t => (S.fiber (γ t)).subtypeL (W t)) (Icc c d) t = 0
      rw [CovariantDerivative.derivAlongWithin_clm_section_apply_of_parallel
        (cov.restrict S hS) cov (fun x => (S.fiber x).subtypeL) (hinc (γ t))
        (congrFun hincpar (γ t)) (hγd t ht) (hW t ht), hpW t ht, map_zero]
    have hZsmall : ∀ t ∈ Icc c d, cov.derivAlongWithin γ Z (Icc c d) t = 0 :=
      fun t ht => cov.derivAlongWithin_eq_zero_mono (hZ t (hsub ht)) hsub (hZpar t (hsub ht))
    have heq := cov.parallel_section_eq_on_Icc hcov ht₀ (hγ.mono hsub)
      hWambient (hZ.mono hsub) hWpar hZsmall (congrArg Subtype.val hW₀)
    intro t ht
    rw [← heq t ht]
    exact (W t).property
  let cover : M → Set (Icc a b) := fun x =>
    (fun t : Icc a b => γ t) ⁻¹'
      (trivializationAt (Fin S.rank → ℝ) (fun x => S.fiber x) x).baseSet
  have hcoverOpen : ∀ x, IsOpen (cover x) := fun x =>
    (trivializationAt (Fin S.rank → ℝ) (fun x => S.fiber x) x).open_baseSet.preimage
      hγ.continuousOn.domRestrict
  have hcover : (univ : Set (Icc a b)) ⊆ ⋃ x, cover x := by
    intro t _
    exact mem_iUnion.mpr ⟨γ t,
      mem_baseSet_trivializationAt (Fin S.rank → ℝ) (fun x => S.fiber x) (γ t)⟩
  obtain ⟨τ, hτ₀, hmono, ⟨N, hN⟩, hτ⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hcoverOpen hcover
  have hstep (n : ℕ) :
      Z (τ (n + 1)) ∈ S.fiber (γ (τ (n + 1))) ↔ Z (τ n) ∈ S.fiber (γ (τ n)) := by
    obtain ⟨x, hx⟩ := hτ n
    let e := trivializationAt (Fin S.rank → ℝ) (fun x => S.fiber x) x
    have hsub : Icc (τ n : ℝ) (τ (n + 1) : ℝ) ⊆ Icc a b := fun t ht =>
      ⟨(τ n).property.1.trans ht.1, ht.2.trans (τ (n + 1)).property.2⟩
    have he : ∀ t ∈ Icc (τ n : ℝ) (τ (n + 1) : ℝ), γ t ∈ e.baseSet := by
      intro t ht
      exact hx (show (⟨t, hsub ht⟩ : Icc a b) ∈ Icc (τ n) (τ (n + 1)) from ht)
    have hle : (τ n : ℝ) ≤ τ (n + 1) := hmono (Nat.le_succ n)
    constructor
    · intro hi
      exact hlocal (right_mem_Icc.mpr hle) hsub e he hi (τ n) (left_mem_Icc.mpr hle)
    · intro hi
      exact hlocal (left_mem_Icc.mpr hle) hsub e he hi (τ (n + 1)) (right_mem_Icc.mpr hle)
  have hall (n : ℕ) :
      Z (τ n) ∈ S.fiber (γ (τ n)) ↔ Z (τ 0) ∈ S.fiber (γ (τ 0)) := by
    induction n with
    | zero => rfl
    | succ n ih => exact (hstep n).trans ih
  have hb := congrArg (fun t : ℝ => Z t ∈ S.fiber (γ t)) (hN N le_rfl)
  have ha := congrArg (fun t : ℝ => Z t ∈ S.fiber (γ t)) hτ₀
  exact (Iff.of_eq hb).symm.trans ((hall N).trans (Iff.of_eq ha))

theorem mem_of_parallel_section_of_covariantly_invariant
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V)
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {J : Set ℝ} {t₀ : ℝ} {Z : ∀ t : ℝ, V (γ t)}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ J)
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) J)
    (hZpar : ∀ t ∈ J, cov.derivAlongWithin γ Z J t = 0)
    (hinit : Z t₀ ∈ S.fiber (γ t₀)) : ∀ t ∈ J, Z t ∈ S.fiber (γ t) := by
  have hpair {c d : ℝ} (hcd : c ≤ d) (hc : c ∈ J) (hd : d ∈ J) :
      Z d ∈ S.fiber (γ d) ↔ Z c ∈ S.fiber (γ c) := by
    have hsub : Icc c d ⊆ J := hJ.out' hc hd
    exact S.parallel_section_endpoint_mem_iff cov hS hcov hcd (hγ.mono hsub)
      (hZ.mono hsub)
      (fun t ht => cov.derivAlongWithin_eq_zero_mono (hZ t (hsub ht)) hsub (hZpar t (hsub ht)))
  intro t ht
  rcases le_total t t₀ with htt₀ | ht₀t
  · exact (hpair htt₀ ht ht₀).mp hinit
  · exact (hpair ht₀t ht₀ ht).mpr hinit

theorem isParallelSet_of_covariantly_invariant
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (cov : CovariantDerivative I F V)
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞) :
    cov.IsParallelSet {p : TotalSpace F V | p.2 ∈ S.fiber p.1} := by
  refine ⟨?_⟩
  intro a b t₀ γ Z ht₀ hγ hZ hZpar hinit t ht
  exact S.mem_of_parallel_section_of_covariantly_invariant cov hS hcov ordConnected_Icc ht₀
    (hγ.of_le (by simp)) hZ hZpar hinit t ht

end ContMDiffVectorSubbundle
