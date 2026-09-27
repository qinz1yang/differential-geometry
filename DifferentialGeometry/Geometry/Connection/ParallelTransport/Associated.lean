import DifferentialGeometry.Geometry.Connection.Associated
import DifferentialGeometry.Geometry.Connection.ParallelTransport.ConvexFamily
import DifferentialGeometry.Geometry.LieGroup.Representation.InvariantSet
import DifferentialGeometry.Topology.Order.Interval
import DifferentialGeometry.Topology.ConnectedCompactNeighborhood

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B] [IsManifold I 1 B]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private theorem continuousOn_apply_mfderiv_mfderivWithin
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) {Ω : Set B} (hΩ : IsOpen Ω)
    {γ : ℝ → B} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ J) (hγΩ : MapsTo γ J Ω)
    {s : B → P} (hs : ContMDiffOn I IP 1 s Ω)
    (form : ∀ p : P, TangentSpace IP p →L[ℝ] Z)
    (hform : Continuous (fun X : TangentBundle IP P => form X.proj X.snd)) :
    ContinuousOn (fun t => form (s (γ t))
      (mfderiv I IP s (γ t)
        (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1)))) J := by
  let v : ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ := fun t =>
    ⟨t, (NormedSpace.fromTangentSpace t).symm 1⟩
  have hv : Continuous v := by
    exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hvel : ContinuousOn (fun t => tangentMapWithin 𝓘(ℝ, ℝ) I γ J (v t)) J :=
    (hγ.continuousOn_tangentMapWithin le_rfl hJ.uniqueMDiffOn).comp hv.continuousOn
      (fun _ ht => ht)
  have hsvel := (hs.continuousOn_tangentMapWithin le_rfl hΩ.uniqueMDiffOn).comp
    hvel (fun t ht => hγΩ ht)
  have hc := hform.comp_continuousOn hsvel
  apply hc.congr
  intro t ht
  change form (s (γ t)) (mfderiv I IP s (γ t) _) =
    form (s (γ t)) (mfderivWithin I IP s Ω (γ t) _)
  rw [mfderivWithin_of_mem_nhds (hΩ.mem_nhds (hγΩ ht))]
  rfl

end

namespace ContRepresentation

variable {G B W : Type*} [Group G]
  [TopologicalSpace G] [TopologicalSpace B] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [ChartedSpace H B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners ℝ EP HP)
  [ChartedSpace HP (TotalSpace G P)]

theorem associatedCovariantDerivativeOfLocalSections_connectionForm [FiniteDimensional ℝ W]
    [ContMDiffMul IG 1 G]
    (ρ : ContRepresentation ℝ G W)
    (hρ : ContMDiff IG 𝓘(ℝ, W →L[ℝ] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[ℝ] GroupLieAlgebra IG G)
    (hform : ∀ (g : G) (p : TotalSpace G P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv IG IG (fun h => g * h * g⁻¹) 1 (form p X))
    (hnorm : ∀ (p : TotalSpace G P) (U : GroupLieAlgebra IG G),
      form p (mfderiv IG IP (fun g : G => g • p) 1 U) = U)
    (e : Trivialization G (π G P)) (he : e ∈ A) {x : B} (hx : x ∈ e.baseSet)
    (X : TangentSpace I x) (w : W) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
    let := hA e he
    let eA : Trivialization W (π W (fun y => P y →ₑ[ρ.toRepresentation] W)) :=
      ρ.toRepresentation.associatedTrivialization
      ((hρ.continuous.comp continuous_fst).clm_apply continuous_snd) e
    let _ : MemTrivializationAtlas eA := ⟨e, he, rfl⟩
    (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form).connectionForm
      eA x X w =
        -mvfderiv IG (fun g => ρ g) 1
          (form ⟨x, e.principalSection x⟩
            (mfderiv I IP (fun y => (⟨y, e.principalSection y⟩ : TotalSpace G P)) x X)) w := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
  let := hA e he
  let eA : Trivialization W (π W (fun y => P y →ₑ[ρ.toRepresentation] W)) :=
      ρ.toRepresentation.associatedTrivialization
    ((hρ.continuous.comp continuous_fst).clm_apply continuous_snd) e
  let _ : MemTrivializationAtlas eA := ⟨e, he, rfl⟩
  let cov := ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form
  let σ : ∀ y, P y →ₑ[ρ.toRepresentation] W := fun y => eA.symmL ℝ y w
  have hxA : x ∈ eA.baseSet := hx
  have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, W))
      (fun y => (⟨y, σ y⟩ : TotalSpace W (fun z => P z →ₑ[ρ.toRepresentation] W))) x := by
    rw [eA.mdifferentiableAt_section_iff I σ hxA]
    apply (mdifferentiableAt_const (c := w)).congr_of_eventuallyEq
    filter_upwards [eA.open_baseSet.mem_nhds hxA] with y hy
    rw [← eA.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact eA.continuousLinearMapAt_symmL hy w
  have hcoords : (fun y => σ y (e.principalSection y)) =ᶠ[𝓝 x] fun _ => w := by
    filter_upwards [eA.open_baseSet.mem_nhds hxA] with y hy
    change (eA ⟨y, σ y⟩).2 = w
    rw [← eA.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact eA.continuousLinearMapAt_symmL hy w
  have hd : mvfderiv I (fun y => σ y (e.principalSection y)) x = 0 := by
    have hzero := (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, W)) (c := w) (x := x)).congr_of_eventuallyEq hcoords
    rw [mvfderiv, hzero.mfderiv]
    ext v
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (σ x (e.principalSection x))).map_zero
  have h := ρ.associatedCovariantDerivativeOfLocalSections_eval_eq
    I IG IP hρ A hA e₀ he₀ hx₀ hP form hform hnorm σ e he hx X hσ
  have hvalue : σ x (e.principalSection x) = w := hcoords.self_of_nhds
  rw [hd, zero_apply, zero_sub, hvalue] at h
  change cov.connectionForm eA x X w = _
  rw [cov.connectionForm_apply eA hxA X w, eA.continuousLinearMapAt_apply_of_mem ℝ hxA]
  exact h

theorem hasDerivWithinAt_of_associatedCovariantDerivativeOfLocalSections_eq_zero [FiniteDimensional ℝ W]
    [ContMDiffMul IG 1 G]
    (ρ : ContRepresentation ℝ G W)
    (hρ : ContMDiff IG 𝓘(ℝ, W →L[ℝ] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[ℝ] GroupLieAlgebra IG G)
    (hform : ∀ (g : G) (p : TotalSpace G P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv IG IG (fun h => g * h * g⁻¹) 1 (form p X))
    (hnorm : ∀ (p : TotalSpace G P) (U : GroupLieAlgebra IG G),
      form p (mfderiv IG IP (fun g : G => g • p) 1 U) = U)
    (e : Trivialization G (π G P)) (he : e ∈ A)
    {γ : ℝ → B} {Z : ∀ t : ℝ, P (γ t) →ₑ[ρ.toRepresentation] W}
    {J : Set ℝ} {t : ℝ} (ht : t ∈ J) (hJ : MapsTo γ J e.baseSet) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, W))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace W (fun y => P y →ₑ[ρ.toRepresentation] W))) J t →
    (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form).derivAlongWithin γ Z J t = 0 →
    HasDerivWithinAt (fun s => Z s (e.principalSection (γ s)))
      (mvfderiv IG (fun g => ρ g) 1
        (form ⟨γ t, e.principalSection (γ t)⟩
          (mfderiv I IP (fun y => (⟨y, e.principalSection y⟩ : TotalSpace G P)) (γ t)
            (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1))))
        (Z t (e.principalSection (γ t)))) J t := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
  let := hA e he
  let eA : Trivialization W (π W (fun y => P y →ₑ[ρ.toRepresentation] W)) :=
      ρ.toRepresentation.associatedTrivialization
    ((hρ.continuous.comp continuous_fst).clm_apply continuous_snd) e
  let _ : MemTrivializationAtlas eA := ⟨e, he, rfl⟩
  dsimp only
  intro hZ hpar
  let cov := ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form
  have hcoords (s : ℝ) (hs : s ∈ J) :
      eA.continuousLinearMapAt ℝ (γ s) (Z s) = Z s (e.principalSection (γ s)) :=
    eA.continuousLinearMapAt_apply_of_mem ℝ (hJ hs) (Z s)
  have h := cov.hasDerivWithinAt_coord eA (hJ ht) hZ
  rw [hpar, map_zero, zero_sub,
    ρ.associatedCovariantDerivativeOfLocalSections_connectionForm
      I IG IP hρ A hA e₀ he₀ hx₀ hP form hform hnorm e he (hJ ht),
    neg_neg, hcoords t ht] at h
  exact h.congr (fun s hs => (hcoords s hs).symm) (hcoords t ht).symm

private theorem mem_associatedSet_iff_of_parallel_within_chart [FiniteDimensional ℝ W] [IG.Boundaryless]
    [ContMDiffMul IG 1 G]
    (ρ : ContRepresentation ℝ G W)
    (hρ : ContMDiff IG 𝓘(ℝ, W →L[ℝ] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[ℝ] GroupLieAlgebra IG G)
    (hform : ∀ (g : G) (p : TotalSpace G P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv IG IG (fun h => g * h * g⁻¹) 1 (form p X))
    (hnorm : ∀ (p : TotalSpace G P) (U : GroupLieAlgebra IG G),
      form p (mfderiv IG IP (fun g : G => g • p) 1 U) = U)
    (e : Trivialization G (π G P)) (he : e ∈ A)
    {C : Set W} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hC : ∀ g, MapsTo (ρ g) C C)
    {γ : ℝ → B} {Z : ∀ t : ℝ, P (γ t) →ₑ[ρ.toRepresentation] W}
    {a b t₀ t : ℝ} (ht₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hJ : MapsTo γ (Icc a b) e.baseSet)
    (hcoeff : ContinuousOn (fun s =>
      form ⟨γ s, e.principalSection (γ s)⟩
        (mfderiv I IP (fun y => (⟨y, e.principalSection y⟩ : TotalSpace G P)) (γ s)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) s ((NormedSpace.fromTangentSpace s).symm 1))))
      (Icc a b)) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
    MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, W))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace W (fun y => P y →ₑ[ρ.toRepresentation] W))) (Icc a b) →
    (∀ s ∈ Icc a b,
      (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form).derivAlongWithin γ Z (Icc a b) s = 0) →
    (Z t ∈ ρ.toRepresentation.associatedSet (P (γ t)) C ↔
      Z t₀ ∈ ρ.toRepresentation.associatedSet (P (γ t₀)) C) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
  dsimp only
  intro hZ hpar
  rw [ρ.toRepresentation.mem_associatedSet_iff hC (e.principalSection (γ t)),
    ρ.toRepresentation.mem_associatedSet_iff hC (e.principalSection (γ t₀))]
  apply ρ.mem_iff_of_isIntegralCurveOn_mvfderiv_of_finiteDimensional
    ((hρ 1).mdifferentiableAt (by simp)) hclosed hconvex hC ht₀ ht _ hcoeff
  intro s hs
  exact ρ.hasDerivWithinAt_of_associatedCovariantDerivativeOfLocalSections_eq_zero
    I IG IP hρ A hA e₀ he₀ hx₀ hP form hform hnorm e he hs hJ (hZ s hs) (hpar s hs)

theorem mem_associatedSet_iff_of_parallel_in_chart [FiniteDimensional ℝ W] [IG.Boundaryless]
    [IsManifold I 1 B] [IsManifold IP 1 (TotalSpace G P)]
    [ContMDiffMul IG 1 G]
    (ρ : ContRepresentation ℝ G W)
    (hρ : ContMDiff IG 𝓘(ℝ, W →L[ℝ] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[ℝ] GroupLieAlgebra IG G)
    (hform : ∀ (g : G) (p : TotalSpace G P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv IG IG (fun h => g * h * g⁻¹) 1 (form p X))
    (hnorm : ∀ (p : TotalSpace G P) (U : GroupLieAlgebra IG G),
      form p (mfderiv IG IP (fun g : G => g • p) 1 U) = U)
    (e : Trivialization G (π G P)) (he : e ∈ A)
    {C : Set W} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hC : ∀ g, MapsTo (ρ g) C C)
    {γ : ℝ → B} {Z : ∀ t : ℝ, P (γ t) →ₑ[ρ.toRepresentation] W}
    {a b t₀ t : ℝ} (ht₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hJ : MapsTo γ (Icc a b) e.baseSet)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hforms : Continuous (fun X : TangentBundle IP (TotalSpace G P) => form X.proj X.snd)) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
    MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, W))
      (fun s => (⟨γ s, Z s⟩ : TotalSpace W (fun y => P y →ₑ[ρ.toRepresentation] W))) (Icc a b) →
    (∀ s ∈ Icc a b,
      (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form).derivAlongWithin γ Z (Icc a b) s = 0) →
    (Z t ∈ ρ.toRepresentation.associatedSet (P (γ t)) C ↔
      Z t₀ ∈ ρ.toRepresentation.associatedSet (P (γ t₀)) C) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
  dsimp only
  intro hZ hpar
  by_cases hab : a < b
  · let := hA e he
    have hs := e.contMDiffOn_principalSection (hP e he).2
    have hc := continuousOn_apply_mfderiv_mfderivWithin (Z := EG)
      (uniqueDiffOn_Icc hab) e.open_baseSet hγ hJ hs form hforms
    exact ρ.mem_associatedSet_iff_of_parallel_within_chart
      I IG IP hρ A hA e₀ he₀ hx₀ hP form hform hnorm e he
      hclosed hconvex hC ht₀ ht hJ hc hZ hpar
  · have htt₀ : t = t₀ := by linarith [ht.1, ht.2, ht₀.1, ht₀.2]
    subst t
    rfl

private theorem isParallelSet_associatedSet_of_localSections [FiniteDimensional ℝ W] [IG.Boundaryless]
    [IsManifold I 1 B] [IsManifold IP 1 (TotalSpace G P)]
    [ContMDiffMul IG 1 G]
    (ρ : ContRepresentation ℝ G W)
    (hρ : ContMDiff IG 𝓘(ℝ, W →L[ℝ] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[ℝ] GroupLieAlgebra IG G)
    (hform : ∀ (g : G) (p : TotalSpace G P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv IG IG (fun h => g * h * g⁻¹) 1 (form p X))
    (hnorm : ∀ (p : TotalSpace G P) (U : GroupLieAlgebra IG G),
      form p (mfderiv IG IP (fun g : G => g • p) 1 U) = U)
    (hforms : Continuous (fun X : TangentBundle IP (TotalSpace G P) => form X.proj X.snd))
    {C : Set W} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hC : ∀ g, MapsTo (ρ g) C C) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
    (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form).IsParallelSet
      {v : TotalSpace W (fun y => P y →ₑ[ρ.toRepresentation] W) |
        v.snd ∈ ρ.toRepresentation.associatedSet (P v.proj) C} := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
  let cov := ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form
  constructor
  intro a b t₀ γ Z ht₀ hγ hZ hpar hinit t ht
  change Z t₀ ∈ ρ.toRepresentation.associatedSet (P (γ t₀)) C at hinit
  change Z t ∈ ρ.toRepresentation.associatedSet (P (γ t)) C
  let Q : ℝ → Prop := fun s => Z s ∈ ρ.toRepresentation.associatedSet (P (γ s)) C
  have hloc : ∀ s ∈ Icc a b, ∀ᶠ u in 𝓝[Icc a b] s, Q u ↔ Q s := by
    intro s hs
    let e := e₀ (γ s)
    have he : e ∈ A := he₀ (γ s)
    have hse : γ s ∈ e.baseSet := hx₀ (γ s)
    have hn : γ ⁻¹' e.baseSet ∈ 𝓝[Icc a b] s :=
      (hγ.continuousOn s hs).preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hse)
    obtain ⟨c, d, hs', hnhds, hsub⟩ :=
      ordConnected_Icc.exists_Icc_mem_subset_of_mem_nhdsWithin hs hn
    have hsub' : Icc c d ⊆ Icc a b := fun _ hu => (hsub hu).1
    have hchart : MapsTo γ (Icc c d) e.baseSet := fun _ hu => (hsub hu).2
    have hpar' : ∀ u ∈ Icc c d, cov.derivAlongWithin γ Z (Icc c d) u = 0 := by
      intro u hu
      exact cov.derivAlongWithin_eq_zero_mono (hZ u (hsub' hu)) hsub' (hpar u (hsub' hu))
    filter_upwards [hnhds] with u hu
    exact ρ.mem_associatedSet_iff_of_parallel_in_chart I IG IP hρ A hA e₀ he₀ hx₀ hP
      form hform hnorm e he hclosed hconvex hC hs' hu hchart
      ((hγ.of_le (by simp)).mono hsub') hforms (hZ.mono hsub') hpar'
  exact (isPreconnected_Icc.iff_of_eventually_iff Q hloc ht ht₀).mpr hinit

theorem isParallelSet_associatedSet [FiniteDimensional ℝ W] [IG.Boundaryless]
    [IsManifold I 1 B] [IsManifold IP 1 (TotalSpace G P)]
    [ContMDiffMul IG 1 G]
    (ρ : ContRepresentation ℝ G W)
    (hρ : ContMDiff IG 𝓘(ℝ, W →L[ℝ] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    {n : ℕ∞ω} (form : PrincipalConnectionForm IG G IP P n)
    {C : Set W} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hC : ∀ g, MapsTo (ρ g) C C) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A hA e₀ he₀ hx₀ hP
    (ρ.associatedCovariantDerivative I IG IP hρ.continuous A hA e₀ he₀ hx₀ form).IsParallelSet
      {v : TotalSpace W (fun y => P y →ₑ[ρ.toRepresentation] W) |
        v.snd ∈ ρ.toRepresentation.associatedSet (P v.proj) C} := by
  exact ρ.isParallelSet_associatedSet_of_localSections I IG IP hρ A hA e₀ he₀ hx₀ hP
    form.toFun form.apply_smul form.apply_fundamental form.contMDiff.continuous hclosed hconvex hC


theorem isParallelClosedConvexFamily_associatedSet {Q : Type*} [IG.Boundaryless]
    [IsManifold I 1 B] [IsManifold IP 1 (TotalSpace G P)] [ContMDiffMul IG 1 G]
    [FiniteDimensional ℝ W]
    (ρ : ContRepresentation ℝ G W)
    (hρ : ContMDiff IG 𝓘(ℝ, W →L[ℝ] W) 1 (fun g => ρ g))
    (A₀ : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A₀, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A₀)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A₀, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    {n : ℕ∞ω} (form : Q → PrincipalConnectionForm IG G IP P n)
    {C : Set W} (hclosed : IsClosed C) (hnonempty : C.Nonempty)
    (hconvex : Convex ℝ C) (hC : ∀ g, MapsTo (ρ g) C C) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A₀ hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A₀ hA e₀ he₀ hx₀
    let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A₀ hA e₀ he₀ hx₀ hP
    CovariantDerivative.IsParallelClosedConvexFamily
      (fun q => ρ.associatedCovariantDerivative I IG IP hρ.continuous A₀ hA e₀ he₀ hx₀ (form q))
      {v : TotalSpace W (fun y => P y →ₑ[ρ.toRepresentation] W) |
        v.snd ∈ ρ.toRepresentation.associatedSet (P v.proj) C} := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A₀ hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A₀ hA e₀ he₀ hx₀
  let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG 1 IP hρ A₀ hA e₀ he₀ hx₀ hP
  refine ⟨ρ.toRepresentation.isClosed_totalSpace_associatedSet
    ((hρ.continuous.comp continuous_fst).clm_apply continuous_snd) hclosed hC, ?_, ?_, ?_⟩
  · intro x
    exact (ρ.toRepresentation.associatedSet_nonempty_iff hC).mpr hnonempty
  · intro x
    exact ρ.toRepresentation.convex_associatedSet hconvex
  · intro q
    exact ρ.isParallelSet_associatedSet I IG IP hρ A₀ hA e₀ he₀ hx₀ hP
      (form q) hclosed hconvex hC

end ContRepresentation
