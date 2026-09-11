import DifferentialGeometry.Geometry.Connection.AlongCurveAlternating
import DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Endpoint
import DifferentialGeometry.Geometry.Connection.ParallelTransport.SubbundleInvariance

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [I.Boundaryless]


theorem parallelTransportSectionOnIcc_derivAlongWithin
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) {J : Set ℝ}
    (hJ : UniqueDiffWithinAt ℝ J t) :
    (LeviCivita g).derivAlongWithin γ
      (parallelTransportSectionOnIcc g γ hγ hL v₀) J t = 0 := by
  rw [derivAlongWithin_leviCivita_eq_covDerivAlong_of_mdifferentiableAt g γ _ hJ
    (parallelTransportSectionOnIcc_mdifferentiableAt g γ hγ hL v₀ ht)
    BoundarylessManifold.isInteriorPoint]
  exact parallelTransportSectionOnIcc_covDerivAlong g γ hγ hL v₀ ht


private instance tangentT2Space (x : M) : T2Space (TangentSpace I x) :=
  FiberBundle.t2Space E (TangentSpace I) x

private instance tangentFiberBundle : FiberBundle E (TangentSpace I : M → Type _) :=
  TangentSpace.fiberBundle (I := I) (M := M)

private instance tangentVectorBundle : VectorBundle ℝ E (TangentSpace I : M → Type _) :=
  TangentSpace.vectorBundle (I := I) (M := M)

private instance tangentSmoothVectorBundle :
    ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := by
  have h : IsManifold I ∞ M := inferInstance
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle (I := I) (M := M)

private instance alternatingModelFiniteDimensional (k : ℕ) :
    FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ E)).finiteDimensional_of_finite

private def parallelTransportFamilyOnIcc
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    (L : ℝ) (t : ℝ) :
    TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t) := by
  classical
  exact if ht : t ∈ Icc (0 : ℝ) L then
    if ht₀ : t = 0 then
      ht₀ ▸ ContinuousLinearEquiv.refl ℝ (TangentSpace I (γ 0))
    else (parallelTransportLinearEquivOnIcc g γ hγ
      (lt_of_le_of_ne ht.1 (Ne.symm ht₀))).toContinuousLinearEquiv
  else
    (VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I) (γ 0)).trans
      (VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I) (γ t)).symm

omit [T2Space M] in
private theorem parallelTransportFamilyOnIcc_apply
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L)
    (v : TangentSpace I (γ 0)) :
    parallelTransportFamilyOnIcc g γ hγ L t v =
      parallelTransportSectionOnIcc g γ hγ hL v t := by
  classical
  by_cases ht₀ : t = 0
  · subst t
    simp [parallelTransportFamilyOnIcc, hL.le]
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht₀)
    simp only [parallelTransportFamilyOnIcc, dif_pos ht, dif_neg ht₀]
    exact parallelTransportSectionOnIcc_eq_of_mem g γ hγ htpos hL v
      (right_mem_Icc.mpr htpos.le) ht

omit [T2Space M] in
private theorem parallelTransportFamilyOnIcc_mdifferentiable
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v : TangentSpace I (γ 0)) :
    MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
      (fun s => (⟨γ s, parallelTransportFamilyOnIcc g γ hγ L s v⟩ : TangentBundle I M))
      (Icc (0 : ℝ) L) := by
  have hs : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
      (fun s => (⟨γ s, parallelTransportSectionOnIcc g γ hγ hL v s⟩ : TangentBundle I M))
      (Icc (0 : ℝ) L) :=
    fun t ht => (parallelTransportSectionOnIcc_mdifferentiableAt g γ hγ hL v ht).mdifferentiableWithinAt
  apply hs.congr
  intro t ht
  congr 1
  exact parallelTransportFamilyOnIcc_apply g γ hγ hL ht v

private theorem parallelTransportFamilyOnIcc_derivAlongWithin
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) L) :
    (LeviCivita g).derivAlongWithin γ
      (fun s => parallelTransportFamilyOnIcc g γ hγ L s v) (Icc (0 : ℝ) L) t = 0 := by
  rw [(LeviCivita g).derivAlongWithin_congr
    (fun s hs => parallelTransportFamilyOnIcc_apply g γ hγ hL hs v)
    (parallelTransportFamilyOnIcc_apply g γ hγ hL ht v)]
  exact parallelTransportSectionOnIcc_derivAlongWithin g γ hγ hL v ht
    (uniqueDiffOn_Icc hL t ht)


theorem exists_parallel_alternating_transport_on_Icc
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    (k : ℕ) {L : ℝ} (hL : 0 < L)
    (a₀ : TangentSpace I (γ 0) [⋀^Fin k]→L[ℝ] ℝ) :
    ∃ A : ∀ t, TangentSpace I (γ t) [⋀^Fin k]→L[ℝ] ℝ,
      A 0 = a₀ ∧
      MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ))
        (fun t => (⟨γ t, A t⟩ : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace I : M → Type _) ℝ
            (Bundle.Trivial M ℝ)))) (Icc (0 : ℝ) L) ∧
      (∀ t ∈ Icc (0 : ℝ) L,
        (CovariantDerivative.alternating (M := M) (F := E) (V := TangentSpace I) (LeviCivita g) k).derivAlongWithin γ A (Icc (0 : ℝ) L) t = 0) ∧
      A L = (parallelTransportLinearEquivOnIcc g γ hγ hL).toContinuousLinearEquiv.continuousAlternatingMapCongrLeft a₀ := by
  let T := parallelTransportFamilyOnIcc g γ hγ L
  refine ⟨fun t => (T t).continuousAlternatingMapCongrLeft a₀, ?_, ?_, ?_, ?_⟩
  · have hT₀ : T 0 = ContinuousLinearEquiv.refl ℝ (TangentSpace I (γ 0)) := by
      ext v
      exact (parallelTransportFamilyOnIcc_apply g γ hγ hL (left_mem_Icc.mpr hL.le) v).trans
        (parallelTransportSectionOnIcc_initial g γ hγ hL v)
    change (T 0).continuousAlternatingMapCongrLeft a₀ = a₀
    rw [hT₀]
    ext v
    rfl
  · intro t ht
    exact mdifferentiableWithinAt_alternating_congrLeft_of_pointwise k γ T a₀
      (fun v => parallelTransportFamilyOnIcc_mdifferentiable g γ hγ hL v t ht)
  · intro t ht
    exact CovariantDerivative.derivAlongWithin_alternating_congrLeft_eq_zero
      (LeviCivita g) k γ T a₀
      (fun v => parallelTransportFamilyOnIcc_mdifferentiable g γ hγ hL v t ht)
      (fun v => parallelTransportFamilyOnIcc_derivAlongWithin g γ hγ hL v ht)
  · have hTL : T L = (parallelTransportLinearEquivOnIcc g γ hγ hL).toContinuousLinearEquiv := by
      ext v
      exact parallelTransportFamilyOnIcc_apply g γ hγ hL (right_mem_Icc.mpr hL.le) v
    change (T L).continuousAlternatingMapCongrLeft a₀ = _
    rw [hTL]


theorem parallel_alternating_section_endpoint_eq
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    (k : ℕ) {L : ℝ} (hL : 0 < L)
    (A : ∀ t, TangentSpace I (γ t) [⋀^Fin k]→L[ℝ] ℝ)
    (hA : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ))
      (fun t => (⟨γ t, A t⟩ : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace I : M → Type _) ℝ
          (Bundle.Trivial M ℝ)))) (Icc (0 : ℝ) L))
    (hpar : ∀ t ∈ Icc (0 : ℝ) L,
      (CovariantDerivative.alternating (M := M) (F := E) (V := TangentSpace I) (LeviCivita g) k).derivAlongWithin γ A (Icc (0 : ℝ) L) t = 0) :
    A L = (parallelTransportLinearEquivOnIcc g γ hγ hL).toContinuousLinearEquiv.continuousAlternatingMapCongrLeft (A 0) := by
  obtain ⟨B, hB₀, hB, hBpar, hBL⟩ := exists_parallel_alternating_transport_on_Icc g γ hγ k hL (A 0)
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative (CovariantDerivative.alternating (M := M) (F := E) (V := TangentSpace I) (LeviCivita g) k) ∞ :=
    inferInstance
  exact ((CovariantDerivative.alternating (M := M) (F := E) (V := TangentSpace I) (LeviCivita g) k).parallel_section_eq_on_Icc hcov
    (left_mem_Icc.mpr hL.le) (hγ.contMDiffOn.of_le (by norm_num)) hA hB hpar hBpar hB₀.symm
    L (right_mem_Icc.mpr hL.le)).trans hBL


end DifferentialGeometry.Geometry.Riemannian.Variation


namespace ContMDiffVectorSubbundle

open DifferentialGeometry (SmoothRiemannianMetric)
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [I.Boundaryless]

private instance alternatingModelFiniteDimensional (k : ℕ) :
    FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ E)).finiteDimensional_of_finite

theorem map_parallelTransportLinearEquivBetween_alternating
    (k : ℕ)
    (S : ContMDiffVectorSubbundle (I := I) (F := E [⋀^Fin k]→L[ℝ] ℝ)
      (V := Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace I : M → Type _) ℝ
        (Bundle.Trivial M ℝ)) (n := ∞))
    (g : SmoothRiemannianMetric I M)
    (hS : IsCovariantlyInvariantSubmoduleFamily (CovariantDerivative.alternating (LeviCivita g) k) S.fiber)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) :
    Submodule.map
      ((parallelTransportLinearEquivBetween g γ hγ hab).toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
        (ι := Fin k)).toLinearMap (S.fiber (γ a)) = S.fiber (γ b) := by
  let δ := fun s => γ (s + a)
  let L := b - a
  have hL : 0 < L := sub_pos.mpr hab
  have hδ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) δ :=
    hγ.comp (contMDiff_id.add contMDiff_const)
  let e : (TangentSpace I (δ 0) [⋀^Fin k]→L[ℝ] ℝ) ≃L[ℝ]
      (TangentSpace I (δ L) [⋀^Fin k]→L[ℝ] ℝ) :=
    (parallelTransportLinearEquivOnIcc g δ hδ hL).toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
    (ι := Fin k)
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.alternating (LeviCivita g) k) ∞ := inferInstance
  have hpreserves (v : TangentSpace I (δ 0) [⋀^Fin k]→L[ℝ] ℝ)
      (hv : v ∈ S.fiber (δ 0)) : e v ∈ S.fiber (δ L) := by
    obtain ⟨A, hA₀, hA, hpar, hAL⟩ := exists_parallel_alternating_transport_on_Icc g δ hδ k hL v
    have hmem := S.mem_of_parallel_section_of_covariantly_invariant
      (CovariantDerivative.alternating (LeviCivita g) k) hS hcov ordConnected_Icc
      (left_mem_Icc.mpr hL.le) (hδ.contMDiffOn.of_le (by norm_num)) hA hpar
      (by rw [hA₀]; exact hv) L (right_mem_Icc.mpr hL.le)
    rw [hAL] at hmem
    exact hmem
  have hm : Submodule.map e.toLinearMap (S.fiber (δ 0)) = S.fiber (δ L) := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro w ⟨v, hv, rfl⟩
      exact hpreserves v hv
    · rw [← (Submodule.equivMapOfInjective e.toLinearMap e.injective (S.fiber (δ 0))).finrank_eq,
        S.finrank_fiber, S.finrank_fiber]
  dsimp only [e, δ, L] at hm
  rw [zero_add, sub_add_cancel] at hm
  exact hm



end ContMDiffVectorSubbundle
