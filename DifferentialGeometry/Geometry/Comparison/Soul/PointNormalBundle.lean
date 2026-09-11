import DifferentialGeometry.Geometry.Comparison.Soul.NormalBundle
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem normalSpace_eq_top_of_maxSliceDim_eq_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S)
    (hB : relBoundary I S = ∅) (hdim : maxSliceDim I S = 0)
    {x : M} (hx : x ∈ S) : normalSpace (I := I) g S x = ⊤ := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  have ht : sliceTangent I S x = ⊥ :=
    Submodule.finrank_eq_zero.mp (by
      rw [finrank_sliceTangent
        (isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB) hx, hdim])
  apply top_unique
  intro v _
  rw [mem_normalSpace_iff]
  intro w hw
  have hw0 : w = 0 := by simpa only [ht, Submodule.mem_bot] using hw
  simp only [hw0, map_zero]

theorem exists_point_normalBundle_diffeomorph
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hne : S.Nonempty) (hconv : IsTotallyConvex (I := I) g S)
    (hB : relBoundary I S = ∅) (hdim : maxSliceDim I S = 0) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ∃ Ψ : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
        (normalBundleFiber (I := I) g S) ≃ₘ⟮
          (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
            𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), 𝓘(ℝ, E)⟯ E,
      ∀ q : S, Ψ ⟨q, 0⟩ = 0 := by
  classical
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let FN := Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ
  let IB := 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)
  let IN := IB.prod 𝓘(ℝ, FN)
  let ν := TotalSpace FN (normalBundleFiber (I := I) g S)
  change ∃ Ψ : ν ≃ₘ⟮IN, 𝓘(ℝ, E)⟯ E, ∀ q : S, Ψ ⟨q, 0⟩ = 0
  obtain ⟨x, hSx⟩ := eq_singleton_of_maxSliceDim_eq_zero g hEnorm hconv hne hB hdim
  have hsub : S.Subsingleton := by
    rw [hSx]
    exact subsingleton_singleton
  let _ : Subsingleton S := hsub.coe_sort
  let p : S := ⟨hne.choose, hne.choose_spec⟩
  let e := trivializationAt FN (normalBundleFiber (I := I) g S) p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt FN (normalBundleFiber g S) p
  have hb (q : S) : q ∈ e.baseSet := by
    have hq : q = p := Subsingleton.elim q p
    rwa [hq]
  have hsource (z : ν) : z ∈ e.source := e.mem_source.mpr (hb z.proj)
  have hforward : ContMDiff IN 𝓘(ℝ, FN) ∞ (fun z : ν => (e z).2) :=
    ((e.contMDiff_iff (IB := IB) (IM := IN) (n := ∞) hsource).mp contMDiff_id).2
  have hinverse : ContMDiff 𝓘(ℝ, FN) IN ∞
      (fun v : FN => (⟨p, e.symm p v⟩ : ν)) := by
    apply (e.contMDiff_iff (IB := IB) (IM := 𝓘(ℝ, FN))
      (fun v => hsource ⟨p, e.symm p v⟩)).mpr
    refine ⟨contMDiff_const, ?_⟩
    exact contMDiff_id.congr (fun v => congrArg Prod.snd (e.apply_mk_symm hp v))
  let d : ν ≃ₘ⟮IN, 𝓘(ℝ, FN)⟯ FN :=
    { toEquiv :=
        { toFun := fun z => (e z).2
          invFun := fun v => ⟨p, e.symm p v⟩
          left_inv := by
            rintro ⟨q, v⟩
            have hq : q = p := Subsingleton.elim q p
            subst q
            exact congrArg (TotalSpace.mk p) (e.symm_apply_apply_mk hp v)
          right_inv := fun v => congrArg Prod.snd (e.apply_mk_symm hp v) }
      contMDiff_toFun := hforward
      contMDiff_invFun := hinverse }
  let L : FN ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by
    change Module.finrank ℝ (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ) =
      Module.finrank ℝ E
    simp only [Module.finrank_fin_fun, hdim, Nat.sub_zero])
  refine ⟨d.trans L.toDiffeomorph, ?_⟩
  intro q
  have hzero : d ⟨q, 0⟩ = 0 := by
    change (e (⟨q, 0⟩ : ν)).2 = 0
    exact congrArg Prod.snd (e.zeroSection ℝ (hb q))
  change L (d ⟨q, 0⟩) = 0
  rw [hzero, map_zero]

end DifferentialGeometry.Geometry.Topology

end
