import DifferentialGeometry.Geometry.Comparison.Soul.NormalSplitting
import DifferentialGeometry.Geometry.Comparison.Nonnegative.ParallelVariationRegularity
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

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

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem IsTotallyConvex.pathConnectedSpace
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S) (hne : S.Nonempty) :
    PathConnectedSpace S :=
  isPathConnected_iff_pathConnectedSpace.mp (hconv.isPathConnected g hEnorm hne)

theorem intrinsicGeodesic_mem_of_relBoundary_eq_empty
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S) (hclosed : IsClosed S)
    (hB : relBoundary I S = ∅) {x : M} (hx : x ∈ S)
    {v : TangentSpace I x} (hv : v ∈ sliceTangent I S x) (t : ℝ) :
    intrinsicGeodesic g hEnorm x v t ∈ S := by
  have hN : maxSliceLocus I S = S := relBoundary_eq_empty_iff.mp hB
  have hxN : x ∈ maxSliceLocus I S := by rwa [hN]
  have htv : t • v ∈ sliceTangent I (maxSliceLocus I S) x := by
    rw [hN]
    exact (sliceTangent I S x).smul_mem t hv
  have hall := mem_maxSliceLocus_of_mem_sliceTangent hEnorm hconv hclosed hxN htv
    (O := univ) (by simpa only [univ_inter, hN] using (Subset.rfl : S ⊆ S))
    zero_le_one (fun _ _ => mem_univ _)
  have h := hall 1 ⟨zero_le_one, le_rfl⟩
  rwa [intrinsicGeodesic_smul, hN] at h

theorem expMapIntrinsic_mem_of_relBoundary_eq_empty
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S) (hclosed : IsClosed S)
    (hB : relBoundary I S = ∅) {x : M} (hx : x ∈ S)
    {v : TangentSpace I x} (hv : v ∈ sliceTangent I S x) :
    expMapIntrinsic g hEnorm x v ∈ S := by
  rw [expMapIntrinsic_def]
  exact intrinsicGeodesic_mem_of_relBoundary_eq_empty g hEnorm hconv hclosed hB hx hv 1

theorem exists_embeddedSlice_geodesic_lift
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S) (hclosed : IsClosed S)
    (hB : relBoundary I S = ∅) (p : S) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    ∀ v : TangentSpace 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) p,
      ∃ γ : ℝ → S, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) ∞ γ ∧
        γ 0 = p ∧ IsGeodesic (I := I) g (fun t => (γ t).1) ∧
        ∀ t, (γ t).1 = intrinsicGeodesic g hEnorm p.1
          (mfderiv 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) I (Subtype.val : S → M) p v) t := by
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  change ∀ v : TangentSpace 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) p,
    ∃ γ : ℝ → S, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) ∞ γ ∧
      γ 0 = p ∧ IsGeodesic (I := I) g (fun t => (γ t).1) ∧
      ∀ t, (γ t).1 = intrinsicGeodesic g hEnorm p.1
        (mfderiv 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) I (Subtype.val : S → M) p v) t
  intro v
  let a := mfderiv 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) I (Subtype.val : S → M) p v
  have ha : a ∈ sliceTangent I S p.1 := by
    rw [← embeddedSlice_inclusion_range_mfderiv hS p]
    exact ⟨v, rfl⟩
  have hmem (t : ℝ) : intrinsicGeodesic g hEnorm p.1 a t ∈ S :=
    intrinsicGeodesic_mem_of_relBoundary_eq_empty g hEnorm hconv hclosed hB p.2 ha t
  let γ : ℝ → S := fun t => ⟨intrinsicGeodesic g hEnorm p.1 a t, hmem t⟩
  refine ⟨γ, ?_, ?_, ?_, fun _ => rfl⟩
  · exact embeddedSlice_corestrict_contMDiff hS _
      (intrinsicGeodesic_contMDiff g hEnorm p.1 a) hmem
  · apply Subtype.ext
    exact intrinsicGeodesic_zero g hEnorm p.1 a
  · exact intrinsicGeodesic_isGeodesic g hEnorm p.1 a

omit [T2Space (TangentBundle I M)] in
theorem covDerivAlong_mem_sliceTangent_of_relBoundary_eq_empty
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S) (hclosed : IsClosed S)
    (hB : relBoundary I S = ∅) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hγS : ∀ s, γ s ∈ S)
    {V : ∀ s : ℝ, TangentSpace I (γ s)} {t : ℝ}
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hVS : ∀ᶠ s in 𝓝 t, V s ∈ sliceTangent I S (γ s)) :
    covDerivAlong (I := I) g γ V t ∈ sliceTangent I S (γ t) := by
  have hN : maxSliceLocus I S = S := relBoundary_eq_empty_iff.mp hB
  have hγN (s : ℝ) : γ s ∈ maxSliceLocus I S := by
    rw [hN]
    exact hγS s
  obtain ⟨m, F, W, htW, hfam⟩ :=
    hasSliceDefiningFamilies_of_totallyConvex hEnorm hconv (γ t) (hγN t)
  have hvel : mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) ∈
      sliceTangent I (maxSliceLocus I S) (γ t) :=
    curveVelocity_mem_sliceTangent ((hγ t).mdifferentiableAt (by simp))
      (Filter.Eventually.of_forall (fun s => hγN (t + s)))
  have hVt : V t ∈ sliceTangent I (maxSliceLocus I S) (γ t) := by
    rw [hN]
    exact hVS.self_of_nhds
  rw [← hN]
  apply (hfam.mem_iff (γ t) htW (hγN t) _).2
  intro i
  have hnearW : ∀ᶠ s in 𝓝 t, γ s ∈ W :=
    hγ.continuous.continuousAt.preimage_mem_nhds (hfam.isOpen.mem_nhds htW)
  have hzero : (fun s => g.inner (γ s) (gradFun (I := I) g (F i) (γ s)) (V s))
      =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnearW, hVS] with s hsW hsV
    exact ((hfam.mem_iff (γ s) hsW (hγN s) (V s)).1 (by rwa [hN])) i
  have hess := hessFun_apply_eq_zero_of_mem_sliceTangent hEnorm hconv hclosed
    (hfam.contMDiff i) (hγN t) (hfam.locallyConstant (γ t) htW (hγN t) i) hvel hVt
  have hderiv := hasDerivAt_inner_gradFun g (hfam.contMDiff i) hγ V hV
  simp only [DifferentialGeometry.Geometry.Riemannian.Variation.curveVelocity] at hderiv
  rw [hess, zero_add] at hderiv
  have hderiv0 : HasDerivAt
      (fun s => g.inner (γ s) (gradFun (I := I) g (F i) (γ s)) (V s)) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hzero
  exact hderiv.unique hderiv0

theorem embeddedSlice_inclusion_normal_covDerivAlong_eq_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S) (hclosed : IsClosed S)
    (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    let IB := 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)
    ∀ (γ : ℝ → S), ContMDiff 𝓘(ℝ, ℝ) IB ∞ γ →
      ∀ V : ∀ s : ℝ, TangentSpace IB (γ s),
        ContMDiff 𝓘(ℝ, ℝ) IB.tangent ∞
          (fun s => (⟨γ s, V s⟩ : TangentBundle IB S)) →
        ∀ (t : ℝ) (n : TangentSpace I (γ t).1), n ∈ normalSpace (I := I) g S (γ t).1 →
          g.inner (γ t).1
            (covDerivAlong (I := I) g (fun s => (γ s).1)
              (fun s => mfderiv IB I (Subtype.val : S → M) (γ s) (V s)) t) n = 0 := by
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let IB := 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)
  change ∀ γ : ℝ → S, ContMDiff 𝓘(ℝ, ℝ) IB ∞ γ →
    ∀ V : ∀ s : ℝ, TangentSpace IB (γ s),
      ContMDiff 𝓘(ℝ, ℝ) IB.tangent ∞
        (fun s => (⟨γ s, V s⟩ : TangentBundle IB S)) →
      ∀ (t : ℝ) (n : TangentSpace I (γ t).1), n ∈ normalSpace (I := I) g S (γ t).1 →
        g.inner (γ t).1
          (covDerivAlong (I := I) g (fun s => (γ s).1)
            (fun s => mfderiv IB I (Subtype.val : S → M) (γ s) (V s)) t) n = 0
  intro γ hγ V hV t n hn
  let γM : ℝ → M := fun s => (γ s).1
  let VM : ∀ s : ℝ, TangentSpace I (γM s) :=
    fun s => mfderiv IB I (Subtype.val : S → M) (γ s) (V s)
  have hi : ContMDiff IB I ∞ (Subtype.val : S → M) := embeddedSlice_inclusion_contMDiff hS
  have hγM : ContMDiff 𝓘(ℝ, ℝ) I ∞ γM := hi.comp hγ
  have hVM : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun s => (⟨γM s, VM s⟩ : TangentBundle I M)) :=
    (hi.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  have hVMt (s : ℝ) : VM s ∈ sliceTangent I S (γM s) := by
    rw [← embeddedSlice_inclusion_range_mfderiv hS (γ s)]
    exact ⟨V s, rfl⟩
  have hD := covDerivAlong_mem_sliceTangent_of_relBoundary_eq_empty g hEnorm hconv
    hclosed hB hγM (fun s => (γ s).2)
    (differentiableAt_chartRepAt_of_contMDiff γM VM hVM t)
    (Filter.Eventually.of_forall hVMt)
  change g.inner (γM t) (covDerivAlong (I := I) g γM VM t) n = 0
  rw [g.symm]
  exact (mem_normalSpace_iff g S (γM t) n).mp hn _ hD

end DifferentialGeometry.Geometry.Topology

end
