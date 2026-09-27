import DifferentialGeometry.Geometry.Metric.ExteriorPowerRiemannian
import DifferentialGeometry.Geometry.Metric.BundleMusical
import DifferentialGeometry.Tensor.Alternating.Bundle.Defs
import DifferentialGeometry.Bundle.Hom.Regularity

noncomputable section

open scoped Bundle Manifold ContDiff RealInnerProductSpace Topology

namespace exteriorPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private def dualToAlternating (k : ℕ) :
    ((⋀[ℝ]^k E) →L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ := by
  let : CompleteSpace (⋀[ℝ]^k E) := FiniteDimensional.complete ℝ _
  exact (musicalEquiv k).toContinuousLinearMap.comp
    (InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem dualToAlternating_apply (k : ℕ)
    (a : (⋀[ℝ]^k E) →L[ℝ] ℝ) (v : Fin k → E) :
    dualToAlternating k a v = a (ιMulti ℝ k v) := by
  let : CompleteSpace (⋀[ℝ]^k E) := FiniteDimensional.complete ℝ _
  change musicalEquiv k ((InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm a) v = _
  rw [musicalEquiv_apply, InnerProductSpace.toDual_symm_apply]

end exteriorPower

namespace Bundle.ExteriorPower

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

private theorem musicalEquiv_inCoordinates (k : ℕ) (x y : B)
    (hy : y ∈ (trivializationAt F V x).baseSet) (u : ⋀[ℝ]^k (V y)) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    (trivializationAt (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) x
        ⟨y, exteriorPower.musicalEquiv k u⟩).2 =
      exteriorPower.dualToAlternating k
        ((trivializationAt ((⋀[ℝ]^k F) →L[ℝ] ℝ)
          (fun x => (⋀[ℝ]^k (V x)) →L[ℝ] ℝ) x ⟨y, innerSL ℝ u⟩).2) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply, hom_trivializationAt_apply]
  apply ContinuousAlternatingMap.ext
  intro v
  rw [exteriorPower.dualToAlternating_apply]
  simp only [ContinuousAlternatingMap.inCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  change (trivializationAt ℝ (Bundle.Trivial B ℝ) x).continuousLinearMapAt ℝ y
      (exteriorPower.musicalEquiv k u
        (fun i => (trivializationAt F V x).symmL ℝ y (v i))) = _
  apply congrArg ((trivializationAt ℝ (Bundle.Trivial B ℝ) x).continuousLinearMapAt ℝ y)
  rw [exteriorPower.musicalEquiv_apply]
  change ⟪u, _⟫ = ⟪u, _⟫
  congr 1
  rw [Trivialization.symmL_apply _ (show y ∈
      (trivializationAt (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) x).baseSet from hy),
    trivializationAt_eq F V k x,
    trivialization_symm_apply F V k (trivializationAt F V x) hy,
    exteriorPower.map_apply_ιMulti]
  rfl

variable
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V]

theorem contMDiff_musicalEquiv_map (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) (IB.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun p : TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) =>
        (⟨p.1, exteriorPower.musicalEquiv k p.2⟩ : TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  let := isContMDiffRiemannianBundle (IB := IB) (n := n) F V k
  have hdual := (contMDiff_id :
    ContMDiff (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) n
      (fun p : TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) => p)).innerSL_bundle
  intro p
  have hd := hdual p
  rw [contMDiffAt_totalSpace] at hd ⊢
  refine ⟨hd.1, ?_⟩
  have hL : ContMDiff 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] ℝ) 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ) n
      (exteriorPower.dualToAlternating (E := F) k) :=
    (exteriorPower.dualToAlternating (E := F) k).contMDiff
  have h := hL.contMDiffAt.comp p hd.2
  apply h.congr_of_eventuallyEq
  let e := trivializationAt F V p.1
  have hx : p.1 ∈ e.baseSet := mem_baseSet_trivializationAt F V p.1
  have hbase := hd.1.continuousAt (e.open_baseSet.mem_nhds hx)
  filter_upwards [hbase] with q hq
  exact musicalEquiv_inCoordinates F V k p.1 q.1 hq q.2

theorem contMDiff_musicalEquiv (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff IB (IB.prod 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun x => (⟨x, (exteriorPower.musicalEquiv (E := V x) k).toContinuousLinearMap⟩ :
        TotalSpace ((⋀[ℝ]^k F) →L[ℝ] F [⋀^Fin k]→L[ℝ] ℝ)
          (fun x => (⋀[ℝ]^k (V x)) →L[ℝ] V x [⋀^Fin k]→L[ℝ] ℝ))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  exact ContMDiff.clm_bundle_of_map (contMDiff_musicalEquiv_map F V k)

theorem contMDiff_musicalEquiv_symm (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff IB (IB.prod 𝓘(ℝ, (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k F)) n
      (fun x => (⟨x, (exteriorPower.musicalEquiv (E := V x) k).symm.toContinuousLinearMap⟩ :
        TotalSpace ((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k F)
          (fun x => (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k (V x)))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  let : CompleteSpace (⋀[ℝ]^k F) := FiniteDimensional.complete ℝ _
  have h := (contMDiff_musicalEquiv (IB := IB) (n := n) F V k).clm_bundle_inverse
    (fun _ => ContinuousLinearMap.isInvertible_equiv)
  simpa using h

theorem contMDiff_musicalEquiv_symm_map (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff (IB.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) n
      (fun p : TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) =>
        (⟨p.1, (exteriorPower.musicalEquiv k).symm p.2⟩ :
          TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  exact (contMDiff_musicalEquiv_symm F V k).clm_bundle_map

end Bundle.ExteriorPower
