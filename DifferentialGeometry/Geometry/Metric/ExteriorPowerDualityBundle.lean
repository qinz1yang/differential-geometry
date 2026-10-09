import DifferentialGeometry.Geometry.Metric.ExteriorPowerDuality

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff Topology

namespace Bundle.ExteriorPower

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

omit [FiniteDimensional ℝ F] in
private theorem alternating_symmL_apply (k : ℕ) (x y : B)
    (hy : y ∈ (trivializationAt F V x).baseSet) (a : F [⋀^Fin k]→L[ℝ] ℝ) :
    (trivializationAt (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) x).symmL ℝ y a =
      a.compContinuousLinearMap ((trivializationAt F V x).continuousLinearMapAt ℝ y) := by
  rw [Trivialization.symmL_apply _ (by simpa using hy)]
  change (Pretrivialization.continuousAlternatingMap ℝ (Fin k)
    (trivializationAt F V x) (trivializationAt ℝ (Bundle.Trivial B ℝ) x)).symm y a = _
  rw [Pretrivialization.continuousAlternatingMap_symm_apply' ⟨hy, by simp⟩]
  ext v
  simp

private theorem alternatingDualEquiv_inCoordinates (k : ℕ) (x y : B)
    (hy : y ∈ (trivializationAt F V x).baseSet) (u : ⋀[ℝ]^k (V y)) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    (trivializationAt ((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
      (fun x => (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) x
        ⟨y, exteriorPower.alternatingDualEquiv k u⟩).2 =
      exteriorPower.alternatingDualEquiv k
        ((trivializationAt (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) x ⟨y, u⟩).2) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  rw [hom_trivializationAt_apply, trivializationAt_eq F V k x,
    trivialization_apply F V k (trivializationAt F V x) y u]
  apply ContinuousLinearMap.ext
  intro a
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [alternating_symmL_apply F V k x y hy]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ (by simp)]
  exact (exteriorPower.alternatingDualEquiv_map_apply k
    ((trivializationAt F V x).continuousLinearMapAt ℝ y) u a).symm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B]

theorem mdifferentiableAt_ιMulti (k : ℕ) (Y : Fin k → ∀ x, V x) {x : B}
    (hY : ∀ i, MDifferentiableAt IB (IB.prod 𝓘(ℝ, F))
      (fun y => (⟨y, Y i y⟩ : TotalSpace F V)) x) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    MDifferentiableAt IB (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F))
      (fun y => (⟨y, exteriorPower.ιMulti ℝ k (fun i => Y i y)⟩ :
        TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)))) x := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  rw [mdifferentiableAt_section]
  have hYc := fun i => (mdifferentiableAt_section _ _).mp (hY i)
  have hpi : MDifferentiableAt IB 𝓘(ℝ, Fin k → F)
      (fun y i => (trivializationAt F V x ⟨y, Y i y⟩).2) x := by
    simpa only [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_iff,
      continuousWithinAt_pi, differentiableWithinAt_pi, forall_and,
      extChartAt_model_space_eq_id, Function.comp_def, PartialEquiv.refl_coe, id] using hYc
  have h := Differentiable.comp_mdifferentiableAt
    ((exteriorPower.contDiff_ιMulti (E := F) k 1).differentiable one_ne_zero) hpi
  apply h.congr_of_eventuallyEq
  let e := trivializationAt F V x
  filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x)] with y hy
  rw [trivializationAt_eq F V k x, trivialization_apply,
    exteriorPower.map_apply_ιMulti]
  change exteriorPower.ιMulti ℝ k
      (fun i => e.continuousLinearMapAt ℝ y (Y i y)) =
    exteriorPower.ιMulti ℝ k (fun i => (e ⟨y, Y i y⟩).2)
  apply congrArg (exteriorPower.ιMulti ℝ k)
  funext i
  exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hy (Y i y)

theorem contMDiff_alternatingDualEquiv_map (k : ℕ) (n : ℕ∞ω) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) (IB.prod 𝓘(ℝ, (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)) n
      (fun p : TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) =>
        (⟨p.1, exteriorPower.alternatingDualEquiv k p.2⟩ :
          TotalSpace ((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
            (fun x => (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  intro p
  have hd := (contMDiffAt_id :
    ContMDiffAt (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) n
      (fun q : TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) => q) p)
  rw [contMDiffAt_totalSpace] at hd ⊢
  refine ⟨hd.1, ?_⟩
  have hL : ContMDiff 𝓘(ℝ, ⋀[ℝ]^k F) 𝓘(ℝ, (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) n
      (exteriorPower.alternatingDualEquiv (E := F) k) :=
    (exteriorPower.alternatingDualEquiv (E := F) k).contDiff.contMDiff
  have h := hL.contMDiffAt.comp p hd.2
  apply h.congr_of_eventuallyEq
  let e := trivializationAt F V p.1
  have hx : p.1 ∈ e.baseSet := mem_baseSet_trivializationAt F V p.1
  have hbase := hd.1.continuousAt (e.open_baseSet.mem_nhds hx)
  filter_upwards [hbase] with q hq
  exact alternatingDualEquiv_inCoordinates F V k p.1 q.1 hq q.2

theorem contMDiff_alternatingDualEquiv (k : ℕ) (n : ℕ∞ω) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff IB (IB.prod 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)) n
      (fun x => (⟨x, (exteriorPower.alternatingDualEquiv (E := V x) k).toContinuousLinearMap⟩ :
        TotalSpace ((⋀[ℝ]^k F) →L[ℝ] (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
          (fun x => (⋀[ℝ]^k (V x)) →L[ℝ] (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  exact ContMDiff.clm_bundle_of_map (contMDiff_alternatingDualEquiv_map F V k n)

theorem contMDiff_alternatingDualEquiv_symm (k : ℕ) (n : ℕ∞ω) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff IB (IB.prod 𝓘(ℝ, ((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k F)) n
      (fun x => (⟨x, (exteriorPower.alternatingDualEquiv (E := V x) k).symm.toContinuousLinearMap⟩ :
        TotalSpace (((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k F)
          (fun x => ((V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k (V x)))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  let : CompleteSpace (⋀[ℝ]^k F) := FiniteDimensional.complete ℝ _
  have h := (contMDiff_alternatingDualEquiv (IB := IB) F V k n).clm_bundle_inverse
    (fun _ => ContinuousLinearMap.isInvertible_equiv)
  simpa only [ContinuousLinearMap.inverse_equiv] using h

theorem contMDiff_alternatingDualEquiv_symm_map (k : ℕ) (n : ℕ∞ω) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff (IB.prod 𝓘(ℝ, (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)) (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) n
      (fun p : TotalSpace ((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
        (fun x => (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) =>
        (⟨p.1, (exteriorPower.alternatingDualEquiv k).symm p.2⟩ :
          TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  exact (contMDiff_alternatingDualEquiv_symm F V k n).clm_bundle_map

end Bundle.ExteriorPower
