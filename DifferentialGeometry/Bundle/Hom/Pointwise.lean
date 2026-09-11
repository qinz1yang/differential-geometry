import DifferentialGeometry.Bundle.Section
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace ContinuousLinearMap

variable {k : Type*} [NontriviallyNormedField k] [CompleteSpace k]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace k EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners k EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners k EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace k F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module k (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle k F V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace k W] [FiniteDimensional k W]
  {n : ℕ∞ω} {b : P → B} {φ : ∀ p, W →L[k] V (b p)}

theorem contMDiffWithinAt_bundle_apply_of_pointwise {s : Set P} {p₀ : P} {w₀ : W}
    (hφ : ∀ w, ContMDiffWithinAt IP (IB.prod 𝓘(k, F)) n
      (fun p => (⟨b p, φ p w⟩ : TotalSpace F V)) s p₀) :
    ContMDiffWithinAt (IP.prod 𝓘(k, W)) (IB.prod 𝓘(k, F)) n
      (fun z : P × W => (⟨b z.1, φ z.1 z.2⟩ : TotalSpace F V))
      (s ×ˢ univ) (p₀, w₀) := by
  classical
  let e := Module.finBasis k W
  have hb : ContMDiffWithinAt IP IB n b s p₀ := by
    have h := hφ 0
    rw [Bundle.contMDiffWithinAt_totalSpace] at h
    exact h.1
  have he (i) : ContMDiffWithinAt (IP.prod 𝓘(k, W)) (IB.prod 𝓘(k, F)) n
      (fun z : P × W => (⟨b z.1, φ z.1 (e i)⟩ : TotalSpace F V))
      (s ×ˢ univ) (p₀, w₀) :=
    (hφ (e i)).comp (p₀, w₀) contMDiffWithinAt_fst (fun _ hz => hz.1)
  have hc (i) : ContMDiffWithinAt (IP.prod 𝓘(k, W)) 𝓘(k, k) n
      (fun z : P × W => e.equivFun z.2 i) (s ×ˢ univ) (p₀, w₀) := by
    let L : W →L[k] k := (ContinuousLinearMap.proj i).comp e.equivFunL.toContinuousLinearMap
    exact L.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt
      (p₀, w₀) contMDiffWithinAt_snd
  have h := (hb.comp (p₀, w₀) contMDiffWithinAt_fst (fun _ hz => hz.1)).sum_bundle
    Finset.univ (fun i _ => (hc i).smul_bundle (he i))
  have heq (z : P × W) :
      (⟨b z.1, φ z.1 z.2⟩ : TotalSpace F V) =
        ⟨b z.1, ∑ i, e.equivFun z.2 i • φ z.1 (e i)⟩ := by
    apply TotalSpace.mk_inj.mpr
    simpa only [map_sum, map_smul] using congrArg (φ z.1) (e.sum_equivFun z.2).symm
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall heq) (heq _)

theorem contMDiffAt_bundle_apply_of_pointwise {p₀ : P} {w₀ : W}
    (hφ : ∀ w, ContMDiffAt IP (IB.prod 𝓘(k, F)) n
      (fun p => (⟨b p, φ p w⟩ : TotalSpace F V)) p₀) :
    ContMDiffAt (IP.prod 𝓘(k, W)) (IB.prod 𝓘(k, F)) n
      (fun z : P × W => (⟨b z.1, φ z.1 z.2⟩ : TotalSpace F V)) (p₀, w₀) := by
  simpa only [univ_prod_univ, contMDiffWithinAt_univ] using
    contMDiffWithinAt_bundle_apply_of_pointwise (w₀ := w₀)
      (fun w => (hφ w).contMDiffWithinAt (s := univ))

theorem contMDiffOn_bundle_apply_of_pointwise {s : Set P}
    (hφ : ∀ w, ContMDiffOn IP (IB.prod 𝓘(k, F)) n
      (fun p => (⟨b p, φ p w⟩ : TotalSpace F V)) s) :
    ContMDiffOn (IP.prod 𝓘(k, W)) (IB.prod 𝓘(k, F)) n
      (fun z : P × W => (⟨b z.1, φ z.1 z.2⟩ : TotalSpace F V)) (s ×ˢ univ) :=
  fun z hz => contMDiffWithinAt_bundle_apply_of_pointwise (fun w => hφ w z.1 hz.1)

theorem contMDiff_bundle_apply_of_pointwise
    (hφ : ∀ w, ContMDiff IP (IB.prod 𝓘(k, F)) n
      (fun p => (⟨b p, φ p w⟩ : TotalSpace F V))) :
    ContMDiff (IP.prod 𝓘(k, W)) (IB.prod 𝓘(k, F)) n
      (fun z : P × W => (⟨b z.1, φ z.1 z.2⟩ : TotalSpace F V)) :=
  fun z => contMDiffAt_bundle_apply_of_pointwise (fun w => hφ w z.1)

end ContinuousLinearMap
