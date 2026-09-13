import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

noncomputable section
open Set
open scoped NNReal
namespace DifferentialGeometry.Analysis.Schauder

private theorem exists_holderOnWith_pi
    {X Y ι : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [Fintype ι]
    {s : Set X} {f : X → ι → Y} {α : ℝ≥0}
    (hf : ∀ i, ∃ K : ℝ≥0, HolderOnWith K α (fun x => f x i) s) :
    ∃ K : ℝ≥0, HolderOnWith K α f s := by
  classical
  choose K hK using hf
  refine ⟨∑ i, K i, ?_⟩
  intro x hx y hy
  apply edist_pi_le_iff.mpr
  intro i
  exact (hK i x hx y hy).trans (by
    gcongr
    exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i))

private theorem exists_holderOnWith_clm_of_basis
    {𝕜 X E F ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [PseudoEMetricSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Finite ι]
    (b : Module.Basis ι 𝕜 E) {s : Set X} {f : X → E →L[𝕜] F} {α : ℝ≥0}
    (hf : ∀ i, ∃ K : ℝ≥0, HolderOnWith K α (fun x => f x (b i)) s) :
    ∃ K : ℝ≥0, HolderOnWith K α f s := by
  classical
  let := Fintype.ofFinite ι
  let e : (E →L[𝕜] F) ≃L[𝕜] (ι → F) :=
    (b.equivFunL.arrowCongr (ContinuousLinearEquiv.refl 𝕜 F)).trans
      (ContinuousLinearEquiv.piRing ι)
  have he (A : E →L[𝕜] F) (i : ι) : e A i = A (b i) := by
    change A (b.equivFunL.symm (Pi.single i 1)) = A (b i)
    congr 1
    change b.equivFun.symm (Pi.single i 1) = b i
    simp
  obtain ⟨K, hK⟩ := exists_holderOnWith_pi (f := fun x => e (f x))
    (fun i => by simpa only [he] using hf i)
  refine ⟨‖e.symm.toContinuousLinearMap‖₊ * K, ?_⟩
  have hh := e.symm.lipschitz.holderWith.comp_holderOnWith hK
  intro x hx y hy
  simpa only [Function.comp_def, e.symm_apply_apply, one_mul, NNReal.coe_one,
    NNReal.rpow_one] using! hh x hx y hy

theorem exists_holderOnWith_continuousMultilinearMap_of_basis
    {𝕜 X E F ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [PseudoEMetricSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Finite ι]
    (b : Module.Basis ι 𝕜 E) {s : Set X} {n : ℕ}
    {f : X → E [×n]→L[𝕜] F} {α : ℝ≥0}
    (hf : ∀ v : Fin n → ι, ∃ K : ℝ≥0,
      HolderOnWith K α (fun x => f x (fun i => b (v i))) s) :
    ∃ K : ℝ≥0, HolderOnWith K α f s := by
  induction n with
  | zero =>
      obtain ⟨K, hK⟩ := hf (fun i => Fin.elim0 i)
      refine ⟨K, ?_⟩
      intro x hx y hy
      rw [← (continuousMultilinearCurryFin0 𝕜 E F).edist_map]
      simpa only [continuousMultilinearCurryFin0_apply,
        Subsingleton.elim (0 : Fin 0 → E) (fun i => b (Fin.elim0 i))] using hK x hx y hy
  | succ n ih =>
      let e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F
      obtain ⟨K, hK⟩ := exists_holderOnWith_clm_of_basis b (f := fun x => e (f x)) (by
        intro i
        apply ih (f := fun x => e (f x) (b i))
        intro v
        simpa only [e, continuousMultilinearCurryLeftEquiv_apply,
          ContinuousMultilinearMap.curryLeft_apply, ← Function.comp_def,
          Fin.comp_cons] using hf (Fin.cons i v))
      refine ⟨K, ?_⟩
      intro x hx y hy
      have hh := hK x hx y hy
      simpa only [e, LinearIsometryEquiv.edist_map] using hh

end DifferentialGeometry.Analysis.Schauder
