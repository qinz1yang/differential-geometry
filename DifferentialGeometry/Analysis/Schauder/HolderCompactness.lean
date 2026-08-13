import DifferentialGeometry.Analysis.Calculus.ArzelaAscoli
import DifferentialGeometry.Analysis.Schauder.Holder

noncomputable section

open Filter Set Topology
open scoped NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {X Y F : Type*}

theorem uniformEquicontinuous_of_holderWith
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {ι : Type*} (f : ι → X → Y) {C r : NNReal} (hr : 0 < r)
    (hf : ∀ i, HolderWith C r (f i)) :
    UniformEquicontinuous f := by
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  refine Metric.uniformEquicontinuous_of_continuity_modulus
    (fun s : Real => (C : Real) * s ^ (r : Real)) ?_ f ?_
  · have hcont : ContinuousAt
        (fun s : Real => (C : Real) * s ^ (r : Real)) 0 :=
      continuousAt_const.mul
        (Real.continuousAt_rpow_const 0 (r : Real) (.inr hrReal.le))
    simpa only [Real.zero_rpow hrReal.ne', mul_zero] using hcont.tendsto
  · intro x y i
    exact (hf i).dist_le x y

theorem uniformEquicontinuousOn_of_holderOnWith
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {ι : Type*} (f : ι → X → Y) {s : Set X} {C r : NNReal} (hr : 0 < r)
    (hf : ∀ i, HolderOnWith C r (f i) s) :
    UniformEquicontinuousOn f s := by
  rw [← uniformEquicontinuous_restrict_iff]
  exact uniformEquicontinuous_of_holderWith
    (s.restrict ∘ f) hr (fun i => (hf i).holderWith)

theorem holderOnWith_prodMk
    [PseudoMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace F]
    {s : Set X} {f : X → Y} {g : X → F} {C D r : NNReal}
    (hf : HolderOnWith C r f s) (hg : HolderOnWith D r g s) :
    HolderOnWith (max C D) r (fun x => (f x, g x)) s := by
  intro x hx y hy
  rw [Prod.edist_eq, ENNReal.coe_max, max_mul]
  exact max_le_max (hf x hx y hy) (hg x hx y hy)

theorem equicontinuous_of_locally_holderOnWith
    [PseudoMetricSpace X] [LocallyCompactSpace X] [PseudoMetricSpace Y]
    {ι : Type*} (f : ι → X → Y) {r : NNReal} (hr : 0 < r)
    (hf : ∀ K : Set X, IsCompact K →
      ∃ C : NNReal, ∀ i, HolderOnWith C r (f i) K) :
    Equicontinuous f := by
  intro x
  rcases exists_compact_mem_nhds x with ⟨K, hK, hKmem⟩
  rcases hf K hK with ⟨C, hC⟩
  have hxK : x ∈ K := mem_of_mem_nhds hKmem
  have hequi :=
    (uniformEquicontinuousOn_of_holderOnWith f hr hC).equicontinuousOn x hxK
  unfold EquicontinuousWithinAt at hequi
  unfold EquicontinuousAt
  rwa [nhdsWithin_eq_nhds.mpr hKmem] at hequi

theorem arzela_ascoli_subseq_tendsto_locally_uniformly_of_locally_holderOnWith
    [PseudoMetricSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X]
    [NormedAddCommGroup F] [ProperSpace F]
    (f : Nat → X → F) {r : NNReal} (hr : 0 < r)
    (hholder : ∀ K : Set X, IsCompact K →
      ∃ C : NNReal, ∀ n, HolderOnWith C r (f n) K)
    (hbdd : ∀ x, ∃ M : Real, ∀ n, ‖f n x‖ ≤ M) :
    ∃ (phi : Nat → Nat) (g : X → F),
      StrictMono phi ∧ Continuous g ∧
        ∀ K : Set X, IsCompact K →
          TendstoUniformlyOn (fun n => f (phi n)) g atTop K := by
  have hequi : Equicontinuous f :=
    equicontinuous_of_locally_holderOnWith f hr hholder
  let fc : Nat → C(X, F) := fun n => ⟨f n, hequi.continuous n⟩
  rcases arzela_ascoli_subseq_tendsto_locally_uniformly fc hequi hbdd with
    ⟨phi, g, hphi, hconv⟩
  refine ⟨phi, g, hphi, g.continuous, ?_⟩
  intro K hK
  simpa only [fc] using hconv K hK

theorem arzela_ascoli_subseq_tendsto_locally_uniformly_of_holderWith
    [PseudoMetricSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X]
    [NormedAddCommGroup F] [ProperSpace F]
    (f : Nat → X → F) {C r : NNReal} (hr : 0 < r)
    (hholder : ∀ n, HolderWith C r (f n))
    (hbdd : ∀ x, ∃ M : Real, ∀ n, ‖f n x‖ ≤ M) :
    ∃ (phi : Nat → Nat) (g : X → F),
      StrictMono phi ∧ Continuous g ∧
        ∀ K : Set X, IsCompact K →
          TendstoUniformlyOn (fun n => f (phi n)) g atTop K := by
  exact arzela_ascoli_subseq_tendsto_locally_uniformly_of_locally_holderOnWith
    f hr (fun K _ => ⟨C, fun n => (hholder n).holderOnWith K⟩) hbdd

theorem arzela_ascoli_subseq_tendsto_locally_uniformly_on_of_locally_holderOnWith
    [PseudoMetricSpace X] [NormedAddCommGroup F] [ProperSpace F]
    {U : Set X} [LocallyCompactSpace U] [SigmaCompactSpace U]
    (f : Nat → X → F) {r : NNReal} (hr : 0 < r)
    (hholder : ∀ K : Set U, IsCompact K →
      ∃ C : NNReal, ∀ n,
        HolderOnWith C r (fun x : U => f n (x : X)) K)
    (hbdd : ∀ x ∈ U, ∃ M : Real, ∀ n, ‖f n x‖ ≤ M) :
    ∃ (phi : Nat → Nat) (g : U → F),
      StrictMono phi ∧ Continuous g ∧
        ∀ K : Set U, IsCompact K →
          TendstoUniformlyOn
            (fun n (x : U) => f (phi n) (x : X)) g atTop K := by
  exact arzela_ascoli_subseq_tendsto_locally_uniformly_of_locally_holderOnWith
    (fun n => U.restrict (f n)) hr hholder (fun x => hbdd x x.2)

theorem arzela_ascoli_subseq_tendsto_locally_uniformly_on_of_holderOnWith
    [PseudoMetricSpace X] [NormedAddCommGroup F] [ProperSpace F]
    {U : Set X} [LocallyCompactSpace U] [SigmaCompactSpace U]
    (f : Nat → X → F) {C r : NNReal} (hr : 0 < r)
    (hholder : ∀ n, HolderOnWith C r (f n) U)
    (hbdd : ∀ x ∈ U, ∃ M : Real, ∀ n, ‖f n x‖ ≤ M) :
    ∃ (phi : Nat → Nat) (g : U → F),
      StrictMono phi ∧ Continuous g ∧
        ∀ K : Set U, IsCompact K →
          TendstoUniformlyOn
            (fun n (x : U) => f (phi n) (x : X)) g atTop K := by
  exact arzela_ascoli_subseq_tendsto_locally_uniformly_of_holderWith
    (fun n => U.restrict (f n)) hr
    (fun n => (hholder n).holderWith)
    (fun x => hbdd x x.2)

end DifferentialGeometry.Analysis.Schauder

end
