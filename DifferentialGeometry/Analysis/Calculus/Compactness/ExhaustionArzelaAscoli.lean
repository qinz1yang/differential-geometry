import DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section

namespace DifferentialGeometry.Analysis

open Filter Set
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem exists_subseq_tendstoLocallyUniformly_of_eventually_equicontinuous
    (K : CompactExhaustion X) (f : ℕ → X → ℝ)
    (hequi : ∀ n, ∃ N : ℕ,
      Equicontinuous (fun k (x : K n) => f (N + k) x))
    (hbdd : ∀ n, ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K n, |f k x| ≤ C) :
    ∃ (phi : ℕ → ℕ) (g : C(X, ℝ)), StrictMono phi ∧
      TendstoLocallyUniformly (fun k => f (phi k)) g atTop := by
  classical
  have htail : ∀ n, ∃ (N : ℕ) (C : ℝ),
      Equicontinuous (fun k (x : K n) => f (N + k) x) ∧
        ∀ k (x : K n), |f (N + k) x| ≤ C := by
    intro n
    obtain ⟨N, hN⟩ := hequi n
    obtain ⟨C, hC⟩ := hbdd n
    obtain ⟨N', hN'⟩ := eventually_atTop.mp hC
    refine ⟨N + N', C, ?_, ?_⟩
    · simpa only [Function.comp_def, Nat.add_assoc] using
        hN.comp (fun k => N' + k)
    · intro k x
      exact hN' (N + N' + k) (by omega) x x.property
  choose N C hN hC using htail
  let (n : ℕ) : CompactSpace (K n) := isCompact_iff_compactSpace.mp (K.isCompact n)
  let (n : ℕ) : LocallyCompactSpace (K n) := by infer_instance
  let F : ∀ n, ℕ → C(K n, ℝ) := fun n k =>
    ⟨fun x => f (N n + k) x, (hN n).continuous k⟩
  let Q : ∀ n, Set C(K n, ℝ) := fun n => closure (range (F n))
  have hQ (n : ℕ) : IsCompact (Q n) := by
    apply CheegerGromovCompactness.arzelaAscoli_isCompact_closure (F n) (hN n)
    intro x
    refine ⟨C n, fun k => ?_⟩
    change ‖f (N n + k) x‖ ≤ C n
    simpa only [Real.norm_eq_abs] using hC n k x
  let (n : ℕ) : CompactSpace (Q n) := isCompact_iff_compactSpace.mp (hQ n)
  let seq : ℕ → ∀ n, Q n := fun k n =>
    ⟨F n (k - N n), subset_closure ⟨k - N n, rfl⟩⟩
  obtain ⟨a, _, phi, hphi, ha⟩ :=
    (isCompact_univ : IsCompact (univ : Set (∀ n, Q n))).tendsto_subseq
      (x := seq) (fun _ => mem_univ _)
  have hconv (n : ℕ) :
      TendstoUniformly (fun k (x : K n) => f (phi k) x) (a n).val atTop := by
    have hcoord : Tendsto (fun k => (seq (phi k) n).val) atTop (𝓝 (a n).val) :=
      (continuous_subtype_val.tendsto (a n)).comp ((tendsto_pi_nhds.mp ha) n)
    have hUniform := ContinuousMap.tendsto_iff_tendstoUniformly.mp hcoord
    have heq : (fun k (x : K n) => (seq (phi k) n).val x) =ᶠ[atTop]
        (fun k (x : K n) => f (phi k) x) := by
      filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop (N n))] with k hk
      funext x
      change f (N n + (phi k - N n)) x = f (phi k) x
      have hidx : N n + (phi k - N n) = phi k := by omega
      rw [hidx]
    exact (tendstoUniformly_congr heq).mp hUniform
  let g : X → ℝ := fun x => (a (K.find x)).val ⟨x, K.mem_find x⟩
  have hg (n : ℕ) (x : K n) : g x = (a n).val x := by
    exact tendsto_nhds_unique
      ((hconv (K.find x)).tendsto_at ⟨x, K.mem_find x⟩)
      ((hconv n).tendsto_at x)
  have hrestrict (n : ℕ) : (fun x : K n => g x) = (a n).val := funext (hg n)
  have hgcont (n : ℕ) : ContinuousOn g (K n) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : K n => g x)
    rw [hrestrict n]
    exact (a n).val.continuous
  have hcontinuous : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem_nhds x
    exact (hgcont n).continuousAt hn
  have huniform (n : ℕ) : TendstoUniformlyOn (fun k => f (phi k)) g atTop (K n) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    change TendstoUniformly (fun k (x : K n) => f (phi k) x)
      (fun x : K n => g x) atTop
    rw [hrestrict n]
    exact hconv n
  refine ⟨phi, ⟨g, hcontinuous⟩, hphi, ?_⟩
  apply tendstoLocallyUniformly_of_forall_exists_nhds
  intro x
  obtain ⟨n, hn⟩ := K.exists_mem_nhds x
  exact ⟨K n, hn, huniform n⟩

end DifferentialGeometry.Analysis
