import DifferentialGeometry.Topology.Manifold.LocalSubmersionSlices
import DifferentialGeometry.Topology.Manifold.LocalSliceManifold
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Manifold
namespace DifferentialGeometry.Topology.Manifold
universe u v

theorem exists_local_zero_set_manifold
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (s : Set H) (n k : ℕ) (hdim : ∀ _ : s, Module.finrank ℝ H = n+k)
    (F : s → Type v)
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]
    [∀ x, FiniteDimensional ℝ (F x)]
    (hF : ∀ x, Module.finrank ℝ (F x) = n)
    (U : s → Set H) (hU : ∀ x, IsOpen (U x)) (hx : ∀ x : s, (x : H) ∈ U x)
    (f : ∀ x : s, H → F x)
    (hf : ∀ x, ContDiffOn ℝ ∞ (f x) (U x))
    (hsurj : ∀ x : s, Function.Surjective (fderiv ℝ (f x) (x : H)))
    (hzero : ∀ x : s, ∀ y ∈ U x, y ∈ s ↔ f x y = 0) :
    ∃ cs : ChartedSpace (Fin k → ℝ) s,
      let _ := cs
      IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ s ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ,H) ∞ (Subtype.val : s → H) := by
  obtain ⟨e,he⟩ := exists_local_zero_slice_charts s n k hdim F hF U hU hx f hf hsurj hzero
  let a : s → (Fin n → ℝ) := fun _ => 0
  have hxe := fun x => (he x).1
  have hse := fun x => (he x).2.2.2.2
  have hce := fun x => (he x).2.2.1
  have hci := fun x => (he x).2.2.2.1
  let cs := localSliceChartedSpace s e a hxe hse
  let _ := cs
  have hM : IsManifold 𝓘(ℝ,Fin k → ℝ) ∞ s := localSliceIsManifold s e a hxe hse hce hci
  let _ := hM
  have hc := contMDiff_localSliceInclusion s e a hxe hse hci
  have hd := mfderiv_localSliceInclusion_injective s e a hxe hse hce hci
  exact ⟨cs,hM,⟨isImmersion_of_injective_mfderiv (by simp) hc hd,
    _root_.Topology.IsEmbedding.subtypeVal⟩⟩

end DifferentialGeometry.Topology.Manifold
