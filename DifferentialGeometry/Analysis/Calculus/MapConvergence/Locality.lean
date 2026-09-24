import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sets.Opens

section

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem MapCPConvergenceOn.union {K L : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F}
    (hK : MapCPConvergenceOn K p Φ Φinf)
    (hL : MapCPConvergenceOn L p Φ Φinf) :
    MapCPConvergenceOn (K ∪ L) p Φ Φinf := by
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := hK ε hε
  obtain ⟨k₁, hk₁⟩ := hL ε hε
  refine ⟨max k₀ k₁, fun k hk r hr x hx => ?_⟩
  rcases hx with hx | hx
  · exact hk₀ k ((le_max_left _ _).trans hk) r hr x hx
  · exact hk₁ k ((le_max_right _ _).trans hk) r hr x hx

theorem MapCInfConvergenceOnCompacts.of_nhds {U : Set E}
    {Φ : ℕ → E → F} {Φinf : E → F}
    (h : ∀ x ∈ U, ∃ V ∈ 𝓝 x, MapCInfConvergenceOnCompacts V Φ Φinf) :
    MapCInfConvergenceOnCompacts U Φ Φinf := by
  intro K hK hKU p
  apply hK.induction_on (p := fun L => MapCPConvergenceOn L p Φ Φinf)
  · intro ε hε
    exact ⟨0, fun _ _ _ _ _ hx => hx.elim⟩
  · intro s t hst ht
    exact ht.mono_set hst
  · intro s t hs ht
    exact hs.union ht
  · intro x hx
    obtain ⟨V, hV, hconv⟩ := h x (hKU hx)
    obtain ⟨T, hT, hclosed, hTV⟩ := exists_mem_nhds_isClosed_subset hV
    exact ⟨K ∩ T,
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hT),
      hconv (K ∩ T) (hK.inter_right hclosed) (Set.inter_subset_right.trans hTV) p⟩

end DifferentialGeometry.CheegerGromovCompactness

end

section

noncomputable section
open Set Filter
open scoped Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem MapCInfConvergenceOnCompacts.of_locally_eventually_eqOn_compact
    {U : Set E} (hU : IsOpen U) {f : ℕ → E → F} {fInf : E → F}
    (hlocal : ∀ x ∈ U, ∃ (W : Set E) (g : ℕ → E → F),
      IsOpen W ∧ x ∈ W ∧ MapCInfConvergenceOnCompacts W g fInf ∧
      ∀ K : Set E, IsCompact K → K ⊆ U ∩ W → ∀ᶠ k in atTop, EqOn (f k) (g k) K) :
    MapCInfConvergenceOnCompacts U f fInf := by
  apply MapCInfConvergenceOnCompacts.of_nhds
  intro x hx
  obtain ⟨W, g, hW, hxW, hg, hagree⟩ := hlocal x hx
  obtain ⟨S, hS, hxS, hSUW, hScompact⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_singleton (x := x))
      (hU.inter hW) (singleton_subset_iff.mpr ⟨hx, hxW⟩)
  have hconvS : MapCInfConvergenceOnCompacts S g fInf :=
    fun K hK hKS => hg K hK (fun z hz => (hSUW (subset_closure (hKS hz))).2)
  refine ⟨S, hS.mem_nhds (hxS (mem_singleton x)), ?_⟩
  apply hconvS.congr_eventually hS
  · exact (hagree (closure S) hScompact hSUW).mono fun k hk z hz => hk (subset_closure hz)
  · exact Set.eqOn_refl _ _

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E F Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace Q] {M : ℕ → Type*}

theorem MapCInfConvergenceOnCompacts.of_compact_agreement_in_open_coordinates
    (U : TopologicalSpace.Opens E) (inc : U → Q)
    (hinj : Function.Injective inc) (hinc : Continuous inc)
    (V : Set Q) (hV : IsOpen V)
    (W : U → Set E) (hW : ∀ a, IsOpen (W a)) (hcenter : ∀ a : U, (a : E) ∈ W a)
    (f : U → ∀ k, E → M k) (b : ∀ k, M k) (c : ∀ k, M k → F)
    (Fglobal : ∀ k, Q → M k) (fInf : E → F)
    (hconv : ∀ a, MapCInfConvergenceOnCompacts (W a)
      (fun k z => c k (f a k z)) fInf)
    (hagree : ∀ a (L : Set Q), IsCompact L →
      L ⊆ V ∩ (inc '' (Subtype.val ⁻¹' W a)) →
      ∀ᶠ k in atTop, EqOn (Fglobal k)
        (Function.extend inc (fun z : U => f a k z) (fun _ => b k)) L) :
    MapCInfConvergenceOnCompacts (Subtype.val '' (inc ⁻¹' V))
      (fun k z => @dite F (z ∈ U) (Classical.propDecidable _)
        (fun hz => c k (Fglobal k (inc ⟨z, hz⟩))) (fun _ => 0)) fInf := by
  classical
  have hD : IsOpen (Subtype.val '' (inc ⁻¹' V)) :=
    U.isOpen.isOpenMap_subtype_val _ (hV.preimage hinc)
  apply MapCInfConvergenceOnCompacts.of_locally_eventually_eqOn_compact hD
  rintro x ⟨a, ha, rfl⟩
  refine ⟨W a, fun k z => c k (f a k z), hW a, hcenter a, hconv a, ?_⟩
  intro K hK hKD
  have hKU : K ⊆ (U : Set E) := by
    intro z hz
    obtain ⟨y, _, hy⟩ := (hKD hz).1
    exact hy ▸ y.property
  have hKsub : IsCompact ((Subtype.val : U → E) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKU)
  have hL : inc '' ((Subtype.val : U → E) ⁻¹' K) ⊆
      V ∩ (inc '' (Subtype.val ⁻¹' W a)) := by
    rintro q ⟨z, hz, rfl⟩
    obtain ⟨y, hy, heq⟩ := (hKD hz).1
    have hyz : y = z := Subtype.ext heq
    exact ⟨hyz ▸ hy, z, (hKD hz).2, rfl⟩
  filter_upwards [hagree a _ (hKsub.image hinc) hL] with k hk z hz
  dsimp only
  split_ifs with hzU
  · rw [hk ⟨⟨z, hzU⟩, hz, rfl⟩, hinj.extend_apply]
  · exact (hzU (hKU hz)).elim

end DifferentialGeometry.CheegerGromovCompactness

end

end
