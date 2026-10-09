import DifferentialGeometry.Geometry.Comparison.PairedPacketLocalization
import Mathlib.Topology.Baire.Lemmas

set_option autoImplicit false

open Set Metric Real
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_dense_isGδ_all_paired_qualities
    {X : Type*} [MetricSpace X] [BaireSpace X] {m : ℕ}
    (hdense : ∀ ε : ℝ, 0 < ε → ∀ O : Set X, IsOpen O → O.Nonempty →
      ∃ q ∈ O, ∃ a b : Fin m → X, PairedComparisonPacket ε {q} a b) :
    ∃ S : Set X, IsGδ S ∧ Dense S ∧
      ∀ q ∈ S, ∀ ε : ℝ, 0 < ε →
        ∃ a b : Fin m → X, PairedComparisonPacket ε {q} a b := by
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let P : ℕ → Set X := fun k => {q | ∃ a b : Fin m → X,
    PairedComparisonPacket (δ k) {q} a b}
  have hδ (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hδle (k : ℕ) : δ k ≤ 1 := by
    dsimp [δ]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hP (k : ℕ) : Dense (interior (P k)) := by
    apply dense_iff_inter_open.mpr
    intro O hO hOne
    obtain ⟨q, hqO, a, b, hp⟩ := hdense (δ k / 2) (half_pos (hδ k)) O hO hOne
    have hsmall : δ k / 2 < Real.pi / 2 := by linarith [hδle k, Real.two_le_pi]
    obtain ⟨V, hVo, hqV, _, hpacket, _⟩ :=
      hp.exists_uniform_nhds (hδ k) (hp.not_mem_anchors (mem_singleton q) hsmall) (hO.mem_nhds hqO)
    have hVP : V ⊆ P k := by
      intro z hz
      refine ⟨a, b, ?_⟩
      constructor
      · intro z' hz' i
        rw [mem_singleton_iff] at hz'
        subst z'
        exact hpacket.opposite z hz i
      · intro z' hz' i j hij u hu v hv
        rw [mem_singleton_iff] at hz'
        subst z'
        exact hpacket.cross z hz i j hij u hu v hv
    exact ⟨q, hqO, (interior_maximal hVP hVo) hqV⟩
  refine ⟨⋂ k, interior (P k), IsGδ.iInter_of_isOpen (fun _ => isOpen_interior),
    dense_iInter_of_isOpen_nat (fun _ => isOpen_interior) hP, ?_⟩
  intro q hq ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hqk : q ∈ interior (P k) := mem_iInter.mp hq k
  obtain ⟨a, b, hp⟩ := interior_subset hqk
  refine ⟨a, b, ?_⟩
  have hδε : δ k < ε := hk
  constructor
  · intro z hz i
    linarith [hp.opposite z hz i]
  · intro z hz i j hij u hu v hv
    linarith [hp.cross z hz i j hij u hu v hv]

end DifferentialGeometry.Geometry.Comparison.Toponogov
