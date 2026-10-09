import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# A globally smooth representative of a radial function near its band

Blueprint LC30 (master207A:21214) gives a radial function `η` that is smooth only on an open
set `W` containing the band `K = η⁻¹[a,b]` (it need not be smooth near the base point).
The regular-level, sublevel and flow machinery of this repository is stated for globally
smooth functions. `exists_contMDiff_eqOn_band` produces a globally smooth `f` that agrees with
`η` on an open neighbourhood of `K` and lies below `a` (above `b`) exactly where `η` does. Then
`f` and `η` have the same band, the same levels and the same sublevels and strict sublevels at
every level `t ∈ [a,b]` (`band_le_iff`, `band_lt_iff`, `band_eq_iff`, `band_mem_Icc_iff`).

The construction is `f = θ η + (1 - θ) σ` with a smooth bump `θ` equal to one near `K` and
supported in `W`, and a smooth Urysohn function `σ` equal to `a - 1` on `{η ≤ a}` and to
`b + 1` on `{η ≥ b}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

section Sets

variable {X : Type*} {η f : X → ℝ} {O : Set X} {a b : ℝ}

theorem band_mem_Icc_iff (hEq : EqOn f η O) (hKO : η ⁻¹' Icc a b ⊆ O)
    (hlo : ∀ x, η x < a → f x < a) (hhi : ∀ x, b < η x → b < f x) {x : X} :
    f x ∈ Icc a b ↔ η x ∈ Icc a b := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · by_contra h
      exact absurd hx.1 (not_le.mpr (hlo x (lt_of_not_ge h)))
    · by_contra h
      exact absurd hx.2 (not_le.mpr (hhi x (lt_of_not_ge h)))
  · intro hx
    rw [hEq (hKO hx)]
    exact hx

theorem band_le_iff (hEq : EqOn f η O) (hKO : η ⁻¹' Icc a b ⊆ O)
    (hlo : ∀ x, η x < a → f x < a) (hhi : ∀ x, b < η x → b < f x) {t : ℝ}
    (ht : t ∈ Icc a b) {x : X} : f x ≤ t ↔ η x ≤ t := by
  by_cases hxa : η x < a
  · exact ⟨fun _ => hxa.le.trans ht.1, fun _ => (hlo x hxa).le.trans ht.1⟩
  · by_cases hxb : b < η x
    · exact ⟨fun h => absurd (ht.2.trans_lt (hhi x hxb)) (not_lt.mpr h),
        fun h => absurd (ht.2.trans_lt hxb) (not_lt.mpr h)⟩
    · rw [hEq (hKO ⟨not_lt.mp hxa, not_lt.mp hxb⟩)]

theorem band_lt_iff (hEq : EqOn f η O) (hKO : η ⁻¹' Icc a b ⊆ O)
    (hlo : ∀ x, η x < a → f x < a) (hhi : ∀ x, b < η x → b < f x) {t : ℝ}
    (ht : t ∈ Icc a b) {x : X} : f x < t ↔ η x < t := by
  by_cases hxa : η x < a
  · exact ⟨fun _ => hxa.trans_le ht.1, fun _ => (hlo x hxa).trans_le ht.1⟩
  · by_cases hxb : b < η x
    · exact ⟨fun h => absurd (ht.2.trans_lt (hhi x hxb)) (not_lt.mpr h.le),
        fun h => absurd (ht.2.trans_lt hxb) (not_lt.mpr h.le)⟩
    · rw [hEq (hKO ⟨not_lt.mp hxa, not_lt.mp hxb⟩)]

theorem band_eq_iff (hEq : EqOn f η O) (hKO : η ⁻¹' Icc a b ⊆ O)
    (hlo : ∀ x, η x < a → f x < a) (hhi : ∀ x, b < η x → b < f x) {t : ℝ}
    (ht : t ∈ Icc a b) {x : X} : f x = t ↔ η x = t := by
  rw [le_antisymm_iff, le_antisymm_iff, band_le_iff hEq hKO hlo hhi ht, ← not_lt, ← not_lt,
    band_lt_iff hEq hKO hlo hhi ht]
  exact and_congr_right fun _ => not_lt

end Sets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Globalization of a function smooth near its compact band `η⁻¹[a,b]`. -/
theorem exists_contMDiff_eqOn_band {η : M → ℝ} (hη : Continuous η) {W : Set M}
    (hW : IsOpen W) (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {a b : ℝ} (hab : a < b)
    (hK : IsCompact (η ⁻¹' Icc a b)) (hKW : η ⁻¹' Icc a b ⊆ W) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      (∃ O : Set M, IsOpen O ∧ η ⁻¹' Icc a b ⊆ O ∧ O ⊆ W ∧ EqOn f η O) ∧
      (∀ x, η x < a → f x < a) ∧ (∀ x, b < η x → b < f x) := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨U, hUo, hKU, hUW, -⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  obtain ⟨θ, hθ1, hθ0, hθI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior I
    (n := (⊤ : ℕ∞)) hK.isClosed (hKU.trans_eq hUo.interior_eq.symm)
  obtain ⟨O₁, hO₁o, hKO₁, hO₁⟩ := mem_nhdsSet_iff_exists.mp hθ1
  have hs : IsClosed {x : M | η x ≤ a} := isClosed_le hη continuous_const
  have ht : IsClosed {x : M | b ≤ η x} := isClosed_le continuous_const hη
  have hd : Disjoint {x : M | η x ≤ a} {x : M | b ≤ η x} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd (hx'.trans hx) (not_le.mpr hab)
  obtain ⟨ψ, hψ0, hψ1, hψI⟩ := exists_contMDiffMap_zero_one_of_isClosed I
    (n := (⊤ : ℕ∞)) hs ht hd
  let σ : M → ℝ := fun x => (a - 1) + (b - a + 2) * ψ x
  let f : M → ℝ := fun x => θ x * η x + (1 - θ x) * σ x
  have hθη : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => θ x * η x) := by
    intro x
    by_cases hx : x ∈ W
    · exact (θ.contMDiff x).mul (hηW.contMDiffAt (hW.mem_nhds hx))
    · have hxU : x ∉ closure U := fun h => hx (hUW h)
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxU] with y hy
      have hyU : y ∉ U := fun h => hy (subset_closure h)
      rw [hθ0 y hyU, zero_mul]
  have hσ : ContMDiff I 𝓘(ℝ, ℝ) ∞ σ :=
    contMDiff_const.add (contMDiff_const.mul ψ.contMDiff)
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    hθη.add ((contMDiff_const.sub θ.contMDiff).mul hσ)
  refine ⟨f, hf, ⟨O₁ ∩ U, hO₁o.inter hUo, subset_inter hKO₁ hKU,
    inter_subset_right.trans (subset_closure.trans hUW), ?_⟩, ?_, ?_⟩
  · intro x hx
    change θ x * η x + (1 - θ x) * σ x = η x
    rw [show θ x = 1 from hO₁ hx.1]
    ring
  · intro x hx
    have hσx : σ x = a - 1 := by
      change (a - 1) + (b - a + 2) * ψ x = a - 1
      rw [hψ0 (show x ∈ {x : M | η x ≤ a} from hx.le), Pi.zero_apply, mul_zero, add_zero]
    change θ x * η x + (1 - θ x) * σ x < a
    rw [hσx]
    obtain ⟨h0, h1⟩ := hθI x
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h]
      linarith
    · nlinarith [mul_lt_mul_of_pos_left hx h]
  · intro x hx
    have hσx : σ x = b + 1 := by
      change (a - 1) + (b - a + 2) * ψ x = b + 1
      rw [hψ1 (show x ∈ {x : M | b ≤ η x} from hx.le), Pi.one_apply]
      ring
    change b < θ x * η x + (1 - θ x) * σ x
    rw [hσx]
    obtain ⟨h0, h1⟩ := hθI x
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h]
      linarith
    · nlinarith [mul_lt_mul_of_pos_left hx h]

end DifferentialGeometry.Geometry.Collapse
