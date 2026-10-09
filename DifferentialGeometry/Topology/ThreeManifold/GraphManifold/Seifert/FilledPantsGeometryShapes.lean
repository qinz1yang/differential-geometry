import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Blocks

/-!
# The two shapes of a filled pants block with negative orbifold Euler characteristic

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §0).
Seifert data with `k = 3`, at least one port, at least one filling and `orbChi < 0` are either
the one-cone family (two ports, one cone `(p, q)`) or the two-cone family (one port, two cones
with `(p₁, p₂) ≠ (2, 2)`); in both there is no normal filling. This is the public form of the case
split behind `orbChi_eq_zero_iff_of_open` (`Seifert/Data.lean`), stated with the lists themselves so
that the assembly can rewrite `d` into `oneConeData` or into an explicit two-cone datum.
-/

set_option autoImplicit false

namespace GC.Seifert

namespace SeifertData

theorem filledPants_cases (d : SeifertData) (hk : d.k = 3) (hport : 0 < d.ports)
    (hχ : d.orbChi < 0) (hfill : 0 < d.fillingCount) :
    (d.ports = 2 ∧ ∃ p : ℕ, ∃ q : ℤ, d.cones = [(p, q)] ∧ d.normals = []) ∨
      (d.ports = 1 ∧ ∃ p₁ : ℕ, ∃ q₁ : ℤ, ∃ p₂ : ℕ, ∃ q₂ : ℤ,
        d.cones = [(p₁, q₁), (p₂, q₂)] ∧ d.normals = [] ∧ ¬ (p₁ = 2 ∧ p₂ = 2)) := by
  have hsum := d.ports_add_length_add_length
  have hfill' : 0 < d.cones.length + d.normals.length := hfill
  rw [hk] at hsum
  rcases hcs : d.cones with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    rcases hns : d.normals with _ | ⟨n, _ | ⟨n', l'⟩⟩ <;>
    simp only [hcs, hns, List.length_nil, List.length_cons] at hsum hfill' <;>
    simp only [orbChi, hcs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hχ
  · omega
  · have hp : d.ports = 2 := by omega
    rw [hp] at hχ
    norm_num at hχ
  · have hp : d.ports = 1 := by omega
    rw [hp] at hχ
    norm_num at hχ
  · have hp : d.ports = 2 := by omega
    exact Or.inl ⟨hp, a.1, a.2, rfl, rfl⟩
  · have hp : d.ports = 1 := by omega
    have ha : (0 : ℚ) ≤ 1 / (a.1 : ℚ) := by positivity
    rw [hp] at hχ
    push_cast at hχ
    linarith
  · omega
  · have hp : d.ports = 1 := by omega
    refine Or.inr ⟨hp, a.1, a.2, b.1, b.2, rfl, rfl, fun h => ?_⟩
    rw [hp, h.1, h.2] at hχ
    norm_num at hχ
  · omega
  · omega
  · omega
  · omega
  · omega

end SeifertData

end GC.Seifert
