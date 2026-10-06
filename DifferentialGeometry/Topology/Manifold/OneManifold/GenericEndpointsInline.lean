import DifferentialGeometry.Topology.Manifold.OneManifold.CompactOneManifoldChoiceBCF

/-!
# `GenericEndpoints_BCF` written out: inline-hypothesis variants (lane S-CLEAN, suffix `_SCL`)

The integrator's lint review of B-BCF134 G7 (AJY) records that
`GraphAtlas1_BCF.GenericEndpoints_BCF` (`GraphAtlasCoverGenericBCF.lean:61`) is a NAMED `Prop`
used as a hypothesis, namely of
`GraphAtlas1_BCF.exists_halfChart_of_cover_BCF` (`CompactOneManifoldChoiceBCF.lean:88`). It is the
conjunction of the two explicit conditions on the `2n` endpoints of a finite family of closed chart
intervals `[a r, b r]` (chart `c r`):

* `hdist : ∀ r, param (c r) (a r) ≠ param (c r) (b r)` (each interval has two distinct endpoints);
* `hdisj : ∀ r s, r ≠ s → ∀ p ∈ {param (c r) (a r), param (c r) (b r)},
  p ∉ {param (c s) (a s), param (c s) (b s)}` (different intervals share no endpoint).

This file states every theorem that CONSUMES it with these two conditions as explicit hypotheses,
and the producers of it (which return it as a conjunct) with the conjunct split in two. The old
names are untouched.

* `genericEndpoints_iff_inline_SCL`: `At.GenericEndpoints_BCF c a b ↔ hdist-form ∧ hdisj-form`
  (the definitional unfolding, kept as the bridge);
* `exists_halfChart_of_cover_inline_SCL`: the ONLY theorem of the tree with `GenericEndpoints_BCF`
  as a premise (`exists_halfChart_of_cover_BCF`), inline form;
* `exists_enlarge_family_inline_SCL`, `exists_cover_union_generic_inline_SCL`: the two producers
  (`exists_enlarge_family_BCF`, `exists_cover_union_generic_BCF`), inline form.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace DifferentialGeometry.Topology.GraphAtlas1_BCF

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- **`GenericEndpoints_BCF` written out**: the two explicit endpoint conditions. -/
theorem genericEndpoints_iff_inline_SCL {At : GraphAtlas1_BCF ι Bs} {n : ℕ} {c : Fin n → ι}
    {a b : Fin n → ℝ} :
    At.GenericEndpoints_BCF c a b ↔
      (∀ r, At.param (c r) (a r) ≠ At.param (c r) (b r)) ∧
        ∀ r s, r ≠ s → ∀ p ∈ ({At.param (c r) (a r), At.param (c r) (b r)} : Set H),
          p ∉ ({At.param (c s) (a s), At.param (c s) (b s)} : Set H) :=
  Iff.rfl

variable (At : GraphAtlas1_BCF ι Bs)

/-- **Half charts of a generic finite union of closed chart intervals, inline form**: the
endpoint conditions of `GenericEndpoints_BCF` as explicit hypotheses. -/
theorem exists_halfChart_of_cover_inline_SCL {n : ℕ} {c : Fin n → ι} {a b : Fin n → ℝ}
    (hab : ∀ r, a r < b r ∧ Icc (a r) (b r) ⊆ At.dom (c r))
    (hdist : ∀ r, At.param (c r) (a r) ≠ At.param (c r) (b r))
    (hdisj : ∀ r s, r ≠ s → ∀ p ∈ ({At.param (c r) (a r), At.param (c r) (b r)} : Set H),
      p ∉ ({At.param (c s) (a s), At.param (c s) (b s)} : Set H))
    {y : H} (hy : y ∈ ⋃ r, At.param (c r) '' Icc (a r) (b r)) :
    ∃ d : HalfChart_BCF Bs (⋃ r, At.param (c r) '' Icc (a r) (b r)), y ∈ d.O :=
  At.exists_halfChart_of_cover_BCF hab ⟨hdist, hdisj⟩ hy

/-- **Enlarging a finite family, inline form**: endpoints outside the finite set `G`, pairwise
distinct (the two conditions of `GenericEndpoints_BCF` returned separately). -/
theorem exists_enlarge_family_inline_SCL {G : Set H} (hG : G.Finite) (n : ℕ) (c : Fin n → ι)
    (a b : Fin n → ℝ) (hab : ∀ r, a r < b r ∧ Icc (a r) (b r) ⊆ At.dom (c r)) :
    ∃ a' b' : Fin n → ℝ, (∀ r, a' r < a r ∧ b r < b' r ∧ Icc (a' r) (b' r) ⊆ At.dom (c r)) ∧
      (∀ r, At.param (c r) (a' r) ∉ G ∧ At.param (c r) (b' r) ∉ G) ∧
      (∀ r, At.param (c r) (a' r) ≠ At.param (c r) (b' r)) ∧
      ∀ r s, r ≠ s → ∀ p ∈ ({At.param (c r) (a' r), At.param (c r) (b' r)} : Set H),
        p ∉ ({At.param (c s) (a' s), At.param (c s) (b' s)} : Set H) := by
  obtain ⟨a', b', h1, h2, h3, h4⟩ := At.exists_enlarge_family_BCF hG n c a b hab
  exact ⟨a', b', h1, h2, h3, h4⟩

/-- **(K-a) with generic endpoints, inline form**: the cover of `exists_cover_union_generic_BCF`
with the endpoint conditions returned separately. -/
theorem exists_cover_union_generic_inline_SCL {Kset Fset Dset : Set H} (hK : IsCompact Kset)
    (hKB : Kset ⊆ Bs) (hF : Fset.Finite)
    (hDreg : Dset ⊆ closure (Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs)))
    (hKfront : Dset \ Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs) ⊆ Kset) :
    ∃ (n : ℕ) (c : Fin n → ι) (a b : Fin n → ℝ),
      (∀ r, a r < b r ∧ Icc (a r) (b r) ⊆ At.dom (c r) ∧ At.param (c r) (a r) ∉ Fset ∧
        At.param (c r) (b r) ∉ Fset) ∧
      (∀ r, At.param (c r) (a r) ≠ At.param (c r) (b r)) ∧
      (∀ r s, r ≠ s → ∀ p ∈ ({At.param (c r) (a r), At.param (c r) (b r)} : Set H),
        p ∉ ({At.param (c s) (a s), At.param (c s) (b s)} : Set H)) ∧
      IsCompact (⋃ r, At.param (c r) '' Icc (a r) (b r)) ∧
      (⋃ r, At.param (c r) '' Icc (a r) (b r)) ⊆ Bs ∧
      Kset ⊆ Subtype.val '' interior
        (Subtype.val ⁻¹' (⋃ r, At.param (c r) '' Icc (a r) (b r)) : Set Bs) ∧
      (⋃ r, At.param (c r) '' Icc (a r) (b r)) ∩ Dset ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' ((⋃ r, At.param (c r) '' Icc (a r) (b r)) ∩ Dset) : Set Bs)) := by
  obtain ⟨n, c, a, b, hab, ⟨hdist, hdisj⟩, h3, h4, h5, h6⟩ :=
    At.exists_cover_union_generic_BCF hK hKB hF hDreg hKfront
  exact ⟨n, c, a, b, hab, hdist, hdisj, h3, h4, h5, h6⟩

end DifferentialGeometry.Topology.GraphAtlas1_BCF
