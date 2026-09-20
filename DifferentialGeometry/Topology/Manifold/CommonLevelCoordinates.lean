/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.LevelChartTransition

/-! Common height coordinates matching two end charts at different heights. -/

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H}

theorem exists_common_level_coordinates
    (c : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞)
    (d : Bool → PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞) {f : M → ℝ}
    (hc : ∀ y ∈ c.source, (c y).im = f y)
    (hd : ∀ i y, y ∈ (d i).source → (d i y).im = f y)
    (x : Bool → M) (hxc : ∀ i, x i ∈ c.source) (hxd : ∀ i, x i ∈ (d i).source)
    (horder : f (x true) < f (x false))
    (O : Bool → Set M) (hO : ∀ i, IsOpen (O i)) (hxO : ∀ i, x i ∈ O i) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      (∀ z, (D z).im = z.im) ∧
      let C := c.trans D.toPartialDiffeomorph
      C.source = c.source ∧
      ∀ i, ∃ (R : ℂ ≃L[ℝ] ℂ) (Φ : ℝ → Diffeomorph I I M M ∞),
        (∀ z, (R z).im = z.im) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => Φ z.1 z.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ p y, f (Φ p y) = f y) ∧ (∀ p, Φ p (x i) = x i) ∧
        (∃ V : Set M, IsOpen V ∧ x i ∈ V ∧ V ⊆ c.source ∩ (d i).source ∩ O i ∧
          ∀ y ∈ V, (Φ 1).symm y ∈ (d i).source ∧ R (d i ((Φ 1).symm y)) = C y) ∧
        ∃ K : Set M, IsCompact K ∧ K ⊆ c.source ∩ (d i).source ∩ O i ∧
          ∀ p y, y ∉ K → Φ p y = y ∧ (Φ p).symm y = y := by
  classical
  have htrans (i : Bool) :=
    exists_positive_level_transition c (d i) hc (hd i) (hxc i) (hxd i) (hO i) (hxO i)
  choose a b k R ha hRi Φ hΦ hΦi hΦ0 hΦf hΦx hmatch K hK hKO hfix using htrans
  let l := (2 * f (x true) + f (x false)) / 3
  let u := (f (x true) + 2 * f (x false)) / 3
  have hlu : l < u := by dsimp [l, u]; linarith
  obtain ⟨D, hDi, hDlo, hDhi, _⟩ :=
    exists_diffeomorph_interpolating_fiber_affine hlu (ha true) (ha false)
      (b true) (b false) (k true) (k false)
  let Q := Complex.equivRealProdCLM.toDiffeomorph
  let DC := (Q.trans D).trans Q.symm
  have hDCi (z : ℂ) : (DC z).im = z.im := hDi (Complex.equivRealProdCLM z)
  let B (i : Bool) : Set ℂ := if i then {z | z.im < l} else {z | u < z.im}
  have hB (i : Bool) : IsOpen (B i) := by
    cases i
    · exact isOpen_lt continuous_const Complex.continuous_im
    · exact isOpen_lt Complex.continuous_im continuous_const
  have hxB (i : Bool) : c (x i) ∈ B i := by
    cases i
    · change u < (c (x false)).im
      rw [hc _ (hxc false)]
      dsimp [u]
      linarith
    · change (c (x true)).im < l
      rw [hc _ (hxc true)]
      dsimp [l]
      linarith
  have hDform (i : Bool) (z : ℂ) (hz : z ∈ B i) :
      DC z = ⟨a i * z.re + b i * z.im + k i, z.im⟩ := by
    apply Complex.equivRealProdCLM.injective
    change D (z.re, z.im) = (a i * z.re + b i * z.im + k i, z.im)
    cases i
    · exact hDhi (z.re, z.im) hz.le
    · exact hDlo (z.re, z.im) hz.le
  refine ⟨DC, hDCi, ?_, ?_⟩
  · ext y
    exact and_iff_left (mem_univ (c y))
  · intro i
    have hnear : ∀ᶠ y in 𝓝 (x i),
        y ∈ c.source ∩ (d i).source ∩ O i ∧ c y ∈ B i ∧
          (Φ i 1).symm y ∈ (d i).source ∧
            R i (d i ((Φ i 1).symm y)) =
              ⟨a i * (c y).re + b i * (c y).im + k i, (c y).im⟩ := by
      have ht := (c.contMDiffOn.contMDiffAt (c.open_source.mem_nhds (hxc i))).continuousAt
      filter_upwards [hmatch i, c.open_source.mem_nhds (hxc i),
        (d i).open_source.mem_nhds (hxd i), (hO i).mem_nhds (hxO i),
        ht.preimage_mem_nhds ((hB i).mem_nhds (hxB i))] with y hm hyc hyd hyO hyB
      exact ⟨⟨⟨hyc, hyd⟩, hyO⟩, hyB, hm⟩
    obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hnear
    refine ⟨R i, Φ i, hRi i, hΦ i, hΦi i, hΦ0 i, hΦf i, hΦx i,
      ⟨V, hV, hxV, fun y hy => (hVsub hy).1, ?_⟩, K i, hK i, hKO i, hfix i⟩
    intro y hy
    have hh := hVsub hy
    exact ⟨hh.2.2.1, hh.2.2.2.trans (hDform i (c y) hh.2.1).symm⟩

end DifferentialGeometry.Topology.Manifold
