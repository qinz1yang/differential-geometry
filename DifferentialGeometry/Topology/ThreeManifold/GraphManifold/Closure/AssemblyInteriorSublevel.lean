import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySublevelPieces

/-!
# Chapter-14 assembly, bridges B1-interior and B1-complement

The defining function `f` lives only on an open set `U ⊆ int W`, where its level `{f = c}` is
regular, and the sublevel `K = {x ∈ U | f x ≤ c}` is compact. A smooth cutoff `χ` equal to `1`
near `K` and to `0` near `W \ U` gives the global function `F = χ f + (1 − χ)(c + 1)`, smooth on `W`,
equal to `f` near `K`, with `{F ≤ c} = K`, `{F < c} = {x ∈ U | f x < c}` and `{F = c} = {x ∈ U | f x = c}`
(`exists_regular_extension_of_interior_sublevel`). B1-relative
(`exists_pieces_of_regular_sublevel`) applied to `F` gives B1-interior, and applied to `2c − F` gives
B1-complement: the closed complement `W \ {x ∈ U | f x < c}`, whose boundary is `∂W ∪ {f = c}`.

Both are the frozen statements of the assembly design
(`docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`, §4 row §2).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry GC.Endpoint Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **The cutoff extension.** A defining function on an open subset of the interior with a regular
level and a compact sublevel extends, near the sublevel, to a smooth function on all of `W` with
the same sublevel, strict sublevel and level. -/
theorem exists_regular_extension_of_interior_sublevel (W : CompactCarrier.{u})
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    (hreg : ∀ x ∈ U, f x = c → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
    (hK : IsCompact {x | x ∈ U ∧ f x ≤ c}) :
    ∃ F : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ x, F x = c → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0) ∧
      (∀ x, F x = c → x ∈ W.interior) ∧
      (∀ x, F x ≤ c ↔ (x ∈ U ∧ f x ≤ c)) ∧
      (∀ x, F x < c ↔ (x ∈ U ∧ f x < c)) ∧
      ∀ x, F x = c ↔ (x ∈ U ∧ f x = c) := by
  have hd : Disjoint (U : Set W.Carrier)ᶜ {x | x ∈ U ∧ f x ≤ c} :=
    disjoint_left.mpr fun x hx hx' => hx hx'.1
  obtain ⟨χ, hχ0, hχ1, hχI⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed W.model (n := ⊤)
    U.isOpen.isClosed_compl hK.isClosed hd
  let F : W.Carrier → ℝ := fun x => χ x * f x + (1 - χ x) * (c + 1)
  have hχK : ∀ x, x ∈ U → f x ≤ c → ∀ᶠ y in 𝓝 x, χ y = 1 := fun x hxU hfx =>
    hχ1.filter_mono (nhds_le_nhdsSet (show x ∈ {x | x ∈ U ∧ f x ≤ c} from ⟨hxU, hfx⟩))
  have hFK : ∀ x, x ∈ U → f x ≤ c → F =ᶠ[𝓝 x] f := fun x hxU hfx =>
    (hχK x hxU hfx).mono fun y hy => by simp only [F, hy, one_mul, sub_self, zero_mul, add_zero]
  have hFeqK : ∀ x, x ∈ U → f x ≤ c → F x = f x := fun x hxU hfx => (hFK x hxU hfx).self_of_nhds
  have hmemK : ∀ x, F x ≤ c → x ∈ U ∧ f x ≤ c := by
    intro x hx
    by_contra h
    apply (not_lt.mpr hx)
    by_cases hxU : x ∈ U
    · have hfx : c < f x := lt_of_not_ge fun h' => h ⟨hxU, h'⟩
      obtain ⟨h0, h1⟩ := hχI x
      rcases h1.lt_or_eq with hlt | heq
      · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hfx.le)]
      · simp only [F, heq, one_mul, sub_self, zero_mul, add_zero]
        exact hfx
    · have h0 : χ x = 0 := hχ0.self_of_nhdsSet x hxU
      simp only [F, h0, zero_mul, sub_zero, one_mul, zero_add]
      linarith
  have hle : ∀ x, F x ≤ c ↔ (x ∈ U ∧ f x ≤ c) := fun x =>
    ⟨hmemK x, fun h => (hFeqK x h.1 h.2).symm ▸ h.2⟩
  have hsm : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun x => χ x * f x) := by
    intro x
    by_cases hxU : x ∈ U
    · exact (χ.contMDiff x).mul (hf.contMDiffAt (U.isOpen.mem_nhds hxU))
    · have hloc : (fun _ : W.Carrier => (0 : ℝ)) =ᶠ[𝓝 x] fun y => χ y * f y :=
        (hχ0.filter_mono (nhds_le_nhdsSet hxU)).mono fun y hy => by
          simp only [hy, zero_mul]
      exact contMDiffAt_const.congr_of_eventuallyEq hloc.symm
  have hFs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F :=
    hsm.add ((contMDiff_const.sub χ.contMDiff).mul contMDiff_const)
  refine ⟨F, hFs, ?_, ?_, hle, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxU, hfx⟩ := hmemK x hx.le
    rw [(hFK x hxU hfx).mfderiv_eq]
    exact hreg x hxU ((hFeqK x hxU hfx).symm.trans hx)
  · intro x hx
    exact hU (hmemK x hx.le).1
  · intro x
    constructor
    · intro hx
      obtain ⟨hxU, hfx⟩ := hmemK x hx.le
      exact ⟨hxU, (hFeqK x hxU hfx) ▸ hx⟩
    · rintro ⟨hxU, hfx⟩
      rw [hFeqK x hxU hfx.le]
      exact hfx
  · intro x
    constructor
    · intro hx
      obtain ⟨hxU, hfx⟩ := hmemK x hx.le
      exact ⟨hxU, (hFeqK x hxU hfx) ▸ hx⟩
    · rintro ⟨hxU, hfx⟩
      rw [hFeqK x hxU hfx.le]
      exact hfx

/-- **B1-interior (regular domain inside an open set of the interior).** The defining function
lives only on `U ⊆ W.interior` and the sublevel `{x ∈ U | f x ≤ c}` is compact. Reduced to
B1-relative by a cutoff, or proved directly on the boundaryless open submanifold `U`. -/
theorem exists_pieces_of_interior_sublevel (W : CompactCarrier.{u})
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    (hreg : ∀ x ∈ U, f x = c → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
    (hK : IsCompact {x | x ∈ U ∧ f x ≤ c}) :
    ∃ (m : ℕ) (P : Fin m → PieceEmbedding W),
      (⋃ k, range (P k).map) = {x | x ∈ U ∧ f x ≤ c} ∧
      Pairwise (fun k k' => Disjoint (range (P k).map) (range (P k').map)) ∧
      ∀ k q, (𝓡∂ 3).IsBoundaryPoint q ↔ f ((P k).map q) = c := by
  obtain ⟨F, hF, hFreg, hFint, hle, -, heq⟩ :=
    exists_regular_extension_of_interior_sublevel W U hU f c hf hreg hK
  obtain ⟨m, P, hcov, hdisj, hbd⟩ := exists_pieces_of_regular_sublevel W F c hF hFreg hFint
  have hmem : ∀ k q, (P k).map q ∈ U ∧ f ((P k).map q) ≤ c := by
    intro k q
    have hq : (P k).map q ∈ ⋃ k, range (P k).map := mem_iUnion.mpr ⟨k, q, rfl⟩
    rw [hcov] at hq
    exact (hle _).mp hq
  refine ⟨m, P, ?_, hdisj, ?_⟩
  · rw [hcov]
    ext x
    exact hle x
  · intro k q
    rw [hbd k q]
    constructor
    · rintro (hb | hc)
      · exact absurd hb ((W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
          (hU (hmem k q).1))
      · exact ((heq _).mp hc).2
    · intro hc
      exact Or.inr ((heq _).mpr ⟨(hmem k q).1, hc⟩)

/-- **B1-complement.** The closed complement `W \ {x ∈ U | f x < c}` of a B1-interior domain is a
B1-relative domain: same components statement, boundary `∂W ∪ {f = c}`. Used for the complement
of the rounded circle region (the ball–handle side of the common rounding). -/
theorem exists_pieces_of_interior_superlevel (W : CompactCarrier.{u})
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    (hreg : ∀ x ∈ U, f x = c → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0)
    (hK : IsCompact {x | x ∈ U ∧ f x ≤ c}) :
    ∃ (m : ℕ) (P : Fin m → PieceEmbedding W),
      (⋃ k, range (P k).map) = {x | x ∉ U ∨ c ≤ f x} ∧
      Pairwise (fun k k' => Disjoint (range (P k).map) (range (P k').map)) ∧
      ∀ k q, (𝓡∂ 3).IsBoundaryPoint q ↔
        (W.model.IsBoundaryPoint ((P k).map q) ∨ ((P k).map q ∈ U ∧ f ((P k).map q) = c)) := by
  obtain ⟨F, hF, hFreg, hFint, -, hlt, heq⟩ :=
    exists_regular_extension_of_interior_sublevel W U hU f c hf hreg hK
  let G : W.Carrier → ℝ := fun x => 2 * c - F x
  have hG : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ G :=
    (contDiff_const.sub contDiff_id).contMDiff.comp hF
  have hGeq : ∀ x, G x = c ↔ F x = c := fun x => by
    constructor <;> intro h <;> simp only [G] at * <;> linarith
  have hGreg : ∀ x, G x = c → mfderiv W.model 𝓘(ℝ, ℝ) G x ≠ 0 := by
    intro x hx h0
    apply hFreg x ((hGeq x).mp hx)
    have h := DifferentialGeometry.Manifold.mfderiv_const_sub_real
      ((hF x).mdifferentiableAt (by simp)) (2 * c)
    have h' : -(show EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ from
        mfderiv W.model 𝓘(ℝ, ℝ) F x) = 0 := h.symm.trans h0
    exact neg_eq_zero.mp h'
  have hGint : ∀ x, G x = c → x ∈ W.interior := fun x hx => hFint x ((hGeq x).mp hx)
  obtain ⟨m, P, hcov, hdisj, hbd⟩ := exists_pieces_of_regular_sublevel W G c hG hGreg hGint
  refine ⟨m, P, ?_, hdisj, ?_⟩
  · rw [hcov]
    ext x
    have h1 : G x ≤ c ↔ ¬ F x < c := by
      simp only [G, not_lt]
      constructor <;> intro h <;> linarith
    simp only [mem_ofPred_eq]
    rw [h1, hlt x, not_and_or, not_lt]
  · intro k q
    rw [hbd k q, hGeq, heq]

end GC.GraphManifold.Assembly
