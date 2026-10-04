import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyHalfCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeamCollar

/-!
# Consumer of B2-side: half collars of a regular torus level inside its sublevel piece

The B1-interior output shape (pieces with union `{x ∈ U | f x ≤ c}` and pairwise disjoint ranges,
`AssemblyInteriorSublevel.lean:107`) and the B2 torus seam of the same function
(`AssemblySeamCollar.lean`) feed B2-side directly: the piece containing one point of the torus meets
the seam target exactly in the negative half collar (`halfCollar_range_eq_of_sublevelPieces`), so
it carries the half collar with `map (L (t, s)) = seam (t, -s)` (`exists_halfCollar_of_sublevelPieces`).
This is the `lift` / `lift_eq` input of B3's `RegularCutData` for a seam whose negative side is a
sublevel piece.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The sublevel piece containing a point of the zero section of a seam of the same function
meets the seam target exactly in the negative half collar. -/
theorem halfCollar_range_eq_of_sublevelPieces {W : CompactCarrier.{u}} {U : Set W.Carrier}
    {f : W.Carrier → ℝ} {c : ℝ} {m : ℕ} (P : Fin m → PieceEmbedding W)
    (hunion : (⋃ k, range (P k).map) = {x | x ∈ U ∧ f x ≤ c})
    (hdisj : Pairwise fun k k' => Disjoint (range (P k).map) (range (P k').map))
    (S : TorusSeam W) {δ : ℝ} (hδ : 0 < δ) (hSU : S.collar.target ⊆ U)
    (hval : ∀ p ∈ signedCollarSource, f (S.collar p) = c + δ * p.2)
    (k : Fin m) (t₀ : Torus) (hk : S.collar (t₀, 0) ∈ range (P k).map) :
    range (P k).map ∩ S.collar.target =
      S.collar '' {p | p ∈ signedCollarSource ∧ (if true then p.2 ≤ 0 else 0 ≤ p.2)} := by
  let N : Set (Torus × ℝ) := {p | p ∈ signedCollarSource ∧ (if true then p.2 ≤ 0 else 0 ≤ p.2)}
  have hNsrc : N ⊆ S.collar.source := fun p hp => S.source_eq ▸ hp.1
  have hmemU : ∀ p ∈ N, S.collar p ∈ ⋃ k, range (P k).map := by
    intro p hp
    rw [hunion]
    refine ⟨hSU (S.collar.map_source' (hNsrc hp)), ?_⟩
    rw [hval p hp.1]
    have h2 : p.2 ≤ 0 := hp.2
    nlinarith
  have hNconn : IsPreconnected (S.collar '' N) := by
    have hN : N = univ ×ˢ Ioc (-1 : ℝ) 0 := by
      ext p
      simp only [N, signedCollarSource, mem_ofPred_eq, ite_true, mem_prod, mem_univ, mem_Ioc,
        true_and]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by linarith⟩, h2⟩
    have hpc : IsPreconnected N := by
      rw [hN]
      exact isPreconnected_univ.prod isPreconnected_Ioc
    exact hpc.image _ (S.collar.contMDiffOn_toFun.continuousOn.mono hNsrc)
  ext y
  constructor
  · rintro ⟨hyP, hyT⟩
    refine ⟨S.collar.invFun y, ⟨S.source_eq ▸ S.collar.map_target' hyT, ?_⟩,
      S.collar.right_inv' hyT⟩
    have hsrc : S.collar.invFun y ∈ signedCollarSource := S.source_eq ▸ S.collar.map_target' hyT
    have hf : f y ≤ c := by
      have hyU : y ∈ ⋃ k, range (P k).map := mem_iUnion.mpr ⟨k, hyP⟩
      rw [hunion] at hyU
      exact hyU.2
    have hv := hval _ hsrc
    rw [show S.collar (S.collar.invFun y) = y from S.collar.right_inv' hyT] at hv
    change (S.collar.invFun y).2 ≤ 0
    by_contra hpos
    have hpos' := not_le.mp hpos
    nlinarith
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, S.collar.map_source' (hNsrc hp)⟩
    let t' : Set W.Carrier := ⋃ k' ∈ ({k}ᶜ : Set (Fin m)), range (P k').map
    have hclosed : ∀ k', IsClosed (range (P k').map) := fun k' => (P k').isClosed_range
    have ht' : IsClosed t' := (Set.toFinite _).isClosed_biUnion fun k' _ => hclosed k'
    have hsub : S.collar '' N ⊆ range (P k).map ∪ t' := by
      rintro _ ⟨p', hp', rfl⟩
      obtain ⟨k', hk'⟩ := mem_iUnion.mp (hmemU p' hp')
      by_cases hkk : k' = k
      · exact Or.inl (hkk ▸ hk')
      · exact Or.inr (mem_biUnion (show k' ∈ ({k}ᶜ : Set (Fin m)) from hkk) hk')
    by_contra hnot
    have h0 : ((t₀, 0) : Torus × ℝ) ∈ N := by
      refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
      change (0 : ℝ) ≤ 0
      exact le_rfl
    obtain ⟨z, hzK, hzk, hzt⟩ := isPreconnected_closed_iff.mp hNconn _ _ (hclosed k) ht' hsub
      ⟨_, ⟨_, h0, rfl⟩, hk⟩
      ⟨_, ⟨p, hp, rfl⟩, (hsub ⟨p, hp, rfl⟩).resolve_left hnot⟩
    obtain ⟨k', hk', hzk'⟩ := mem_iUnion₂.mp hzt
    exact (hdisj (show k ≠ k' from fun h => hk' (h ▸ rfl))).le_bot ⟨hzk, hzk'⟩

/-- **Pipeline B1 → B2 → B2-side.** For sublevel pieces of `f` (the B1-interior output shape) and a
regular torus component of the level `{f = c}` inside `U`, the B2 seam and the piece containing the
torus give an actual half collar in that piece over the negative side of the seam. -/
theorem exists_halfCollar_of_sublevelPieces {W : CompactCarrier.{u}}
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    {m : ℕ} (P : Fin m → PieceEmbedding W)
    (hunion : (⋃ k, range (P k).map) = {x | x ∈ U ∧ f x ≤ c})
    (hdisj : Pairwise fun k k' => Disjoint (range (P k).map) (range (P k').map))
    (param : Torus → W.Carrier) (hparam : IsSmoothEmbedding torusModel W.model ∞ param)
    (hSU : range param ⊆ U) (hlev : ∀ t, f (param t) = c)
    (hreg : ∀ t, mfderiv W.model 𝓘(ℝ, ℝ) f (param t) ≠ 0)
    (hiso : ∃ V₀ : Set W.Carrier, IsOpen V₀ ∧ range param ⊆ V₀ ∧
      ∀ x ∈ V₀ ∩ U, f x = c → x ∈ range param) :
    ∃ (S : TorusSeam W) (k : Fin m)
      (L : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) (P k).Piece ∞),
      (∀ t, S.collar (t, 0) = param t) ∧ L.source = halfCollarSource ∧
      ∀ t s (hs : 0 ≤ s), s < 1 → (P k).map (L (t, halfPoint s hs)) = S.collar (t, -s) := by
  obtain ⟨δ, hδ, S, hT, hzero, hval⟩ := exists_torusSeam_of_regular_level W U hU f c hf param
    hparam hSU hlev hreg hiso univ isOpen_univ (subset_univ _)
  let t₀ : Torus := (1, 1)
  have hmem : param t₀ ∈ ⋃ k, range (P k).map := by
    rw [hunion]
    exact ⟨hSU (mem_range_self t₀), (hlev t₀).le⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp hmem
  have hrange := halfCollar_range_eq_of_sublevelPieces P hunion hdisj S hδ
    (fun y hy => (hT hy).2) hval k t₀ (by rw [hzero]; exact hk)
  obtain ⟨L, hsrc, heq⟩ := exists_halfCollar_of_torusSeam S (P k) true hrange
  exact ⟨S, k, L, hzero, hsrc, fun t s hs hs1 => heq t s hs hs1⟩

end GC.GraphManifold.Assembly
