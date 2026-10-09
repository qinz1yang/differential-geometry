import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClass

/-!
# Descending compactly supported plane isotopies to the torus

A compactly supported isotopy `H` of `ℝ²` whose support `K` meets none of its non-zero
`ℤ²`-translates is periodised to `p ↦ p + ∑ᶠ k, (H t (p - k) - (p - k))`; the family of translated
supports is locally finite, so the periodisation is jointly smooth, commutes with `ℤ²`, and has the
periodisation of `(H t).symm` as inverse. `torusFamily` descends it to an isotopy of `T²`
(`exists_torus_push`). `isotopicDiffeomorph_trans_of_refl` precomposes such an isotopy with `φ`.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

private def intVec (k : ℤ × ℤ) : ℝ × ℝ := ((k.1 : ℝ), (k.2 : ℝ))

private theorem intVec_add (k j : ℤ × ℤ) : intVec (k + j) = intVec k + intVec j :=
  Prod.ext (Int.cast_add _ _) (Int.cast_add _ _)

private theorem intVec_sub (k j : ℤ × ℤ) : intVec (k - j) = intVec k - intVec j :=
  Prod.ext (Int.cast_sub _ _) (Int.cast_sub _ _)

private theorem intVec_zero : intVec 0 = 0 :=
  Prod.ext Int.cast_zero Int.cast_zero

private theorem torusCover_add_intVec (p : ℝ × ℝ) (k : ℤ × ℤ) :
    torusCover (p + intVec k) = torusCover p :=
  torusCover_add_int p k.1 k.2

private def periodise (D : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  p + ∑ᶠ k : ℤ × ℤ, (D (p - intVec k) - (p - intVec k))

section Periodise

variable {K : Set (ℝ × ℝ)}

private theorem eq_of_sub_intVec_mem
    (hsep : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ K → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ K →
      m = 0 ∧ n = 0)
    {p : ℝ × ℝ} {k k' : ℤ × ℤ} (hk : p - intVec k ∈ K) (hk' : p - intVec k' ∈ K) : k = k' := by
  have he : ((p - intVec k').1 + ((k'.1 - k.1 : ℤ) : ℝ),
      (p - intVec k').2 + ((k'.2 - k.2 : ℤ) : ℝ)) = p - intVec k := by
    refine Prod.ext ?_ ?_ <;> simp only [intVec, Prod.fst_sub, Prod.snd_sub, Int.cast_sub] <;> ring
  obtain ⟨h1, h2⟩ := hsep _ _ _ hk' (he ▸ hk)
  exact Prod.ext (by omega) (by omega)

private theorem finite_intVec_preimage (c : ℝ × ℝ) (r : ℝ) :
    (intVec ⁻¹' Metric.closedBall c r).Finite := by
  have ht : Filter.Tendsto intVec Filter.cofinite (Filter.cocompact (ℝ × ℝ)) := by
    rw [← Filter.coprod_cofinite, ← Filter.coprod_cocompact]
    exact Int.tendsto_coe_cofinite.prodMap_coprod Int.tendsto_coe_cofinite
  exact tendsto_cofinite_cocompact_iff.mp ht _ (isCompact_closedBall c r)

private theorem locallyFinite_translates (hK : IsCompact K) :
    LocallyFinite fun k : ℤ × ℤ => {q : ℝ × (ℝ × ℝ) | q.2 - intVec k ∈ K} := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  intro q
  refine ⟨Metric.ball q 1, Metric.ball_mem_nhds q one_pos,
    (finite_intVec_preimage q.2 (1 + R)).subset ?_⟩
  rintro k ⟨q', hq'K, hq'⟩
  have h1 : ‖q'.2 - intVec k‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hq'K
  have h2 : ‖q'.2 - q.2‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hq'
    exact lt_of_le_of_lt (norm_snd_le (q' - q)) hq'
  rw [mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  calc ‖intVec k - q.2‖ = ‖(q'.2 - q.2) - (q'.2 - intVec k)‖ := by congr 1; abel
    _ ≤ ‖q'.2 - q.2‖ + ‖q'.2 - intVec k‖ := norm_sub_le _ _
    _ ≤ 1 + R := by linarith

private theorem contDiff_periodise {D : ℝ → ℝ × ℝ → ℝ × ℝ}
    (hD : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => D q.1 q.2)) (hDK : ∀ s z, z ∉ K → D s z = z)
    (hK : IsCompact K) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => periodise (D q.1) q.2) := by
  set f : ℤ × ℤ → ℝ × (ℝ × ℝ) → ℝ × ℝ := fun k q => D q.1 (q.2 - intVec k) - (q.2 - intVec k)
    with hfdef
  have hf (k : ℤ × ℤ) : ContDiff ℝ ∞ (f k) :=
    (hD.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))).sub
      (contDiff_snd.sub contDiff_const)
  have hlf : LocallyFinite fun k => Function.support (f k) := by
    refine (locallyFinite_translates hK).subset fun k q hq => ?_
    by_contra h
    exact hq (by simp only [hfdef, hDK _ _ h, sub_self])
  have hsum : ContDiff ℝ ∞ (fun q => ∑ᶠ k, f k q) := by
    rw [contDiff_iff_contDiffAt]
    intro q
    obtain ⟨s, hs⟩ := finsum_eventually_eq_sum hlf q
    exact (ContDiff.sum fun k _ => hf k).contDiffAt.congr_of_eventuallyEq hs
  exact contDiff_snd.add hsum

variable {D D' : ℝ × ℝ → ℝ × ℝ}

private theorem periodise_eq_of_mem (hD : ∀ z, z ∉ K → D z = z)
    (hsep : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ K → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ K →
      m = 0 ∧ n = 0)
    {p : ℝ × ℝ} {k : ℤ × ℤ} (hk : p - intVec k ∈ K) :
    periodise D p = D (p - intVec k) + intVec k := by
  rw [periodise, finsum_eq_single _ k (fun k' hk' => ?_)]
  · abel
  · have h : p - intVec k' ∉ K := fun h => hk' (eq_of_sub_intVec_mem hsep h hk)
    rw [hD _ h, sub_self]

private theorem periodise_eq_self (hD : ∀ z, z ∉ K → D z = z) {p : ℝ × ℝ}
    (hp : ∀ k, p - intVec k ∉ K) : periodise D p = p := by
  rw [periodise, finsum_eq_zero_of_forall_eq_zero (fun k => by rw [hD _ (hp k), sub_self]),
    add_zero]

private theorem periodise_of_forall_eq (hD : ∀ z, D z = z) (p : ℝ × ℝ) : periodise D p = p := by
  rw [periodise, finsum_eq_zero_of_forall_eq_zero (fun k => by rw [hD, sub_self]), add_zero]

private theorem periodise_comp (hD : ∀ z, z ∉ K → D z = z) (hD' : ∀ z, z ∉ K → D' z = z)
    (hDK : ∀ z, z ∈ K → D z ∈ K) (hc : ∀ z, z ∈ K → D' (D z) = z)
    (hsep : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ K → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ K →
      m = 0 ∧ n = 0)
    (p : ℝ × ℝ) : periodise D' (periodise D p) = p := by
  by_cases h : ∃ k, p - intVec k ∈ K
  · obtain ⟨k, hk⟩ := h
    rw [periodise_eq_of_mem hD hsep hk]
    have hk' : D (p - intVec k) + intVec k - intVec k ∈ K := by
      rw [add_sub_cancel_right]
      exact hDK _ hk
    rw [periodise_eq_of_mem hD' hsep hk', add_sub_cancel_right, hc _ hk, sub_add_cancel]
  · have hp : ∀ k, p - intVec k ∉ K := fun k hk => h ⟨k, hk⟩
    rw [periodise_eq_self hD hp, periodise_eq_self hD' hp]

private theorem periodise_add_intVec (hD : ∀ z, z ∉ K → D z = z)
    (hsep : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ K → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ K →
      m = 0 ∧ n = 0)
    (p : ℝ × ℝ) (j : ℤ × ℤ) : periodise D (p + intVec j) = periodise D p + intVec j := by
  by_cases h : ∃ k, p - intVec k ∈ K
  · obtain ⟨k, hk⟩ := h
    have he : p + intVec j - intVec (k + j) = p - intVec k := by
      rw [intVec_add]
      abel
    have hk' : p + intVec j - intVec (k + j) ∈ K := he ▸ hk
    rw [periodise_eq_of_mem hD hsep hk', periodise_eq_of_mem hD hsep hk, he, intVec_add,
      add_assoc]
  · have hp : ∀ k, p - intVec k ∉ K := fun k hk => h ⟨k, hk⟩
    have hp' : ∀ k, p + intVec j - intVec k ∉ K := fun k hk => by
      refine hp (k - j) ?_
      rw [intVec_sub]
      convert hk using 1
      abel
    rw [periodise_eq_self hD hp', periodise_eq_self hD hp]

end Periodise

theorem exists_torus_push {H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)}
    (hH : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => H q.1 q.2))
    (hH' : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (H q.1).symm q.2))
    (h0 : H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hHK : ∀ s z, z ∉ K → H s z = z)
    (hsep : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ K → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ K →
      m = 0 ∧ n = 0) :
    ∃ Q : TDiff, IsotopicDiffeomorph torusRefl Q ∧
      (∀ z ∈ K, Q (torusCover z) = torusCover (H 1 z)) ∧
      ∀ z, (∀ m n : ℤ, (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∉ K) → Q (torusCover z) = torusCover z := by
  have hmaps (s : ℝ) (z : ℝ × ℝ) (hz : z ∈ K) : H s z ∈ K := by
    by_contra h
    have he : H s z = z := (H s).injective (hHK s _ h)
    rw [he] at h
    exact h hz
  have hoff (s : ℝ) (z : ℝ × ℝ) (hz : z ∉ K) : (H s).symm z = z := by
    conv_lhs => rw [← hHK s z hz]
    exact (H s).symm_apply_apply z
  have hmaps' (s : ℝ) (z : ℝ × ℝ) (hz : z ∈ K) : (H s).symm z ∈ K := by
    by_contra h
    have he := hHK s _ h
    rw [Diffeomorph.apply_symm_apply] at he
    exact h (he ▸ hz)
  have hG : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => periodise (H q.1) q.2) :=
    contDiff_periodise (D := fun s => H s) hH hHK hK
  have hGinv : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => periodise (H q.1).symm q.2) :=
    contDiff_periodise (D := fun s => (H s).symm) hH' hoff hK
  have hleft (t : ℝ) (p : ℝ × ℝ) : periodise (H t).symm (periodise (H t) p) = p :=
    periodise_comp (hHK t) (hoff t) (hmaps t) (fun z _ => (H t).symm_apply_apply z) hsep p
  have hright (t : ℝ) (p : ℝ × ℝ) : periodise (H t) (periodise (H t).symm p) = p :=
    periodise_comp (hoff t) (hHK t) (hmaps' t) (fun z _ => (H t).apply_symm_apply z) hsep p
  have hper (t : ℝ) (p : ℝ × ℝ) (m n : ℤ) :
      torusCover (periodise (H t) (p.1 + m, p.2 + n)) = torusCover (periodise (H t) p) := by
    rw [show ((p.1 + m, p.2 + n) : ℝ × ℝ) = p + intVec (m, n) from rfl,
      periodise_add_intVec (hHK t) hsep, torusCover_add_intVec]
  have hperinv (t : ℝ) (p : ℝ × ℝ) (m n : ℤ) :
      torusCover (periodise (H t).symm (p.1 + m, p.2 + n)) =
        torusCover (periodise (H t).symm p) := by
    rw [show ((p.1 + m, p.2 + n) : ℝ × ℝ) = p + intVec (m, n) from rfl,
      periodise_add_intVec (hoff t) hsep, torusCover_add_intVec]
  let Q : TDiff := torusFamily hG hGinv hleft hright hper hperinv 1
  have hQ (p : ℝ × ℝ) : Q (torusCover p) = torusCover (periodise (H 1) p) :=
    torusFamilyMap_torusCover (G := fun q : ℝ × (ℝ × ℝ) => periodise (H q.1) q.2) hper 1 p
  refine ⟨Q, isotopicDiffeomorph_of_lift hG hGinv hleft hright hper hperinv
    (fun p => ?_) hQ, fun z hz => ?_, fun z hz => ?_⟩
  · change torusCover p = torusCover (periodise (H 0) p)
    rw [periodise_of_forall_eq (fun z => by rw [h0]; rfl)]
  · have hz' : z - intVec 0 ∈ K := by rwa [intVec_zero, sub_zero]
    rw [hQ, periodise_eq_of_mem (hHK 1) hsep hz', intVec_zero, sub_zero, add_zero]
  · have hp : ∀ k, z - intVec k ∉ K := fun k => by
      have he : z - intVec k = (z.1 + ((-k.1 : ℤ) : ℝ), z.2 + ((-k.2 : ℤ) : ℝ)) := by
        refine Prod.ext ?_ ?_ <;> simp only [intVec, Prod.fst_sub, Prod.snd_sub, Int.cast_neg] <;>
          ring
      rw [he]
      exact hz _ _
    rw [hQ, periodise_eq_self (hHK 1) hp]

theorem isotopicDiffeomorph_trans_of_refl (φ : TDiff) {Q : TDiff}
    (hQ : IsotopicDiffeomorph torusRefl Q) : IsotopicDiffeomorph φ (φ.trans Q) := by
  obtain ⟨F, hF, hF', h0, h1⟩ := hQ
  refine ⟨fun t => φ.trans (F t), hF.comp (contMDiff_fst.prodMk (φ.contMDiff.comp contMDiff_snd)),
    φ.symm.contMDiff.comp hF', ?_, ?_⟩
  · refine Diffeomorph.ext fun x => ?_
    change F 0 (φ x) = φ x
    rw [h0]
    rfl
  · change φ.trans (F 1) = φ.trans Q
    rw [h1]

end GC.Seifert
