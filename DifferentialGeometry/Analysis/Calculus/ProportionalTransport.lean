import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis

open Set

private theorem exists_contDiffOn_supported_proportional_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : E → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {W J : Set E} (hW : IsOpen W) (hJ : IsCompact J) (hJW : J ⊆ W)
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ J,
      (1 - t) * A x + t * B x = 0 →
        fderiv ℝ (fun y => (1 - t) * A y + t * B y) x ≠ 0)
    (hprop : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ W,
      (1 - t) * A x + t * B x = 0 → x ∉ J →
        ∃ r : ℝ, 0 < r ∧ ∃ N : Set E, IsOpen N ∧ x ∈ N ∧ N ⊆ W ∧
          EqOn B (fun y => r * A y) N) :
    ∃ (B₀ : Set E) (Ω : Set (ℝ × E)) (Q : ℝ × E → E × ℝ),
      IsCompact B₀ ∧ J ⊆ interior B₀ ∧ B₀ ⊆ W ∧
      IsOpen Ω ∧ Icc (0 : ℝ) 1 ×ˢ W ⊆ Ω ∧ Ω ⊆ univ ×ˢ W ∧
      ContDiffOn ℝ ∞ Q Ω ∧
      ∀ z ∈ Ω,
        (deriv (fun t => (1 - t) * A z.2 + t * B z.2) z.1 +
          fderiv ℝ (fun y => (1 - z.1) * A y + z.1 * B y) z.2 (Q z).1 =
            (Q z).2 * ((1 - z.1) * A z.2 + z.1 * B z.2)) ∧
        (z.2 ∉ interior B₀ → (Q z).1 = 0) := by
  classical
  obtain ⟨B₀, hB₀, hJB₀, hB₀W⟩ := exists_compact_between hJ hW hJW
  let H : ℝ × E → ℝ := fun z => (1 - z.1) * A z.2 + z.1 * B z.2
  let D : ℝ × E → ℝ := fun z => B z.2 - A z.2
  let L : ℝ × E → E →L[ℝ] ℝ := fun z => fderiv ℝ (fun y => H (z.1, y)) z.2
  have hH : ContDiff ℝ ∞ H :=
    ((contDiff_const.sub contDiff_fst).mul (hA.comp contDiff_snd)).add
      (contDiff_fst.mul (hB.comp contDiff_snd))
  have hD : ContDiff ℝ ∞ D := (hB.comp contDiff_snd).sub (hA.comp contDiff_snd)
  have hL : ContDiff ℝ ∞ L :=
    (hH.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv
      (f := fun (z : ℝ × E) y => H (z.1, y)) contDiff_snd (by simp)
  have htime (t : ℝ) (x : E) :
      deriv (fun u => (1 - u) * A x + u * B x) t = D (t, x) := by
    have h : HasDerivAt (fun u => (1 - u) * A x + u * B x)
        ((0 - 1) * A x + 1 * B x) t :=
      (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const (A x)).add
        ((hasDerivAt_id t).mul_const (B x))
    simpa only [D, zero_sub, zero_add, neg_one_mul, one_mul, sub_eq_add_neg, add_comm]
      using h.deriv
  let C : ℝ × E → Set (E × ℝ) := fun z => {q |
    D z + L z q.1 = q.2 * H z ∧ (z.2 ∉ interior B₀ → q.1 = 0)}
  have hC (z : ℝ × E) : Convex ℝ (C z) := by
    rw [convex_iff_add_mem]
    intro u hu v hv a b _ _ hab
    constructor
    · change D z + L z (a • u.1 + b • v.1) = (a * u.2 + b * v.2) * H z
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      linear_combination a * hu.1 + b * hv.1 - D z * hab
    · intro hz
      change a • u.1 + b • v.1 = 0
      rw [hu.2 hz, hv.2 hz, smul_zero, smul_zero, add_zero]
  let S : Set (ℝ × E) := Icc (0 : ℝ) 1 ×ˢ W
  have hlocal (z : S) : ∃ U : Set (ℝ × E), IsOpen U ∧ (z : ℝ × E) ∈ U ∧
      U ⊆ univ ×ˢ W ∧ ∃ g : ℝ × E → E × ℝ,
        ContDiffOn ℝ ∞ g U ∧ ∀ q ∈ U, g q ∈ C q := by
    by_cases hz : H z = 0
    · by_cases hzJ : z.1.2 ∈ J
      · have hLz : L z ≠ 0 := hregular z.1.1 z.2.1 z.1.2 hzJ hz
        obtain ⟨w, hw⟩ : ∃ w : E, L z w ≠ 0 := by
          by_contra! hn
          apply hLz
          ext w
          exact hn w
        have hLw : ContDiff ℝ ∞ (fun q => L q w) := hL.clm_apply contDiff_const
        let U := (univ ×ˢ (W ∩ interior B₀)) ∩ {q : ℝ × E | L q w ≠ 0}
        have hU : IsOpen U := (isOpen_univ.prod (hW.inter isOpen_interior)).inter
          (isClosed_eq hLw.continuous continuous_const).isOpen_compl
        refine ⟨U, hU, ⟨⟨mem_univ _, z.2.2, hJB₀ hzJ⟩, hw⟩,
          (fun q hq => ⟨mem_univ _, hq.1.2.1⟩),
          (fun q => ((-D q / L q w) • w, 0)), ?_, ?_⟩
        · exact ((hD.contDiffOn.neg.div hLw.contDiffOn
            (fun q hq => hq.2)).smul contDiffOn_const).prodMk contDiffOn_const
        · intro q hq
          constructor
          · change D q + L q ((-D q / L q w) • w) = 0 * H q
            rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hq.2, add_neg_cancel, zero_mul]
          · intro hn
            exact False.elim (hn hq.1.2.2)
      · obtain ⟨r, hr, N, hN, hzN, hNW, he⟩ :=
          hprop z.1.1 z.2.1 z.1.2 z.2.2 hz hzJ
        let c : ℝ × E → ℝ := fun q => (1 - q.1) + q.1 * r
        have hc : ContDiff ℝ ∞ c :=
          (contDiff_const.sub contDiff_fst).add (contDiff_fst.mul contDiff_const)
        have hcz : 0 < c z := by
          rcases eq_or_lt_of_le z.2.1.1 with ht | ht
          · change 0 < (1 - z.1.1) + z.1.1 * r
            rw [← ht]
            norm_num
          · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr z.2.1.2) (mul_pos ht hr)
        let U := {q : ℝ × E | 0 < c q} ∩ (univ ×ˢ N)
        refine ⟨U, (isOpen_lt continuous_const hc.continuous).inter (isOpen_univ.prod hN),
          ⟨hcz, mem_univ _, hzN⟩, (fun q hq => ⟨mem_univ _, hNW hq.2.2⟩),
          (fun q => (0, (r - 1) / c q)), ?_, ?_⟩
        · exact contDiffOn_const.prodMk
            (contDiffOn_const.div hc.contDiffOn (fun q hq => hq.1.ne'))
        · intro q hq
          refine ⟨?_, fun _ => rfl⟩
          change D q + L q 0 = (r - 1) / c q * H q
          rw [map_zero, add_zero]
          have heH : H q = c q * A q.2 := by
            dsimp only [H, c]
            rw [he hq.2.2]
            ring
          rw [heH, ← mul_assoc, div_mul_cancel₀ _ hq.1.ne']
          change B q.2 - A q.2 = (r - 1) * A q.2
          rw [he hq.2.2]
          ring
    · let U := (univ ×ˢ W) ∩ {q : ℝ × E | H q ≠ 0}
      refine ⟨U, (isOpen_univ.prod hW).inter
          (isClosed_eq hH.continuous continuous_const).isOpen_compl,
        ⟨⟨mem_univ _, z.2.2⟩, hz⟩, inter_subset_left,
        (fun q => (0, D q / H q)), ?_, ?_⟩
      · exact contDiffOn_const.prodMk
          (hD.contDiffOn.div hH.contDiffOn (fun q hq => hq.2))
      · intro q hq
        refine ⟨?_, fun _ => rfl⟩
        change D q + L q 0 = D q / H q * H q
        rw [map_zero, add_zero, div_mul_cancel₀ _ hq.2]
  choose U hU hzU hUW g hg hgC using hlocal
  let Ω : Set (ℝ × E) := ⋃ z : S, U z
  have hΩ : IsOpen Ω := isOpen_iUnion hU
  have hSΩ : S ⊆ Ω := fun z hz => mem_iUnion_of_mem ⟨z, hz⟩ (hzU ⟨z, hz⟩)
  have hΩW : Ω ⊆ univ ×ˢ W := iUnion_subset hUW
  let O : TopologicalSpace.Opens (ℝ × E) := ⟨Ω, hΩ⟩
  have : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  have hloc (x : O) : ∃ V ∈ 𝓝 x, ∃ G : O → E × ℝ,
      ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E × ℝ) (⊤ : ℕ∞) G V ∧
        ∀ y ∈ V, G y ∈ C y := by
    obtain ⟨z, hx⟩ := mem_iUnion.mp x.2
    refine ⟨Subtype.val ⁻¹' U z,
      ((hU z).preimage continuous_subtype_val).mem_nhds hx,
      (fun y => g z y), ?_, ?_⟩
    · exact (hg z).contMDiffOn.comp
        (contMDiff_subtype_val (U := O)).contMDiffOn (fun y hy => hy)
    · intro y hy
      exact hgC z y hy
  obtain ⟨q, hq⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (I := 𝓘(ℝ, ℝ × E)) (M := O) (n := (⊤ : ℕ∞))
    (t := fun x : O => C x) (fun x => hC x) hloc
  let Q : ℝ × E → E × ℝ := Subtype.val.extend (fun x : O => q x) 0
  have hQ (x : O) : Q x = q x := Subtype.val_injective.extend_apply (fun x : O => q x) 0 x
  have hQs : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E × ℝ) ∞ (fun x : O => Q x) :=
    q.contMDiff.congr hQ
  refine ⟨B₀, Ω, Q, hB₀, hJB₀, hB₀W, hΩ, hSΩ, hΩW, ?_, ?_⟩
  · apply contMDiffOn_iff_contDiffOn.mp
    intro y hy
    exact (contMDiffAt_subtype_iff.mp (hQs ⟨y, hy⟩)).contMDiffWithinAt
  · intro z hz
    have hm : Q z ∈ C z := by
      rw [hQ ⟨z, hz⟩]
      exact hq ⟨z, hz⟩
    rw [htime]
    exact hm

private theorem exists_contDiff_compact_extension_of_spatial_vanishing
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K W : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω) (hcover : Icc (0 : ℝ) 1 ×ˢ W ⊆ Ω)
    {f : ℝ × E → F} (hf : ContDiffOn ℝ ∞ f Ω)
    (hzero : ∀ z ∈ Ω, z.2 ∉ K → f z = 0) :
    ∃ (V : ℝ × E → F) (U : Set (ℝ × E)),
      ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      IsOpen U ∧ Icc (0 : ℝ) 1 ×ˢ W ⊆ U ∧ U ⊆ Ω ∧
      EqOn V f U ∧ ∀ t x, x ∉ K → V (t, x) = 0 := by
  obtain ⟨χ, hχ, hsχ, hχone, hχΩ, _⟩ :=
    exists_bump_compact (isCompact_Icc.prod hK) hΩ
      (fun z hz => hcover ⟨hz.1, hKW hz.2⟩)
  obtain ⟨N, hN, hKN, hNone⟩ := mem_nhdsSet_iff_exists.mp hχone
  let V : ℝ × E → F := fun z => χ z • f z
  let U := Ω ∩ (N ∪ (univ ×ˢ Kᶜ))
  have hVzero (t : ℝ) (x : E) (hx : x ∉ K) : V (t, x) = 0 := by
    change χ (t, x) • f (t, x) = 0
    by_cases hz : (t, x) ∈ Ω
    · rw [hzero (t, x) hz hx, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hχΩ h)), zero_smul]
  refine ⟨V, U, contDiff_cutoff_smul hΩ hχ hχΩ hf, hsχ.smul_right,
    hΩ.inter (hN.union (isOpen_univ.prod hK.isClosed.isOpen_compl)), ?_,
    inter_subset_left, ?_, hVzero⟩
  · intro z hz
    refine ⟨hcover hz, ?_⟩
    by_cases hx : z.2 ∈ K
    · exact Or.inl (hKN ⟨hz.1, hx⟩)
    · exact Or.inr ⟨mem_univ _, hx⟩
  · intro z hz
    rcases hz.2 with hn | hx
    · change χ z • f z = f z
      have he : χ z = 1 := hNone hn
      rw [he, one_smul]
    · rw [hzero z hz.1 hx.2]
      exact hVzero z.1 z.2 hx.2

theorem exists_contDiff_compactly_supported_proportional_vector_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : E → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {W J : Set E} (hW : IsOpen W) (hJ : IsCompact J) (hJW : J ⊆ W)
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ J,
      (1 - t) * A x + t * B x = 0 →
        fderiv ℝ (fun y => (1 - t) * A y + t * B y) x ≠ 0)
    (hprop : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ W,
      (1 - t) * A x + t * B x = 0 → x ∉ J →
        ∃ r : ℝ, 0 < r ∧ ∃ N : Set E, IsOpen N ∧ x ∈ N ∧ N ⊆ W ∧
          EqOn B (fun y => r * A y) N) :
    ∃ (K : Set E) (V : ℝ × E → E) (Ω : Set (ℝ × E)) (κ : ℝ × E → ℝ),
      IsCompact K ∧ J ⊆ interior K ∧ K ⊆ W ∧
      ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      IsOpen Ω ∧ Icc (0 : ℝ) 1 ×ˢ W ⊆ Ω ∧ Ω ⊆ univ ×ˢ W ∧
      ContDiffOn ℝ ∞ κ Ω ∧
      (∀ z ∈ Ω,
        deriv (fun t => (1 - t) * A z.2 + t * B z.2) z.1 +
          fderiv ℝ (fun y => (1 - z.1) * A y + z.1 * B y) z.2 (V z) =
            κ z * ((1 - z.1) * A z.2 + z.1 * B z.2)) ∧
      ∀ t x, x ∉ K → V (t, x) = 0 := by
  obtain ⟨K, O, Q, hK, hJK, hKW, hO, hcover, hOW, hQ, htransport⟩ :=
    exists_contDiffOn_supported_proportional_pair hA hB hW hJ hJW hregular hprop
  obtain ⟨V, U, hV, hsV, hU, hUcover, hUO, heq, hzero⟩ :=
    exists_contDiff_compact_extension_of_spatial_vanishing hK hKW hO hcover hQ.fst
      (fun z hz hx => (htransport z hz).2 (fun hi => hx (interior_subset hi)))
  refine ⟨K, V, U, (fun z => (Q z).2), hK, hJK, hKW, hV, hsV,
    hU, hUcover, hUO.trans hOW, hQ.snd.mono hUO, ?_, hzero⟩
  intro z hz
  rw [heq hz]
  exact (htransport z (hUO hz)).1

end DifferentialGeometry.Analysis
