import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.ChartUnion
import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.ChartPiece
import DifferentialGeometry.Analysis.Calculus.ContDiff.LocallyFiniteJetSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Analysis

private theorem norm_iteratedFDeriv_sub_le_of_tsupport {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {P Q : E → F} {S : Set E}
    {k : ℕ} {x : E} {c : ℝ} (hP : ContDiffAt ℝ k P x) (hQ : ContDiffAt ℝ k Q x)
    (hPS : tsupport P ⊆ S) (hQS : tsupport Q ⊆ S) (hc : 0 ≤ c)
    (hin : x ∈ S → ‖iteratedFDeriv ℝ k P x - iteratedFDeriv ℝ k Q x‖ ≤ c) :
    ‖iteratedFDeriv ℝ k (fun y => P y - Q y) x‖ ≤ c := by
  rw [fun_iteratedFDeriv_sub_apply hP hQ]
  by_cases hx : x ∈ S
  · exact hin hx
  · have h1 : x ∉ tsupport (iteratedFDeriv ℝ k P) := fun hmem =>
      hx (hPS (tsupport_iteratedFDeriv_subset k hmem))
    have h2 : x ∉ tsupport (iteratedFDeriv ℝ k Q) := fun hmem =>
      hx (hQS (tsupport_iteratedFDeriv_subset k hmem))
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2, sub_self,
      norm_zero]
    exact hc

private theorem exists_chartUnion_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {r : ℕ} (χ : ι → OpenPartialHomeomorph E E)
    (hχ : ∀ a, ContDiffOn ℝ r (χ a) (χ a).source)
    (hχsymm : ∀ a, ContDiffOn ℝ r (χ a).symm (χ a).target)
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source)
    (hne : Nonempty (chartUnionOpens χ)) (a : ι) (U : Set (chartUnionOpens χ))
    (hU : IsOpen U) (hUa : U ⊆ Subtype.val ⁻¹' (χ a).source) (ρ : chartUnionOpens χ → ℝ)
    (hρ : letI := chartUnionChartedSpace χ hne; ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hρU : tsupport ρ ⊆ U) (hρc : HasCompactSupport ρ) {ε : E → ℝ}
    (hε : ContinuousOn ε (chartUnionOpens χ)) (hεpos : ∀ x ∈ chartUnionOpens χ, 0 < ε x) :
    ∃ p q : E → E, ContDiff ℝ r p ∧ ContDiff ℝ r q ∧
      (∀ x, x ∉ Subtype.val '' U → p x = 0 ∧ q x = 0) ∧
      (∀ z : chartUnionOpens χ, q z = ρ z • (z : E)) ∧
      (∀ k, k ≤ r → ∀ x ∈ chartUnionOpens χ,
        ‖iteratedFDeriv ℝ k (fun y => p y - q y) x‖ ≤ ε x) ∧
      (letI := chartUnionChartedSpace χ hne
       ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z : chartUnionOpens χ => p z)) := by
  have hV : IsOpen (Subtype.val '' U) := (chartUnionOpens χ).isOpenEmbedding'.isOpenMap U hU
  obtain ⟨e, hes, het, hecoe, hesymmcoe⟩ : ∃ e : OpenPartialHomeomorph E E,
      e.source = (χ a).source ∩ Subtype.val '' U ∧ e.target ⊆ (χ a).target ∧
        (∀ x, e x = χ a x) ∧ ∀ y, e.symm y = (χ a).symm y :=
    ⟨(χ a).restrOpen (Subtype.val '' U) hV, (χ a).restrOpen_source _ hV, inter_subset_left,
      fun _ => rfl, fun _ => rfl⟩
  have hsrc : e.source ⊆ (χ a).source := by
    rw [hes]
    exact inter_subset_left
  have hsrcV : e.source ⊆ Subtype.val '' U := by
    rw [hes]
    exact inter_subset_right
  have he : ContDiffOn ℝ r e e.source := ((hχ a).mono hsrc).congr fun x _ => hecoe x
  have hesymm : ContDiffOn ℝ r e.symm e.target :=
    ((hχsymm a).mono het).congr fun y _ => hesymmcoe y
  have hK : IsCompact (Subtype.val '' tsupport ρ) := hρc.isCompact.image continuous_subtype_val
  have hKs : Subtype.val '' tsupport ρ ⊆ e.source := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hes]
    exact ⟨hUa (hρU hz), mem_image_of_mem Subtype.val (hρU hz)⟩
  have hσ : ContDiffOn ℝ r (fun y => ρ (((χ a).subtypeRestr hne).symm y)) e.target :=
    ((contDiffOn_comp_chartUnion_symm χ hne htrans ρ hρ a).of_le ENat.LEInfty.out).mono het
  have hσK : ∀ y ∈ e.target, e.symm y ∉ Subtype.val '' tsupport ρ →
      ρ (((χ a).subtypeRestr hne).symm y) = 0 := by
    intro y hy hyK
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hyK
    have hval : (((χ a).subtypeRestr hne).symm y : E) = e.symm y := by
      rw [hesymmcoe y]
      exact chartUnion_symm_apply χ hne (het hy)
    rw [← hval]
    exact mem_image_of_mem Subtype.val hmem
  have hεe : ContinuousOn ε e.source :=
    hε.mono fun x hx => mem_chartUnionOpens.mpr ⟨a, hsrc hx⟩
  have hεepos : ∀ x ∈ e.source, 0 < ε x :=
    fun x hx => hεpos x (mem_chartUnionOpens.mpr ⟨a, hsrc hx⟩)
  obtain ⟨g, hg, hpreg, hpts, hqreg, hqts, hbd⟩ :=
    exists_chart_piece_approximation e r he hesymm hσ hK hKs hσK hεe hεepos
  refine ⟨e.source.indicator (g ∘ e),
    e.source.indicator (fun z => ρ (((χ a).subtypeRestr hne).symm (e z)) • z),
    hpreg, hqreg, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxs : x ∉ e.source := fun h => hx (hsrcV h)
    exact ⟨indicator_of_notMem hxs _, indicator_of_notMem hxs _⟩
  · intro z
    by_cases hz : (z : E) ∈ e.source
    · have hzs : (z : E) ∈ (χ a).source := hsrc hz
      have hleft : ((χ a).subtypeRestr hne).symm (χ a z) = z :=
        Subtype.ext ((chartUnion_symm_apply χ hne ((χ a).map_source hzs)).trans
          ((χ a).left_inv hzs))
      rw [indicator_of_mem hz, hecoe, hleft]
    · have hρz : ρ z = 0 :=
        image_eq_zero_of_notMem_tsupport fun hmem => hz (hKs (mem_image_of_mem Subtype.val hmem))
      rw [indicator_of_notMem hz, hρz, zero_smul]
  · intro k hk x hx
    have hk' : (k : ℕ∞ω) ≤ r := Nat.cast_le.mpr hk
    exact norm_iteratedFDeriv_sub_le_of_tsupport (hpreg.contDiffAt.of_le hk')
      (hqreg.contDiffAt.of_le hk') hpts hqts (hεpos x hx).le fun hxs => (hbd k hk x hxs).le
  · let _ : ChartedSpace E (chartUnionOpens χ) := chartUnionChartedSpace χ hne
    refine contMDiff_of_tsupport fun z hz => ?_
    have hzs : (z : E) ∈ e.source :=
      hpts (tsupport_comp_subset_preimage (e.source.indicator (g ∘ e)) continuous_subtype_val hz)
    have hzs' : z ∈ Subtype.val ⁻¹' e.source := hzs
    have heq : (fun w : chartUnionOpens χ => e.source.indicator (g ∘ e) w) =ᶠ[𝓝 z]
        (fun w : chartUnionOpens χ => g (χ a w)) := by
      filter_upwards [(e.open_source.preimage continuous_subtype_val).mem_nhds hzs'] with w hw
      have hw' : (w : E) ∈ e.source := hw
      rw [indicator_of_mem hw']
      exact congrArg g (hecoe w)
    exact (contMDiffAt_comp_chartUnion χ hne htrans g hg a z (hsrc hzs)).congr_of_eventuallyEq heq

private theorem exists_chart_smooth_fine_approximation_of_not_nonempty {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} {r : ℕ}
    (χ : ι → OpenPartialHomeomorph E E) {ε : E → ℝ} (hem : ¬Nonempty (chartUnionOpens χ)) :
    ∃ h : E → E,
      (∀ a, ContDiffOn ℝ ∞ (h ∘ (χ a).symm) (χ a).target) ∧
      ContDiffOn ℝ r h (⋃ a, (χ a).source) ∧
      ∀ x ∈ ⋃ a, (χ a).source, ∀ k, k ≤ r →
        ‖iteratedFDeriv ℝ k (fun y => h y - y) x‖ ≤ ε x := by
  have hfalse : ∀ x, x ∈ ⋃ a, (χ a).source → False := fun x hx =>
    hem ⟨⟨x, mem_chartUnionOpens.mpr (mem_iUnion.mp hx)⟩⟩
  refine ⟨id, fun a y hy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact (hfalse _ (mem_iUnion_of_mem a ((χ a).map_target hy))).elim
  · exact (hfalse x hx).elim
  · exact (hfalse x hx).elim

private theorem tsum_geometric_two_encode_le_two {κ : Type*} [Encodable κ] :
    ∑' i : κ, (1 / 2 : ℝ) ^ (Encodable.encode i) ≤ 2 :=
  (Summable.tsum_le_tsum_of_inj (f := fun i : κ => (1 / 2 : ℝ) ^ (Encodable.encode i))
    (g := fun n : ℕ => (1 / 2 : ℝ) ^ n) Encodable.encode Encodable.encode_injective
    (fun c _ => pow_nonneg (by norm_num) c) (fun _ => le_rfl)
    summable_geometric_two_encode summable_geometric_two).trans_eq tsum_geometric_two

theorem exists_chart_smooth_fine_approximation_of_nonempty {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} {r : ℕ}
    (χ : ι → OpenPartialHomeomorph E E)
    (hχ : ∀ a, ContDiffOn ℝ r (χ a) (χ a).source)
    (hχsymm : ∀ a, ContDiffOn ℝ r (χ a).symm (χ a).target)
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source)
    {ε : E → ℝ} (hε : ContinuousOn ε (⋃ a, (χ a).source))
    (hεpos : ∀ x ∈ ⋃ a, (χ a).source, 0 < ε x) (hne : Nonempty (chartUnionOpens χ)) :
    ∃ h : E → E,
      (∀ a, ContDiffOn ℝ ∞ (h ∘ (χ a).symm) (χ a).target) ∧
      ContDiffOn ℝ r h (⋃ a, (χ a).source) ∧
      ∀ x ∈ ⋃ a, (χ a).source, ∀ k, k ≤ r →
        ‖iteratedFDeriv ℝ k (fun y => h y - y) x‖ ≤ ε x := by
  let _ : ChartedSpace E (chartUnionOpens χ) := chartUnionChartedSpace χ hne
  have hWo : IsOpen (chartUnionOpens χ : Set E) := (chartUnionOpens χ).isOpen
  have hεW : ContinuousOn ε (chartUnionOpens χ : Set E) := hε
  have hmemW : ∀ x ∈ ⋃ a, (χ a).source, x ∈ chartUnionOpens χ :=
    fun x hx => mem_chartUnionOpens.mpr (mem_iUnion.mp hx)
  have hmemU : ∀ x ∈ chartUnionOpens χ, x ∈ ⋃ a, (χ a).source :=
    fun x hx => mem_iUnion.mpr (mem_chartUnionOpens.mp hx)
  obtain ⟨κ, ⟨hκ⟩, a, U, ρ, hUo, hUlf, hρU, hρc, hUa⟩ :=
    exists_chartUnion_partition χ hne htrans
  choose p q hp hq hvan hqρ hbd hpm using fun i : κ =>
    exists_chartUnion_piece χ hχ hχsymm htrans hne (a i) (U i) (hUo i) (hUa i) (ρ i)
      (ρ i).contMDiff (hρU i) (hρc i)
      (ε := fun x => (1 / 2 : ℝ) ^ (Encodable.encode i) * (ε x / 2))
      (continuousOn_const.fun_mul (hεW.div_const 2))
      (fun x hx => mul_pos (pow_pos (by norm_num) _) (half_pos (hεpos x (hmemU x hx))))
  have hnotimg : ∀ i (z : chartUnionOpens χ), z ∉ U i → (z : E) ∉ Subtype.val '' U i := by
    rintro i z hzU ⟨w, hw, hwz⟩
    have hwz' : w = z := Subtype.ext hwz
    rw [hwz'] at hw
    exact hzU hw
  have hsuppP : ∀ i, support (fun z : chartUnionOpens χ => p i z) ⊆ U i := by
    intro i z hz
    by_contra hzU
    exact (Function.mem_support.mp hz) (hvan i z (hnotimg i z hzU)).1
  have hsuppQ : ∀ i, support (fun z : chartUnionOpens χ => q i z) ⊆ U i := by
    intro i z hz
    by_contra hzU
    exact (Function.mem_support.mp hz) (hvan i z (hnotimg i z hzU)).2
  have hsuppPQ : ∀ i, support (fun z : chartUnionOpens χ => p i z - q i z) ⊆ U i := by
    intro i z hz
    by_contra hzU
    have hne0 : p i z - q i z ≠ 0 := Function.mem_support.mp hz
    rw [(hvan i z (hnotimg i z hzU)).1, (hvan i z (hnotimg i z hzU)).2, sub_self] at hne0
    exact hne0 rfl
  have hlocP : LocallyFinite fun i => support (fun z : chartUnionOpens χ => p i z) :=
    hUlf.subset hsuppP
  have hlocQ : LocallyFinite fun i => support (fun z : chartUnionOpens χ => q i z) :=
    hUlf.subset hsuppQ
  have hlocPQ : LocallyFinite fun i => support (fun z : chartUnionOpens χ => p i z - q i z) :=
    hUlf.subset hsuppPQ
  have hsumq : ∀ z : chartUnionOpens χ, ∑ᶠ i, q i z = (z : E) := by
    intro z
    have hfin : Function.HasFiniteSupport fun i => ρ i z := ρ.locallyFinite.point_finite z
    calc ∑ᶠ i, q i z = ∑ᶠ i, ρ i z • (z : E) := finsum_congr fun i => hqρ i z
      _ = (∑ᶠ i, ρ i z) • (z : E) := (finsum_smul' hfin (z : E)).symm
      _ = (z : E) := by rw [ρ.sum_eq_one (mem_univ z), one_smul]
  refine ⟨fun x => ∑ᶠ i, p i x, fun b => ?_, ?_, fun x hx k hk => ?_⟩
  · have hH : letI := chartUnionChartedSpace χ hne
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z : chartUnionOpens χ => ∑ᶠ i, p i z) := by
      have hpm' : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z : chartUnionOpens χ => p i z) := hpm
      exact contMDiff_finsum hpm' hlocP
    refine (contDiffOn_comp_chartUnion_symm χ hne htrans _ hH b).congr fun y hy => ?_
    change ∑ᶠ i, p i ((χ b).symm y) = ∑ᶠ i, p i (((χ b).subtypeRestr hne).symm y : E)
    rw [chartUnion_symm_apply χ hne hy]
  · have hc : ContDiffOn ℝ r (fun x => ∑ᶠ i, p i x) (chartUnionOpens χ : Set E) :=
      contDiffOn_finsum_of_locallyFinite_restrict (f := p) hWo hlocP (r : ℕ∞ω)
        fun i => (hp i).contDiffOn
    exact hc
  · have hxW : x ∈ (chartUnionOpens χ : Set E) := hmemW x hx
    have hev : (fun y => ∑ᶠ i, p i y - y) =ᶠ[𝓝 x] (fun y => ∑ᶠ i, (p i y - q i y)) := by
      filter_upwards [hWo.mem_nhds hxW] with y hy
      have hfp : Function.HasFiniteSupport fun i => p i y := hlocP.point_finite ⟨y, hy⟩
      have hfq : Function.HasFiniteSupport fun i => q i y := hlocQ.point_finite ⟨y, hy⟩
      have hq' : ∑ᶠ i, q i y = y := hsumq ⟨y, hy⟩
      rw [finsum_sub_distrib hfp hfq, hq']
    have hjet : iteratedFDeriv ℝ k (fun y => ∑ᶠ i, p i y - y) x =
        iteratedFDeriv ℝ k (fun y => ∑ᶠ i, (p i y - q i y)) x :=
      (hev.iteratedFDeriv ℝ k).eq_of_nhds
    have hk' : (k : ℕ∞ω) ≤ r := Nat.cast_le.mpr hk
    have hbound := norm_iteratedFDeriv_finsum_le_of_locallyFinite_restrict
      (f := fun i y => p i y - q i y) hWo hlocPQ k hxW
      (fun i => ((hp i).sub (hq i)).contDiffAt.of_le hk')
      (summable_geometric_two_encode.mul_right (ε x / 2))
      (fun i => hbd i k hk x hxW)
    have hfinal : ‖iteratedFDeriv ℝ k (fun y => ∑ᶠ i, (p i y - q i y)) x‖ ≤ ε x := by
      refine hbound.trans ?_
      rw [Summable.tsum_mul_right _ summable_geometric_two_encode]
      calc (∑' i : κ, (1 / 2 : ℝ) ^ (Encodable.encode i)) * (ε x / 2) ≤ 2 * (ε x / 2) :=
            mul_le_mul_of_nonneg_right tsum_geometric_two_encode_le_two
              (half_pos (hεpos x hx)).le
        _ = ε x := by ring
    rw [← hjet] at hfinal
    exact hfinal

theorem exists_chart_smooth_fine_approximation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} {r : ℕ}
    (χ : ι → OpenPartialHomeomorph E E)
    (hχ : ∀ a, ContDiffOn ℝ r (χ a) (χ a).source)
    (hχsymm : ∀ a, ContDiffOn ℝ r (χ a).symm (χ a).target)
    (htrans : ∀ a b,
      ContDiffOn ℝ ∞ ((χ a).symm.trans (χ b)) ((χ a).symm.trans (χ b)).source)
    {ε : E → ℝ} (hε : ContinuousOn ε (⋃ a, (χ a).source))
    (hεpos : ∀ x ∈ ⋃ a, (χ a).source, 0 < ε x) :
    ∃ h : E → E,
      (∀ a, ContDiffOn ℝ ∞ (h ∘ (χ a).symm) (χ a).target) ∧
      ContDiffOn ℝ r h (⋃ a, (χ a).source) ∧
      ∀ x ∈ ⋃ a, (χ a).source, ∀ k, k ≤ r →
        ‖iteratedFDeriv ℝ k (fun y => h y - y) x‖ ≤ ε x := by
  by_cases hne : Nonempty (chartUnionOpens χ)
  · exact exists_chart_smooth_fine_approximation_of_nonempty χ hχ hχsymm htrans hε hεpos hne
  · exact exists_chart_smooth_fine_approximation_of_not_nonempty χ hne

end DifferentialGeometry.Analysis
