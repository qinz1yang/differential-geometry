import DifferentialGeometry.Analysis.Calculus.Cutoff.ExponentialProfile
import DifferentialGeometry.Topology.OpenPartialHomeomorph.FiniteCollarFrontier
import DifferentialGeometry.Topology.Manifold.CollarStep
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

noncomputable section

open Set Filter _root_.Topology _root_.Manifold
open DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private theorem common_positive_radius {ι : Type*} [Finite ι]
    {R : ℝ} (hR : 0 < R) (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ i, r < f i := by
  have hnear : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i, r < f i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (eventually_lt_nhds (hf i)).filter_mono nhdsWithin_le_nhds
  have hnearR : ∀ᶠ r : ℝ in 𝓝[>] 0, r < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := eventually_mem_nhdsWithin
  exact (hpos.and (hnearR.and hnear)).exists

variable {E F H G N M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [CompactSpace N]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [Finite ι]

private theorem finite_outward_band [PreconnectedSpace N]
    (e : ι → PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    {L : Set M} (hregular : closure (interior L) = L)
    (hfront : frontier L = ⋃ i, range (fun s : N => e i (s, 0)))
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun s : N => e i (s, 0))) (range (fun s : N => e j (s, 0)))))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ i, univ ×ˢ Icc (-R) R ⊆ (e i).source)
    (hpositive : ∀ i s r, r ∈ Ioc (0 : ℝ) R → e i (s, r) ∉ L) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      (∀ i, univ ×ˢ Icc (-r) r ⊆ (e i).source) ∧
      Pairwise (fun i j => Disjoint
        (e i '' (univ ×ˢ Ioo (-r) r)) (e j '' (univ ×ˢ Ioo (-r) r))) ∧
      ∀ i s h, h ∈ Ioo (-r) r →
        (e i (s, h) ∈ L ↔ h ≤ 0) ∧
        (e i (s, h) ∈ interior L ↔ h < 0) := by
  classical
  rcases isEmpty_or_nonempty N with hN | hN
  · let := hN
    refine ⟨R / 2, half_pos hR, half_lt_self hR, ?_, ?_, ?_⟩
    · intro i p hp
      exact isEmptyElim p.1
    · intro i j hij
      apply disjoint_left.mpr
      rintro x ⟨p, hp, hpx⟩ hxj
      exact isEmptyElim p.1
    · intro i s
      exact isEmptyElim s
  · let := hN
    let s₀ : N := Classical.choice hN
    let f i := (e i).toOpenPartialHomeomorph
    have hz (i : ι) (s : N) : (s, (0 : ℝ)) ∈ (f i).source :=
      hsource i ⟨mem_univ _, neg_nonpos.mpr hR.le, hR.le⟩
    have hm (i : ι) : (range (fun s : N => f i (s, 0)) ∩ frontier L).Nonempty := by
      refine ⟨f i (s₀, 0), mem_range_self s₀, ?_⟩
      rw [hfront]
      exact mem_iUnion.mpr ⟨i, mem_range_self s₀⟩
    obtain ⟨_, hsides⟩ := frontier_eq_iUnion_of_finite_disjoint_collars
      f hz hdisjoint hregular hfront.subset
    choose w σ hw hσ hws hside hinterior using fun i => hsides i (hm i)
    have hσone (i : ι) : σ i = 1 := by
      rcases hσ i with h | h
      · exact h
      · let z := min (w i) R / 2
        have hzpos : 0 < z := half_pos (lt_min (hw i) hR)
        have hzw : z < w i := (half_lt_self (lt_min (hw i) hR)).trans_le (min_le_left _ _)
        have hzR : z ≤ R := ((half_lt_self (lt_min (hw i) hR)).trans_le (min_le_right _ _)).le
        have hzmem : z ∈ Ioo (-w i) (w i) := ⟨(neg_lt_zero.mpr (hw i)).trans hzpos, hzw⟩
        have hin := (hside i s₀ z hzmem).mpr (by rw [h]; linarith)
        exact False.elim (hpositive i s₀ z ⟨hzpos, hzR⟩ hin)
    have hzeroBand (i : ι) :
        f i '' (univ ×ˢ Icc (0 : ℝ) 0) = range (fun s : N => f i (s, 0)) := by
      ext x
      constructor
      · rintro ⟨⟨s, h⟩, hh, rfl⟩
        have hh0 : h = 0 := le_antisymm hh.2.2 hh.2.1
        subst h
        exact mem_range_self s
      · rintro ⟨s, rfl⟩
        exact ⟨(s, 0), ⟨mem_univ _, le_rfl, le_rfl⟩, rfl⟩
    obtain ⟨a, b, hab, hsrc, hsep⟩ :=
      Compactness.exists_larger_product_chart_bands_preserving_disjointness f
        (fun _ => 0) (fun _ => 0) (fun _ => le_rfl)
        (fun i p hp => by
          rcases p with ⟨s, h⟩
          have hh0 : h = 0 := le_antisymm hp.2.2 hp.2.1
          subst h
          exact hz i s)
        (fun i j => i ≠ j) (fun i j hij => by
          rw [hzeroBand, hzeroBand]
          simpa only [f, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph] using hdisjoint hij)
    obtain ⟨r, hr, hrR, hrall⟩ := common_positive_radius hR
      (fun i => min (w i) (min (-a i) (b i)))
      (fun i => lt_min (hw i) (lt_min (neg_pos.mpr (hab i).1) (hab i).2))
    have hrw (i : ι) : r < w i := (hrall i).trans_le (min_le_left _ _)
    have hrsmall (i : ι) : (univ : Set N) ×ˢ Ioo (-r) r ⊆ univ ×ˢ Ioo (a i) (b i) := by
      intro p hp
      have hleft := (hrall i).trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hright := (hrall i).trans_le ((min_le_right _ _).trans (min_le_right _ _))
      exact ⟨hp.1, by linarith [hp.2.1], hp.2.2.trans hright⟩
    refine ⟨r, hr, hrR, ?_, ?_, ?_⟩
    · intro i p hp
      exact hsource i ⟨hp.1, by linarith [hp.2.1], hp.2.2.trans hrR.le⟩
    · intro i j hij
      exact (hsep i j hij).mono (image_mono (hrsmall i)) (image_mono (hrsmall j))
    · intro i s h hh
      have hhw : h ∈ Ioo (-w i) (w i) := ⟨by linarith [hh.1, hrw i], hh.2.trans (hrw i)⟩
      have hs := hside i s h hhw
      have hi := hinterior i s h hhw
      simp only [f, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
        hσone i, one_mul] at hs hi
      exact ⟨hs, hi⟩

private def collarBand
    (e : ι → PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞) (r : ℝ) (i : ι) : Set M :=
  e i '' (univ ×ˢ Ioo (-r) r)

omit [T2Space M] in
private theorem glue_finite_collar_height
    (e : ι → PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    {r : ℝ}
    (hsource : ∀ i, univ ×ˢ Icc (-r) r ⊆ (e i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint (collarBand e r i) (collarBand e r j))) :
    ∃ q : M → ℝ,
      ContMDiffOn I 𝓘(ℝ) ∞ q (⋃ i, collarBand e r i) ∧
      (∀ i x, x ∈ collarBand e r i → q x = ((e i).symm x).2) ∧
      (∀ i s h, h ∈ Ioo (-r) r → q (e i (s, h)) = h) ∧
      ∀ a b : ℝ, -r < a → b < r →
        IsCompact ((⋃ i, collarBand e r i) ∩ q ⁻¹' Icc a b) := by
  classical
  let U := ⋃ i, collarBand e r i
  let q : M → ℝ := fun x =>
    if h : ∃ i, x ∈ collarBand e r i then ((e h.choose).symm x).2 else 0
  have hsrc (i : ι) : univ ×ˢ Ioo (-r) r ⊆ (e i).source :=
    fun p hp => hsource i ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  have hopen (i : ι) : IsOpen (collarBand e r i) :=
    (e i).toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_univ.prod isOpen_Ioo) (hsrc i)
  have heq (i : ι) (x : M) (hx : x ∈ collarBand e r i) : q x = ((e i).symm x).2 := by
    have hh : ∃ j, x ∈ collarBand e r j := ⟨i, hx⟩
    have hji : hh.choose = i := by
      by_contra hne
      exact disjoint_left.mp (hdisjoint hne) hh.choose_spec hx
    simp only [q, dite_eq_left hh, hji]
  have hq : ContMDiffOn I 𝓘(ℝ) ∞ q U := by
    apply (contMDiffOn_iUnion_iff_of_isOpen hopen).mpr
    intro i
    have hi : collarBand e r i ⊆ (e i).target := by
      rintro x ⟨p, hp, rfl⟩
      exact (e i).toPartialEquiv.map_source (hsrc i hp)
    exact (contMDiff_snd.comp_contMDiffOn ((e i).symm.contMDiffOn.mono hi)).congr
      (fun x hx => heq i x hx)
  have happly (i : ι) (s : N) (h : ℝ) (hh : h ∈ Ioo (-r) r) : q (e i (s, h)) = h := by
    rw [heq i _ ⟨(s, h), ⟨mem_univ _, hh⟩, rfl⟩]
    exact congrArg Prod.snd ((e i).toPartialEquiv.left_inv (hsrc i ⟨mem_univ _, hh⟩))
  refine ⟨q, hq, heq, happly, ?_⟩
  intro a b ha hb
  have hbands : U ∩ q ⁻¹' Icc a b = ⋃ i, e i '' (univ ×ˢ Icc a b) := by
    ext x
    constructor
    · rintro ⟨hx, hqx⟩
      obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, p, ⟨hp.1, by simpa only [mem_preimage, happly i p.1 p.2 hp.2] using hqx⟩, rfl⟩
    · intro hx
      obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hx
      have hp' : p.2 ∈ Ioo (-r) r := ⟨ha.trans_le hp.2.1, hp.2.2.trans_lt hb⟩
      exact ⟨mem_iUnion.mpr ⟨i, p, ⟨hp.1, hp'⟩, rfl⟩,
        by simpa only [mem_preimage, happly i p.1 p.2 hp'] using hp.2⟩
  rw [hbands]
  apply isCompact_iUnion
  intro i
  exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    ((e i).contMDiffOn.continuousOn.mono (fun p hp =>
      hsource i ⟨hp.1, (ha.trans_le hp.2.1).le, (hp.2.2.trans_lt hb).le⟩))


open scoped Classical in
/-- Glue the prescribed exponential profile at a radius fixed by the caller.
The oriented bands are geometric inputs of this construction engine. -/
theorem exists_smooth_defining_function_of_oriented_finite_collars
    (e : ι → PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    {L : Set M} (hclosed : IsClosed L)
    (hfront : frontier L ⊆ ⋃ i, range (fun s : N => e i (s, 0)))
    {r : ℝ} (hr : 0 < r)
    (hsource : ∀ i, univ ×ˢ Icc (-r) r ⊆ (e i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (e i '' (univ ×ˢ Ioo (-r) r)) (e j '' (univ ×ˢ Ioo (-r) r))))
    (hside : ∀ i s h, h ∈ Ioo (-r) r →
      (e i (s, h) ∈ L ↔ h ≤ 0) ∧
      (e i (s, h) ∈ interior L ↔ h < 0)) :
    let a : ℝ := (Real.exp (r / 2) - 1) / 2
    0 < a ∧ Real.log (1 + a) < r / 2 ∧
    ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ ρ ∧
      (interior L)ᶜ = {x | ρ x ≤ 0} ∧
      (∀ i s h, h ∈ Ioo (-r) r →
        ρ (e i (s, h)) = DifferentialGeometry.Analysis.flattenedExponentialProfile r h) ∧
      (∀ x, x ∉ ⋃ i, e i '' (univ ×ˢ Ioo (-r) r) →
        ρ x = if x ∈ L then Real.exp (r / 2) - 1 else Real.exp (-r / 2) - 1) ∧
      ∀ x, 0 ≤ ρ x → ρ x < a →
        ∃ i, x ∈ e i '' (univ ×ˢ Ioo (-r) r) ∧
          ρ =ᶠ[𝓝 x] (fun y => Real.exp (-((e i).symm y).2) - 1) := by
  classical
  have hcollarSide := hside
  obtain ⟨q, hq, hqinv, hqapply, hcompact⟩ :=
    glue_finite_collar_height e hsource hdisjoint
  let U : Set M := ⋃ i, collarBand e r i
  have hopeni (i : ι) : IsOpen (collarBand e r i) :=
    (e i).toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_univ.prod isOpen_Ioo)
      (fun p hp => hsource i ⟨hp.1, hp.2.1.le, hp.2.2.le⟩)
  have hopen : IsOpen U := isOpen_iUnion hopeni
  have hside : ∀ x ∈ U, x ∈ L ↔ q x ≤ 0 := by
    intro x hx
    obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hx
    rw [hqapply i p.1 p.2 hp.2]
    exact (hcollarSide i p.1 p.2 hp.2).1
  have hsideInterior : ∀ x ∈ U, x ∈ interior L ↔ q x < 0 := by
    intro x hx
    obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hx
    rw [hqapply i p.1 p.2 hp.2]
    exact (hcollarSide i p.1 p.2 hp.2).2
  have hfrontU : frontier L ⊆ U := by
    intro x hx
    obtain ⟨i, s, rfl⟩ := mem_iUnion.mp (hfront hx)
    exact mem_iUnion.mpr ⟨i, (s, 0), ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩
  have hfrontBand : frontier L ⊆ U ∩ q ⁻¹' Icc (-3 * r / 4) (3 * r / 4) := by
    intro x hx
    obtain ⟨i, s, rfl⟩ := mem_iUnion.mp (hfront hx)
    refine ⟨mem_iUnion.mpr ⟨i, (s, 0), ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩, ?_⟩
    rw [mem_preimage, hqapply i s 0 ⟨neg_lt_zero.mpr hr, hr⟩]
    constructor <;> linarith
  have hL : 0 < Real.exp (r / 2) - 1 :=
    sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr (half_pos hr))
  have hQ : Real.exp (-r / 2) - 1 < 0 :=
    sub_neg.mpr (by simpa using Real.exp_lt_exp.mpr (show -r / 2 < 0 by linarith))
  have hdiff : (Real.exp (-r / 2) - 1) - (Real.exp (r / 2) - 1) ≠ 0 := ne_of_lt (by linarith)
  let β : ℝ → ℝ := fun s => (flattenedExponentialProfile r s - (Real.exp (r / 2) - 1)) /
    ((Real.exp (-r / 2) - 1) - (Real.exp (r / 2) - 1))
  have hβ : ContDiff ℝ ∞ β := ((contDiff_flattenedExponentialProfile r).sub contDiff_const).div_const _
  have hβzero : ∀ s, s ≤ -3 * r / 4 → β s = 0 := by
    intro s hs
    simp only [β, flattenedExponentialProfile_eq_left hr hs, sub_self, zero_div]
  have hβone : ∀ s, 3 * r / 4 ≤ s → β s = 1 := by
    intro s hs
    simp only [β, flattenedExponentialProfile_eq_right hr hs, div_self hdiff]
  let θ := DifferentialGeometry.Topology.Manifold.collarStep U L q β
  have hθ : ContMDiff I 𝓘(ℝ) ∞ θ :=
    DifferentialGeometry.Topology.Manifold.contMDiff_collarStep hopen hclosed q hq β hβ
      (-3 * r / 4) 0 (3 * r / 4) (by linarith) (by linarith) hside hβzero hβone
      (hcompact _ _ (by linarith) (by linarith)).isClosed hfrontBand
  let ρ : M → ℝ := fun x => (Real.exp (r / 2) - 1) + ((Real.exp (-r / 2) - 1) - (Real.exp (r / 2) - 1)) * θ x
  have hρ : ContMDiff I 𝓘(ℝ) ∞ ρ := by
    have haffine : ContDiff ℝ ∞ (fun s : ℝ =>
        (Real.exp (r / 2) - 1) +
          ((Real.exp (-r / 2) - 1) - (Real.exp (r / 2) - 1)) * s) :=
      contDiff_const.add (contDiff_const.mul contDiff_id)
    exact haffine.comp_contMDiff hθ
  have hρU (x : M) (hx : x ∈ U) : ρ x = flattenedExponentialProfile r (q x) := by
    simp only [ρ, θ, DifferentialGeometry.Topology.Manifold.collarStep, ite_eq_left hx, β]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hdiff]
    ring
  have hρoff (x : M) (hx : x ∉ U) :
      ρ x = if x ∈ L then (Real.exp (r / 2) - 1) else (Real.exp (-r / 2) - 1) := by
    simp only [ρ, θ, DifferentialGeometry.Topology.Manifold.collarStep, ite_eq_right hx]
    split_ifs <;> ring
  have hρregion : (interior L)ᶜ = {x | ρ x ≤ 0} := by
    ext x
    by_cases hx : x ∈ U
    · rw [mem_compl_iff, mem_ofPred_eq, hsideInterior x hx, hρU x hx,
        (flattenedExponentialProfile_sign hr).1, not_lt]
    · rw [mem_compl_iff, mem_ofPred_eq, hρoff x hx]
      have hnotfront : x ∉ frontier L := fun h => hx (hfrontU h)
      have hi : x ∈ interior L ↔ x ∈ L := by
        refine ⟨fun hxI => interior_subset hxI, fun h => ?_⟩
        by_contra hn
        exact hnotfront ⟨subset_closure h, hn⟩
      rw [hi]
      by_cases hxl : x ∈ L
      · simp only [hxl, ite_true, not_true_eq_false, false_iff]
        exact not_le_of_gt hL
      · simp only [hxl, ite_false, not_false_eq_true, true_iff]
        exact hQ.le
  let a := (Real.exp (r / 2) - 1) / 2
  have ha : 0 < a := half_pos hL
  have haL : a < (Real.exp (r / 2) - 1) := half_lt_self hL
  have hlog : Real.log (1 + a) < r / 2 := by
    rw [Real.log_lt_iff_lt_exp (by linarith)]
    linarith
  refine ⟨ha, hlog, ρ, hρ, hρregion, ?_, hρoff, ?_⟩
  · intro i s h hh
    rw [hρU _ (mem_iUnion.mpr ⟨i, (s, h), ⟨mem_univ _, hh⟩, rfl⟩), hqapply i s h hh]
  · intro x hx0 hxa
    have hxU : x ∈ U := by
      by_contra hx
      have hh := hρoff x hx
      by_cases hl : x ∈ L
      · rw [ite_eq_left hl] at hh
        linarith
      · rw [ite_eq_right hl] at hh
        linarith
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxU
    have hc : q x ∈ Ioo (-r / 2) (r / 2) :=
      mem_central_interval_of_flattenedExponentialProfile_mem_Ico hr haL (by rw [← hρU x hxU]; exact ⟨hx0, hxa⟩)
    have hqAt : ContinuousAt q x :=
      (hq.continuousOn x hxU).continuousAt (hopen.mem_nhds hxU)
    refine ⟨i, hxi, ?_⟩
    filter_upwards [(hopeni i).mem_nhds hxi, hqAt (isOpen_Ioo.mem_nhds hc)] with y hyi hyc
    have hyU : y ∈ U := mem_iUnion.mpr ⟨i, hyi⟩
    rw [hρU y hyU, flattenedExponentialProfile_eq_exp hr ⟨hyc.1.le, hyc.2.le⟩, hqinv i y hyi]


open scoped Classical in
/-- The whole frontier and positive-side exclusion determine outward orientations
and one common radius before constructing the defining function. -/
theorem exists_smooth_defining_function_of_finite_collars [PreconnectedSpace N]
    (e : ι → PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    {L : Set M} (hregular : closure (interior L) = L)
    (hfront : frontier L = ⋃ i, range (fun s : N => e i (s, 0)))
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun s : N => e i (s, 0))) (range (fun s : N => e j (s, 0)))))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ i, univ ×ˢ Icc (-R) R ⊆ (e i).source)
    (hpositive : ∀ i s h, h ∈ Ioc (0 : ℝ) R → e i (s, h) ∉ L) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      (∀ i, univ ×ˢ Icc (-r) r ⊆ (e i).source) ∧
      Pairwise (fun i j => Disjoint
        (e i '' (univ ×ˢ Ioo (-r) r)) (e j '' (univ ×ˢ Ioo (-r) r))) ∧
      (∀ i s h, h ∈ Ioo (-r) r →
        (e i (s, h) ∈ L ↔ h ≤ 0) ∧
        (e i (s, h) ∈ interior L ↔ h < 0)) ∧
      let a : ℝ := (Real.exp (r / 2) - 1) / 2
    0 < a ∧ Real.log (1 + a) < r / 2 ∧
    ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ ρ ∧
      (interior L)ᶜ = {x | ρ x ≤ 0} ∧
      (∀ i s h, h ∈ Ioo (-r) r →
        ρ (e i (s, h)) = DifferentialGeometry.Analysis.flattenedExponentialProfile r h) ∧
      (∀ x, x ∉ ⋃ i, e i '' (univ ×ˢ Ioo (-r) r) →
        ρ x = if x ∈ L then Real.exp (r / 2) - 1 else Real.exp (-r / 2) - 1) ∧
      ∀ x, 0 ≤ ρ x → ρ x < a →
        ∃ i, x ∈ e i '' (univ ×ˢ Ioo (-r) r) ∧
          ρ =ᶠ[𝓝 x] (fun y => Real.exp (-((e i).symm y).2) - 1) := by
  obtain ⟨r, hr, hrR, hrsrc, hrdisjoint, hrside⟩ :=
    finite_outward_band e hregular hfront hdisjoint hR hsource hpositive
  refine ⟨r, hr, hrR, hrsrc, hrdisjoint, hrside, ?_⟩
  exact exists_smooth_defining_function_of_oriented_finite_collars e
    (hregular ▸ isClosed_closure) hfront.subset hr hrsrc hrdisjoint hrside

end DifferentialGeometry.Topology.Manifold
