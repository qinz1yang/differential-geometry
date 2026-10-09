/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.FixedLocusDistance

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.StratumMaximum

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open HyperbolicConvexity OrbifoldStrata FixedLocusGeometry LorentzExtremal
open StratumDeformation AxisGeometry AxialStratumDeformation FixedLocusDistance

variable {n : ℕ}

theorem normalEnergy_smul_of_label (hn : 1 ≤ n) (g : PO n 1)
    {σ : Set (HUpper n)}
    (hσ : (fun x : HUpper n => (poMulAction hn).smul g x) '' σ = σ) (x : HUpper n) :
    normalEnergy σ ((poMulAction hn).smul g x) = normalEnergy σ x := by
  have hi : Isometry (fun x : HUpper n => (poMulAction hn).smul g x) :=
    Isometry.of_dist_eq (po_dist_smul hn g)
  have h := Metric.infDist_image (x := x) (t := σ) hi
  rw [hσ] at h
  simp only [normalEnergy, h]

theorem exists_compact_label_cover (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) {σ : Set (HUpper n)} (hσ : σ.Nonempty) :
    ∃ C : Set (HUpper n), IsCompact C ∧ C ⊆ closure (fixedStratum hn Γ ε σ) ∧
      ∀ x ∈ closure (fixedStratum hn Γ ε σ), ∃ γ : Γ,
        (fun p : HUpper n => (poMulAction hn).smul (γ : PO n 1) p) '' σ = σ ∧
        (poMulAction hn).smul (γ : PO n 1) x ∈ C := by
  classical
  let := poMulAction hn
  obtain ⟨K, hK, hcover⟩ := exists_compact_cover_closure_fixedStratum hn Γ hΓ hcov hε hσ
  let S : Set (Set (HUpper n)) :=
    {τ | (closure (fixedStratum hn Γ ε τ) ∩ K).Nonempty ∧
      ∃ δ : Γ, (fun p : HUpper n => (δ : PO n 1) • p) '' σ = τ}
  have hS : S.Finite :=
    ((locallyFinite_fixedStratum hn Γ hΓ ε).closure.finite_nonempty_inter_compact hK).subset
      (fun _ h => h.1)
  let : Finite S := hS
  choose δ hδ using fun τ : S => τ.property.2
  let C : Set (HUpper n) :=
    (⋃ τ : S, (fun p : HUpper n => ((δ τ : Γ) : PO n 1)⁻¹ • p) '' K) ∩
      closure (fixedStratum hn Γ ε σ)
  have hC : IsCompact C := by
    apply IsCompact.inter_right _ isClosed_closure
    apply isCompact_iUnion
    intro τ
    exact hK.image ((ContinuousAction.continuous_po_smul hn).comp
      (continuous_const.prodMk continuous_id))
  refine ⟨C, hC, inter_subset_right, fun x hx => ?_⟩
  obtain ⟨d, hd⟩ := hcover x hx
  let τ : S := ⟨(fun p : HUpper n => (d : PO n 1) • p) '' σ,
    ⟨⟨(d : PO n 1) • x, smul_mem_closure_fixedStratum hn Γ ε hx d, hd⟩, d, rfl⟩⟩
  let γ : Γ := (δ τ)⁻¹ * d
  have hlabel : (fun p : HUpper n => (γ : PO n 1) • p) '' σ = σ := by
    change (fun p : HUpper n => (((δ τ : Γ) : PO n 1)⁻¹ * (d : PO n 1)) • p) '' σ = σ
    simp only [mul_smul, ← image_image]
    change (fun p : HUpper n => ((δ τ : Γ) : PO n 1)⁻¹ • p) '' τ.val = σ
    rw [← hδ τ, image_image]
    simp only [inv_smul_smul, image_id']
  refine ⟨γ, hlabel, ?_, ?_⟩
  · apply mem_iUnion.mpr
    refine ⟨τ, (d : PO n 1) • x, hd, ?_⟩
    change _ = (((δ τ : Γ) : PO n 1)⁻¹ * (d : PO n 1)) • x
    rw [mul_smul]
  · have h := smul_mem_closure_fixedStratum hn Γ ε hx γ
    change (γ : PO n 1) • x ∈
      closure (fixedStratum hn Γ ε ((fun p : HUpper n => (γ : PO n 1) • p) '' σ)) at h
    rwa [hlabel] at h

theorem exists_normalEnergy_maximum (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) {σ : Set (HUpper n)} (hσ : σ.Nonempty)
    {z : HUpper n} (hz : z ∈ fixedStratum hn Γ ε σ) (hzσ : z ∉ σ) :
    ∃ x ∈ closure (fixedStratum hn Γ ε σ), 0 < normalEnergy σ x ∧
      ∀ y ∈ closure (fixedStratum hn Γ ε σ), normalEnergy σ y ≤ normalEnergy σ x := by
  have he : fixedLocus hn (closedSmallSubgroup hn Γ ε z) = σ := hz
  have hclosed : IsClosed σ := he ▸ isClosed_fixedLocus hn _
  obtain ⟨C, hC, hCsub, hcover⟩ := exists_compact_label_cover hn Γ hΓ hcov hε hσ
  obtain ⟨δ, hδlabel, hδ⟩ := hcover z (subset_closure hz)
  obtain ⟨x, hx, hmax⟩ := hC.exists_isMaxOn ⟨_, hδ⟩ (continuous_normalEnergy σ).continuousOn
  have hpos : 0 < normalEnergy σ x := by
    have h : normalEnergy σ ((poMulAction hn).smul (δ : PO n 1) z) ≤ normalEnergy σ x := hmax hδ
    rw [normalEnergy_smul_of_label hn δ hδlabel z] at h
    exact (normalEnergy_pos hσ hclosed hzσ).trans_le h
  refine ⟨x, hCsub hx, hpos, fun y hy => ?_⟩
  obtain ⟨γ, hγlabel, hγ⟩ := hcover y hy
  have h : normalEnergy σ ((poMulAction hn).smul (γ : PO n 1) y) ≤ normalEnergy σ x := hmax hγ
  rwa [normalEnergy_smul_of_label hn γ hγlabel y] at h

theorem submodule_eq_top_of_all_val (V : Submodule ℝ (LorVec n))
    (hV : ∀ p : HUpper n, p.val ∈ V) : V = ⊤ := by
  classical
  have hb : ∀ i : Fin n ⊕ Fin 1, Pi.single i (1 : ℝ) ∈ V := by
    intro i
    rcases i with i | i
    · have h := V.sub_mem (hV (boostH i)) (V.smul_mem (Real.sqrt 2) (hV basepointH))
      change eBoost i - Real.sqrt 2 • eTime ∈ V at h
      rwa [eBoost_sub_smul_eTime] at h
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hV basepointH
  apply top_le_iff.mp
  intro v _
  have h := V.sum_mem (t := Finset.univ) (fun i _ => V.smul_mem (v i) (hb i))
  convert h using 1
  ext i
  simp [Pi.single_apply]

theorem interior_axis_eq_empty (hn : 2 ≤ n) (ξ η : BoundaryH n) :
    interior (axis ξ η) = ∅ := by
  classical
  apply Set.not_nonempty_iff_eq_empty.mp
  intro h
  have htop := submodule_eq_top_of_all_val (axisPlane ξ η)
    (StratumIncidence.val_mem_of_interior_section_nonempty (axisPlane ξ η) h)
  have hdim : Module.finrank ℝ (axisPlane ξ η) ≤ 2 := by
    have h := finrank_span_finset_le_card (R := ℝ) ({ξ.val, η.val} : Finset (LorVec n))
    have hc : ({ξ.val, η.val} : Finset (LorVec n)).card ≤ 2 := by
      simpa only [Finset.card_singleton] using Finset.card_insert_le ξ.val {η.val}
    have he : (({ξ.val, η.val} : Finset (LorVec n)) : Set (LorVec n)) = {ξ.val, η.val} := by
      ext v
      simp
    change Module.finrank ℝ (Submodule.span ℝ _) ≤ _ at h
    rw [he] at h
    exact h.trans hc
  rw [htop] at hdim
  simp only [finrank_top, LorVec, Module.finrank_pi, Fintype.card_sum,
    Fintype.card_fin] at hdim
  omega

theorem not_isOpen_of_axial_maximum (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ : Set (HUpper n)} (hσ : σ.Nonempty) {x : HUpper n}
    (hx : x ∈ closure (fixedStratum hn Γ ε σ))
    (hpos : 0 < normalEnergy σ x)
    (hmax : ∀ y ∈ closure (fixedStratum hn Γ ε σ), normalEnergy σ y ≤ normalEnergy σ x)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : ∀ γ : closedSmallSubgroup hn Γ ε x,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n))) :
    ¬IsOpen (fixedStratum hn Γ ε σ) := by
  intro hopen
  obtain ⟨z, hz, hzF⟩ := mem_closure_iff_nhds.mp hx _
    (eventually_closedSmallSubgroup_le hn Γ hΓ ε x)
  have hlabel : fixedLocus hn (closedSmallSubgroup hn Γ ε z) = σ := hzF
  have hclosed : IsClosed σ := hlabel ▸ isClosed_fixedLocus hn _
  have hsection : σ = {p : HUpper n | p.val ∈ locusSpan σ} := by
    simpa only [hlabel] using fixedLocus_eq_preimage_span hn
      (closedSmallSubgroup hn Γ ε z) (hlabel.symm ▸ hσ)
  have hproj : ∀ p ∈ σ, axisFoot ξ η hne p ∈ σ := by
    intro p hp
    have h := axisFoot_mem_fixedLocus hn (closedSmallSubgroup hn Γ ε z) ξ η hne
      (fun γ => hpair ⟨γ, hz γ.property⟩) (hlabel.symm ▸ hp)
    exact hlabel ▸ h
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_closedSmallSubgroup_le hn Γ hΓ ε x)
  let s : ℝ := r / 4
  have hs : 0 < s := by dsimp [s]; positivity
  have hcs : 1 < Real.cosh s ^ 2 := by nlinarith [Real.one_lt_cosh.mpr hs.ne']
  have hcspos : 0 < Real.cosh s ^ 2 := by positivity
  let b := normalEnergy σ x / Real.cosh s ^ 2
  have hb : b < normalEnergy σ x := by
    apply (div_lt_iff₀ hcspos).mpr
    nlinarith
  let N : Set (HUpper n) := Metric.ball x s ∩ {y | b < normalEnergy σ y}
  have hNopen : IsOpen N :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const (continuous_normalEnergy σ))
  have hxN : N ∈ 𝓝 x :=
    inter_mem (Metric.ball_mem_nhds x hs)
      ((isOpen_lt continuous_const (continuous_normalEnergy σ)).mem_nhds hb)
  obtain ⟨z, hzN, hzF⟩ := mem_closure_iff_nhds.mp hx N hxN
  have hOopen : IsOpen (fixedStratum hn Γ ε σ ∩ N) := hopen.inter hNopen
  have hnotSub : ¬fixedStratum hn Γ ε σ ∩ N ⊆ axis ξ η := by
    intro hsub
    have h := (hOopen.subset_interior_iff.mpr hsub) ⟨hzF, hzN⟩
    rw [interior_axis_eq_empty hdim ξ η] at h
    exact h
  obtain ⟨y, ⟨hyF, hyN⟩, hyaxis⟩ := Set.not_subset.mp hnotSub
  have hpy : axisFoot ξ η hne y ≠ y :=
    fun he => hyaxis (he ▸ axisFoot_mem ξ η hne y)
  have hyclose : dist y x < s := hyN.1
  let p := axisFoot ξ η hne y
  let q : ℝ → HUpper n := fun t => geodFromTo p y hpy (dist p y + t)
  have hqcont : Continuous q :=
    (continuous_geodFromTo (hd := hpy)).comp (continuous_const.add continuous_id)
  have hqzero : q 0 = y := by dsimp [q]; rw [add_zero, geodFromTo_dist]
  have hqball : ∀ t ∈ Icc 0 s, q t ∈ Metric.ball x r := by
    intro t ht
    have hd : dist (q t) y = t := by
      have h := dist_geodFromTo hpy (dist p y + t) (dist p y)
      simpa only [p, geodFromTo_dist, add_sub_cancel_left, abs_of_nonneg ht.1] using h
    have h := dist_triangle (q t) y x
    rw [hd] at h
    change dist (q t) x < r
    dsimp [s] at ht hyclose
    linarith [ht.2]
  have hout : q s ∉ closure (fixedStratum hn Γ ε σ) := by
    intro hcl
    have hgrowth := normalEnergy_normal_geod_ge hσ hclosed hsection ξ η hne hproj y hpy hs.le
    have hlow : normalEnergy σ x < normalEnergy σ y * Real.cosh s ^ 2 :=
      (div_lt_iff₀ hcspos).mp hyN.2
    have hupper := hmax (q s) hcl
    change Real.cosh s ^ 2 * normalEnergy σ y ≤ normalEnergy σ (q s) at hgrowth
    nlinarith
  have hqclosed : ∀ t ∈ Icc 0 s, q t ∈ closure (fixedStratum hn Γ ε σ) →
      q t ∈ fixedStratum hn Γ ε σ := by
    intro t ht hcl
    have hle := closedSmallSubgroup_normal_le hn Γ ε (closedSmallSubgroup hn Γ ε x)
      ξ η hne hpair y hpy (le_add_of_nonneg_right ht.1) (hball (hqball t ht))
    have hsub := fixedLocus_antitone hn hle
    have hsup := fixedLocus_subset_of_incident hn Γ hΓ ε (x := q t) rfl hcl
    change fixedLocus hn (closedSmallSubgroup hn Γ ε (q t)) = σ
    apply Subset.antisymm hsup
    simpa only [show fixedLocus hn (closedSmallSubgroup hn Γ ε y) = σ from hyF] using hsub
  have hconn : IsPreconnected (q '' Icc 0 s) :=
    isPreconnected_Icc.image q hqcont.continuousOn
  have hstart : ((q '' Icc 0 s) ∩ fixedStratum hn Γ ε σ).Nonempty :=
    ⟨y, ⟨0, ⟨le_rfl, hs.le⟩, hqzero⟩, hyF⟩
  have hwhole : q '' Icc 0 s ⊆ fixedStratum hn Γ ε σ :=
    hconn.subset_of_closure_inter_subset hopen hstart (by
      rintro z ⟨hz, t, ht, rfl⟩
      exact hqclosed t ht hz)
  exact hout (subset_closure (hwhole ⟨s, ⟨hs.le, le_rfl⟩, rfl⟩))

theorem not_isOpen_fixedStratum (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε)
    (hgeometry : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (closedSmallSubgroup hn Γ ε x))
    {σ : Set (HUpper n)} (hσ : σ.Nonempty)
    (hF : (fixedStratum hn Γ ε σ).Nonempty) (hproper : σ ≠ univ) :
    ¬IsOpen (fixedStratum hn Γ ε σ) := by
  intro hopen
  have hnotSub : ¬fixedStratum hn Γ ε σ ⊆ σ :=
    fun hsub => StratumIncidence.not_isOpen_of_subset_fixedLocus hn Γ ε hF hproper hsub hopen
  obtain ⟨z, hz, hzσ⟩ := Set.not_subset.mp hnotSub
  obtain ⟨x, hx, hpos, hmax⟩ := exists_normalEnergy_maximum hn Γ hΓ hcov hε hσ hz hzσ
  have hxσ : x ∉ σ := fun hp => hpos.ne' (normalEnergy_eq_zero_of_mem hp)
  have hlabel : fixedLocus hn (closedSmallSubgroup hn Γ ε z) = σ := hz
  have hclosed : IsClosed σ := hlabel ▸ isClosed_fixedLocus hn _
  have hsection : σ = {p : HUpper n | p.val ∈ locusSpan σ} := by
    simpa only [hlabel] using fixedLocus_eq_preimage_span hn
      (closedSmallSubgroup hn Γ ε z) (hlabel.symm ▸ hσ)
  have hext : ∀ y ∈ closure (fixedStratum hn Γ ε σ), ∀ c : ℝ, 1 < c →
      ∀ w ∈ locusSpan σ, w ∈ futureCone → y.val ≠ c • x.val - w := by
    intro y hy c hc w hw _ he
    have h := normalEnergy_eq_of_val_eq hσ hclosed hsection x y c w hw he
    have hm := hmax y hy
    have hc2 : 1 < c ^ 2 := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr hc2) hpos]
  rcases hgeometry x with ⟨hfinite, _⟩ | ⟨ξ, η, hne, hpair⟩ | ⟨ξ, hhor⟩
  · let := hfinite
    exact not_isOpen_of_finite_extremal hn Γ hΓ ε hx hxσ hext hopen
  · exact not_isOpen_of_axial_maximum hn hdim Γ hΓ ε hσ hx hpos hmax ξ η hne hpair hopen
  · exact not_isOpen_of_horospherical_extremal hn Γ hΓ ε hσ hx hext ξ hhor hopen

end DifferentialGeometry.StratumMaximum
