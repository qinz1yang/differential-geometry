/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.TopologicalCellNestedShell
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isTopologicalCell_of_convex {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ K) (hcl : IsClosed K) (hb : Bornology.IsBounded K)
    (hne : (interior K).Nonempty) : IsTopologicalCell n K := by
  obtain ⟨e, -, hclos, -⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv
      hne hb
  rw [hcl.closure_eq] at hclos
  exact ⟨(e.image K).trans (Homeomorph.setCongr hclos)⟩

theorem IsTopologicalCell.image_of_continuousOn_injOn {n : ℕ} {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {S : Set X} (hS : IsTopologicalCell n S) {g : X → Y}
    (hg : ContinuousOn g S) (hinj : InjOn g S) : IsTopologicalCell n (g '' S) := by
  obtain ⟨φ⟩ := hS
  have : CompactSpace (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have : CompactSpace S := φ.symm.compactSpace
  let G : S → g '' S := fun x => ⟨g x, x, x.2, rfl⟩
  have hGc : Continuous G := (hg.comp_continuous continuous_subtype_val
      Subtype.property).subtype_mk _
  have hGb : Function.Bijective G := by
    refine ⟨fun x y hxy => Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy)), fun z => ?_⟩
    obtain ⟨x, hx, hxz⟩ := z.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
  exact ⟨(hGc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G hGb)).symm.trans φ⟩

theorem IsPLBall.isPLCellOn_frontier {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : IsPLBall 3 A) :
    IsPLCellOn 3 A (frontier A) := by
  have hpoly := hA.isPolyhedron
  obtain ⟨r, hr⟩ := hA
  have hid : IsPLHomeomorphOn id A (id '' A) := by
    rw [image_id]
    exact hpoly.isPLHomeomorphOn_id
  refine ⟨A, r, id, hr, isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hid hpoly subset_rfl,
    (image_id A).symm, ?_⟩
  rw [image_id]
  exact hr.image_stdSimplexBoundary.symm

theorem exists_pos_forall_le_of_finite {ι : Type*} [Finite ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ δ, 0 < δ ∧ ∀ i, δ ≤ d i := by
  cases isEmpty_or_nonempty ι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min d
    exact ⟨d i₀, hd i₀, hi₀⟩

theorem exists_pos_thickening_inter_thickening_subset {α : Type*} [MetricSpace α]
    [ProperSpace α] {X Y O : Set α} (hX : IsCompact X) (hY : IsCompact Y) (hO : IsOpen O)
    (hXYO : X ∩ Y ⊆ O) : ∃ δ, 0 < δ ∧ thickening δ X ∩ thickening δ Y ⊆ O := by
  rcases X.eq_empty_or_nonempty with rfl | hXne
  · exact ⟨1, one_pos, by simp⟩
  rcases Y.eq_empty_or_nonempty with rfl | hYne
  · exact ⟨1, one_pos, by simp⟩
  have hZc : IsCompact (cthickening 1 X \ O) := hX.cthickening.diff hO
  have hφc : Continuous fun z => infDist z X + infDist z Y :=
    (continuous_infDist_pt X).add (continuous_infDist_pt Y)
  rcases (cthickening 1 X \ O).eq_empty_or_nonempty with hZ | hZne
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    by_contra hzO
    have hmem : z ∈ cthickening 1 X \ O := ⟨thickening_subset_cthickening 1 X hz.1, hzO⟩
    rw [hZ] at hmem
    exact hmem
  obtain ⟨z₀, hz₀, hmin⟩ := hZc.exists_isMinOn hZne hφc.continuousOn
  have hpos : 0 < infDist z₀ X + infDist z₀ Y := by
    by_contra hle
    have hX0 : infDist z₀ X = 0 := le_antisymm (by linarith [infDist_nonneg (x := z₀) (s := Y)])
      infDist_nonneg
    have hY0 : infDist z₀ Y = 0 := le_antisymm (by linarith [infDist_nonneg (x := z₀) (s := X)])
      infDist_nonneg
    exact hz₀.2 (hXYO ⟨(hX.isClosed.mem_iff_infDist_zero hXne).mpr hX0,
      (hY.isClosed.mem_iff_infDist_zero hYne).mpr hY0⟩)
  refine ⟨min 1 ((infDist z₀ X + infDist z₀ Y) / 2), lt_min one_pos (by linarith), ?_⟩
  rintro z ⟨hzX, hzY⟩
  by_contra hzO
  rw [mem_thickening_iff_infDist_lt hXne] at hzX
  rw [mem_thickening_iff_infDist_lt hYne] at hzY
  have hz1 : z ∈ cthickening 1 X := by
    refine thickening_subset_cthickening 1 X ?_
    rw [mem_thickening_iff_infDist_lt hXne]
    exact hzX.trans_le (min_le_left _ _)
  have hge : infDist z₀ X + infDist z₀ Y ≤ infDist z X + infDist z Y := hmin ⟨hz1, hzO⟩
  have h2 := min_le_right (1 : ℝ) ((infDist z₀ X + infDist z₀ Y) / 2)
  linarith

theorem exists_pos_forall_not_isBounded_connectedComponentIn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Ob₀ : Set E}
    (hcl : IsClosed Ob₀) (hb : Bornology.IsBounded Ob₀) {y : E}
    (hy : ¬ Bornology.IsBounded (connectedComponentIn Ob₀ᶜ y)) :
    ∃ d, 0 < d ∧ ∀ Ob : Set E, Ob ⊆ cthickening d Ob₀ →
      ¬ Bornology.IsBounded (connectedComponentIn Obᶜ y) := by
  obtain ⟨R₁, hR₁⟩ := hb.subset_closedBall (0 : E)
  set R₀ := |R₁| with hR₀def
  have hR₀ : Ob₀ ⊆ closedBall (0 : E) R₀ := hR₁.trans (closedBall_subset_closedBall (le_abs_self
      R₁))
  have hR₀nn : 0 ≤ R₀ := abs_nonneg R₁
  have hne : (connectedComponentIn Ob₀ᶜ y).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hy
    exact hy Bornology.isBounded_empty
  have hyO : y ∈ Ob₀ᶜ := connectedComponentIn_nonempty_iff.mp hne
  have hZo : IsOpen (connectedComponentIn Ob₀ᶜ y) := hcl.isOpen_compl.connectedComponentIn
  have hZp : IsPathConnected (connectedComponentIn Ob₀ᶜ y) :=
    hZo.isConnected_iff_isPathConnected.mp (isConnected_connectedComponentIn_iff.mpr hyO)
  obtain ⟨z, hzZ, hz⟩ : ∃ z ∈ connectedComponentIn Ob₀ᶜ y, R₀ + 2 < ‖z‖ := by
    by_contra hall
    exact hy ((isBounded_closedBall (x := (0 : E)) (r := R₀ + 2)).subset fun x hx => by
      rw [mem_closedBall, dist_zero_right]
      exact not_lt.mp fun hlt => hall ⟨x, hx, hlt⟩)
  obtain ⟨γ, hγ⟩ := hZp.joinedIn y (mem_connectedComponentIn hyO) z hzZ
  have hrange : range γ ⊆ Ob₀ᶜ := by
    rintro _ ⟨t, rfl⟩
    exact connectedComponentIn_subset _ _ (hγ t)
  obtain ⟨d₀, hd₀, hd₀sub⟩ :=
    (isCompact_range γ.continuous).exists_cthickening_subset_open hcl.isOpen_compl hrange
  refine ⟨min (d₀ / 2) 1, lt_min (half_pos hd₀) one_pos, fun Ob hOb => ?_⟩
  have hObball : Ob ⊆ closedBall (0 : E) (R₀ + 1) := by
    intro x hx
    have hx' := hOb hx
    have hsub : cthickening (min (d₀ / 2) 1) Ob₀ ⊆ cthickening 1 (closedBall (0 : E) R₀) :=
      (cthickening_mono (min_le_right _ _) Ob₀).trans (cthickening_subset_of_subset _ hR₀)
    have hx'' := hsub hx'
    rw [cthickening_closedBall zero_le_one hR₀nn] at hx''
    exact closedBall_subset_closedBall (by linarith) hx''
  have hγOb : range γ ⊆ Obᶜ := by
    rintro _ ⟨t, rfl⟩ hmem
    have hthick : γ t ∈ thickening d₀ Ob₀ :=
      cthickening_subset_thickening' hd₀ (by linarith [min_le_left (d₀ / 2) 1]) Ob₀ (hOb hmem)
    obtain ⟨o, ho, hdist⟩ := mem_thickening_iff.mp hthick
    have hoγ : o ∈ cthickening d₀ (range γ) :=
      mem_cthickening_of_dist_le o (γ t) d₀ (range γ) ⟨t, rfl⟩ (by rw [dist_comm]; exact hdist.le)
    exact hd₀sub hoγ ho
  have hγcomp : range γ ⊆ connectedComponentIn Obᶜ y :=
    (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn
      ⟨0, γ.source⟩ hγOb
  have hzcomp : z ∈ connectedComponentIn Obᶜ y := hγcomp ⟨1, γ.target⟩
  have hray : (fun c : ℝ => c • z) '' Ici 1 ⊆ connectedComponentIn Obᶜ y := by
    rw [connectedComponentIn_eq hzcomp]
    have hcont : Continuous fun c : ℝ => c • z := continuous_id.smul continuous_const
    refine (isPreconnected_Ici.image _ hcont.continuousOn).subset_connectedComponentIn
      ⟨1, mem_Ici.mpr le_rfl, one_smul ℝ z⟩ ?_
    rintro _ ⟨c, hc, rfl⟩ hmem
    have hn : ‖c • z‖ ≤ R₀ + 1 := by
      have := hObball hmem
      rwa [mem_closedBall, dist_zero_right] at this
    rw [norm_smul, Real.norm_of_nonneg (by linarith [mem_Ici.mp hc])] at hn
    have hzpos : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [mem_Ici.mp hc]
  intro hbdd
  obtain ⟨M, hM⟩ := (hbdd.subset hray).subset_closedBall (0 : E)
  have hzne : 0 < ‖z‖ := by linarith
  have hc : (1 : ℝ) ≤ (|M| + 1) / ‖z‖ + 1 := by
    have : 0 ≤ (|M| + 1) / ‖z‖ := div_nonneg (by positivity) hzne.le
    linarith
  have hmem := hM ⟨(|M| + 1) / ‖z‖ + 1, hc, rfl⟩
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by linarith)] at hmem
  have hkey : ((|M| + 1) / ‖z‖ + 1) * ‖z‖ = |M| + 1 + ‖z‖ := by
    field_simp
  rw [hkey] at hmem
  linarith [le_abs_self M]

theorem exists_pos_forall_not_isBounded_connectedComponentIn_of_finite {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Ob₀ Y₀ : Set E}
    (hcl : IsClosed Ob₀) (hb : Bornology.IsBounded Ob₀) (hY₀ : Y₀.Finite)
    (hy : ∀ y ∈ Y₀, ¬ Bornology.IsBounded (connectedComponentIn Ob₀ᶜ y)) :
    ∃ d, 0 < d ∧ ∀ Ob : Set E, Ob ⊆ cthickening d Ob₀ →
      ∀ y ∈ Y₀, ¬ Bornology.IsBounded (connectedComponentIn Obᶜ y) := by
  have : Finite Y₀ := hY₀.to_subtype
  choose d hd hdOb using fun y : Y₀ =>
    exists_pos_forall_not_isBounded_connectedComponentIn hcl hb (hy y y.2)
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_forall_le_of_finite d hd
  exact ⟨δ, hδ, fun Ob hOb y hyY =>
    hdOb ⟨y, hyY⟩ Ob (hOb.trans (cthickening_mono (hδle ⟨y, hyY⟩) Ob₀))⟩

theorem Moise305Tame.exists_isPLBall_image_of_isTopologicalCell
    {V : Set E3} {h : E3 → E3} (hcont : ContinuousOn h V) (hinj : InjOn h V) {Y K : Set E3}
    (hY : IsTopologicalCell 3 Y) (hYV : Y ⊆ V) (hK : IsCompact K) (hKY : K ⊆ interior Y) :
    ∃ A, IsPLBall 3 A ∧ h '' K ⊆ interior A ∧ A ⊆ interior (h '' Y) := by
  have hhY : IsTopologicalCell 3 (h '' Y) :=
    hY.image_of_continuousOn_injOn (hcont.mono hYV) (hinj.mono hYV)
  have hopen : IsOpen (h '' interior Y) :=
    invariance_of_domain_isOpen_image isOpen_interior (hcont.mono (interior_subset.trans hYV))
      (hinj.mono (interior_subset.trans hYV))
  have hKc : IsCompact (h '' K) :=
    hK.image_of_continuousOn (hcont.mono (hKY.trans (interior_subset.trans hYV)))
  exact Moise305Tame.exists_isPLBall_of_isTopologicalCell hhY hKc
    ((image_mono hKY).trans (interior_maximal (image_mono interior_subset) hopen))

theorem subset_interior_cthickening {α : Type*} [PseudoMetricSpace α] {r : ℝ} (hr : 0 < r)
    (X : Set α) : X ⊆ interior (cthickening r X) :=
  (self_subset_thickening hr X).trans
    (interior_maximal (thickening_subset_cthickening r X) isOpen_thickening)

theorem isTopologicalCell_cthickening {X : Set E3} (hX : Convex ℝ X) (hXc : IsCompact X)
    (hXne : X.Nonempty) {r : ℝ} (hr : 0 < r) : IsTopologicalCell 3 (cthickening r X) :=
  isTopologicalCell_of_convex (hX.cthickening r) isClosed_cthickening
    hXc.isBounded.cthickening (hXne.mono (subset_interior_cthickening hr X))

theorem Moise305Tame.exists_isPLBall_image_of_convex {V O X : Set E3}
    (hV : IsOpen V) {h : E3 → E3} (hcont : ContinuousOn h V) (hinj : InjOn h V) (hO : IsOpen O)
    (hX : Convex ℝ X) (hXc : IsCompact X) (hXne : X.Nonempty) (hXV : X ⊆ V)
    (hXO : h '' X ⊆ O) : ∃ A, IsPLBall 3 A ∧ h '' X ⊆ interior A ∧ A ⊆ O := by
  have hW : IsOpen (V ∩ h ⁻¹' O) := hcont.isOpen_inter_preimage hV hO
  have hXW : X ⊆ V ∩ h ⁻¹' O := fun x hx => ⟨hXV hx, hXO (mem_image_of_mem h hx)⟩
  obtain ⟨r, hr, hrW⟩ := hXc.exists_cthickening_subset_open hW hXW
  obtain ⟨A, hA, hXA, hAY⟩ := Moise305Tame.exists_isPLBall_image_of_isTopologicalCell hcont hinj
    (isTopologicalCell_cthickening hX hXc hXne hr) (hrW.trans inter_subset_left) hXc
    (subset_interior_cthickening hr X)
  refine ⟨A, hA, hXA, hAY.trans (interior_subset.trans ?_)⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (hrW hy).2

theorem Moise305Tame.exists_isPLBall_capping {V O X R : Set E3}
    (hV : IsOpen V) {h : E3 → E3} (hcont : ContinuousOn h V) (hinj : InjOn h V) (hO : IsOpen O)
    (hX : Convex ℝ X) (hXc : IsCompact X) (hXV : X ⊆ V) (hRc : IsCompact R) (hRne : R.Nonempty)
    (hRX : R ⊆ X) {n g : E3} (hn : ‖n‖ = 1) (hXn : ∀ x ∈ X, inner ℝ n (x - g) = 0)
    (hRO : h '' R ⊆ O) : ∃ A, IsPLBall 3 A ∧ h '' R ⊆ interior A ∧ A ∩ h '' X ⊆ O := by
  have hU : IsOpen (V ∩ h ⁻¹' O) := hcont.isOpen_inter_preimage hV hO
  have hRU : R ⊆ V ∩ h ⁻¹' O := fun x hx => ⟨hXV (hRX hx), hRO (mem_image_of_mem h hx)⟩
  obtain ⟨μ, hμ, hμU⟩ := hRc.exists_cthickening_subset_open hU hRU
  obtain ⟨ε₀, hε₀, hε₀V⟩ := hXc.exists_cthickening_subset_open hV hXV
  have hη : 0 < ε₀ / 2 := half_pos hε₀
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  let u : E3 → E3 := fun x => x - inner ℝ n (x - g) • n
  let ρ : E3 → ℝ := fun x => ε₀ / 2 * min 1 (infDist (u x) R)
  have hushift : ∀ (x : E3) (c : ℝ), u (x + c • n) = u x := by
    intro x c
    change x + c • n - inner ℝ n (x + c • n - g) • n = x - inner ℝ n (x - g) • n
    rw [show x + c • n - g = (x - g) + c • n by abel, inner_add_right, real_inner_smul_right,
      hnn, mul_one, add_smul]
    abel
  have hρshift : ∀ (x : E3) (c : ℝ), ρ (x + c • n) = ρ x := fun x c => by
    change ε₀ / 2 * min 1 (infDist (u (x + c • n)) R) = ε₀ / 2 * min 1 (infDist (u x) R)
    rw [hushift]
  have hρshift' : ∀ (x : E3) (c : ℝ), ρ (x - c • n) = ρ x := fun x c => by
    rw [sub_eq_add_neg, ← neg_smul, hρshift]
  have hicont : Continuous fun x : E3 => inner ℝ n (x - g) :=
    continuous_const.inner (continuous_id.sub continuous_const)
  have hucont : Continuous u := continuous_id.sub (hicont.smul continuous_const)
  have hρcont : Continuous ρ :=
    continuous_const.mul (continuous_const.min ((continuous_infDist_pt R).comp hucont))
  let Φ : E3 ≃ₜ E3 :=
    { toFun := fun x => x + ρ x • n
      invFun := fun y => y - ρ y • n
      left_inv := fun x => by
        change x + ρ x • n - ρ (x + ρ x • n) • n = x
        rw [hρshift, add_sub_cancel_right]
      right_inv := fun y => by
        change y - ρ y • n + ρ (y - ρ y • n) • n = y
        rw [hρshift', sub_add_cancel]
      continuous_toFun := continuous_id.add (hρcont.smul continuous_const)
      continuous_invFun := continuous_id.sub (hρcont.smul continuous_const) }
  have hΦ : ∀ x, Φ x = x + ρ x • n := fun x => rfl
  have hρnn : ∀ x, 0 ≤ ρ x := fun x => mul_nonneg hη.le (le_min zero_le_one infDist_nonneg)
  have hρle : ∀ x, ρ x ≤ ε₀ / 2 := fun x =>
    mul_le_of_le_one_right hη.le (min_le_left _ _)
  have hXΦ : X ⊆ Φ ⁻¹' V := by
    intro x hx
    refine hε₀V (mem_cthickening_of_dist_le (Φ x) x ε₀ X hx ?_)
    rw [hΦ, dist_eq_norm, add_sub_cancel_left, norm_smul, hn, mul_one,
      Real.norm_of_nonneg (hρnn x)]
    linarith [hρle x]
  obtain ⟨r₁, hr₁, hr₁V⟩ := hXc.exists_cthickening_subset_open (hV.preimage Φ.continuous) hXΦ
  have hr : 0 < min r₁ (min (ε₀ / 2 / 2) (μ * (ε₀ / 2))) :=
    lt_min hr₁ (lt_min (half_pos hη) (mul_pos hμ hη))
  set r := min r₁ (min (ε₀ / 2 / 2) (μ * (ε₀ / 2))) with hrdef
  have hXne : X.Nonempty := hRne.mono hRX
  have hBcell : IsTopologicalCell 3 (Φ '' cthickening r X) :=
    (isTopologicalCell_cthickening hX hXc hXne hr).image_of_continuousOn_injOn
      Φ.continuous.continuousOn Φ.injective.injOn
  have hBV : Φ '' cthickening r X ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact hr₁V (cthickening_mono (min_le_left _ _) X hx)
  have hΦR : ∀ x ∈ R, Φ x = x := by
    intro x hx
    have hux : u x = x := by
      change x - inner ℝ n (x - g) • n = x
      rw [hXn x (hRX hx), zero_smul, sub_zero]
    rw [hΦ]
    change x + (ε₀ / 2 * min 1 (infDist (u x) R)) • n = x
    rw [hux, infDist_zero_of_mem hx, min_eq_right zero_le_one, mul_zero, zero_smul, add_zero]
  have hRint : R ⊆ interior (Φ '' cthickening r X) := by
    intro x hx
    have hmem : x ∈ Φ '' interior (cthickening r X) :=
      ⟨x, subset_interior_cthickening hr X (hRX hx), hΦR x hx⟩
    exact interior_maximal (image_mono interior_subset) (Φ.isOpenMap _ isOpen_interior) hmem
  have hBX : Φ '' cthickening r X ∩ X ⊆ cthickening μ R := by
    rintro _ ⟨⟨x', hx', rfl⟩, hyX⟩
    rw [cthickening_eq_biUnion_closedBall X hr.le, hXc.isClosed.closure_eq] at hx'
    obtain ⟨x, hx, hxx'⟩ := mem_iUnion₂.mp hx'
    have h0 : inner ℝ n (Φ x' - g) = 0 := hXn _ hyX
    rw [hΦ, show x' + ρ x' • n - g = (x' - g) + ρ x' • n by abel, inner_add_right,
      real_inner_smul_right, hnn, mul_one] at h0
    have hsplit : inner ℝ n (x' - g) = inner ℝ n (x' - x) + inner ℝ n (x - g) := by
      rw [← inner_add_right, sub_add_sub_cancel]
    have hcs := real_inner_le_norm n (x - x')
    rw [hn, one_mul, ← dist_eq_norm, dist_comm] at hcs
    have hneg : inner ℝ n (x - x') = - inner ℝ n (x' - x) := by
      rw [← inner_neg_right, neg_sub]
    have hρx' : ρ x' ≤ r := by
      have := mem_closedBall.mp hxx'
      linarith [hXn x hx]
    have hrη : r < ε₀ / 2 :=
      ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hη)
    have hrμ : r ≤ μ * (ε₀ / 2) := (min_le_right _ _).trans (min_le_right _ _)
    have hmin : min 1 (infDist (u x') R) = infDist (u x') R := by
      rcases min_choice 1 (infDist (u x') R) with h1 | h1
      · have hρeq : ρ x' = ε₀ / 2 := by
          change ε₀ / 2 * min 1 (infDist (u x') R) = ε₀ / 2
          rw [h1, mul_one]
        linarith
      · exact h1
    have hΦu : Φ x' = u x' := by
      rw [hΦ]
      change x' + ρ x' • n = x' - inner ℝ n (x' - g) • n
      rw [show ρ x' = - inner ℝ n (x' - g) by linarith, neg_smul, ← sub_eq_add_neg]
    have hid : infDist (u x') R ≤ μ := by
      have hρeq : ρ x' = ε₀ / 2 * infDist (u x') R := by
        change ε₀ / 2 * min 1 (infDist (u x') R) = _
        rw [hmin]
      have : ε₀ / 2 * infDist (u x') R ≤ ε₀ / 2 * μ := by nlinarith
      exact le_of_mul_le_mul_left this hη
    obtain ⟨z, hz, hzd⟩ := hRc.exists_infDist_eq_dist hRne (u x')
    rw [hΦu]
    exact mem_cthickening_of_dist_le _ z μ R hz (hzd ▸ hid)
  obtain ⟨A, hA, hRA, hAB⟩ :=
    Moise305Tame.exists_isPLBall_image_of_isTopologicalCell hcont hinj hBcell hBV hRc hRint
  refine ⟨A, hA, hRA, ?_⟩
  rintro _ ⟨hyA, x, hx, rfl⟩
  obtain ⟨b, hb, hbx⟩ := interior_subset (hAB hyA)
  have hbx' : b = x := hinj (hBV hb) (hXV hx) hbx
  rw [hbx'] at hb
  exact (hμU (hBX ⟨hb, hx⟩)).2

theorem exists_unit_normal_of_card_eq_three {s : Finset E3} (hs : s.card = 3) :
    ∃ n g : E3, ‖n‖ = 1 ∧ ∀ x ∈ convexHull ℝ (s : Set E3), inner ℝ n (x - g) = 0 := by
  classical
  have hle : Module.finrank ℝ (vectorSpan ℝ (s : Set E3)) ≤ 2 := by
    have := finrank_vectorSpan_image_finset_le ℝ (id : E3 → E3) s (n := 2) hs
    rwa [Finset.image_id] at this
  have hsum := (vectorSpan ℝ (s : Set E3)).finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at hsum
  have hne : (vectorSpan ℝ (s : Set E3))ᗮ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hsum
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨g, hg⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨(‖v‖⁻¹ : ℝ) • v, g, norm_smul_inv_norm (𝕜 := ℝ) hv0, fun x hx => ?_⟩
  have hxg : x -ᵥ g ∈ vectorSpan ℝ (s : Set E3) :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan (convexHull_subset_affineSpan _ hx)
      (mem_affineSpan ℝ (Finset.mem_coe.mpr hg))
  rw [vsub_eq_sub] at hxg
  rw [real_inner_smul_left, (Submodule.mem_orthogonal' _ v).mp hv _ hxg, mul_zero]

theorem isCompact_section34CompactSimplexRim (t : Finset E3) :
    IsCompact (section34CompactSimplexRim t) := by
  refine Set.Finite.isCompact_biUnion ?_ fun s _ => s.finite_toSet.isCompact_convexHull ℝ
  exact t.powerset.finite_toSet.subset fun s hs =>
    Finset.mem_coe.mpr (Finset.mem_powerset.mpr (subset_of_ssubset hs))

theorem section34CompactSimplexRim_nonempty {t : Finset E3} (ht : 2 ≤ t.card) :
    (section34CompactSimplexRim t).Nonempty := by
  obtain ⟨v, hv⟩ : t.Nonempty := Finset.card_pos.mp (by omega)
  have hvt : ({v} : Finset E3) ⊂ t := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hv, fun he => ?_⟩
    rw [← he, Finset.card_singleton] at ht
    omega
  exact ⟨v, mem_biUnion (x := ({v} : Finset E3)) hvt (subset_convexHull ℝ _ (by simp))⟩

theorem convexHull_subset_section34CompactCarrierSupport
    {K : Geometry.SimplicialComplex ℝ E3} {s t : Finset E3} (hs : s ∈ K.faces)
    (ht : t ∈ K.faces) (hst : Section34Incident s t) :
    convexHull ℝ (s : Set E3) ⊆ section34CompactCarrierSupport K t := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have hvt : v ∈ t := (K.vertex_mem_convexHull_iff
    (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)) ht).mp
      (hst hv)
  intro x hx
  exact mem_iUnion₂.mpr ⟨v, Finset.mem_coe.mpr hvt, mem_iUnion₂.mpr ⟨s, ⟨hs, hv⟩, hx⟩⟩

theorem image_convexHull_inter_subset_interior_of_ne {V : Set E3} {h f₁ : E3 → E3}
    {K K' : Geometry.SimplicialComplex ℝ E3}
    {src : Section34CompactLabelOf K K' → Set E3} (hinj : InjOn h V)
    (hsV : ∀ s : Section34CompactSimplexIndex K 3, convexHull ℝ (s.1 : Set E3) ⊆ V)
    (hnhds : f₁ '' section34CompactCutNeighborhood src ∈
      nhdsSet (h '' section34CompactGraphSkeleton K))
    {s s' : Section34CompactSimplexIndex K 3} (hss : s ≠ s') :
    h '' convexHull ℝ (s.1 : Set E3) ∩ h '' convexHull ℝ (s'.1 : Set E3) ⊆
      interior (⋃ w, section34CompactVertexBallImage src f₁ w) := by
  have hΓ : h '' section34CompactGraphSkeleton K ⊆
      interior (⋃ w, section34CompactVertexBallImage src f₁ w) := by
    have := subset_interior_iff_mem_nhdsSet.mpr hnhds
    rwa [section34CompactCutNeighborhood, image_iUnion] at this
  rintro _ ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx'⟩⟩
  have hxeq : x' = x := hinj (hsV s' hx') (hsV s hx) hxx'
  rw [hxeq] at hx'
  have hmem : x ∈ convexHull ℝ ((s.1 : Set E3) ∩ s'.1) := by
    rw [← K.convexHull_inter_convexHull s.2.1 s'.2.1]
    exact ⟨hx, hx'⟩
  refine hΓ ⟨x, ?_, rfl⟩
  rw [← Finset.coe_inter] at hmem
  rcases (s.1 ∩ s'.1).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.coe_empty, convexHull_empty] at hmem
    exact hmem.elim
  refine mem_biUnion (x := s.1 ∩ s'.1) ⟨K.down_closed s.2.1 Finset.inter_subset_left hne, ?_⟩ hmem
  by_contra hcard
  have h3 : (s.1 ∩ s'.1).card = 3 :=
    le_antisymm ((Finset.card_le_card Finset.inter_subset_left).trans s.2.2.le) (by omega)
  have e1 : s.1 ∩ s'.1 = s.1 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h3, s.2.2])
  have e2 : s.1 ∩ s'.1 = s'.1 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h3, s'.2.2])
  exact hss (Subtype.ext (e1.symm.trans e2))

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactFaceEnvelopes (hV : IsOpen V) (hCV : C ⊆ V)
    (hh : Topology.IsEmbedding (V.domRestrict h))
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hcar : Section34CompactCarrierControl K h ε H)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁) :
    ∃ env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      Section34CompactFaceEnvelopes K K' h H (section34CompactVertexBallImage src f₁) env := by
  classical
  have hcont : ContinuousOn h V := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinj : InjOn h V := fun x hx y hy hxy =>
    congrArg Subtype.val (hh.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  obtain ⟨hKC, hKfin, hK'fin, -, -, -, hcell, -⟩ := hcut
  obtain ⟨hcarsupp, -, -⟩ := hcar
  obtain ⟨-, hf₁, hnhds, -, -, -, hVinc, hrimT, -, -, hext⟩ := hgraph
  have _ := finite_section34CompactSimplexIndex hKfin 3
  have _ := finite_section34CompactSimplexIndex hKfin 4
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  have hsV : ∀ s : Section34CompactSimplexIndex K 3, convexHull ℝ (s.1 : Set E3) ⊆ V :=
    fun s => (K.convexHull_subset_space s.2.1).trans (hKC ▸ hCV)
  have hXc : ∀ s : Section34CompactSimplexIndex K 3,
      IsCompact (h '' convexHull ℝ (s.1 : Set E3)) := fun s =>
    (s.1.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn (hcont.mono (hsV s))
  have htgtVc : ∀ w, IsCompact (section34CompactVertexBallImage src f₁ w) := fun w =>
    (hcell (.vertexBall w)).isCompact.image_of_continuousOn
      (hf₁.isPiecewiseAffineOn.continuousOn.mono
        (subset_iUnion (fun w => src (.vertexBall w)) w))
  have hcap : ∀ s : Section34CompactSimplexIndex K 3, ∃ A, IsPLBall 3 A ∧
      h '' section34CompactSimplexRim s.1 ⊆ interior A ∧
      A ∩ h '' convexHull ℝ (s.1 : Set E3) ⊆
        interior (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
    intro s
    obtain ⟨n, g, hn, hng⟩ := exists_unit_normal_of_card_eq_three s.2.2
    exact Moise305Tame.exists_isPLBall_capping hV hcont hinj isOpen_interior (convex_convexHull ℝ _)
      (s.1.finite_toSet.isCompact_convexHull ℝ) (hsV s) (isCompact_section34CompactSimplexRim s.1)
      (section34CompactSimplexRim_nonempty (by rw [s.2.2]; norm_num))
      (section34CompactSimplexRim_subset s.1) hn hng (hrimT s)
  choose A hA hrimA hAT using hcap
  have hpair : ∀ p : Section34CompactSimplexIndex K 3 × Section34CompactSimplexIndex K 3,
      ∃ δ, 0 < δ ∧ (p.1 ≠ p.2 → thickening δ (h '' convexHull ℝ (p.1.1 : Set E3)) ∩
        thickening δ (h '' convexHull ℝ (p.2.1 : Set E3)) ⊆
          interior (⋃ w, section34CompactVertexBallImage src f₁ w)) := by
    rintro ⟨s, s'⟩
    by_cases hss : s = s'
    · exact ⟨1, one_pos, fun hne => absurd hss hne⟩
    obtain ⟨δ, hδ, hsub⟩ := exists_pos_thickening_inter_thickening_subset (hXc s) (hXc s')
      isOpen_interior (image_convexHull_inter_subset_interior_of_ne hinj hsV hnhds hss)
    exact ⟨δ, hδ, fun _ => hsub⟩
  choose δ₁ hδ₁ hδ₁sub using hpair
  obtain ⟨d₁, hd₁, hd₁le⟩ := exists_pos_forall_le_of_finite δ₁ hδ₁
  have hOb₀c : ∀ t, IsCompact (section34CompactTetraObstacle
      (section34CompactVertexBallImage src f₁)
      (fun s => h '' convexHull ℝ (s.1 : Set E3)) t) := fun t =>
    (isCompact_iUnion fun _ => isCompact_iUnion fun _ => htgtVc _).union
      (isCompact_iUnion fun s => isCompact_iUnion fun _ => hXc s)
  have hextd : ∀ p : Section34CompactSimplexIndex K 4 × Section34CompactVertexIndex K K',
      ∃ d, 0 < d ∧ (¬ Section34Incident p.2.1 p.1.1 → ∀ Ob : Set E3,
        Ob ⊆ cthickening d (section34CompactTetraObstacle
          (section34CompactVertexBallImage src f₁)
          (fun s => h '' convexHull ℝ (s.1 : Set E3)) p.1) →
        ∀ y ∈ h '' (p.2.1 : Set E3), ¬ Bornology.IsBounded (connectedComponentIn Obᶜ y)) := by
    rintro ⟨t, w⟩
    by_cases hinc : Section34Incident w.1 t.1
    · exact ⟨1, one_pos, fun hn => absurd hinc hn⟩
    obtain ⟨d, hd, hdOb⟩ := exists_pos_forall_not_isBounded_connectedComponentIn_of_finite
      (hOb₀c t).isClosed (hOb₀c t).isBounded (w.1.finite_toSet.image h) (hext t w hinc)
    exact ⟨d, hd, fun _ => hdOb⟩
  choose δ₂ hδ₂ hδ₂sub using hextd
  obtain ⟨d₂, hd₂, hd₂le⟩ := exists_pos_forall_le_of_finite δ₂ hδ₂
  have hδ : 0 < min d₁ d₂ := lt_min hd₁ hd₂
  refine ⟨fun s => thickening (min d₁ d₂) (h '' convexHull ℝ (s.1 : Set E3)) ∩
    (⋃ (w : Section34CompactVertexIndex K K') (_ : ¬ Section34Incident w.1 s.1),
      section34CompactVertexBallImage src f₁ w)ᶜ ∩
    (⋂ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident s.1 t.1),
      interior (H t.1)) ∩
    (A s \ interior (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))ᶜ,
    fun s => ?_, fun s => ?_, fun s w hw => ?_, fun s s' hss => ?_, fun s t hst => ?_,
    fun s => ?_, ?_⟩
  · refine ((isOpen_thickening.inter ?_).inter ?_).inter ?_
    · exact (isClosed_iUnion_of_finite fun w =>
        isClosed_iUnion_of_finite fun _ => (htgtVc w).isClosed).isOpen_compl
    · exact isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ => isOpen_interior
    · exact ((hA s).isPLCellOn_frontier.isCompact.isClosed.sdiff isOpen_interior).isOpen_compl
  · intro y hy
    refine ⟨⟨⟨self_subset_thickening hδ _ hy, ?_⟩, ?_⟩, ?_⟩
    · intro hyw
      obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hyw
      exact hw (hVinc w s ⟨y, hyw, hy⟩)
    · refine mem_iInter₂.mpr fun t hst => hcarsupp t.1 t.2.1 ?_
      obtain ⟨x, hx, rfl⟩ := hy
      exact mem_image_of_mem h
        (convexHull_subset_section34CompactCarrierSupport s.2.1 t.2.1 hst hx)
    · exact fun hyA => hyA.2 (hAT s ⟨hyA.1, hy⟩)
  · refine eq_empty_iff_forall_notMem.mpr fun y hy => hy.1.1.1.2 ?_
    exact mem_iUnion₂.mpr ⟨w, hw, hy.2⟩
  · rintro y ⟨hy, hy'⟩
    exact hδ₁sub (s, s') hss ⟨thickening_mono ((min_le_left _ _).trans (hd₁le (s, s'))) _
      hy.1.1.1, thickening_mono ((min_le_left _ _).trans (hd₁le (s, s'))) _ hy'.1.1.1⟩
  · intro y hy
    exact mem_iInter₂.mp hy.1.2 t hst
  · refine ⟨A s, hA s, hrimA s, fun y hy => ?_⟩
    by_contra hyT
    exact hy.1.2 ⟨hy.2, hyT⟩
  · intro t w hw y hy
    refine hδ₂sub (t, w) hw _ (union_subset ?_ ?_) y hy
    · exact subset_union_left.trans (self_subset_cthickening _)
    · refine iUnion₂_subset fun s hst => ?_
      refine (closure_mono (inter_subset_left.trans (inter_subset_left.trans
        inter_subset_left))).trans ((closure_thickening_subset_cthickening _ _).trans
        ((cthickening_mono ((min_le_right _ _).trans (hd₂le (t, w))) _).trans
        (cthickening_subset_of_subset _ ?_)))
      exact (subset_iUnion₂ (s := fun s (_ : Section34Incident s.1 t.1) =>
        h '' convexHull ℝ (s.1 : Set E3)) s hst).trans subset_union_right

theorem exists_compactFaceShellBalls (hV : IsOpen V) (hCV : C ⊆ V)
    (hh : Topology.IsEmbedding (V.domRestrict h))
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (henv : Section34CompactFaceEnvelopes K K' h H (section34CompactVertexBallImage src f₁)
      env) :
    ∃ fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      ∀ s : Section34CompactSimplexIndex K 3, IsPLCellOn 3 (fbl s) (fblBd s) ∧
        h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ interior (fbl s) ∧
        fbl s ⊆ env s := by
  have hcont : ContinuousOn h V := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinj : InjOn h V := fun x hx y hy hxy =>
    congrArg Subtype.val (hh.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  obtain ⟨hKC, -⟩ := hcut
  obtain ⟨henvo, henvX, -⟩ := henv
  have hball : ∀ s : Section34CompactSimplexIndex K 3, ∃ A, IsPLBall 3 A ∧
      h '' convexHull ℝ (s.1 : Set E3) ⊆ interior A ∧ A ⊆ env s := fun s =>
    Moise305Tame.exists_isPLBall_image_of_convex hV hcont hinj (henvo s) (convex_convexHull ℝ _)
      (s.1.finite_toSet.isCompact_convexHull ℝ)
      (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces s.2.1)))
      ((K.convexHull_subset_space s.2.1).trans (hKC ▸ hCV)) (henvX s)
  choose A hA hXA hAenv using hball
  exact ⟨A, fun s => frontier (A s), fun s => ⟨(hA s).isPLCellOn_frontier, hXA s, hAenv s⟩⟩

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
