import DifferentialGeometry.Topology.PiecewiseLinear.Arrangement
import DifferentialGeometry.Topology.PiecewiseLinear.Derived

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_ne_zero_of_signLE_ne {ι : Type*} {σ τ : ι → SignType} (h : SignLE σ τ)
    (hne : σ ≠ τ) : ∃ k, τ k ≠ 0 ∧ σ k = 0 := by
  by_contra hcon
  push Not at hcon
  apply hne
  funext k
  rcases h k with h1 | h1
  · exact h1
  · by_cases hτ : τ k = 0
    · rw [h1, hτ]
    · exact absurd h1 (hcon k hτ)

section SignSupport

variable {ι : Type*} [Fintype ι]

def signSupport (σ : ι → SignType) : Finset ι := Finset.univ.filter fun k => σ k ≠ 0

theorem mem_signSupport {σ : ι → SignType} {k : ι} : k ∈ signSupport σ ↔ σ k ≠ 0 := by
  simp [signSupport]

theorem signSupport_mono {σ τ : ι → SignType} (h : SignLE σ τ) :
    signSupport σ ⊆ signSupport τ := by
  intro k hk
  rw [mem_signSupport] at hk ⊢
  rcases h k with h1 | h1
  · rw [← h1]
    exact hk
  · exact absurd h1 hk

theorem SignLE.eq_of_signSupport_subset {σ τ : ι → SignType} (h : SignLE σ τ)
    (hs : signSupport τ ⊆ signSupport σ) : σ = τ := by
  funext k
  rcases h k with h1 | h1
  · exact h1
  · by_cases hτ : τ k = 0
    · rw [h1, hτ]
    · exact absurd h1 (mem_signSupport.mp (hs (mem_signSupport.mpr hτ)))

theorem signSupport_ssubset_of_signLE_ne {σ τ : ι → SignType} (h : SignLE σ τ) (hne : σ ≠ τ) :
    signSupport σ ⊂ signSupport τ :=
  Finset.ssubset_iff_subset_ne.mpr ⟨signSupport_mono h, fun heq =>
    hne (h.eq_of_signSupport_subset heq.ge)⟩

end SignSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_of_combo_eq {p y : E} {a : ℝ} (ha : a < 1)
    (h : p = a • p + (1 - a) • y) : y = p := by
  have h1 : 0 < 1 - a := sub_pos.mpr ha
  have h2 : (1 - a) • y = (1 - a) • p := by
    have h3 : p - a • p = (1 - a) • y := (sub_eq_iff_eq_add').mpr h
    rw [← h3, sub_smul, one_smul]
  exact smul_right_injective E h1.ne' h2

variable {ι : Type*} (l : ι → E →ᵃ[ℝ] ℝ) (P : Set E)

def IsCellClosed : Prop := ∀ x ∈ P, closedCell l (signVec l x) ⊆ P

def cellsOf : Set (ι → SignType) := {σ | ∃ x ∈ P, signVec l x = σ}

theorem signVec_mem_cellsOf {x : E} (hx : x ∈ P) : signVec l x ∈ cellsOf l P := ⟨x, hx, rfl⟩

open Classical in
noncomputable def cellPt (σ : ι → SignType) : E :=
  if h : ∃ x ∈ P, signVec l x = σ then Classical.choose h else 0

theorem cellPt_spec {σ : ι → SignType} (hσ : σ ∈ cellsOf l P) :
    cellPt l P σ ∈ P ∧ cellPt l P σ ∈ openCell l σ := by
  have h : ∃ x ∈ P, signVec l x = σ := hσ
  rw [cellPt, dif_pos h]
  exact Classical.choose_spec h

theorem cellPt_mem {σ : ι → SignType} (hσ : σ ∈ cellsOf l P) : cellPt l P σ ∈ P :=
  (cellPt_spec l P hσ).1

theorem cellPt_mem_openCell {σ : ι → SignType} (hσ : σ ∈ cellsOf l P) :
    cellPt l P σ ∈ openCell l σ :=
  (cellPt_spec l P hσ).2

theorem cellPt_mem_closedCell {σ τ : ι → SignType} (hσ : σ ∈ cellsOf l P) (h : SignLE σ τ) :
    cellPt l P σ ∈ closedCell l τ :=
  closedCell_mono l h (openCell_subset_closedCell l σ (cellPt_mem_openCell l P hσ))

theorem cellPt_injOn : Set.InjOn (cellPt l P) (cellsOf l P) := by
  intro σ hσ τ hτ h
  by_contra hne
  exact Set.disjoint_left.mp (openCell_disjoint l hne) (cellPt_mem_openCell l P hσ)
    (h ▸ cellPt_mem_openCell l P hτ)

theorem closedCell_subset_of_isCellClosed (hP : IsCellClosed l P) {σ : ι → SignType}
    (hσ : σ ∈ cellsOf l P) : closedCell l σ ⊆ P := by
  obtain ⟨x, hx, rfl⟩ := hσ
  exact hP x hx

def IsCellFlag (d : Finset (ι → SignType)) : Prop :=
  (∀ σ ∈ d, σ ∈ cellsOf l P) ∧ ∀ σ ∈ d, ∀ τ ∈ d, SignLE σ τ ∨ SignLE τ σ

namespace IsCellFlag

variable {l P} {d : Finset (ι → SignType)}

theorem mem_cells (h : IsCellFlag l P d) {σ : ι → SignType} (hσ : σ ∈ d) : σ ∈ cellsOf l P :=
  h.1 σ hσ

theorem le_or_le (h : IsCellFlag l P d) {σ τ : ι → SignType} (hσ : σ ∈ d) (hτ : τ ∈ d) :
    SignLE σ τ ∨ SignLE τ σ :=
  h.2 σ hσ τ hτ

theorem mono (h : IsCellFlag l P d) {d' : Finset (ι → SignType)} (hd' : d' ⊆ d) :
    IsCellFlag l P d' :=
  ⟨fun σ hσ => h.1 σ (hd' hσ), fun σ hσ τ hτ => h.2 σ (hd' hσ) τ (hd' hτ)⟩

theorem injOn (h : IsCellFlag l P d) : Set.InjOn (cellPt l P) (d : Set (ι → SignType)) :=
  (cellPt_injOn l P).mono fun σ hσ => h.1 σ (Finset.mem_coe.mp hσ)

theorem singleton {σ : ι → SignType} (hσ : σ ∈ cellsOf l P) : IsCellFlag l P {σ} :=
  ⟨fun τ hτ => by
      rw [Finset.mem_singleton] at hτ
      exact hτ ▸ hσ,
    fun τ hτ τ' hτ' => by
      rw [Finset.mem_singleton] at hτ hτ'
      exact Or.inl (hτ ▸ hτ' ▸ SignLE.refl _)⟩

theorem exists_top [Finite ι] (h : IsCellFlag l P d) (hd : d.Nonempty) :
    ∃ u ∈ d, ∀ σ ∈ d, SignLE σ u := by
  cases nonempty_fintype ι
  obtain ⟨u, hu, hmax⟩ := d.exists_max_image (fun σ => (signSupport σ).card) hd
  refine ⟨u, hu, fun σ hσ => ?_⟩
  rcases h.le_or_le hσ hu with h1 | h1
  · exact h1
  · have heq : signSupport σ ⊆ signSupport u :=
      (Finset.eq_of_subset_of_card_le (signSupport_mono h1) (hmax σ hσ)).ge
    rw [h1.eq_of_signSupport_subset heq]
    exact SignLE.refl _

end IsCellFlag

theorem notMem_openCell_of_mem_closedCell_of_signLE_ne {σ τ : ι → SignType} (h : SignLE σ τ)
    (hne : σ ≠ τ) {y : E} (hy : y ∈ closedCell l σ) : y ∉ openCell l τ := by
  obtain ⟨k, hτk, hσk⟩ := exists_ne_zero_of_signLE_ne h hne
  intro hyτ
  have h1 : l k y = 0 := eq_zero_of_mem_closedCell l hy hσk
  have h2 : SignType.sign (l k y) = τ k := congrFun hyτ k
  rw [h1, sign_zero] at h2
  exact hτk h2.symm

theorem convexHull_image_cellPt_subset_closedCell [DecidableEq E] {d : Finset (ι → SignType)}
    (hd : IsCellFlag l P d) {u : ι → SignType} (htop : ∀ σ ∈ d, SignLE σ u) :
    convexHull ℝ ((d.image (cellPt l P) : Finset E) : Set E) ⊆ closedCell l u := by
  refine convexHull_min (fun p hp => ?_) (convex_closedCell l u)
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
  exact cellPt_mem_closedCell l P (hd.mem_cells hσ) (htop σ hσ)

section FiniteIota

variable [Finite ι]

omit [Finite ι] in
theorem eq_singleton_of_erase_eq_empty [DecidableEq (ι → SignType)] {d : Finset (ι → SignType)}
    {u : ι → SignType} (hu : u ∈ d)
    (h : d.erase u = ∅) : d = {u} :=
  Finset.eq_singleton_iff_unique_mem.mpr ⟨hu, fun σ hσ => by
    by_contra hne
    exact Finset.notMem_empty σ (h ▸ Finset.mem_erase.mpr ⟨hne, hσ⟩)⟩

theorem eq_zero_of_sum_smul_cellPt_eq_zero {d : Finset (ι → SignType)} (hd : IsCellFlag l P d)
    {m : (ι → SignType) → ℝ} (hm₀ : ∑ σ ∈ d, m σ = 0)
    (hmx : ∑ σ ∈ d, m σ • cellPt l P σ = 0) : ∀ σ ∈ d, m σ = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨σ₀, hσ₀, hmσ₀⟩ := hcon
  set S := d.filter fun σ => m σ ≠ 0 with hSdef
  have hSne : S.Nonempty := ⟨σ₀, Finset.mem_filter.mpr ⟨hσ₀, hmσ₀⟩⟩
  have hS : IsCellFlag l P S := hd.mono (Finset.filter_subset _ _)
  obtain ⟨s₀, hs₀, htop₀⟩ := hS.exists_top hSne
  have hms₀ : m s₀ ≠ 0 := (Finset.mem_filter.mp hs₀).2
  have hsumS : ∑ σ ∈ S, m σ = 0 := by
    rw [← hm₀]
    exact Finset.sum_filter_of_ne fun σ _ h => h
  have hsmulS : ∑ σ ∈ S, m σ • cellPt l P σ = 0 := by
    rw [← hmx]
    exact Finset.sum_filter_of_ne fun σ _ h h0 => h (by rw [h0, zero_smul])
  by_cases hrest : (S.erase s₀).Nonempty
  · obtain ⟨s₁, hs₁, htop₁⟩ := (hS.mono (Finset.erase_subset s₀ S)).exists_top hrest
    obtain ⟨k, hk₀, hk₁⟩ := exists_ne_zero_of_signLE_ne (htop₀ s₁ (Finset.mem_of_mem_erase hs₁))
      (Finset.ne_of_mem_erase hs₁)
    have hl : ∀ q : E, (l k).linear q = l k q - l k 0 := fun q => by
      have h := (l k).linearMap_vsub q 0
      rwa [vsub_eq_sub, sub_zero, vsub_eq_sub] at h
    have hlin : ∑ σ ∈ S, m σ * l k (cellPt l P σ) = 0 := by
      have h := congrArg (l k).linear hsmulS
      rw [map_sum, map_zero] at h
      simp_rw [map_smul, hl, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hsumS, zero_mul, sub_zero] at h
      exact h
    have hzero : ∀ σ ∈ S.erase s₀, l k (cellPt l P σ) = 0 := fun σ hσ =>
      eq_zero_of_mem_closedCell l (cellPt_mem_closedCell l P
        (hS.mem_cells (Finset.mem_of_mem_erase hσ)) (htop₁ σ hσ)) hk₁
    rw [← Finset.add_sum_erase S _ hs₀,
      Finset.sum_eq_zero fun σ hσ => by rw [hzero σ hσ, mul_zero], add_zero] at hlin
    have hlk : l k (cellPt l P s₀) ≠ 0 := by
      intro h0
      have h := congrFun (cellPt_mem_openCell l P (hS.mem_cells hs₀)) k
      change SignType.sign (l k (cellPt l P s₀)) = s₀ k at h
      rw [h0, sign_zero] at h
      exact hk₀ h.symm
    exact hms₀ ((mul_eq_zero.mp hlin).resolve_right hlk)
  · rw [Finset.not_nonempty_iff_eq_empty] at hrest
    rw [eq_singleton_of_erase_eq_empty hs₀ hrest, Finset.sum_singleton] at hsumS
    exact hms₀ hsumS

theorem ray_of_decomp {p x z : E} {a : ℝ} (ha : a < 1) (hz : x = a • p + (1 - a) • z) :
    z = p + (1 - a)⁻¹ • (x - p) := by
  have h1 : 0 < 1 - a := sub_pos.mpr ha
  rw [hz]
  have h2 : a • p + (1 - a) • z - p = (1 - a) • (z - p) := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rw [h2, smul_smul, inv_mul_cancel₀ h1.ne', one_smul, add_sub_cancel]

variable [DecidableEq E]

theorem exists_decomp [DecidableEq (ι → SignType)] {d : Finset (ι → SignType)}
    (hd : IsCellFlag l P d) {u : ι → SignType}
    (hu : u ∈ d) (htop : ∀ σ ∈ d, SignLE σ u) {w : (ι → SignType) → ℝ}
    (hw₀ : ∀ σ ∈ d, 0 < w σ) (hw₁ : ∑ σ ∈ d, w σ = 1) (hrest : (d.erase u).Nonempty) :
    ∃ y : E, w u < 1 ∧ ∑ σ ∈ d, w σ • cellPt l P σ = w u • cellPt l P u + (1 - w u) • y ∧
      y ∈ closedCell l u ∧ y ∉ openCell l u ∧ y ∈ openSimplex ((d.erase u).image (cellPt l P)) := by
  have hpos : 0 < ∑ σ ∈ d.erase u, w σ :=
    Finset.sum_pos (fun σ hσ => hw₀ σ (Finset.mem_of_mem_erase hσ)) hrest
  have hsum : ∑ σ ∈ d.erase u, w σ = 1 - w u := by
    rw [Finset.sum_erase_eq_sub hu, hw₁]
  have hlt : w u < 1 := by linarith
  have h1 : 0 < 1 - w u := sub_pos.mpr hlt
  have hy : (1 - w u)⁻¹ • ∑ σ ∈ d.erase u, w σ • cellPt l P σ =
      ∑ σ ∈ d.erase u, (w σ / (1 - w u)) • cellPt l P σ := by
    simp_rw [div_eq_inv_mul, mul_smul]
    rw [Finset.smul_sum]
  have hw' : ∑ σ ∈ d.erase u, w σ / (1 - w u) = 1 := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, hsum, mul_inv_cancel₀ h1.ne']
  have hmem : ∀ s : ι → SignType, (∀ σ ∈ d.erase u, SignLE σ s) →
      (1 - w u)⁻¹ • ∑ σ ∈ d.erase u, w σ • cellPt l P σ ∈ closedCell l s := by
    intro s hs
    rw [hy]
    exact (convex_closedCell l s).sum_mem (fun σ hσ =>
        div_nonneg (hw₀ σ (Finset.mem_of_mem_erase hσ)).le h1.le) hw'
      fun σ hσ => cellPt_mem_closedCell l P (hd.mem_cells (Finset.mem_of_mem_erase hσ)) (hs σ hσ)
  obtain ⟨s₁, hs₁, htop₁⟩ := (hd.mono (Finset.erase_subset u d)).exists_top hrest
  refine ⟨(1 - w u)⁻¹ • ∑ σ ∈ d.erase u, w σ • cellPt l P σ, hlt, ?_,
    hmem u fun σ hσ => htop σ (Finset.mem_of_mem_erase hσ), ?_, ?_⟩
  · rw [← Finset.add_sum_erase d _ hu, smul_smul, mul_inv_cancel₀ h1.ne', one_smul]
  · exact notMem_openCell_of_mem_closedCell_of_signLE_ne l
      (htop s₁ (Finset.mem_of_mem_erase hs₁)) (Finset.ne_of_mem_erase hs₁) (hmem s₁ htop₁)
  · rw [mem_openSimplex_image_iff (hd.mono (Finset.erase_subset u d)).injOn]
    exact ⟨fun σ => w σ / (1 - w u),
      fun σ hσ => div_pos (hw₀ σ (Finset.mem_of_mem_erase hσ)) h1, hw', hy.symm⟩

theorem mem_openCell_top {d : Finset (ι → SignType)} (hd : IsCellFlag l P d) {u : ι → SignType}
    (hu : u ∈ d) (htop : ∀ σ ∈ d, SignLE σ u) {x : E}
    (hx : x ∈ openSimplex (d.image (cellPt l P))) : x ∈ openCell l u := by
  classical
  obtain ⟨w, hw₀, hw₁, hwx⟩ := (mem_openSimplex_image_iff hd.injOn).mp hx
  by_cases hrest : (d.erase u).Nonempty
  · obtain ⟨y, hlt, hdecomp, hyc, -, -⟩ := exists_decomp l P hd hu htop hw₀ hw₁ hrest
    rw [← hwx, hdecomp]
    exact combo_mem_openCell l (cellPt_mem_openCell l P (hd.mem_cells hu)) hyc (hw₀ u hu)
      (sub_pos.mpr hlt).le (by ring)
  · rw [Finset.not_nonempty_iff_eq_empty] at hrest
    rw [eq_singleton_of_erase_eq_empty hu hrest, Finset.sum_singleton] at hwx hw₁
    rw [← hwx, hw₁, one_smul]
    exact cellPt_mem_openCell l P (hd.mem_cells hu)

omit [DecidableEq E] in
theorem top_coeff_eq {d d' : Finset (ι → SignType)} (hd : IsCellFlag l P d)
    (hd' : IsCellFlag l P d') {u : ι → SignType} (hu : u ∈ d) (htop : ∀ σ ∈ d, SignLE σ u)
    (hu' : u ∈ d') (htop' : ∀ σ ∈ d', SignLE σ u) {w w' : (ι → SignType) → ℝ}
    (hw₀ : ∀ σ ∈ d, 0 < w σ) (hw₁ : ∑ σ ∈ d, w σ = 1) (hw'₀ : ∀ σ ∈ d', 0 < w' σ)
    (hw'₁ : ∑ σ ∈ d', w' σ = 1)
    (heq : ∑ σ ∈ d, w σ • cellPt l P σ = ∑ σ ∈ d', w' σ • cellPt l P σ) : w u = w' u := by
  classical
  have hp : cellPt l P u ∈ openCell l u := cellPt_mem_openCell l P (hd.mem_cells hu)
  by_cases hrest : (d.erase u).Nonempty
  · by_cases hrest' : (d'.erase u).Nonempty
    · obtain ⟨y, hlt, hdec, hyc, hyo, -⟩ := exists_decomp l P hd hu htop hw₀ hw₁ hrest
      obtain ⟨y', hlt', hdec', hyc', hyo', -⟩ :=
        exists_decomp l P hd' hu' htop' hw'₀ hw'₁ hrest'
      have hy := ray_of_decomp hlt hdec
      have hy' := ray_of_decomp hlt' (heq.trans hdec')
      have hT := exit_unique l hp (inv_pos.mpr (sub_pos.mpr hlt)) (inv_pos.mpr (sub_pos.mpr hlt'))
        (by rw [← hy]; exact hyc) (by rw [← hy']; exact hyc') (by rw [← hy]; exact hyo)
        (by rw [← hy']; exact hyo')
      have := inv_inj.mp hT
      linarith
    · exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hrest'
      rw [eq_singleton_of_erase_eq_empty hu' hrest', Finset.sum_singleton] at heq hw'₁
      rw [hw'₁, one_smul] at heq
      obtain ⟨y, hlt, hdec, -, hyo, -⟩ := exists_decomp l P hd hu htop hw₀ hw₁ hrest
      rw [heq] at hdec
      apply hyo
      rw [eq_of_combo_eq hlt hdec]
      exact hp
  · rw [Finset.not_nonempty_iff_eq_empty] at hrest
    rw [eq_singleton_of_erase_eq_empty hu hrest, Finset.sum_singleton] at heq hw₁
    rw [hw₁, one_smul] at heq
    by_cases hrest' : (d'.erase u).Nonempty
    · exfalso
      obtain ⟨y', hlt', hdec', -, hyo', -⟩ :=
        exists_decomp l P hd' hu' htop' hw'₀ hw'₁ hrest'
      rw [← heq] at hdec'
      apply hyo'
      rw [eq_of_combo_eq hlt' hdec']
      exact hp
    · rw [Finset.not_nonempty_iff_eq_empty] at hrest'
      rw [eq_singleton_of_erase_eq_empty hu' hrest', Finset.sum_singleton] at hw'₁
      rw [hw₁, hw'₁]

theorem eq_of_mem_openSimplex_image_cellPt_aux :
    ∀ (n : ℕ) {d d' : Finset (ι → SignType)}, d.card ≤ n → IsCellFlag l P d →
      IsCellFlag l P d' → d.Nonempty → d'.Nonempty → ∀ {x : E},
        x ∈ openSimplex (d.image (cellPt l P)) → x ∈ openSimplex (d'.image (cellPt l P)) →
          d = d' := by
  classical
  intro n
  induction n with
  | zero =>
    intro d d' hcard _ _ hne _ _ _ _
    exact absurd (Finset.card_pos.mpr hne) (by omega)
  | succ n ih =>
    intro d d' hcard hd hd' hne hne' x hx hx'
    obtain ⟨u, hu, htop⟩ := hd.exists_top hne
    obtain ⟨u', hu', htop'⟩ := hd'.exists_top hne'
    have huu' : u = u' := by
      by_contra hne''
      exact Set.disjoint_left.mp (openCell_disjoint l hne'')
        (mem_openCell_top l P hd hu htop hx) (mem_openCell_top l P hd' hu' htop' hx')
    subst huu'
    obtain ⟨w, hw₀, hw₁, hwx⟩ := (mem_openSimplex_image_iff hd.injOn).mp hx
    obtain ⟨w', hw'₀, hw'₁, hw'x⟩ := (mem_openSimplex_image_iff hd'.injOn).mp hx'
    have heq := hwx.trans hw'x.symm
    have hwu := top_coeff_eq l P hd hd' hu htop hu' htop' hw₀ hw₁ hw'₀ hw'₁ heq
    by_cases hrest : (d.erase u).Nonempty
    · obtain ⟨y, hlt, hdec, -, -, hy⟩ := exists_decomp l P hd hu htop hw₀ hw₁ hrest
      have hrest' : (d'.erase u).Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        rw [eq_singleton_of_erase_eq_empty hu' h, Finset.sum_singleton] at hw'₁
        linarith
      obtain ⟨y', -, hdec', -, -, hy'⟩ := exists_decomp l P hd' hu' htop' hw'₀ hw'₁ hrest'
      have hyy' : y = y' := by
        have h := hdec.symm.trans (heq.trans hdec')
        rw [← hwu] at h
        exact smul_right_injective E (sub_pos.mpr hlt).ne' (add_left_cancel h)
      have hcard' : (d.erase u).card ≤ n := by
        rw [Finset.card_erase_of_mem hu]
        omega
      have := ih hcard' (hd.mono (Finset.erase_subset u d)) (hd'.mono (Finset.erase_subset u d'))
        hrest hrest' hy (hyy' ▸ hy')
      rw [← Finset.insert_erase hu, ← Finset.insert_erase hu', this]
    · rw [Finset.not_nonempty_iff_eq_empty] at hrest
      have hd1 := eq_singleton_of_erase_eq_empty hu hrest
      have hw1 : w u = 1 := by
        rw [hd1, Finset.sum_singleton] at hw₁
        exact hw₁
      have hemp : d'.erase u = ∅ := by
        by_contra hne''
        have h0 : ∑ σ ∈ d'.erase u, w' σ = 0 := by
          rw [Finset.sum_erase_eq_sub hu', hw'₁, ← hwu, hw1, sub_self]
        exact absurd h0 (Finset.sum_pos (fun σ hσ => hw'₀ σ (Finset.mem_of_mem_erase hσ))
          (Finset.nonempty_iff_ne_empty.mpr hne'')).ne'
      rw [hd1, eq_singleton_of_erase_eq_empty hu' hemp]

theorem eq_of_mem_openSimplex_image_cellPt {d d' : Finset (ι → SignType)}
    (hd : IsCellFlag l P d) (hd' : IsCellFlag l P d') (hne : d.Nonempty) (hne' : d'.Nonempty)
    {x : E} (hx : x ∈ openSimplex (d.image (cellPt l P)))
    (hx' : x ∈ openSimplex (d'.image (cellPt l P))) : d = d' :=
  eq_of_mem_openSimplex_image_cellPt_aux l P d.card le_rfl hd hd' hne hne' hx hx'

theorem affineIndependent_image_cellPt {d : Finset (ι → SignType)} (hd : IsCellFlag l P d) :
    AffineIndependent ℝ ((↑) : ((d.image (cellPt l P) : Finset E) : Set E) → E) := by
  classical
  have hind : AffineIndependent ℝ fun σ : d => cellPt l P σ := by
    rw [affineIndependent_iff_of_fintype]
    intro w hw hvs
    rw [Finset.weightedVSub_eq_linear_combination _ hw] at hvs
    let m : (ι → SignType) → ℝ := fun σ => if h : σ ∈ d then w ⟨σ, h⟩ else 0
    have hm : ∀ i : d, m i = w i := fun i => by simp [m, i.2]
    have hm₀ : ∑ σ ∈ d, m σ = 0 := by
      rw [← Finset.sum_coe_sort d m]
      simp_rw [hm]
      exact hw
    have hmx : ∑ σ ∈ d, m σ • cellPt l P σ = 0 := by
      rw [← Finset.sum_coe_sort d (fun σ => m σ • cellPt l P σ)]
      simp_rw [hm]
      exact hvs
    intro i
    rw [← hm i]
    exact eq_zero_of_sum_smul_cellPt_eq_zero l P hd hm₀ hmx i i.2
  have hrange : Set.range (fun σ : d => cellPt l P σ) =
      ((d.image (cellPt l P) : Finset E) : Set E) := by
    ext y
    simp [Finset.coe_image]
  have h := hind.range
  rwa [hrange] at h

def cellDerivedFaces : Set (Finset E) :=
  {f | ∃ d : Finset (ι → SignType), IsCellFlag l P d ∧ d.Nonempty ∧ f = d.image (cellPt l P)}

omit [Finite ι] in
theorem cellDerivedFaces_isRelLowerSet :
    IsRelLowerSet (cellDerivedFaces l P) Finset.Nonempty := by
  rintro f ⟨d, hd, hne, rfl⟩
  refine ⟨hne.image _, fun g hgf hg => ?_⟩
  refine ⟨d.filter fun σ => cellPt l P σ ∈ g, hd.mono (Finset.filter_subset _ _), ?_,
    (image_filter_mem_eq hgf).symm⟩
  obtain ⟨p, hp⟩ := hg
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (hgf hp)
  exact ⟨σ, Finset.mem_filter.mpr ⟨hσ, hp⟩⟩

theorem cellDerivedFaces_indep {f : Finset E} (hf : f ∈ cellDerivedFaces l P) :
    AffineIndependent ℝ ((↑) : f → E) := by
  obtain ⟨d, hd, -, rfl⟩ := hf
  exact affineIndependent_image_cellPt l P hd

theorem cellDerivedFaces_inter {f g : Finset E} (hf : f ∈ cellDerivedFaces l P)
    (hg : g ∈ cellDerivedFaces l P) :
    convexHull ℝ (f : Set E) ∩ convexHull ℝ (g : Set E) ⊆ convexHull ℝ ((f : Set E) ∩ g) := by
  obtain ⟨d, hd, hne, rfl⟩ := hf
  obtain ⟨d', hd', hne', rfl⟩ := hg
  rintro x ⟨hxf, hxg⟩
  obtain ⟨T, hTf, hTne, hxT⟩ := exists_openSimplex_of_mem_convexHull hxf
  obtain ⟨T', hTg, hTne', hxT'⟩ := exists_openSimplex_of_mem_convexHull hxg
  rw [← image_filter_mem_eq hTf] at hxT
  rw [← image_filter_mem_eq hTg] at hxT'
  have heT : (d.filter fun σ => cellPt l P σ ∈ T).Nonempty := by
    obtain ⟨p, hp⟩ := hTne
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (hTf hp)
    exact ⟨σ, Finset.mem_filter.mpr ⟨hσ, hp⟩⟩
  have heT' : (d'.filter fun σ => cellPt l P σ ∈ T').Nonempty := by
    obtain ⟨p, hp⟩ := hTne'
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (hTg hp)
    exact ⟨σ, Finset.mem_filter.mpr ⟨hσ, hp⟩⟩
  have heq := eq_of_mem_openSimplex_image_cellPt l P (hd.mono (Finset.filter_subset _ _))
    (hd'.mono (Finset.filter_subset _ _)) heT heT' hxT hxT'
  refine convexHull_mono ?_ (openSimplex_subset_convexHull _ hxT)
  intro p hp
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
  refine ⟨Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_of_mem_filter σ hσ)), ?_⟩
  rw [heq] at hσ
  exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_of_mem_filter σ hσ))

noncomputable def cellDerived : Geometry.SimplicialComplex ℝ E where
  faces := cellDerivedFaces l P
  isRelLowerSet_faces := cellDerivedFaces_isRelLowerSet l P
  indep hf := cellDerivedFaces_indep l P hf
  inter_subset_convexHull hf hg := cellDerivedFaces_inter l P hf hg

theorem mem_cellDerived_faces_iff {f : Finset E} :
    f ∈ (cellDerived l P).faces ↔
      ∃ d : Finset (ι → SignType), IsCellFlag l P d ∧ d.Nonempty ∧ f = d.image (cellPt l P) :=
  Iff.rfl

theorem finite_cellDerived_faces : (cellDerived l P).faces.Finite := by
  classical
  cases nonempty_fintype ι
  refine Set.Finite.subset (Set.Finite.image (fun d : Finset (ι → SignType) => d.image (cellPt l P))
    (Set.toFinite (univ : Set (Finset (ι → SignType))))) ?_
  rintro f ⟨d, -, -, rfl⟩
  exact ⟨d, mem_univ d, rfl⟩

variable [FiniteDimensional ℝ E]

omit [Finite ι] [DecidableEq E] in
theorem isCompact_closedCell_of_mem_cellsOf (hP : IsCellClosed l P) (hPc : IsCompact P)
    {σ : ι → SignType} (hσ : σ ∈ cellsOf l P) : IsCompact (closedCell l σ) :=
  hPc.of_isClosed_subset (isClosed_closedCell l σ) (closedCell_subset_of_isCellClosed l P hP hσ)

omit [DecidableEq E] in
theorem exists_step (hP : IsCellClosed l P) (hPc : IsCompact P) {x : E} (hx : x ∈ P) :
    x = cellPt l P (signVec l x) ∨
      ∃ (a b : ℝ) (y : E), 0 ≤ a ∧ 0 < b ∧ a + b = 1 ∧ y ∈ P ∧
        SignLE (signVec l y) (signVec l x) ∧ signVec l y ≠ signVec l x ∧
        x = a • cellPt l P (signVec l x) + b • y := by
  have hσ : signVec l x ∈ cellsOf l P := signVec_mem_cellsOf l P hx
  have hp : cellPt l P (signVec l x) ∈ openCell l (signVec l x) := cellPt_mem_openCell l P hσ
  by_cases hxp : x = cellPt l P (signVec l x)
  · exact Or.inl hxp
  · right
    have hxc : x ∈ closedCell l (signVec l x) :=
      openCell_subset_closedCell l _ (mem_openCell_signVec l x)
    obtain ⟨T, hT1, hyc, hyo⟩ := exists_exit_of_mem_openCell l
      (isCompact_closedCell_of_mem_cellsOf l P hP hPc hσ) hp hxc hxp
    have hT : 0 < T := by linarith
    refine ⟨1 - T⁻¹, T⁻¹, cellPt l P (signVec l x) + T • (x - cellPt l P (signVec l x)),
      ?_, inv_pos.mpr hT, by ring, closedCell_subset_of_isCellClosed l P hP hσ hyc, hyc, ?_, ?_⟩
    · rw [sub_nonneg]
      exact inv_le_one_of_one_le₀ hT1
    · intro heq
      exact hyo ((mem_openCell_iff l).mpr heq)
    · rw [smul_add, smul_smul, inv_mul_cancel₀ hT.ne', one_smul, sub_smul, one_smul]
      abel

section FintypeIota

variable [Fintype ι]

theorem exists_cellFlag_aux (hP : IsCellClosed l P) (hPc : IsCompact P) :
    ∀ (n : ℕ) {x : E}, x ∈ P → (signSupport (signVec l x)).card ≤ n →
      ∃ d : Finset (ι → SignType), IsCellFlag l P d ∧ d.Nonempty ∧
        (∀ σ ∈ d, SignLE σ (signVec l x)) ∧
        x ∈ convexHull ℝ ((d.image (cellPt l P) : Finset E) : Set E) := by
  have hsingle : ∀ {x : E}, x ∈ P → x = cellPt l P (signVec l x) →
      ∃ d : Finset (ι → SignType), IsCellFlag l P d ∧ d.Nonempty ∧
        (∀ σ ∈ d, SignLE σ (signVec l x)) ∧
        x ∈ convexHull ℝ ((d.image (cellPt l P) : Finset E) : Set E) := by
    intro x hx hxp
    refine ⟨{signVec l x}, IsCellFlag.singleton (signVec_mem_cellsOf l P hx),
      Finset.singleton_nonempty _, fun σ hσ => ?_, ?_⟩
    · rw [Finset.mem_singleton] at hσ
      exact hσ ▸ SignLE.refl _
    · rw [Finset.image_singleton, Finset.coe_singleton]
      exact subset_convexHull ℝ _ (Set.mem_singleton_iff.mpr hxp)
  intro n
  induction n with
  | zero =>
    intro x hx hcard
    rcases exists_step l P hP hPc hx with h | ⟨a, b, y, -, -, -, -, hle, hne, -⟩
    · exact hsingle hx h
    · exfalso
      have := Finset.card_lt_card (signSupport_ssubset_of_signLE_ne hle hne)
      omega
  | succ n ih =>
    intro x hx hcard
    rcases exists_step l P hP hPc hx with h | ⟨a, b, y, ha, hb, hab, hy, hle, hne, hxy⟩
    · exact hsingle hx h
    · have hcard' : (signSupport (signVec l y)).card ≤ n := by
        have := Finset.card_lt_card (signSupport_ssubset_of_signLE_ne hle hne)
        omega
      obtain ⟨d₁, hd₁, hne₁, htop₁, hyd₁⟩ := ih hy hcard'
      refine ⟨insert (signVec l x) d₁, ⟨fun σ hσ => ?_, fun σ hσ τ hτ => ?_⟩,
        Finset.insert_nonempty _ _, fun σ hσ => ?_, ?_⟩
      · rcases Finset.mem_insert.mp hσ with hσx | hσ
        · rw [hσx]
          exact signVec_mem_cellsOf l P hx
        · exact hd₁.mem_cells hσ
      · rcases Finset.mem_insert.mp hσ with hσx | hσ <;>
          rcases Finset.mem_insert.mp hτ with hτx | hτ
        · rw [hσx, hτx]
          exact Or.inl (SignLE.refl _)
        · rw [hσx]
          exact Or.inr ((htop₁ τ hτ).trans hle)
        · rw [hτx]
          exact Or.inl ((htop₁ σ hσ).trans hle)
        · exact hd₁.le_or_le hσ hτ
      · rcases Finset.mem_insert.mp hσ with hσx | hσ
        · rw [hσx]
          exact SignLE.refl _
        · exact (htop₁ σ hσ).trans hle
      · have hmem : a • cellPt l P (signVec l x) + b • y ∈
            convexHull ℝ (((insert (signVec l x) d₁).image (cellPt l P) : Finset E) : Set E) := by
          refine (convex_convexHull ℝ _) ?_ ?_ ha hb.le hab
          · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr
              (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)))
          · exact convexHull_mono (Finset.coe_subset.mpr
              (Finset.image_subset_image (Finset.subset_insert _ _))) hyd₁
        rw [← hxy] at hmem
        exact hmem

end FintypeIota

theorem exists_cellFlag (hP : IsCellClosed l P) (hPc : IsCompact P) {x : E} (hx : x ∈ P) :
    ∃ d : Finset (ι → SignType), IsCellFlag l P d ∧ d.Nonempty ∧
      (∀ σ ∈ d, SignLE σ (signVec l x)) ∧
      x ∈ convexHull ℝ ((d.image (cellPt l P) : Finset E) : Set E) := by
  cases nonempty_fintype ι
  exact exists_cellFlag_aux l P hP hPc _ hx le_rfl

theorem space_cellDerived (hP : IsCellClosed l P) (hPc : IsCompact P) :
    (cellDerived l P).space = P := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨f, ⟨d, hd, hne, rfl⟩, hxf⟩ := (cellDerived l P).mem_space_iff.mp hx
    obtain ⟨u, hu, htop⟩ := hd.exists_top hne
    exact closedCell_subset_of_isCellClosed l P hP (hd.mem_cells hu)
      (convexHull_image_cellPt_subset_closedCell l P hd htop hxf)
  · intro x hx
    obtain ⟨d, hd, hne, -, hxd⟩ := exists_cellFlag l P hP hPc hx
    exact (cellDerived l P).convexHull_subset_space ⟨d, hd, hne, rfl⟩ hxd

theorem eq_biUnion_cellDerived_faces (hP : IsCellClosed l P) (hPc : IsCompact P) {C : Set E}
    (hC : IsCellClosed l C) (hCP : C ⊆ P) :
    C = ⋃ s ∈ {s ∈ (cellDerived l P).faces | convexHull ℝ (s : Set E) ⊆ C},
      convexHull ℝ (s : Set E) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨d, hd, hne, htop, hxd⟩ := exists_cellFlag l P hP hPc (hCP hx)
    refine mem_biUnion (s := {s ∈ (cellDerived l P).faces | convexHull ℝ (s : Set E) ⊆ C})
      (t := fun s : Finset E => convexHull ℝ (s : Set E)) ⟨⟨d, hd, hne, rfl⟩, ?_⟩ hxd
    exact (convexHull_image_cellPt_subset_closedCell l P hd htop).trans (hC x hx)
  · exact iUnion₂_subset fun s hs => hs.2

end FiniteIota

end DifferentialGeometry.Topology.PiecewiseLinear
