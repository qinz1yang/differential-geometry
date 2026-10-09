import Mathlib.Topology.Path
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UniformSpace.Compact
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import DifferentialGeometry.Geometry.Comparison.Toponogov.RemoteTriangle

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open scoped ENNReal Topology Manifold ContDiff



section

variable {Y : Type*} [PseudoMetricSpace Y]

theorem eVariationOn_extend_trans_le {a b c : Y} (γ₁ : Path a b) (γ₂ : Path b c) :
    eVariationOn (γ₁.trans γ₂).extend (Set.Icc (0 : ℝ) 1) ≤
      eVariationOn γ₁.extend (Set.Icc (0 : ℝ) 1) +
        eVariationOn γ₂.extend (Set.Icc (0 : ℝ) 1) := by
  have hhalf : (1 : ℝ) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hsplit :=
    eVariationOn.Icc_add_Icc (⇑(γ₁.trans γ₂).extend) (s := Set.Icc (0 : ℝ) 1) (a := (0 : ℝ))
      (b := 1 / 2) (c := 1) (by norm_num) (by norm_num) hhalf
  have e1 : Set.Icc (0 : ℝ) 1 ∩ Set.Icc (0 : ℝ) (1 / 2) = Set.Icc (0 : ℝ) (1 / 2) :=
    Set.inter_eq_right.2 (Set.Icc_subset_Icc le_rfl (by norm_num))
  have e2 : Set.Icc (0 : ℝ) 1 ∩ Set.Icc (1 / 2 : ℝ) 1 = Set.Icc (1 / 2 : ℝ) 1 :=
    Set.inter_eq_right.2 (Set.Icc_subset_Icc (by norm_num) le_rfl)
  have e3 : Set.Icc (0 : ℝ) 1 ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.inter_self _
  rw [e1, e2, e3] at hsplit
  have hmono₁ : MonotoneOn (fun t : ℝ => 2 * t) (Set.Icc (0 : ℝ) (1 / 2)) :=
    fun _ _ _ _ huv => by linarith
  have hmono₂ : MonotoneOn (fun t : ℝ => 2 * t - 1) (Set.Icc (1 / 2 : ℝ) 1) :=
    fun _ _ _ _ huv => by linarith
  have himg₁ : (fun t : ℝ => 2 * t) '' Set.Icc (0 : ℝ) (1 / 2) = Set.Icc (0 : ℝ) 1 := by
    ext v
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      constructor <;> linarith
    · rintro ⟨hv0, hv1⟩
      exact ⟨v / 2, ⟨by linarith, by linarith⟩, by linarith⟩
  have himg₂ : (fun t : ℝ => 2 * t - 1) '' Set.Icc (1 / 2 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := by
    ext v
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      constructor <;> linarith
    · rintro ⟨hv0, hv1⟩
      exact ⟨(v + 1) / 2, ⟨by linarith, by linarith⟩, by linarith⟩
  have heq₁ : Set.EqOn (⇑(γ₁.trans γ₂).extend)
      ((⇑γ₁.extend) ∘ fun t : ℝ => 2 * t) (Set.Icc (0 : ℝ) (1 / 2)) :=
    fun _ ht => Path.extend_trans_of_le_half γ₁ γ₂ ht.2
  have heq₂ : Set.EqOn (⇑(γ₁.trans γ₂).extend)
      ((⇑γ₂.extend) ∘ fun t : ℝ => 2 * t - 1) (Set.Icc (1 / 2 : ℝ) 1) :=
    fun _ ht => Path.extend_trans_of_half_le γ₁ γ₂ ht.1
  rw [eVariationOn.eq_of_eqOn heq₁,
    eVariationOn.comp_eq_of_monotoneOn (⇑γ₁.extend) (fun t : ℝ => 2 * t) hmono₁, himg₁,
    eVariationOn.eq_of_eqOn heq₂,
    eVariationOn.comp_eq_of_monotoneOn (⇑γ₂.extend) (fun t : ℝ => 2 * t - 1) hmono₂,
    himg₂] at hsplit
  exact le_of_eq hsplit.symm

theorem dist_start_lt_of_eVariationOn_lt {a b : Y} (γ : Path a b) {r : ℝ}
    (hr : eVariationOn γ.extend (Set.Icc (0 : ℝ) 1) < ENNReal.ofReal r) (s : unitInterval) :
    dist a (γ s) < r := by
  have hrpos : 0 < r := by
    by_contra hcon
    rw [ENNReal.ofReal_eq_zero.2 (not_lt.1 hcon)] at hr
    simp at hr
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hs : (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := s.2
  have hle := eVariationOn.edist_le (⇑γ.extend) h0 hs
  rw [Path.extend_zero, Path.extend_extends'] at hle
  have hlt : edist a (γ s) < ENNReal.ofReal r := lt_of_le_of_lt hle hr
  rw [edist_dist] at hlt
  exact (ENNReal.ofReal_lt_ofReal_iff hrpos).1 hlt

theorem exists_path_of_chain {S : Set Y} (w : ℕ → Y) (hw : w 0 ∈ S) :
    ∀ n : ℕ,
      (∀ k, k < n → ∃ γ : Path (w k) (w (k + 1)),
          BoundedVariationOn γ.extend (Set.Icc (0 : ℝ) 1) ∧ ∀ s, γ s ∈ S) →
        ∃ γ : Path (w 0) (w n),
          BoundedVariationOn γ.extend (Set.Icc (0 : ℝ) 1) ∧ ∀ s, γ s ∈ S := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨Path.refl (w 0), ?_, ?_⟩
    · have hzero : eVariationOn (⇑(Path.refl (w 0)).extend) (Set.Icc (0 : ℝ) 1) = 0 := by
        refine eVariationOn.constant_on ?_
        rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
        simp
      have hne : eVariationOn (⇑(Path.refl (w 0)).extend) (Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
        rw [hzero]
        exact ENNReal.zero_ne_top
      exact hne
    · intro s
      simpa using hw
  | succ n ih =>
    intro hchain
    obtain ⟨γ, hγvar, hγS⟩ := ih fun k hk => hchain k (Nat.lt_succ_of_lt hk)
    obtain ⟨γ', hγ'var, hγ'S⟩ := hchain n (Nat.lt_succ_self n)
    refine ⟨γ.trans γ', ?_, ?_⟩
    · exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hγvar, hγ'var⟩)
        (eVariationOn_extend_trans_le γ γ')
    · intro s
      have hmem : (γ.trans γ') s ∈ Set.range ⇑(γ.trans γ') := ⟨s, rfl⟩
      rw [Path.trans_range] at hmem
      rcases hmem with ⟨v, hv⟩ | ⟨v, hv⟩
      · exact hv ▸ hγS v
      · exact hv ▸ hγ'S v

end



def IsApproxLengthSpace (Y : Type*) [PseudoMetricSpace Y] : Prop :=
  ∀ (v w : Y) (η : ℝ), 0 < η →
    ∃ γ : Path v w, eVariationOn γ.extend (Set.Icc (0 : ℝ) 1) < ENNReal.ofReal (dist v w + η)

theorem exists_partition_eventually_rectifiable_path_avoiding_ball
    {X : Type*} [PseudoMetricSpace X] (p : X) {Xj : ℕ → Type*} [∀ j, MetricSpace (Xj j)]
    (pj : ∀ j, Xj j) (hlen : ∀ j, IsApproxLengthSpace (Xj j)) (zeta : ℝ → X)
    (hzeta : ContinuousOn zeta (Set.Icc (0 : ℝ) 1)) {delta : ℝ} (hdelta : 0 < delta)
    (hclear : ∀ t ∈ Set.Icc (0 : ℝ) 1, delta ≤ dist p (zeta t))
    (hdata : ∀ (N : ℕ) (t : ℕ → ℝ), 0 < N → t 0 = 0 → t N = 1 → (∀ k, k < N → t k < t (k + 1)) →
      ∃ z : ∀ j, ℕ → Xj j,
        (∀ k, k ≤ N → Filter.Tendsto (fun j => dist (pj j) (z j k)) Filter.atTop
          (𝓝 (dist p (zeta (t k))))) ∧
        (∀ k, k < N → Filter.Tendsto (fun j => dist (z j k) (z j (k + 1))) Filter.atTop
          (𝓝 (dist (zeta (t k)) (zeta (t (k + 1))))))) :
    ∃ (N : ℕ) (t : ℕ → ℝ) (z : ∀ j, ℕ → Xj j),
      0 < N ∧ t 0 = 0 ∧ t N = 1 ∧ (∀ k, k < N → t k < t (k + 1)) ∧
        (∀ k, k ≤ N → Filter.Tendsto (fun j => dist (pj j) (z j k)) Filter.atTop
          (𝓝 (dist p (zeta (t k))))) ∧
        (∀ k, k < N → Filter.Tendsto (fun j => dist (z j k) (z j (k + 1))) Filter.atTop
          (𝓝 (dist (zeta (t k)) (zeta (t (k + 1)))))) ∧
        ∀ᶠ j in Filter.atTop, ∃ γ : Path (z j 0) (z j N),
          BoundedVariationOn γ.extend (Set.Icc (0 : ℝ) 1) ∧
            ∀ s, γ s ∉ Metric.ball (pj j) (delta / 2) := by
  have huc : UniformContinuousOn zeta (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hzeta
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨eps, heps, huc⟩ := huc (delta / 16) (by linarith)
  obtain ⟨N, hNpos, hNeps⟩ : ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) < eps := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / eps)
    refine ⟨N₀ + 1, Nat.succ_pos N₀, ?_⟩
    have hinv : (0 : ℝ) < 1 / eps := by positivity
    have hgt : 1 / eps < ((N₀ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hlt := one_div_lt_one_div_of_lt hinv hgt
    rwa [one_div_one_div] at hlt
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  obtain ⟨tp, ht0, htN, htmono, htmem, htdist⟩ :
      ∃ tp : ℕ → ℝ, tp 0 = 0 ∧ tp N = 1 ∧ (∀ k, k < N → tp k < tp (k + 1)) ∧
        (∀ k, k ≤ N → tp k ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ k, k < N → dist (tp k) (tp (k + 1)) < eps := by
    refine ⟨fun k => (k : ℝ) / (N : ℝ), by norm_num, div_self (ne_of_gt hNR), ?_, ?_, ?_⟩
    · intro k _
      have hk : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      calc (k : ℝ) / (N : ℝ) = (k : ℝ) * (1 / (N : ℝ)) := by rw [mul_one_div]
        _ < ((k + 1 : ℕ) : ℝ) * (1 / (N : ℝ)) :=
            mul_lt_mul_of_pos_right hk (by positivity)
        _ = ((k + 1 : ℕ) : ℝ) / (N : ℝ) := by rw [mul_one_div]
    · intro k hk
      have hkR : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
      have hup : (k : ℝ) * (1 / (N : ℝ)) ≤ (N : ℝ) * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hkR (by positivity)
      rw [mul_one_div, mul_one_div, div_self (ne_of_gt hNR)] at hup
      exact ⟨by positivity, hup⟩
    · intro k _
      have hdiff : ((k + 1 : ℕ) : ℝ) / (N : ℝ) - (k : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by
        rw [div_sub_div_same]
        congr 1
        push_cast
        ring
      have hpos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
      rw [Real.dist_eq, abs_sub_comm, hdiff, abs_of_pos hpos]
      exact hNeps
  obtain ⟨z, hz1, hz2⟩ := hdata N tp hNpos ht0 htN htmono
  refine ⟨N, tp, z, hNpos, ht0, htN, htmono, hz1, hz2, ?_⟩
  have hev1 : ∀ᶠ j in Filter.atTop, ∀ k : Fin (N + 1),
      15 * delta / 16 < dist (pj j) (z j (k : ℕ)) := by
    rw [Filter.eventually_all]
    intro k
    have hmemk : tp (k : ℕ) ∈ Set.Icc (0 : ℝ) 1 :=
      htmem (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)
    have hbig := hclear (tp (k : ℕ)) hmemk
    exact (hz1 (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)).eventually_const_lt (by linarith)
  have hev2 : ∀ᶠ j in Filter.atTop, ∀ k : Fin N,
      dist (z j (k : ℕ)) (z j ((k : ℕ) + 1)) < delta / 8 := by
    rw [Filter.eventually_all]
    intro k
    have hsmall := huc (tp (k : ℕ)) (htmem (k : ℕ) (le_of_lt k.isLt)) (tp ((k : ℕ) + 1))
      (htmem ((k : ℕ) + 1) k.isLt) (htdist (k : ℕ) k.isLt)
    exact (hz2 (k : ℕ) k.isLt).eventually_lt_const (by linarith)
  filter_upwards [hev1, hev2] with j h1 h2
  have hw0 : z j 0 ∈ {y : Xj j | delta / 2 ≤ dist y (pj j)} := by
    have hbase : 15 * delta / 16 < dist (pj j) (z j 0) := by
      simpa using h1 ⟨0, Nat.succ_pos N⟩
    have hfar : delta / 2 ≤ dist (z j 0) (pj j) := by
      rw [dist_comm]
      linarith
    exact hfar
  have hchain : ∀ k, k < N → ∃ γ : Path (z j k) (z j (k + 1)),
      BoundedVariationOn γ.extend (Set.Icc (0 : ℝ) 1) ∧
        ∀ s, γ s ∈ {y : Xj j | delta / 2 ≤ dist y (pj j)} := by
    intro k hk
    obtain ⟨γ, hγ⟩ := hlen j (z j k) (z j (k + 1)) (delta / 8) (by linarith)
    have hedge : dist (z j k) (z j (k + 1)) < delta / 8 := by
      simpa using h2 ⟨k, hk⟩
    have hbase : 15 * delta / 16 < dist (pj j) (z j k) := by
      simpa using h1 ⟨k, Nat.lt_succ_of_lt hk⟩
    refine ⟨γ, ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_of_lt hγ), ?_⟩
    intro s
    have hnear : dist (z j k) (γ s) < dist (z j k) (z j (k + 1)) + delta / 8 :=
      dist_start_lt_of_eVariationOn_lt γ hγ s
    have htri : dist (pj j) (z j k) ≤ dist (pj j) (γ s) + dist (γ s) (z j k) :=
      dist_triangle _ _ _
    have hcomm : dist (γ s) (z j k) = dist (z j k) (γ s) := dist_comm _ _
    have hfar : delta / 2 ≤ dist (γ s) (pj j) := by
      rw [dist_comm]
      linarith
    exact hfar
  obtain ⟨γ, hγvar, hγS⟩ := exists_path_of_chain (z j) hw0 N hchain
  refine ⟨γ, hγvar, ?_⟩
  intro s
  rw [Metric.mem_ball]
  exact not_lt.2 (hγS s)




end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
