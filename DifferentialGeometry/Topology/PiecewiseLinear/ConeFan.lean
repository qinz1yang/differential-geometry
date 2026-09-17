import DifferentialGeometry.Topology.PiecewiseLinear.ConeAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.StdConeSector

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem centralConeMap_one_eq_lineMap (a b : F) {z : ℝ × ℝ} (hz : z.1 + z.2 = 1) :
    centralConeMap 1 0 a b z = AffineMap.lineMap a b z.2 := by
  rw [centralConeMap_eq_combo, AffineMap.lineMap_apply_module]
  have h1 : z.1 = 1 - z.2 := by linarith
  rw [h1]
  match_scalars <;> ring

theorem exists_isPiecewiseAffineOn_stdConeSector {N : ℕ} {σ : ℕ → ℝ} {u u' : ℝ} (hu : u < u')
    (A B : ℕ → F) (hσ0 : σ 0 = 0) (hσN : σ (N + 1) = 1) (hmono : ∀ k ≤ N, σ k < σ (k + 1))
    (hAB : A 0 = B 0) :
    ∃ Φ : ℝ × ℝ → F, IsPiecewiseAffineOn Φ (stdConeSector u u') ∧ Φ (0, 0) = A 0 ∧
      (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
        Φ (t * (1 - u), t * u) =
          AffineMap.lineMap (A k) (A (k + 1)) ((t - σ k) / (σ (k + 1) - σ k))) ∧
      (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
        Φ (t * (1 - u'), t * u') =
          AffineMap.lineMap (B k) (B (k + 1)) ((t - σ k) / (σ (k + 1) - σ k))) ∧
      (∀ r ∈ Icc u u',
        Φ (1 - r, r) = AffineMap.lineMap (A (N + 1)) (B (N + 1)) ((r - u) / (u' - u))) ∧
      (∀ z ∈ stdConeSector u u', ∃ k ≤ N, σ k ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ σ (k + 1) ∧
        Φ z ∈ convexHull ℝ ({A k, B k, A (k + 1), B (k + 1)} : Set F)) := by
  obtain ⟨Ψ, hPA, hapex, hedge, hbot, hleft, himg⟩ :=
    exists_isPiecewiseAffineOn_stdCone_of_layers A B hσ0 hσN hmono hAB
  have hd : 0 < u' - u := sub_pos.mpr hu
  have hmaps := mapsTo_sectorCoord hu
  refine ⟨Ψ ∘ (sectorCoord u u'), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hsub : stdConeSector u u' ⊆ ⇑(sectorCoord u u').toAffineMap ⁻¹' stdCone :=
      fun z hz => hmaps hz
    have hcomp := hPA.comp (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (sectorCoord u u').toAffineMap (isHPolytope_stdConeSector u u'))
    rw [inter_eq_self_of_subset_left hsub] at hcomp
    exact hcomp
  · have h0 : sectorCoord u u' (0, 0) = (0, 0) := by
      rw [sectorCoord_apply]
      refine Prod.ext ?_ ?_ <;> simp
    simp only [Function.comp_apply, h0]
    exact hapex
  · intro k hk t ht
    simp only [Function.comp_apply, sectorCoord_smul_left hu]
    exact hbot k hk t ht
  · intro k hk t ht
    simp only [Function.comp_apply, sectorCoord_smul_right hu]
    exact hleft k hk t ht
  · intro r hr
    simp only [Function.comp_apply, sectorCoord_outer hu]
    have hne : u' - u ≠ 0 := ne_of_gt hd
    have hsum : (u' - r) / (u' - u) + (r - u) / (u' - u) = 1 := by
      have hrw : (u' - r) + (r - u) = u' - u := by ring
      rw [← add_div, hrw, div_self hne]
    rw [hedge ⟨div_nonneg (by linarith [hr.2]) hd.le, div_nonneg (by linarith [hr.1]) hd.le,
      hsum⟩]
    exact centralConeMap_one_eq_lineMap _ _ hsum
  · intro z hz
    obtain ⟨k, hk, hloc, hmem⟩ := himg _ (hmaps hz)
    refine ⟨k, hk, ?_, ?_, hmem⟩
    · rw [← sectorCoord_add hu z]
      exact hloc.2.2.1
    · rw [← sectorCoord_add hu z]
      exact hloc.2.2.2

theorem dist_cellCorner_le {u u' p q a b : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ stdConeSector u u') (h1 : p ≤ z.1 + z.2) (h2 : z.1 + z.2 ≤ q)
    (ha : a ∈ Icc p q) (hb : b ∈ Icc u u') (hu : 0 ≤ u) (hu' : u' ≤ 1) :
    dist ((a * (1 - b), a * b) : ℝ × ℝ) z ≤ 2 * (q - p) + (u' - u) := by
  obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := hz
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hs0 : 0 ≤ z.1 + z.2 := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hb1' : b ≤ 1 := by linarith
  have hqp : 0 ≤ q - p := by linarith
  have hkey : |a * b - z.2| ≤ q - p + (u' - u) := by
    rw [abs_le]
    constructor <;>
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ q - p - (a - (z.1 + z.2))) hb0,
        mul_nonneg (by linarith : (0 : ℝ) ≤ a - (z.1 + z.2) - (p - q)) hb0,
        mul_nonneg hqp (by linarith : (0 : ℝ) ≤ 1 - b),
        mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ u' - b),
        mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ b - u),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (z.1 + z.2)) (by linarith : (0 : ℝ) ≤ u' - u)]
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
  rw [abs_le] at hkey
  refine ⟨?_, ?_⟩
  · rw [abs_le]
    constructor <;> nlinarith [hkey.1, hkey.2]
  · rw [abs_le]
    constructor <;> nlinarith [hkey.1, hkey.2]

open Classical in
theorem exists_isPiecewiseAffineOn_stdCone_fan {M N : ℕ} {u σ : ℕ → ℝ} (w : ℕ → ℕ → F)
    (hu0 : u 0 = 0) (huM : u (M + 1) = 1) (humono : ∀ j ≤ M, u j < u (j + 1))
    (hσ0 : σ 0 = 0) (hσN : σ (N + 1) = 1) (hσmono : ∀ k ≤ N, σ k < σ (k + 1))
    (hw0 : ∀ j, w 0 j = w 0 0) :
    ∃ Ψ : ℝ × ℝ → F, IsPiecewiseAffineOn Ψ stdCone ∧ Ψ (0, 0) = w 0 0 ∧
      (∀ j ≤ M, ∀ r ∈ Icc (u j) (u (j + 1)),
        Ψ (1 - r, r) =
          AffineMap.lineMap (w (N + 1) j) (w (N + 1) (j + 1)) ((r - u j) / (u (j + 1) - u j))) ∧
      (∀ z ∈ stdCone, ∃ k ≤ N, ∃ j ≤ M, σ k ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ σ (k + 1) ∧
        z ∈ stdConeSector (u j) (u (j + 1)) ∧
        Ψ z ∈ convexHull ℝ ({w k j, w k (j + 1), w (k + 1) j, w (k + 1) (j + 1)} : Set F)) := by
  classical
  have huchain := le_of_chain (fun j hj => (humono j hj).le)
  have hσchain := le_of_chain (fun k hk => (hσmono k hk).le)
  have hunn : ∀ j ≤ M + 1, 0 ≤ u j := by
    intro j hj
    have h := huchain j hj 0 (Nat.zero_le _)
    rwa [hu0] at h
  have hule : ∀ j ≤ M + 1, u j ≤ 1 := by
    intro j hj
    have h := huchain (M + 1) le_rfl j hj
    rwa [huM] at h
  have hσ01 : ∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)), t ∈ Icc (0 : ℝ) 1 := by
    intro k hk t ht
    have h1 := hσchain k (by omega) 0 (Nat.zero_le _)
    have h2 := hσchain (N + 1) le_rfl (k + 1) (by omega)
    rw [hσ0] at h1
    rw [hσN] at h2
    exact ⟨le_trans h1 ht.1, le_trans ht.2 h2⟩
  have hUclosed : ∀ j : ℕ, IsClosed (⋃ i ≤ j, stdConeSector (u i) (u (i + 1))) := by
    intro j
    exact Set.Finite.isClosed_biUnion (Set.finite_Iic j)
      (fun i _ => (isHPolytope_stdConeSector _ _).isClosed)
  have hmemOuter : ∀ i ≤ M, ∀ r ∈ Icc (u i) (u (i + 1)),
      ((1 - r, r) : ℝ × ℝ) ∈ stdConeSector (u i) (u (i + 1)) := by
    intro i hi r hr
    have h1 : 0 ≤ u i := hunn i (by omega)
    have h2 : u (i + 1) ≤ 1 := hule (i + 1) (by omega)
    exact ⟨by linarith [hr.2], by linarith [hr.1], by linarith, by linarith [hr.1],
      by linarith [hr.2]⟩
  have key : ∀ j, j ≤ M → ∃ Ψ : ℝ × ℝ → F,
      IsPiecewiseAffineOn Ψ (⋃ i ≤ j, stdConeSector (u i) (u (i + 1))) ∧ Ψ (0, 0) = w 0 0 ∧
      (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
        Ψ (t * (1 - u (j + 1)), t * u (j + 1)) =
          AffineMap.lineMap (w k (j + 1)) (w (k + 1) (j + 1)) ((t - σ k) / (σ (k + 1) - σ k))) ∧
      (∀ i ≤ j, ∀ r ∈ Icc (u i) (u (i + 1)),
        Ψ (1 - r, r) =
          AffineMap.lineMap (w (N + 1) i) (w (N + 1) (i + 1)) ((r - u i) / (u (i + 1) - u i))) ∧
      (∀ z ∈ ⋃ i ≤ j, stdConeSector (u i) (u (i + 1)), ∃ k ≤ N, ∃ i ≤ j,
        σ k ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ σ (k + 1) ∧ z ∈ stdConeSector (u i) (u (i + 1)) ∧
        Ψ z ∈ convexHull ℝ ({w k i, w k (i + 1), w (k + 1) i, w (k + 1) (i + 1)} : Set F)) := by
    intro j
    induction j with
    | zero =>
      intro hj
      obtain ⟨Φ, hΦPA, hΦapex, hΦbot, hΦleft, hΦouter, hΦimg⟩ :=
        exists_isPiecewiseAffineOn_stdConeSector (humono 0 hj) (fun k => w k 0)
          (fun k => w k (0 + 1)) hσ0 hσN hσmono (by rw [hw0 0, hw0 (0 + 1)])
      have hU : (⋃ i ≤ 0, stdConeSector (u i) (u (i + 1))) = stdConeSector (u 0) (u (0 + 1)) := by
        ext z
        simp only [mem_iUnion, exists_prop]
        constructor
        · rintro ⟨i, hi, hz⟩
          have hi0 : i = 0 := by omega
          subst hi0
          exact hz
        · intro hz
          exact ⟨0, le_rfl, hz⟩
      refine ⟨Φ, ?_, ?_, hΦleft, ?_, ?_⟩
      · rw [hU]
        exact hΦPA
      · exact hΦapex
      · intro i hi r hr
        have hi0 : i = 0 := by omega
        subst hi0
        exact hΦouter r hr
      · rw [hU]
        intro z hz
        obtain ⟨k, hk, h1, h2, hmem⟩ := hΦimg z hz
        exact ⟨k, hk, 0, le_rfl, h1, h2, hz, hmem⟩
    | succ j ih =>
      intro hj
      obtain ⟨Ψ, hPA, hapex, hray, houterj, himgj⟩ := ih (by omega)
      obtain ⟨Φ, hΦPA, hΦapex, hΦbot, hΦleft, hΦouter, hΦimg⟩ :=
        exists_isPiecewiseAffineOn_stdConeSector (humono (j + 1) hj) (fun k => w k (j + 1))
          (fun k => w k (j + 1 + 1)) hσ0 hσN hσmono (by rw [hw0 (j + 1), hw0 (j + 1 + 1)])
      have hUsucc : (⋃ i ≤ j + 1, stdConeSector (u i) (u (i + 1))) =
          (⋃ i ≤ j, stdConeSector (u i) (u (i + 1))) ∪
            stdConeSector (u (j + 1)) (u (j + 1 + 1)) := by
        ext z
        simp only [mem_iUnion, mem_union, exists_prop]
        constructor
        · rintro ⟨i, hi, hz⟩
          rcases Nat.lt_or_ge i (j + 1) with h | h
          · exact Or.inl ⟨i, by omega, hz⟩
          · have hij : i = j + 1 := by omega
            subst hij
            exact Or.inr hz
        · rintro (⟨i, hi, hz⟩ | hz)
          · exact ⟨i, by omega, hz⟩
          · exact ⟨j + 1, le_rfl, hz⟩
      have hcompat : EqOn Ψ Φ ((⋃ i ≤ j, stdConeSector (u i) (u (i + 1))) ∩
          stdConeSector (u (j + 1)) (u (j + 1 + 1))) := by
        rintro z ⟨hz1, hz2⟩
        simp only [mem_iUnion, exists_prop] at hz1
        obtain ⟨i, hi, hzi⟩ := hz1
        have hiu : u (i + 1) ≤ u (j + 1) := huchain (j + 1) (by omega) (i + 1) (by omega)
        have hzray := eq_smul_of_mem_inter hiu hzi hz2
        have hzst : z ∈ stdCone := stdConeSector_subset_stdCone _ _ hz2
        have ht01 : z.1 + z.2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hzst.1, hzst.2.1], hzst.2.2⟩
        obtain ⟨k, hk, hkt⟩ := exists_mem_Icc_of_subdivision hσ0 hσN ht01
        have hΨz : Ψ z = Ψ ((z.1 + z.2) * (1 - u (j + 1)), (z.1 + z.2) * u (j + 1)) :=
          congrArg Ψ hzray
        have hΦz : Φ z = Φ ((z.1 + z.2) * (1 - u (j + 1)), (z.1 + z.2) * u (j + 1)) :=
          congrArg Φ hzray
        rw [hΨz, hΦz, hray k hk _ hkt]
        exact (hΦbot k hk _ hkt).symm
      have hΦval : ∀ z ∈ stdConeSector (u (j + 1)) (u (j + 1 + 1)),
          (⋃ i ≤ j, stdConeSector (u i) (u (i + 1))).piecewise Ψ Φ z = Φ z := by
        intro z hz
        by_cases hmem : z ∈ ⋃ i ≤ j, stdConeSector (u i) (u (i + 1))
        · rw [piecewise_eq_of_mem _ _ _ hmem]
          exact hcompat ⟨hmem, hz⟩
        · exact piecewise_eq_of_notMem _ _ _ hmem
      refine ⟨(⋃ i ≤ j, stdConeSector (u i) (u (i + 1))).piecewise Ψ Φ, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hUsucc]
        exact hPA.piecewise_of_isClosed hΦPA (hUclosed j)
          (isHPolytope_stdConeSector _ _).isClosed hcompat
      · have h00 : ((0, 0) : ℝ × ℝ) ∈ ⋃ i ≤ j, stdConeSector (u i) (u (i + 1)) := by
          simp only [mem_iUnion, exists_prop]
          exact ⟨0, Nat.zero_le _, le_rfl, le_rfl, by norm_num, by simp, by simp⟩
        rw [piecewise_eq_of_mem _ _ _ h00]
        exact hapex
      · intro k hk t ht
        have hmem : ((t * (1 - u (j + 1 + 1)), t * u (j + 1 + 1)) : ℝ × ℝ) ∈
            stdConeSector (u (j + 1)) (u (j + 1 + 1)) :=
          mem_stdConeSector_smul_right (humono (j + 1) hj).le (hunn (j + 1) (by omega))
            (hule (j + 1 + 1) (by omega)) (hσ01 k hk t ht)
        rw [hΦval _ hmem]
        exact hΦleft k hk t ht
      · intro i hi r hr
        rcases Nat.lt_or_ge i (j + 1) with hij | hij
        · have hmem : ((1 - r, r) : ℝ × ℝ) ∈ ⋃ i' ≤ j, stdConeSector (u i') (u (i' + 1)) := by
            simp only [mem_iUnion, exists_prop]
            exact ⟨i, by omega, hmemOuter i (by omega) r hr⟩
          rw [piecewise_eq_of_mem _ _ _ hmem]
          exact houterj i (by omega) r hr
        · have hi1 : i = j + 1 := by omega
          subst hi1
          rw [hΦval _ (hmemOuter (j + 1) hj r hr)]
          exact hΦouter r hr
      · intro z hz
        rw [hUsucc] at hz
        rcases hz with hz | hz
        · obtain ⟨k, hk, i, hi, h1, h2, hsec, hmem⟩ := himgj z hz
          refine ⟨k, hk, i, by omega, h1, h2, hsec, ?_⟩
          rwa [piecewise_eq_of_mem _ _ _ hz]
        · obtain ⟨k, hk, h1, h2, hmem⟩ := hΦimg z hz
          refine ⟨k, hk, j + 1, le_rfl, h1, h2, hz, ?_⟩
          rwa [hΦval _ hz]
  obtain ⟨Ψ, hPA, hapex, -, houter, himg⟩ := key M le_rfl
  rw [stdConeSector_union hu0 huM] at hPA himg
  exact ⟨Ψ, hPA, hapex, houter, himg⟩

theorem exists_pos_forall_exists_isPiecewiseAffineOn_stdCone_dist_le
    (f : ℝ × ℝ → F) (hf : ContinuousOn f stdCone) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (M : ℕ) (u : ℕ → ℝ) (g : ℕ → F), u 0 = 0 → u (M + 1) = 1 →
      (∀ j ≤ M, u j < u (j + 1)) → (∀ j ≤ M, u (j + 1) - u j < δ) →
      (∀ j ≤ M + 1, dist (g j) (f (1 - u j, u j)) ≤ ε) →
      ∃ Ψ : ℝ × ℝ → F, IsPiecewiseAffineOn Ψ stdCone ∧
        (∀ j ≤ M, ∀ r ∈ Icc (u j) (u (j + 1)),
          Ψ (1 - r, r) = AffineMap.lineMap (g j) (g (j + 1)) ((r - u j) / (u (j + 1) - u j))) ∧
        ∀ z ∈ stdCone, dist (Ψ z) (f z) ≤ 2 * ε := by
  classical
  have hcompact : IsCompact stdCone := by
    rw [← stdConeLayer_zero_one]
    exact (isHPolytope_stdConeLayer le_rfl).isCompact
  obtain ⟨δ₀, hδ₀, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hf) ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show (0 : ℝ) < δ₀ / 4 by linarith)
  refine ⟨δ₀ / 2, by linarith, ?_⟩
  intro M u g hu0 huM humono humesh hgclose
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have huchain := le_of_chain (fun j hj => (humono j hj).le)
  have hunn : ∀ j ≤ M + 1, 0 ≤ u j := by
    intro j hj
    have h := huchain j hj 0 (Nat.zero_le _)
    rwa [hu0] at h
  have hule : ∀ j ≤ M + 1, u j ≤ 1 := by
    intro j hj
    have h := huchain (M + 1) le_rfl j hj
    rwa [huM] at h
  set σ : ℕ → ℝ := fun k => (k : ℝ) / ((N : ℝ) + 1) with hσdef
  have hσ0 : σ 0 = 0 := by
    simp [hσdef]
  have hσN : σ (N + 1) = 1 := by
    simp only [hσdef]
    push_cast
    field_simp
  have hmesh : ∀ k : ℕ, σ (k + 1) - σ k = 1 / ((N : ℝ) + 1) := by
    intro k
    simp only [hσdef]
    push_cast
    rw [← sub_div]
    congr 1
    ring
  have hσmono : ∀ k ≤ N, σ k < σ (k + 1) := by
    intro k _
    have h := hmesh k
    have h2 : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    linarith
  have hσ01 : ∀ a ≤ N + 1, σ a ∈ Icc (0 : ℝ) 1 := by
    intro a ha
    refine ⟨by positivity, ?_⟩
    simp only [hσdef]
    rw [div_le_one hNpos]
    have : (a : ℝ) ≤ ((N : ℝ) + 1) := by
      have := Nat.cast_le (α := ℝ) |>.mpr ha
      push_cast at this
      linarith
    linarith
  set w : ℕ → ℕ → F := fun k j => if k ≤ N then f (σ k * (1 - u j), σ k * u j) else g j with hwdef
  have hwle : ∀ k ≤ N, ∀ j, w k j = f (σ k * (1 - u j), σ k * u j) := by
    intro k hk j
    simp only [hwdef]
    rw [if_pos hk]
  have hwtop : ∀ j, w (N + 1) j = g j := by
    intro j
    simp only [hwdef]
    rw [if_neg (by omega)]
  have hw0 : ∀ j, w 0 j = w 0 0 := by
    intro j
    rw [hwle 0 (Nat.zero_le N) j, hwle 0 (Nat.zero_le N) 0, hσ0]
    norm_num
  obtain ⟨Ψ, hPA, hapex, houter, himg⟩ :=
    exists_isPiecewiseAffineOn_stdCone_fan w hu0 huM humono hσ0 hσN hσmono hw0
  refine ⟨Ψ, hPA, ?_, ?_⟩
  · intro j hj r hr
    rw [houter j hj r hr, hwtop j, hwtop (j + 1)]
  · intro z hz
    obtain ⟨k, hk, j, hj, h1, h2, hsec, hmem⟩ := himg z hz
    have hcorner : ∀ a b : ℕ, a ≤ N + 1 → b ≤ M + 1 → σ a ∈ Icc (σ k) (σ (k + 1)) →
        u b ∈ Icc (u j) (u (j + 1)) → dist (w a b) (f z) ≤ 2 * ε := by
      intro a b ha hb hσa hub
      have hp : ((σ a * (1 - u b), σ a * u b) : ℝ × ℝ) ∈ stdCone :=
        stdConeSector_subset_stdCone _ _
          (mem_stdConeSector_smul_left le_rfl (hunn b hb) (hule b hb) (hσ01 a ha))
      have hdcell := dist_cellCorner_le hsec h1 h2 hσa hub (hunn j (by omega))
        (hule (j + 1) (by omega))
      have hdlt : dist ((σ a * (1 - u b), σ a * u b) : ℝ × ℝ) z < δ₀ := by
        have e1 := hmesh k
        have e2 := humesh j hj
        have e3 : 1 / ((N : ℝ) + 1) < δ₀ / 4 := hN
        linarith
      have hfd : dist (f (σ a * (1 - u b), σ a * u b)) (f z) < ε := hunif _ hp _ hz hdlt
      have hwd : dist (w a b) (f (σ a * (1 - u b), σ a * u b)) ≤ ε := by
        by_cases hc : a ≤ N
        · rw [hwle a hc b, dist_self]
          exact hε.le
        · have haN : a = N + 1 := by omega
          subst haN
          rw [hwtop b, hσN, one_mul, one_mul]
          exact hgclose b hb
      calc dist (w a b) (f z)
          ≤ dist (w a b) (f (σ a * (1 - u b), σ a * u b)) +
            dist (f (σ a * (1 - u b), σ a * u b)) (f z) := dist_triangle _ _ _
        _ ≤ 2 * ε := by linarith
    have hball : ({w k j, w k (j + 1), w (k + 1) j, w (k + 1) (j + 1)} : Set F) ⊆
        Metric.closedBall (f z) (2 * ε) := by
      intro x hx
      have hσk : σ k ∈ Icc (σ k) (σ (k + 1)) := ⟨le_rfl, (hσmono k hk).le⟩
      have hσk1 : σ (k + 1) ∈ Icc (σ k) (σ (k + 1)) := ⟨(hσmono k hk).le, le_rfl⟩
      have huj : u j ∈ Icc (u j) (u (j + 1)) := ⟨le_rfl, (humono j hj).le⟩
      have huj1 : u (j + 1) ∈ Icc (u j) (u (j + 1)) := ⟨(humono j hj).le, le_rfl⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hcorner k j (by omega) (by omega) hσk huj
      · exact hcorner k (j + 1) (by omega) (by omega) hσk huj1
      · exact hcorner (k + 1) j (by omega) (by omega) hσk1 huj
      · exact hcorner (k + 1) (j + 1) (by omega) (by omega) hσk1 huj1
    exact convexHull_min hball (convex_closedBall (f z) (2 * ε)) hmem

end DifferentialGeometry.Topology.PiecewiseLinear
