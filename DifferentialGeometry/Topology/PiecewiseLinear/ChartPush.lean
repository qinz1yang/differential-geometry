/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLHomeomorphOn_univ_chartConj {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {U : Set E} {V : Set F} {φ : E → F} (hU : IsOpen U)
    (hφ : IsPLHomeomorphOn φ U V) {ψ : F → F} (hψ : IsPLHomeomorphOn ψ univ univ) {K : Set F}
    (hK : IsCompact K) (hKV : K ⊆ V) (hfix : ∀ z, z ∉ K → ψ z = z) :
    IsPLHomeomorphOn (fun y => if y ∈ U then Function.invFunOn φ U (ψ (φ y)) else y)
      univ univ := by
  classical
  set g := Function.invFunOn φ U with hgdef
  have hg : IsPLHomeomorphOn g V U := hφ.symm
  have hgφ : ∀ y ∈ U, g (φ y) = y := fun y hy => hφ.bijOn.invOn_invFunOn.1 hy
  have hφg : ∀ z ∈ V, φ (g z) = z := fun z hz => hφ.bijOn.invOn_invFunOn.2 hz
  have hgV : ∀ z ∈ V, g z ∈ U := fun z hz => hg.bijOn.mapsTo hz
  have hφU : ∀ y ∈ U, φ y ∈ V := fun y hy => hφ.bijOn.mapsTo hy
  have hKE : IsCompact (g '' K) := hK.image_of_continuousOn
    (hg.isPiecewiseAffineOn.continuousOn.mono hKV)
  have hKEU : g '' K ⊆ U := image_subset_iff.mpr fun z hz => hgV z (hKV hz)
  have hmaps : ∀ θ : F → F, (∀ z, z ∉ K → θ z = z) → Function.Injective θ →
      ∀ z ∈ K, θ z ∈ K := by
    intro θ hθ hinj z hz
    by_contra h
    have h1 := hθ _ h
    exact h (by rw [hinj h1]; exact hz)
  have hPL : ∀ θ : F → F, IsPiecewiseAffineOn θ univ → (∀ z, z ∉ K → θ z = z) →
      (∀ z ∈ K, θ z ∈ K) →
        IsPiecewiseAffineOn (fun y => if y ∈ U then g (θ (φ y)) else y) univ := by
    intro θ hθ hθfix hθK
    have hθV : ∀ z ∈ V, θ z ∈ V := by
      intro z hz
      by_cases hzK : z ∈ K
      · exact hKV (hθK z hzK)
      · rw [hθfix z hzK]
        exact hz
    have hcomp := hg.isPiecewiseAffineOn.comp (hθ.comp hφ.isPiecewiseAffineOn)
    have hsubU : U ⊆ (U ∩ φ ⁻¹' univ) ∩ (θ ∘ φ) ⁻¹' V := fun y hy =>
      ⟨⟨hy, mem_univ _⟩, hθV _ (hφU y hy)⟩
    have hon : IsPiecewiseAffineOn (fun y => if y ∈ U then g (θ (φ y)) else y) U :=
      (hcomp.mono hU hsubU).congr fun y hy => by simp only [ite_eq_left hy, Function.comp_apply]
    have hoff : IsPiecewiseAffineOn (fun y => if y ∈ U then g (θ (φ y)) else y) (g '' K)ᶜ := by
      refine (isPiecewiseAffineOn_id hKE.isClosed.isOpen_compl).congr fun y hy => ?_
      by_cases hyU : y ∈ U
      · simp only [ite_eq_left hyU, id]
        have hφy : φ y ∉ K := fun h => hy ⟨φ y, h, hgφ y hyU⟩
        rw [hθfix _ hφy, hgφ y hyU]
      · simp only [ite_eq_right hyU, id]
    have hunion := hon.union_of_open hoff
      (fun y hy _ => ⟨U, hU, hy, fun z hz => hz.2⟩)
      (fun y hy _ => ⟨(g '' K)ᶜ, hKE.isClosed.isOpen_compl, hy, fun z hz => hz.2⟩)
    have heq : U ∪ (g '' K)ᶜ = univ := by
      refine eq_univ_of_forall fun y => ?_
      by_cases hy : y ∈ g '' K
      · exact Or.inl (hKEU hy)
      · exact Or.inr hy
    rwa [heq] at hunion
  set ψ' := Function.invFunOn ψ univ with hψ'def
  have hψinv : ∀ z, ψ' (ψ z) = z := fun z => hψ.bijOn.invOn_invFunOn.1 (mem_univ z)
  have hψinv' : ∀ z, ψ (ψ' z) = z := fun z => hψ.bijOn.invOn_invFunOn.2 (mem_univ z)
  have hψ'fix : ∀ z, z ∉ K → ψ' z = z := fun z hz => by
    have h1 := hψinv z
    rwa [hfix z hz] at h1
  have hψinj : Function.Injective ψ := fun a b h => by rw [← hψinv a, h, hψinv b]
  have hψ'inj : Function.Injective ψ' := fun a b h => by rw [← hψinv' a, h, hψinv' b]
  have hψK := hmaps ψ hfix hψinj
  have hψ'K := hmaps ψ' hψ'fix hψ'inj
  have hPLψ := hPL ψ hψ.isPiecewiseAffineOn hfix hψK
  have hPLψ' := hPL ψ' hψ.isPiecewiseAffineOn_invFunOn hψ'fix hψ'K
  set Θ := fun y => if y ∈ U then g (ψ (φ y)) else y with hΘdef
  set Θ' := fun y => if y ∈ U then g (ψ' (φ y)) else y with hΘ'def
  have hmapV : ∀ θ : F → F, (∀ z, z ∉ K → θ z = z) → (∀ z ∈ K, θ z ∈ K) → ∀ z ∈ V, θ z ∈ V := by
    intro θ hθfix hθK z hz
    by_cases hzK : z ∈ K
    · exact hKV (hθK z hzK)
    · rw [hθfix z hzK]
      exact hz
  have hleft : ∀ y, Θ' (Θ y) = y := by
    intro y
    by_cases hyU : y ∈ U
    · have hV1 := hmapV ψ hfix hψK _ (hφU y hyU)
      have hU1 := hgV _ hV1
      simp only [hΘdef, hΘ'def, ite_eq_left hyU, ite_eq_left hU1, hφg _ hV1, hψinv, hgφ y hyU]
    · simp only [hΘdef, hΘ'def, ite_eq_right hyU]
  have hright : ∀ y, Θ (Θ' y) = y := by
    intro y
    by_cases hyU : y ∈ U
    · have hV1 := hmapV ψ' hψ'fix hψ'K _ (hφU y hyU)
      have hU1 := hgV _ hV1
      simp only [hΘdef, hΘ'def, ite_eq_left hyU, ite_eq_left hU1, hφg _ hV1, hψinv', hgφ y hyU]
    · simp only [hΘdef, hΘ'def, ite_eq_right hyU]
  have hbij : BijOn Θ univ univ :=
    ⟨mapsTo_univ _ _, fun a _ b _ h => by rw [← hleft a, h, hleft b],
      fun y _ => ⟨Θ' y, mem_univ _, hright y⟩⟩
  refine ⟨hbij, hPLψ, hPLψ'.congr fun y _ => ?_⟩
  have h1 : Θ (Function.invFunOn Θ univ y) = y := hbij.invOn_invFunOn.2 (mem_univ y)
  have h2 := congrArg Θ' h1
  rw [hleft] at h2
  exact h2

open Classical in
theorem exists_isPLHomeomorphOn_push_of_chart {U : Set E} {V : Set (ℝ × ℝ × ℝ)}
    {φ : E → ℝ × ℝ × ℝ}
    (hU : IsOpen U) (hφ : IsPLHomeomorphOn φ U V) {x : E} (hx : x ∈ U) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (φ x) r ⊆ V) {s : ℝ} (hs : s = 1 ∨ s = -1) {A C X : Set E}
    (hA : ∀ y ∈ U, φ y ∈ Metric.ball (φ x) r → (y ∈ A ↔ (φ y).2.2 = (φ x).2.2))
    (hC : ∀ y ∈ U, φ y ∈ Metric.ball (φ x) r → (y ∈ C ↔ 0 ≤ s * ((φ y).2.2 - (φ x).2.2)))
    (hX : ∀ y ∈ U, ∀ y' ∈ U, φ y ∈ Metric.ball (φ x) r → φ y' ∈ Metric.ball (φ x) r →
      (φ y).1 = (φ y').1 → (φ y).2.1 = (φ y').2.1 → (y ∈ X ↔ y' ∈ X)) :
    ∃ (Ψ : E → E) (W : Set E), IsPLHomeomorphOn Ψ univ univ ∧ W ∈ 𝓝 x ∧
      (∀ y, y ∉ U → Ψ y = y) ∧ (∀ y, Ψ y ∈ X ↔ y ∈ X) ∧
        ∀ y ∈ C, Ψ y ∈ C ∧ (Ψ y ∈ A → y ∈ A ∧ y ∉ W ∧ Ψ y = y) := by
  classical
  obtain ⟨τ, k, hτpl, hτlip, hτ01, hτ1, hτ0⟩ := exists_piecewiseAffine_lipschitz_cutoff_at
    (p := φ x) (Metric.ball_mem_nhds (φ x) (half_pos hr))
  set ε : ℝ := 1 / ((k : ℝ) + 2) with hεdef
  have hkpos : (0 : ℝ) ≤ k := k.2
  have hε : 0 < ε := by positivity
  have hεk : ε * k < 1 := by
    rw [hεdef, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  set w : ℝ × ℝ × ℝ := ((0 : ℝ), (0 : ℝ), s) with hwdef
  have hs2 : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hsabs : |s| = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hwnorm : ‖w‖ = 1 := by
    simp only [hwdef, Prod.norm_def, norm_zero, Real.norm_eq_abs, hsabs]
    norm_num
  set f : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun z => (ε * τ z) • w with hfdef
  have hfpl : IsPiecewiseAffineOn f univ := by
    have h := hτpl.affine_comp (LinearMap.toSpanSingleton ℝ (ℝ × ℝ × ℝ) (ε • w)).toAffineMap
    refine h.congr fun z _ => ?_
    simp only [hfdef, Function.comp_apply, LinearMap.coe_toAffineMap,
      LinearMap.toSpanSingleton_apply, smul_smul, mul_comm]
  have hflip : LipschitzWith (⟨ε, hε.le⟩ * k) f := by
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    rw [dist_eq_norm, hfdef]
    simp only
    have hcoe : ((⟨ε, hε.le⟩ * k : NNReal) : ℝ) = ε * k := rfl
    rw [← sub_smul, norm_smul, hwnorm, mul_one, Real.norm_eq_abs, ← mul_sub, abs_mul,
      abs_of_pos hε, hcoe, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    have := hτlip.dist_le_mul z z'
    rwa [Real.dist_eq] at this
  have hk1 : (⟨ε, hε.le⟩ * k : NNReal) < 1 := by
    have hcoe : ((⟨ε, hε.le⟩ * k : NNReal) : ℝ) = ε * k := rfl
    rw [← NNReal.coe_lt_coe, hcoe, NNReal.coe_one]
    exact hεk
  have hψ := isPLHomeomorphOn_id_add_of_lipschitz hfpl hflip hk1
  set ψ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun z => z + f z with hψdef
  have hψ1 : ∀ z, (ψ z).1 = z.1 := fun z => by simp [hψdef, hfdef, hwdef]
  have hψ21 : ∀ z, (ψ z).2.1 = z.2.1 := fun z => by simp [hψdef, hfdef, hwdef]
  have hψ22 : ∀ z, (ψ z).2.2 = z.2.2 + ε * τ z * s := fun z => by
    simp [hψdef, hfdef, hwdef, mul_assoc]
  set K := Metric.closedBall (φ x) (r / 2) with hKdef
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKV : K ⊆ V := (Metric.closedBall_subset_closedBall (half_le_self hr.le)).trans hball
  have hKball : K ⊆ Metric.ball (φ x) r := Metric.closedBall_subset_ball (half_lt_self hr)
  have hψfix : ∀ z, z ∉ K → ψ z = z := by
    intro z hz
    have h0 : τ z = 0 := hτ0 fun h => hz (Metric.ball_subset_closedBall h)
    simp [hψdef, hfdef, h0]
  have hΨ := isPLHomeomorphOn_univ_chartConj hU hφ hψ hKc hKV hψfix
  set g := Function.invFunOn φ U with hgdef
  set Ψ := fun y => if y ∈ U then g (ψ (φ y)) else y with hΨdef
  have hgφ : ∀ y ∈ U, g (φ y) = y := fun y hy => hφ.bijOn.invOn_invFunOn.1 hy
  have hφg : ∀ z ∈ V, φ (g z) = z := fun z hz => hφ.bijOn.invOn_invFunOn.2 hz
  have hgV : ∀ z ∈ V, g z ∈ U := fun z hz => hφ.symm.bijOn.mapsTo hz
  have hψinj : Function.Injective ψ := Set.injOn_univ.mp hψ.bijOn.injOn
  have hψK : ∀ z ∈ K, ψ z ∈ K := by
    intro z hz
    by_contra h
    have h1 := hψfix _ h
    exact h (by rw [hψinj h1]; exact hz)
  have hΨoff : ∀ y, (y ∉ U ∨ φ y ∉ K) → Ψ y = y := by
    rintro y (hy | hy)
    · simp only [hΨdef, ite_eq_right hy]
    · by_cases hyU : y ∈ U
      · simp only [hΨdef, ite_eq_left hyU, hψfix _ hy, hgφ y hyU]
      · simp only [hΨdef, ite_eq_right hyU]
  have hΨon : ∀ y ∈ U, φ y ∈ K → Ψ y ∈ U ∧ φ (Ψ y) = ψ (φ y) := by
    intro y hyU hyK
    have hV1 := hKV (hψK _ hyK)
    simp only [hΨdef, ite_eq_left hyU]
    exact ⟨hgV _ hV1, hφg _ hV1⟩
  set W := U ∩ φ ⁻¹' (τ ⁻¹' {1}) with hWdef
  have hW : W ∈ 𝓝 x := by
    have hcont : ContinuousAt φ x :=
      hφ.isPiecewiseAffineOn.continuousAt hU hx
    exact Filter.inter_mem (hU.mem_nhds hx) (hcont.preimage_mem_nhds hτ1)
  have hWK : ∀ y ∈ W, φ y ∈ K := by
    intro y hy
    by_contra h
    have h0 : τ (φ y) = 0 := hτ0 fun h' => h (Metric.ball_subset_closedBall h')
    have h1 : τ (φ y) = 1 := hy.2
    rw [h0] at h1
    exact zero_ne_one h1
  refine ⟨Ψ, W, hΨ, hW, fun y hy => hΨoff y (Or.inl hy), fun y => ?_, fun y hyC => ?_⟩
  · by_cases hyU : y ∈ U
    · by_cases hyK : φ y ∈ K
      · obtain ⟨h1, h2⟩ := hΨon y hyU hyK
        refine hX _ h1 y hyU ?_ (hKball hyK) ?_ ?_
        · rw [h2]
          exact hKball (hψK _ hyK)
        · rw [h2, hψ1]
        · rw [h2, hψ21]
      · rw [hΨoff y (Or.inr hyK)]
    · rw [hΨoff y (Or.inl hyU)]
  · by_cases hmove : y ∈ U ∧ φ y ∈ K
    · obtain ⟨hyU, hyK⟩ := hmove
      obtain ⟨h1, h2⟩ := hΨon y hyU hyK
      have hyball := hKball hyK
      have hΨball : φ (Ψ y) ∈ Metric.ball (φ x) r := by
        rw [h2]
        exact hKball (hψK _ hyK)
      have hc := (hC y hyU hyball).mp hyC
      have hτnn : 0 ≤ τ (φ y) := (hτ01 _).1
      have hkey : s * ((φ (Ψ y)).2.2 - (φ x).2.2) =
          s * ((φ y).2.2 - (φ x).2.2) + ε * τ (φ y) := by
        rw [h2, hψ22]
        linear_combination ε * τ (φ y) * hs2
      refine ⟨(hC _ h1 hΨball).mpr (by rw [hkey]; exact add_nonneg hc (mul_nonneg hε.le hτnn)),
        fun hA' => ?_⟩
      have hzero := (hA _ h1 hΨball).mp hA'
      have hsum : s * ((φ (Ψ y)).2.2 - (φ x).2.2) = 0 := by rw [hzero, sub_self, mul_zero]
      rw [hkey] at hsum
      have hετ : ε * τ (φ y) = 0 := by nlinarith [mul_nonneg hε.le hτnn]
      have hτ0' : τ (φ y) = 0 := by
        rcases mul_eq_zero.mp hετ with h | h
        · exact absurd h hε.ne'
        · exact h
      have hc0 : s * ((φ y).2.2 - (φ x).2.2) = 0 := by linarith
      have hyA : (φ y).2.2 = (φ x).2.2 := by
        have hs0 : s ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
        have := (mul_eq_zero.mp hc0).resolve_left hs0
        linarith
      have hfixy : Ψ y = y := by
        simp only [hΨdef, ite_eq_left hyU]
        have hψy : ψ (φ y) = φ y := by simp [hψdef, hfdef, hτ0']
        rw [hψy, hgφ y hyU]
      refine ⟨(hA y hyU hyball).mpr hyA, fun hyW => ?_, hfixy⟩
      have h1' : τ (φ y) = 1 := hyW.2
      rw [hτ0'] at h1'
      exact zero_ne_one h1'
    · have hfixy : Ψ y = y := by
        by_cases hyU : y ∈ U
        · exact hΨoff y (Or.inr fun h => hmove ⟨hyU, h⟩)
        · exact hΨoff y (Or.inl hyU)
      rw [hfixy]
      refine ⟨hyC, fun hyA => ⟨hyA, fun hyW => hmove ⟨hyW.1, hWK y hyW⟩, rfl⟩⟩

theorem exists_isPLHomeomorphOn_push_of_forall {Z A C X O : Set E} (hZ : IsCompact Z)
    (hloc : ∀ x ∈ Z, ∃ (Ψ : E → E) (W : Set E), IsPLHomeomorphOn Ψ univ univ ∧ W ∈ 𝓝 x ∧
      (∀ y, y ∉ O → Ψ y = y) ∧ (∀ y, Ψ y ∈ X ↔ y ∈ X) ∧
        ∀ y ∈ C, Ψ y ∈ C ∧ (Ψ y ∈ A → y ∈ A ∧ y ∉ W ∧ Ψ y = y)) :
    ∃ Φ : E → E, IsPLHomeomorphOn Φ univ univ ∧ (∀ y, y ∉ O → Φ y = y) ∧
      (∀ y, Φ y ∈ X ↔ y ∈ X) ∧ ∀ y ∈ C, Φ y ∈ C ∧ (Φ y ∈ A → y ∉ Z ∧ Φ y = y) := by
  classical
  choose! Ψ W hΨ hW hΨO hΨX hΨC using hloc
  obtain ⟨t, htZ, hcover⟩ := hZ.elim_nhds_subcover W hW
  have hind : ∀ s : Finset E, s ⊆ t → ∃ Φ : E → E, IsPLHomeomorphOn Φ univ univ ∧
      (∀ y, y ∉ O → Φ y = y) ∧ (∀ y, Φ y ∈ X ↔ y ∈ X) ∧
        ∀ y ∈ C, Φ y ∈ C ∧ (Φ y ∈ A → (∀ a ∈ s, y ∉ W a) ∧ Φ y = y) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨id, ?_, fun y _ => rfl, fun y => Iff.rfl, fun y hy => ⟨hy, fun _ => ⟨?_, rfl⟩⟩⟩
      · refine ⟨bijOn_id univ, isPiecewiseAffineOn_id isOpen_univ,
          (isPiecewiseAffineOn_id isOpen_univ).congr fun z _ => ?_⟩
        simpa using (bijOn_id univ).invOn_invFunOn.2 (mem_univ z)
      · intro a ha
        exact absurd ha (Finset.notMem_empty a)
    | insert a s has ih =>
      intro hst
      obtain ⟨Φ, hΦ, hΦO, hΦX, hΦC⟩ := ih ((Finset.subset_insert a s).trans hst)
      have haZ : a ∈ Z := htZ a (hst (Finset.mem_insert_self a s))
      refine ⟨Ψ a ∘ Φ, hΦ.trans (hΨ a haZ), fun y hy => ?_, fun y => ?_, fun y hy => ?_⟩
      · simp only [Function.comp_apply, hΦO y hy, hΨO a haZ y hy]
      · simp only [Function.comp_apply, hΨX a haZ, hΦX]
      · obtain ⟨h1, h2⟩ := hΦC y hy
        obtain ⟨h3, h4⟩ := hΨC a haZ (Φ y) h1
        refine ⟨h3, fun hA' => ?_⟩
        obtain ⟨hΦA, hΦW, hΨfix⟩ := h4 hA'
        obtain ⟨hs', hΦfix⟩ := h2 hΦA
        refine ⟨fun b hb => ?_, ?_⟩
        · rcases Finset.mem_insert.mp hb with rfl | hb'
          · rw [← hΦfix]
            exact hΦW
          · exact hs' b hb'
        · rw [Function.comp_apply, hΨfix, hΦfix]
  obtain ⟨Φ, hΦ, hΦO, hΦX, hΦC⟩ := hind t subset_rfl
  refine ⟨Φ, hΦ, hΦO, hΦX, fun y hy => ⟨(hΦC y hy).1, fun hA' => ⟨fun hyZ => ?_,
    ((hΦC y hy).2 hA').2⟩⟩⟩
  obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp (hcover hyZ)
  exact ((hΦC y hy).2 hA').1 a ha hya

end DifferentialGeometry.Topology.PiecewiseLinear
