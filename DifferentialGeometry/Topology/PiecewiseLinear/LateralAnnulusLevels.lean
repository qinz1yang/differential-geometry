/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismLateralCircleSides

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLHomeomorphOn_mul_add_Icc {m c a b a' b' : ℝ} (hm : 0 < m) (ha' : m * a + c = a')
    (hb' : m * b + c = b') :
    IsPLHomeomorphOn (fun t : ℝ => m * t + c) (Icc a b) (Icc a' b') := by
  subst ha' hb'
  have hm0 : m ≠ 0 := hm.ne'
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (m • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ c) isHPolytope_Icc) ⟨?_, ?_, ?_⟩
  · intro t ht
    change m * t + c ∈ Icc (m * a + c) (m * b + c)
    have h1 := mul_le_mul_of_nonneg_left ht.1 hm.le
    have h2 := mul_le_mul_of_nonneg_left ht.2 hm.le
    exact ⟨by linarith, by linarith⟩
  · intro s _ t _ hst
    change m * s + c = m * t + c at hst
    exact mul_left_cancel₀ hm0 (by linarith)
  · intro y hy
    have hy1 : m * a + c ≤ y := hy.1
    have hy2 : y ≤ m * b + c := hy.2
    have hdiv : m * ((y - c) / m) = y - c := by field_simp
    refine ⟨(y - c) / m, ⟨(le_div_iff₀ hm).mpr (by linarith), (div_le_iff₀ hm).mpr
      (by linarith)⟩, ?_⟩
    change m * ((y - c) / m) + c = y
    rw [hdiv]
    ring

theorem eqOn_piecewise_of_eqOn_inter {α β : Type*} {P Q : Set α} [∀ x, Decidable (x ∈ P)]
    {f g : α → β} (hfg : EqOn f g (P ∩ Q)) : EqOn (P.piecewise f g) g Q := by
  intro x hx
  by_cases hxP : x ∈ P
  · rw [piecewise_eq_of_mem P f g hxP]
    exact hfg ⟨hxP, hx⟩
  · exact piecewise_eq_of_notMem P f g hxP

theorem exists_Ioo_subset_of_isPreconnected_of_finite {T S₀ : Set ℝ} (hT : IsPreconnected T)
    (hTne : T.Nonempty) (hT01 : T ⊆ Ioo 0 1) (hS₀ : S₀.Finite) (hTS : Disjoint T S₀) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ T ⊆ Ioo a b ∧ ∀ s ∈ S₀, s ≤ a ∨ b ≤ s := by
  obtain ⟨t₀, ht₀⟩ := hTne
  have hLofin : (insert (0 : ℝ) {s ∈ S₀ | s < t₀}).Finite :=
    (hS₀.subset (sep_subset _ _)).insert 0
  have hHifin : (insert (1 : ℝ) {s ∈ S₀ | t₀ < s}).Finite :=
    (hS₀.subset (sep_subset _ _)).insert 1
  have ha := (insert_nonempty (0 : ℝ) {s ∈ S₀ | s < t₀}).csSup_mem hLofin
  have hb := (insert_nonempty (1 : ℝ) {s ∈ S₀ | t₀ < s}).csInf_mem hHifin
  have hLoa : ∀ s ∈ insert (0 : ℝ) {s ∈ S₀ | s < t₀},
      s ≤ sSup (insert (0 : ℝ) {s ∈ S₀ | s < t₀}) := fun s hs => le_csSup hLofin.bddAbove hs
  have hHib : ∀ s ∈ insert (1 : ℝ) {s ∈ S₀ | t₀ < s},
      sInf (insert (1 : ℝ) {s ∈ S₀ | t₀ < s}) ≤ s := fun s hs => csInf_le hHifin.bddBelow hs
  have hat : sSup (insert (0 : ℝ) {s ∈ S₀ | s < t₀}) < t₀ := by
    rcases ha with h | h
    · rw [h]
      exact (hT01 ht₀).1
    · exact h.2
  have htb : t₀ < sInf (insert (1 : ℝ) {s ∈ S₀ | t₀ < s}) := by
    rcases hb with h | h
    · rw [h]
      exact (hT01 ht₀).2
    · exact h.2
  have hnotT : ∀ x, x ∈ insert (0 : ℝ) {s ∈ S₀ | s < t₀} ∨
      x ∈ insert (1 : ℝ) {s ∈ S₀ | t₀ < s} → x ∉ T := by
    rintro x (hx | hx) hxT
    · rcases hx with rfl | hx
      · exact lt_irrefl _ (hT01 hxT).1
      · exact disjoint_left.mp hTS hxT hx.1
    · rcases hx with rfl | hx
      · exact lt_irrefl _ (hT01 hxT).2
      · exact disjoint_left.mp hTS hxT hx.1
  refine ⟨_, _, hLoa 0 (mem_insert _ _), hat.trans htb, hHib 1 (mem_insert _ _), ?_, ?_⟩
  · intro t ht
    constructor
    · by_contra h
      push Not at h
      exact hnotT _ (Or.inl ha) (hT.Icc_subset ht ht₀ ⟨h, hat.le⟩)
    · by_contra h
      push Not at h
      exact hnotT _ (Or.inr hb) (hT.Icc_subset ht₀ ht ⟨htb.le, h⟩)
  · intro s hs
    rcases lt_trichotomy s t₀ with h | h | h
    · exact Or.inl (hLoa s (mem_insert_of_mem _ ⟨hs, h⟩))
    · exact (disjoint_left.mp hTS ht₀ (h ▸ hs)).elim
    · exact Or.inr (hHib s (mem_insert_of_mem _ ⟨hs, h⟩))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_eqOn_eqOn_union {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f g : E → F} {P Q : Set E} {R S : Set F}
    (hf : IsPLHomeomorphOn f P R) (hg : IsPLHomeomorphOn g Q S) (hP : IsPolyhedron P)
    (hQ : IsPolyhedron Q) (hfg : EqOn f g (P ∩ Q)) (hmeet : f '' (P ∩ Q) = R ∩ S) :
    ∃ h : E → F, IsPLHomeomorphOn h (P ∪ Q) (R ∪ S) ∧ EqOn h f P ∧ EqOn h g Q := by
  classical
  exact ⟨_, hf.piecewise hg hP hQ hfg hmeet, P.piecewise_eqOn f g,
    eqOn_piecewise_of_eqOn_inter hfg⟩

theorem IsPolyhedron.exists_isPLHomeomorphOn_prod_Icc_of_slab {P : Set E} (hP : IsPolyhedron P)
    {Ψ : E × ℝ → E × ℝ} (hΨ : IsPLHomeomorphOn Ψ (P ×ˢ Icc 0 1) (P ×ˢ Icc 0 1))
    (hΨ0 : ∀ x ∈ P, Ψ (x, 0) = (x, 0)) {μ : E → E} (hμ : IsPLHomeomorphOn μ P P)
    (hΨ1 : ∀ x ∈ P, Ψ (x, 1) = (μ x, 1)) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ Θ : E × ℝ → E × ℝ, IsPLHomeomorphOn Θ (P ×ˢ Icc 0 1) (P ×ˢ Icc 0 1) ∧
      (∀ z ∈ P ×ˢ Icc 0 a, Θ z = z) ∧ (∀ z ∈ P ×ˢ Icc b 1, Θ z = (μ z.1, z.2)) ∧
      ∀ z ∈ P ×ˢ Icc (0 : ℝ) 1,
        Θ (z.1, (b - a) * z.2 + a) = ((Ψ z).1, (b - a) * (Ψ z).2 + a) := by
  have hpoly : ∀ c d : ℝ, IsPolyhedron (P ×ˢ Icc c d) :=
    fun c d => hP.prod isHPolytope_Icc.isPolyhedron
  have hσ : IsPLHomeomorphOn (Prod.map id fun t : ℝ => (b - a) * t + a) (P ×ˢ Icc 0 1)
      (P ×ˢ Icc a b) :=
    hP.isPLHomeomorphOn_id.prodMap (isPLHomeomorphOn_mul_add_Icc (sub_pos.mpr hab)
      (by ring) (by ring))
  set σ : E × ℝ → E × ℝ := Prod.map id fun t : ℝ => (b - a) * t + a with hσdef
  have hσi : ∀ z ∈ P ×ˢ Icc (0 : ℝ) 1, Function.invFunOn σ (P ×ˢ Icc (0 : ℝ) 1) (σ z) = z :=
    fun z hz => hσ.bijOn.invOn_invFunOn.1 hz
  have hM : IsPLHomeomorphOn (σ ∘ Ψ ∘ Function.invFunOn σ (P ×ˢ Icc (0 : ℝ) 1))
      (P ×ˢ Icc a b) (P ×ˢ Icc a b) := (hσ.symm.trans hΨ).trans hσ
  set M := σ ∘ Ψ ∘ Function.invFunOn σ (P ×ˢ Icc (0 : ℝ) 1) with hMdef
  have hMσ : ∀ z ∈ P ×ˢ Icc (0 : ℝ) 1, M (σ z) = σ (Ψ z) := by
    intro z hz
    change σ (Ψ (Function.invFunOn σ (P ×ˢ Icc (0 : ℝ) 1) (σ z))) = σ (Ψ z)
    rw [hσi z hz]
  have hMa : ∀ x ∈ P, M (x, a) = (x, a) := by
    intro x hx
    have h := hMσ (x, 0) ⟨hx, le_rfl, zero_le_one⟩
    have e0 : σ (x, 0) = (x, a) := Prod.ext rfl (show (b - a) * 0 + a = a by ring)
    rw [e0, hΨ0 x hx, e0] at h
    exact h
  have hMb : ∀ x ∈ P, M (x, b) = (μ x, b) := by
    intro x hx
    have h := hMσ (x, 1) ⟨hx, zero_le_one, le_rfl⟩
    have e1 : σ (x, 1) = (x, b) := Prod.ext rfl (show (b - a) * 1 + a = b by ring)
    have e1' : σ (μ x, 1) = (μ x, b) := Prod.ext rfl (show (b - a) * 1 + a = b by ring)
    rw [e1, hΨ1 x hx, e1'] at h
    exact h
  have hT : IsPLHomeomorphOn (Prod.map μ (id : ℝ → ℝ)) (P ×ˢ Icc b 1) (P ×ˢ Icc b 1) :=
    hμ.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  have hmeet₁ : P ×ˢ Icc 0 a ∩ P ×ˢ Icc a b = P ×ˢ {a} := by
    ext z
    constructor
    · rintro ⟨⟨hz, -, hza⟩, -, haz, -⟩
      exact ⟨hz, le_antisymm hza haz⟩
    · rintro ⟨hz, hza⟩
      have hza' : z.2 = a := hza
      exact ⟨⟨hz, hza' ▸ ha, hza'.le⟩, hz, hza'.ge, hza' ▸ hab.le⟩
  obtain ⟨Θ₁, hΘ₁, hΘ₁id, hΘ₁M⟩ := (hpoly 0 a).isPLHomeomorphOn_id.exists_eqOn_eqOn_union hM
    (hpoly 0 a) (hpoly a b) (fun z hz => by
      rw [hmeet₁] at hz
      have hz2 : z.2 = a := hz.2
      rw [show z = (z.1, a) from Prod.ext rfl hz2, hMa z.1 hz.1]
      rfl) (by rw [image_id])
  have hmeet₂ : (P ×ˢ Icc 0 a ∪ P ×ˢ Icc a b) ∩ P ×ˢ Icc b 1 = P ×ˢ {b} := by
    ext z
    constructor
    · rintro ⟨hzu, hz, hbz, -⟩
      rcases hzu with ⟨-, -, hza⟩ | ⟨-, -, hzb⟩
      · exact absurd (hza.trans_lt hab) (not_lt.mpr hbz)
      · exact ⟨hz, le_antisymm hzb hbz⟩
    · rintro ⟨hz, hzb⟩
      have hzb' : z.2 = b := hzb
      exact ⟨Or.inr ⟨hz, hzb' ▸ hab.le, hzb'.le⟩, hz, hzb'.ge, hzb' ▸ hb⟩
  have hΘ₁b : ∀ x ∈ P, Θ₁ (x, b) = (μ x, b) := by
    intro x hx
    rw [hΘ₁M ⟨hx, hab.le, le_rfl⟩, hMb x hx]
  obtain ⟨Θ, hΘ, hΘΘ₁, hΘT⟩ := hΘ₁.exists_eqOn_eqOn_union hT ((hpoly 0 a).union (hpoly a b))
    (hpoly b 1) (fun z hz => by
      rw [hmeet₂] at hz
      have hz2 : z.2 = b := hz.2
      rw [show z = (z.1, b) from Prod.ext rfl hz2, hΘ₁b z.1 hz.1]
      rfl) (by
      rw [hmeet₂]
      exact image_prod_singleton_of_map_level hμ hΘ₁b)
  have hcover : (P ×ˢ Icc 0 a ∪ P ×ˢ Icc a b) ∪ P ×ˢ Icc b 1 = P ×ˢ Icc 0 1 := by
    ext z
    constructor
    · rintro ((⟨hz, h0, h1⟩ | ⟨hz, h0, h1⟩) | ⟨hz, h0, h1⟩)
      · exact ⟨hz, h0, by linarith⟩
      · exact ⟨hz, by linarith, by linarith⟩
      · exact ⟨hz, by linarith, h1⟩
    · rintro ⟨hz, h0, h1⟩
      by_cases hza : z.2 ≤ a
      · exact Or.inl (Or.inl ⟨hz, h0, hza⟩)
      · by_cases hzb : z.2 ≤ b
        · exact Or.inl (Or.inr ⟨hz, by linarith, hzb⟩)
        · exact Or.inr ⟨hz, by linarith, h1⟩
  refine ⟨Θ, hcover ▸ hΘ, fun z hz => ?_, fun z hz => hΘT hz, fun z hz => ?_⟩
  · rw [hΘΘ₁ (Or.inl hz), hΘ₁id hz]
    rfl
  · have hσz : σ z ∈ P ×ˢ Icc a b := hσ.bijOn.mapsTo hz
    change Θ (σ z) = σ (Ψ z)
    rw [hΘΘ₁ (Or.inr hσz), hΘ₁M hσz, hMσ z hz]

theorem IsPLSphere.exists_isPLHomeomorphOn_prism_lateral_level
    {K : Set ((Fin 3 → ℝ) × ℝ)} (hK : IsPLSphere 1 K)
    (hKA : K ⊆ stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
    (hess : ¬ ∃ (D : Set ((Fin 3 → ℝ) × ℝ)) (r : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧ r '' stdSimplexBoundary 2 = K) :
    ∃ (Ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ) (ν : (Fin 3 → ℝ) → (Fin 3 → ℝ)),
      IsPLHomeomorphOn Ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      IsPLHomeomorphOn ν (stdSimplexBoundary 2) (stdSimplexBoundary 2) ∧
      (∀ x ∈ stdSimplexBoundary 2, Ψ (x, 0) = (x, 0)) ∧
      (∀ x ∈ stdSimplexBoundary 2, Ψ (x, 1) = (ν x, 1)) ∧
      Ψ '' (stdSimplexBoundary 2 ×ˢ {1 / 2}) = K := by
  classical
  obtain ⟨ψ₀, ψ₁, hψ₀, hψ₁, hUn, hIn, hψ₀0, hψ₁1, hψ₀1, hψ₁0⟩ :=
    hK.exists_lateral_sides_of_subset_prism_lateral hKA hess
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  have hsub1 : stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ) ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num⟩
  have hsub0 : stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ) ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num⟩
  have h1 : IsPLHomeomorphOn ψ₀ (stdSimplexBoundary 2 ×ˢ {1}) K := by
    have h := hψ₀.restrict (isPolyhedron_prod_singleton hBpoly 1) hsub1
    rwa [hψ₀1] at h
  have h0 : IsPLHomeomorphOn ψ₁ (stdSimplexBoundary 2 ×ˢ {0}) K := by
    have h := hψ₁.restrict (isPolyhedron_prod_singleton hBpoly 0) hsub0
    rwa [hψ₁0] at h
  have hν : IsPLHomeomorphOn (Prod.fst ∘ Function.invFunOn ψ₁ (stdSimplexBoundary 2 ×ˢ {0}) ∘
      ψ₀ ∘ fun x => (x, (1 : ℝ))) (stdSimplexBoundary 2) (stdSimplexBoundary 2) :=
    (((hBpoly.isPLHomeomorphOn_prod_const 1).trans h1).trans h0.symm).trans
      (hBpoly.isPLHomeomorphOn_fst_prod_const 0)
  set ν := Prod.fst ∘ Function.invFunOn ψ₁ (stdSimplexBoundary 2 ×ˢ {0}) ∘
      ψ₀ ∘ fun x => (x, (1 : ℝ)) with hνdef
  have hνspec : ∀ x ∈ stdSimplexBoundary 2, ψ₁ (ν x, 0) = ψ₀ (x, 1) := by
    intro x hx
    have hk : ψ₀ (x, 1) ∈ K := h1.bijOn.mapsTo ⟨hx, rfl⟩
    have hw : Function.invFunOn ψ₁ (stdSimplexBoundary 2 ×ˢ {0}) (ψ₀ (x, 1)) ∈
        stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ) := h0.symm.bijOn.mapsTo hk
    have hw2 : (Function.invFunOn ψ₁ (stdSimplexBoundary 2 ×ˢ {0}) (ψ₀ (x, 1))).2 = 0 := hw.2
    calc ψ₁ (ν x, 0)
        = ψ₁ (Function.invFunOn ψ₁ (stdSimplexBoundary 2 ×ˢ {0}) (ψ₀ (x, 1))) :=
          congrArg ψ₁ (Prod.ext rfl hw2.symm)
      _ = ψ₀ (x, 1) := h0.bijOn.invOn_invFunOn.2 hk
  have hlow : IsPLHomeomorphOn (Prod.map id fun t : ℝ => 2 * t + 0)
      (stdSimplexBoundary 2 ×ˢ Icc 0 (1 / 2)) (stdSimplexBoundary 2 ×ˢ Icc 0 1) :=
    hBpoly.isPLHomeomorphOn_id.prodMap (isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num)
      (by norm_num))
  have hup : IsPLHomeomorphOn (Prod.map ν fun t : ℝ => 2 * t + -1)
      (stdSimplexBoundary 2 ×ˢ Icc (1 / 2) 1) (stdSimplexBoundary 2 ×ˢ Icc 0 1) :=
    hν.prodMap (isPLHomeomorphOn_mul_add_Icc two_pos (by norm_num) (by norm_num))
  have hL := hlow.trans hψ₀
  have hU := hup.trans hψ₁
  set L := ψ₀ ∘ Prod.map id fun t : ℝ => 2 * t + 0 with hLdef
  set U := ψ₁ ∘ Prod.map ν fun t : ℝ => 2 * t + -1 with hUdef
  have hLv : ∀ x, L (x, 1 / 2) = ψ₀ (x, 1) := fun x => congrArg ψ₀ (Prod.ext rfl (by norm_num))
  have hmid : stdSimplexBoundary 2 ×ˢ Icc 0 (1 / 2) ∩ stdSimplexBoundary 2 ×ˢ Icc (1 / 2) 1 =
      stdSimplexBoundary 2 ×ˢ ({1 / 2} : Set ℝ) := by
    ext z
    simp only [mem_inter_iff, mem_prod, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hz, -, h1⟩, -, h2, -⟩
      exact ⟨hz, le_antisymm h1 h2⟩
    · rintro ⟨hz, hz2⟩
      exact ⟨⟨hz, by rw [hz2]; norm_num, hz2.le⟩, hz, hz2.ge, by rw [hz2]; norm_num⟩
  have hLmid : L '' (stdSimplexBoundary 2 ×ˢ ({1 / 2} : Set ℝ)) = K := by
    rw [← hψ₀1]
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hz2 : z.2 = 1 / 2 := hz.2
      rw [show z = (z.1, 1 / 2) from Prod.ext rfl hz2, hLv]
      exact ⟨(z.1, 1), ⟨hz.1, rfl⟩, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hz2 : z.2 = 1 := hz.2
      refine ⟨(z.1, 1 / 2), ⟨hz.1, rfl⟩, ?_⟩
      rw [hLv, show z = (z.1, 1) from Prod.ext rfl hz2]
  have hpoly : ∀ c d : ℝ, IsPolyhedron (stdSimplexBoundary 2 ×ˢ Icc c d) :=
    fun c d => hBpoly.prod isHPolytope_Icc.isPolyhedron
  obtain ⟨Ψ, hΨ, hΨL, hΨU⟩ := hL.exists_eqOn_eqOn_union hU (hpoly 0 (1 / 2)) (hpoly (1 / 2) 1)
    (fun z hz => by
      rw [hmid] at hz
      have hz2 : z.2 = 1 / 2 := hz.2
      rw [show z = (z.1, 1 / 2) from Prod.ext rfl hz2, hLv]
      change ψ₀ (z.1, 1) = ψ₁ (ν z.1, 2 * (1 / 2) + -1)
      rw [show (2 : ℝ) * (1 / 2) + -1 = 0 by norm_num, hνspec z.1 hz.1])
    (by rw [hmid, hLmid, hIn])
  have hdom : stdSimplexBoundary 2 ×ˢ Icc 0 (1 / 2) ∪ stdSimplexBoundary 2 ×ˢ Icc (1 / 2) 1 =
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro (⟨hz, h0, h1⟩ | ⟨hz, h0, h1⟩)
      · exact ⟨hz, h0, by linarith⟩
      · exact ⟨hz, by linarith, h1⟩
    · rintro ⟨hz, h0, h1⟩
      by_cases hm : z.2 ≤ 1 / 2
      · exact Or.inl ⟨hz, h0, hm⟩
      · exact Or.inr ⟨hz, by linarith, h1⟩
  rw [hdom, hUn] at hΨ
  refine ⟨Ψ, ν, hΨ, hν, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [hΨL ⟨hx, le_rfl, by norm_num⟩]
    change ψ₀ (x, 2 * 0 + 0) = (x, 0)
    rw [show (2 : ℝ) * 0 + 0 = 0 by norm_num, hψ₀0 x hx]
  · rw [hΨU ⟨hx, by norm_num, le_rfl⟩]
    change ψ₁ (ν x, 2 * 1 + -1) = (ν x, 1)
    rw [show (2 : ℝ) * 1 + -1 = 1 by norm_num, hψ₁1 (ν x) (hν.bijOn.mapsTo hx)]
  · rw [← hLmid]
    refine image_congr fun z hz => hΨL ?_
    have hz2 : z.2 = 1 / 2 := hz.2
    exact ⟨hz.1, by rw [hz2]; norm_num, hz2.le⟩

theorem exists_isPLHomeomorphOn_prism_lateral_levels_insert
    {C : Set (Set ((Fin 3 → ℝ) × ℝ))} (hC : C.Finite) {K : Set ((Fin 3 → ℝ) × ℝ)}
    (hK : IsPLSphere 1 K) (hKA : K ⊆ stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
    (hKess : ¬ ∃ (D : Set ((Fin 3 → ℝ) × ℝ)) (r : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧ r '' stdSimplexBoundary 2 = K)
    (hKC : ∀ L ∈ C, Disjoint K L) {Φ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ}
    {s : Set ((Fin 3 → ℝ) × ℝ) → ℝ}
    (hΦ : IsPLHomeomorphOn Φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
      (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hΦ0 : Φ '' (stdSimplexBoundary 2 ×ˢ {0}) = stdSimplexBoundary 2 ×ˢ {0})
    (hΦ1 : Φ '' (stdSimplexBoundary 2 ×ˢ {1}) = stdSimplexBoundary 2 ×ˢ {1})
    (hΦC : ∀ L ∈ C, s L ∈ Ioo (0 : ℝ) 1 ∧ Φ '' (stdSimplexBoundary 2 ×ˢ {s L}) = L) :
    ∃ (Φ' : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ) (s' : Set ((Fin 3 → ℝ) × ℝ) → ℝ),
      IsPLHomeomorphOn Φ' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      Φ' '' (stdSimplexBoundary 2 ×ˢ {0}) = stdSimplexBoundary 2 ×ˢ {0} ∧
      Φ' '' (stdSimplexBoundary 2 ×ˢ {1}) = stdSimplexBoundary 2 ×ˢ {1} ∧
      ∀ L ∈ insert K C, s' L ∈ Ioo (0 : ℝ) 1 ∧ Φ' '' (stdSimplexBoundary 2 ×ˢ {s' L}) = L := by
  classical
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  have hKA' : K ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    fun y hy => ⟨(hKA hy).1, Ioo_subset_Icc_self (hKA hy).2⟩
  have hΦi : IsPLHomeomorphOn (Function.invFunOn Φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
      (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := hΦ.symm
  have hK' : IsPLSphere 1 (Function.invFunOn Φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K) :=
    hK.of_isPLHomeomorphOn (hΦi.restrict hK.isPolyhedron hKA')
  have hΦK' : Φ '' (Function.invFunOn Φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K) = K :=
    LeftInvOn.image_image (hΦ.bijOn.invOn_invFunOn.2.mono hKA')
  have hK'Ioo : Function.invFunOn Φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K ⊆
      stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1 := by
    rintro _ ⟨k, hk, rfl⟩
    have hyA := hΦi.bijOn.mapsTo (hKA' hk)
    have hΦy := hΦ.bijOn.invOn_invFunOn.2 (hKA' hk)
    refine ⟨hyA.1, lt_of_le_of_ne hyA.2.1 fun h0 => ?_, lt_of_le_of_ne hyA.2.2 fun h1 => ?_⟩
    · have hm : k ∈ Φ '' (stdSimplexBoundary 2 ×ˢ {0}) := ⟨_, ⟨hyA.1, h0.symm⟩, hΦy⟩
      rw [hΦ0] at hm
      have h := (hKA hk).2.1
      rw [mem_singleton_iff.mp hm.2] at h
      exact lt_irrefl _ h
    · have hm : k ∈ Φ '' (stdSimplexBoundary 2 ×ˢ {1}) := ⟨_, ⟨hyA.1, h1⟩, hΦy⟩
      rw [hΦ1] at hm
      have h := (hKA hk).2.2
      rw [mem_singleton_iff.mp hm.2] at h
      exact lt_irrefl _ h
  have hK'lev : ∀ L ∈ C, ∀ y ∈ Function.invFunOn Φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K,
      y.2 ≠ s L := by
    rintro L hL _ ⟨k, hk, rfl⟩ hyL
    have hyA := hΦi.bijOn.mapsTo (hKA' hk)
    have hmem : k ∈ Φ '' (stdSimplexBoundary 2 ×ˢ {s L}) :=
      ⟨_, ⟨hyA.1, hyL⟩, hΦ.bijOn.invOn_invFunOn.2 (hKA' hk)⟩
    rw [(hΦC L hL).2] at hmem
    exact disjoint_left.mp (hKC L hL) hk hmem
  have hK'ess : ¬ ∃ (D : Set ((Fin 3 → ℝ) × ℝ)) (r : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧
      r '' stdSimplexBoundary 2 =
        Function.invFunOn Φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K := by
    rintro ⟨D, r, hr, hDA, hrb⟩
    exact hKess ⟨Φ '' D, Φ ∘ r, hr.trans (hΦ.restrict (IsPLBall.isPolyhedron ⟨r, hr⟩) hDA),
      image_subset_iff.mpr fun d hd => hΦ.bijOn.mapsTo (hDA hd), by rw [image_comp, hrb, hΦK']⟩
  generalize Function.invFunOn Φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K = K' at *
  obtain ⟨a, b, ha, hab, hb, hTab, hlev⟩ := exists_Ioo_subset_of_isPreconnected_of_finite
    (hK'.isConnected.isPreconnected.image _ continuous_snd.continuousOn) (hK'.nonempty.image _)
    (by rintro _ ⟨y, hy, rfl⟩; exact (hK'Ioo hy).2) (hC.image s)
    (disjoint_left.mpr (by
      rintro _ ⟨y, hy, rfl⟩ ⟨L, hL, hLy⟩
      exact hK'lev L hL y hy hLy.symm))
  have hK'Icc : K' ⊆ stdSimplexBoundary 2 ×ˢ Icc a b :=
    fun y hy => ⟨(hK'Ioo hy).1, Ioo_subset_Icc_self (hTab ⟨y, hy, rfl⟩)⟩
  have hba : 0 < b - a := sub_pos.mpr hab
  have hσ : IsPLHomeomorphOn (Prod.map id fun t : ℝ => (b - a) * t + a)
      (stdSimplexBoundary 2 ×ˢ Icc 0 1) (stdSimplexBoundary 2 ×ˢ Icc a b) :=
    hBpoly.isPLHomeomorphOn_id.prodMap (isPLHomeomorphOn_mul_add_Icc hba (by ring) (by ring))
  set σ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ := Prod.map id fun t : ℝ => (b - a) * t + a
    with hσdef
  have hσi : IsPLHomeomorphOn (Function.invFunOn σ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
      (stdSimplexBoundary 2 ×ˢ Icc a b) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := hσ.symm
  have hK'' : IsPLSphere 1 (Function.invFunOn σ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K') :=
    hK'.of_isPLHomeomorphOn (hσi.restrict hK'.isPolyhedron hK'Icc)
  have hσK'' : σ '' (Function.invFunOn σ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K') = K' :=
    LeftInvOn.image_image (hσ.bijOn.invOn_invFunOn.2.mono hK'Icc)
  have hK''Ioo : Function.invFunOn σ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K' ⊆
      stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1 := by
    rintro _ ⟨k, hk, rfl⟩
    have hyA := hσi.bijOn.mapsTo (hK'Icc hk)
    have hσy := hσ.bijOn.invOn_invFunOn.2 (hK'Icc hk)
    have e : (b - a) * (Function.invFunOn σ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) k).2 + a =
        k.2 := congrArg Prod.snd hσy
    have hk2 := hTab ⟨k, hk, rfl⟩
    refine ⟨hyA.1, ?_, ?_⟩
    · by_contra h
      push Not at h
      nlinarith [mul_nonneg hba.le (neg_nonneg.mpr h), hk2.1]
    · by_contra h
      push Not at h
      nlinarith [mul_le_mul_of_nonneg_left h hba.le, hk2.2]
  have hK''ess : ¬ ∃ (D : Set ((Fin 3 → ℝ) × ℝ)) (r : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧
      r '' stdSimplexBoundary 2 =
        Function.invFunOn σ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K' := by
    rintro ⟨D, r, hr, hDA, hrb⟩
    refine hK'ess ⟨σ '' D, σ ∘ r, hr.trans (hσ.restrict (IsPLBall.isPolyhedron ⟨r, hr⟩) hDA),
      image_subset_iff.mpr fun d hd => ?_, by rw [image_comp, hrb, hσK'']⟩
    have h := hσ.bijOn.mapsTo (hDA hd)
    exact ⟨h.1, ha.trans h.2.1, h.2.2.trans hb⟩
  generalize Function.invFunOn σ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K' = K'' at *
  obtain ⟨Ψ, ν, hΨ, hν, hΨ0, hΨ1, hΨK⟩ :=
    hK''.exists_isPLHomeomorphOn_prism_lateral_level hK''Ioo hK''ess
  obtain ⟨Θ, hΘ, hΘlow, hΘhigh, hΘσ⟩ :=
    hBpoly.exists_isPLHomeomorphOn_prod_Icc_of_slab hΨ hΨ0 hν hΨ1 ha hab hb
  have hΘ0 : Θ '' (stdSimplexBoundary 2 ×ˢ {0}) = stdSimplexBoundary 2 ×ˢ {0} :=
    image_prod_singleton_of_map_level hBpoly.isPLHomeomorphOn_id
      fun x hx => hΘlow (x, 0) ⟨hx, le_rfl, ha⟩
  have hΘ1 : Θ '' (stdSimplexBoundary 2 ×ˢ {1}) = stdSimplexBoundary 2 ×ˢ {1} :=
    image_prod_singleton_of_map_level hν fun x hx => hΘhigh (x, 1) ⟨hx, hb, le_rfl⟩
  refine ⟨Φ ∘ Θ, fun L => if L = K then (b - a) * (1 / 2) + a else s L, hΘ.trans hΦ, ?_, ?_, ?_⟩
  · rw [image_comp, hΘ0, hΦ0]
  · rw [image_comp, hΘ1, hΦ1]
  · intro L hL
    rcases hL with rfl | hL
    · dsimp only
      rw [ite_eq_left rfl]
      refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
      have hσmid : σ '' (stdSimplexBoundary 2 ×ˢ {1 / 2}) =
          stdSimplexBoundary 2 ×ˢ {(b - a) * (1 / 2) + a} := by
        ext w
        constructor
        · rintro ⟨z, hz, rfl⟩
          refine ⟨hz.1, ?_⟩
          change (b - a) * z.2 + a = (b - a) * (1 / 2) + a
          rw [mem_singleton_iff.mp hz.2]
        · rintro ⟨hw1, hw2⟩
          exact ⟨(w.1, 1 / 2), ⟨hw1, rfl⟩, Prod.ext rfl (mem_singleton_iff.mp hw2).symm⟩
      have hΘmid : Θ '' (stdSimplexBoundary 2 ×ˢ {(b - a) * (1 / 2) + a}) = K' := by
        rw [← hσmid, ← hσK'', ← hΨK, ← image_comp, ← image_comp]
        exact image_congr fun z hz => hΘσ z ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num,
          by rw [mem_singleton_iff.mp hz.2]; norm_num⟩
      rw [image_comp, hΘmid, hΦK']
    · have hLK : L ≠ K := by
        rintro rfl
        obtain ⟨k, hk⟩ := hK.nonempty
        exact disjoint_left.mp (hKC _ hL) hk hk
      dsimp only
      rw [ite_eq_right hLK]
      obtain ⟨hsL, hΦL⟩ := hΦC L hL
      refine ⟨hsL, ?_⟩
      have hΘL : Θ '' (stdSimplexBoundary 2 ×ˢ {s L}) = stdSimplexBoundary 2 ×ˢ {s L} := by
        rcases hlev (s L) ⟨L, hL, rfl⟩ with h | h
        · exact image_prod_singleton_of_map_level hBpoly.isPLHomeomorphOn_id
            fun x hx => hΘlow (x, s L) ⟨hx, hsL.1.le, h⟩
        · exact image_prod_singleton_of_map_level hν
            fun x hx => hΘhigh (x, s L) ⟨hx, h, hsL.2.le⟩
      rw [image_comp, hΘL, hΦL]

theorem exists_isPLHomeomorphOn_prism_lateral_levels
    (C : Set (Set ((Fin 3 → ℝ) × ℝ))) (hC : C.Finite)
    (hCsph : ∀ K ∈ C, IsPLSphere 1 K)
    (hCA : ∀ K ∈ C, K ⊆ stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
    (hCess : ∀ K ∈ C, ¬ ∃ (D : Set ((Fin 3 → ℝ) × ℝ)) (r : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧ r '' stdSimplexBoundary 2 = K)
    (hCdisj : C.PairwiseDisjoint id) :
    ∃ (Φ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ) (s : Set ((Fin 3 → ℝ) × ℝ) → ℝ),
      IsPLHomeomorphOn Φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      Φ '' (stdSimplexBoundary 2 ×ˢ {0}) = stdSimplexBoundary 2 ×ˢ {0} ∧
      Φ '' (stdSimplexBoundary 2 ×ˢ {1}) = stdSimplexBoundary 2 ×ˢ {1} ∧
      ∀ K ∈ C, s K ∈ Ioo (0 : ℝ) 1 ∧ Φ '' (stdSimplexBoundary 2 ×ˢ {s K}) = K := by
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  have hApoly : IsPolyhedron (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    hBpoly.prod isHPolytope_Icc.isPolyhedron
  induction C, hC using Set.Finite.induction_on with
  | empty =>
    exact ⟨id, fun _ => 1 / 2, hApoly.isPLHomeomorphOn_id, image_id _, image_id _,
      fun K hK => (notMem_empty K hK).elim⟩
  | @insert K C hKC hCfin ih =>
    obtain ⟨Φ, s, hΦ, hΦ0, hΦ1, hΦC⟩ := ih (fun L hL => hCsph L (mem_insert_of_mem _ hL))
      (fun L hL => hCA L (mem_insert_of_mem _ hL)) (fun L hL => hCess L (mem_insert_of_mem _ hL))
      (hCdisj.subset (subset_insert _ _))
    exact exists_isPLHomeomorphOn_prism_lateral_levels_insert hCfin (hCsph K (mem_insert _ _))
      (hCA K (mem_insert _ _)) (hCess K (mem_insert _ _))
      (fun L hL => hCdisj (mem_insert _ _) (mem_insert_of_mem _ hL) (by rintro rfl; exact hKC hL))
      hΦ hΦ0 hΦ1 hΦC

end DifferentialGeometry.Topology.PiecewiseLinear
