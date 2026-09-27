import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

open Module

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem exists_ker_eq_of_finrank_succ_eq {N : Submodule ℝ E}
    (hN : Module.finrank ℝ N + 1 = Module.finrank ℝ E) :
    ∃ f : E →ₗ[ℝ] ℝ, LinearMap.ker f = N := by
  have hlt : N < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => ?_
    rw [h, finrank_top] at hN
    omega
  obtain ⟨f, hf0, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hle : N ≤ LinearMap.ker f := by
    intro y hy
    have hmem : f y ∈ Submodule.map f N := ⟨y, hy, rfl⟩
    rw [hfmap] at hmem
    simpa using hmem
  have hker : LinearMap.ker f ≠ ⊤ := fun h => hf0 (LinearMap.ker_eq_top.mp h)
  have h1 : Module.finrank ℝ (LinearMap.ker f) < Module.finrank ℝ E := Submodule.finrank_lt hker
  have h2 : Module.finrank ℝ N ≤ Module.finrank ℝ (LinearMap.ker f) := Submodule.finrank_mono hle
  exact ⟨f, (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm⟩

theorem exists_linearEquiv_of_transverse_planes {P Q : Submodule ℝ E}
    (hP : Module.finrank ℝ P = 2) (hQ : Module.finrank ℝ Q = 2)
    (hPQ : Module.finrank ℝ (P ⊓ Q : Submodule ℝ E) = 1) (hsup : P ⊔ Q = ⊤) :
    ∃ L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ,
      (∀ y : E, y ∈ P ↔ (L y).2.2 = 0) ∧ (∀ y : E, y ∈ Q ↔ (L y).2.1 = 0) := by
  have hdim : Module.finrank ℝ E = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [hsup, finrank_top, hP, hQ, hPQ] at h
    omega
  obtain ⟨β, hβ⟩ := exists_ker_eq_of_finrank_succ_eq (N := P) (by omega)
  obtain ⟨γ, hγ⟩ := exists_ker_eq_of_finrank_succ_eq (N := Q) (by omega)
  have hne : (P ⊓ Q : Submodule ℝ E) ≠ ⊥ := by
    intro h
    rw [h] at hPQ
    simp at hPQ
  obtain ⟨u, huPQ, hu0⟩ := (P ⊓ Q : Submodule ℝ E).ne_bot_iff.mp hne
  obtain ⟨α, hα⟩ := Module.Projective.exists_dual_ne_zero ℝ hu0
  have hspan : Submodule.span ℝ {u} = (P ⊓ Q : Submodule ℝ E) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rwa [Submodule.span_singleton_le_iff_mem]
    · rw [hPQ, finrank_span_singleton hu0]
  have hinj : Function.Injective (α.prod (γ.prod β)) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have hy' : (α.prod (γ.prod β)) y = 0 := hy
    have hαy : α y = 0 := congrArg Prod.fst hy'
    have hγy : γ y = 0 := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hy'
    have hβy : β y = 0 := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hy'
    have hmem : y ∈ Submodule.span ℝ {u} := by
      rw [hspan]
      exact ⟨hβ ▸ hβy, hγ ▸ hγy⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    rw [← ht, map_smul, smul_eq_mul] at hαy
    rcases mul_eq_zero.mp hαy with h | h
    · rw [← ht, h, zero_smul]
    · exact absurd h hα
  have hdim3 : Module.finrank ℝ (ℝ × ℝ × ℝ) = 3 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
  have hbij : Function.Bijective (α.prod (γ.prod β)) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hdim, hdim3])).mp hinj⟩
  refine ⟨LinearEquiv.ofBijective (α.prod (γ.prod β)) hbij, fun y => ?_, fun y => ?_⟩
  · change y ∈ P ↔ β y = 0
    rw [← hβ]
    exact LinearMap.mem_ker
  · change y ∈ Q ↔ γ y = 0
    rw [← hγ]
    exact LinearMap.mem_ker

omit [FiniteDimensional ℝ E] in
theorem mem_inf_iff_of_linearEquiv_of_transverse_planes {P Q : Submodule ℝ E}
    {L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ} (hPL : ∀ y : E, y ∈ P ↔ (L y).2.2 = 0)
    (hQL : ∀ y : E, y ∈ Q ↔ (L y).2.1 = 0) (y : E) :
    y ∈ (P ⊓ Q : Submodule ℝ E) ↔ (L y).2 = 0 := by
  rw [Submodule.mem_inf, hPL y, hQL y]
  constructor
  · rintro ⟨h1, h2⟩
    exact Prod.ext h2 h1
  · intro h
    exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩

theorem triple_eq_smul_add_smul_add_smul (p : ℝ × ℝ × ℝ) :
    p = p.1 • ((1, 0, 0) : ℝ × ℝ × ℝ) + p.2.1 • ((0, 1, 0) : ℝ × ℝ × ℝ)
      + p.2.2 • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
  obtain ⟨x, y, z⟩ := p
  simp

theorem map_triple_eq_smul_add_smul_add_smul {F : Type*} [AddCommGroup F] [Module ℝ F]
    (T : (ℝ × ℝ × ℝ) →ₗ[ℝ] F) (p : ℝ × ℝ × ℝ) :
    T p = p.1 • T (1, 0, 0) + p.2.1 • T (0, 1, 0) + p.2.2 • T (0, 0, 1) := by
  conv_lhs => rw [triple_eq_smul_add_smul_add_smul p]
  simp only [map_add, map_smul]

theorem linearMap_triple_apply (m : (ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ) (p : ℝ × ℝ × ℝ) :
    m p = m (1, 0, 0) * p.1 + m (0, 1, 0) * p.2.1 + m (0, 0, 1) * p.2.2 := by
  rw [map_triple_eq_smul_add_smul_add_smul m p]
  simp only [smul_eq_mul]
  ring

noncomputable def triangularEquiv (α β γ δ ε : ℝ) (hα : α ≠ 0) (hδ : δ ≠ 0) (hε : ε ≠ 0) :
    (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ℝ × ℝ × ℝ where
  toFun p := (α * p.1 + β * p.2.1 + γ * p.2.2, δ * p.2.1, ε * p.2.2)
  map_add' p q := by
    obtain ⟨x, y, z⟩ := p
    obtain ⟨x', y', z'⟩ := q
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩
  map_smul' c p := by
    obtain ⟨x, y, z⟩ := p
    simp only [Prod.smul_mk, smul_eq_mul, RingHom.id_apply, Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩
  invFun q := (α⁻¹ * (q.1 - β * (δ⁻¹ * q.2.1) - γ * (ε⁻¹ * q.2.2)), δ⁻¹ * q.2.1, ε⁻¹ * q.2.2)
  left_inv p := by
    obtain ⟨x, y, z⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, inv_mul_cancel_left₀ hδ y, inv_mul_cancel_left₀ hε z⟩
    rw [inv_mul_cancel_left₀ hδ y, inv_mul_cancel_left₀ hε z,
      show α * x + β * y + γ * z - β * y - γ * z = α * x by ring]
    exact inv_mul_cancel_left₀ hα x
  right_inv q := by
    obtain ⟨x, y, z⟩ := q
    simp only [Prod.mk.injEq]
    refine ⟨?_, mul_inv_cancel_left₀ hδ y, mul_inv_cancel_left₀ hε z⟩
    rw [mul_inv_cancel_left₀ hα]
    ring

theorem triangularEquiv_apply (α β γ δ ε : ℝ) (hα : α ≠ 0) (hδ : δ ≠ 0) (hε : ε ≠ 0)
    (p : ℝ × ℝ × ℝ) :
    triangularEquiv α β γ δ ε hα hδ hε p
      = (α * p.1 + β * p.2.1 + γ * p.2.2, δ * p.2.1, ε * p.2.2) := rfl

theorem triangularEquiv_symm_apply (α β γ δ ε : ℝ) (hα : α ≠ 0) (hδ : δ ≠ 0) (hε : ε ≠ 0)
    (q : ℝ × ℝ × ℝ) :
    (triangularEquiv α β γ δ ε hα hδ hε).symm q
      = (α⁻¹ * (q.1 - β * (δ⁻¹ * q.2.1) - γ * (ε⁻¹ * q.2.2)), δ⁻¹ * q.2.1, ε⁻¹ * q.2.2) := rfl

theorem triangularEquiv_snd_snd_eq_zero_iff (α β γ δ ε : ℝ) (hα : α ≠ 0) (hδ : δ ≠ 0)
    (hε : ε ≠ 0) (p : ℝ × ℝ × ℝ) :
    (triangularEquiv α β γ δ ε hα hδ hε p).2.2 = 0 ↔ p.2.2 = 0 := by
  rw [triangularEquiv_apply]
  simp only [mul_eq_zero, hε, false_or]

theorem triangularEquiv_snd_fst_eq_zero_iff (α β γ δ ε : ℝ) (hα : α ≠ 0) (hδ : δ ≠ 0)
    (hε : ε ≠ 0) (p : ℝ × ℝ × ℝ) :
    (triangularEquiv α β γ δ ε hα hδ hε p).2.1 = 0 ↔ p.2.1 = 0 := by
  rw [triangularEquiv_apply]
  simp only [mul_eq_zero, hδ, false_or]

theorem image_triangularEquiv_setOf_snd_snd_eq_zero (α β γ δ ε : ℝ) (hα : α ≠ 0) (hδ : δ ≠ 0)
    (hε : ε ≠ 0) :
    triangularEquiv α β γ δ ε hα hδ hε '' {p : ℝ × ℝ × ℝ | p.2.2 = 0}
      = {p : ℝ × ℝ × ℝ | p.2.2 = 0} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (triangularEquiv_snd_snd_eq_zero_iff α β γ δ ε hα hδ hε p).mpr hp
  · intro hq
    refine ⟨(triangularEquiv α β γ δ ε hα hδ hε).symm q, ?_,
      (triangularEquiv α β γ δ ε hα hδ hε).apply_symm_apply q⟩
    have h := triangularEquiv_snd_snd_eq_zero_iff α β γ δ ε hα hδ hε
      ((triangularEquiv α β γ δ ε hα hδ hε).symm q)
    rw [(triangularEquiv α β γ δ ε hα hδ hε).apply_symm_apply q] at h
    exact h.mp hq

theorem image_triangularEquiv_setOf_snd_fst_eq_zero (α β γ δ ε : ℝ) (hα : α ≠ 0) (hδ : δ ≠ 0)
    (hε : ε ≠ 0) :
    triangularEquiv α β γ δ ε hα hδ hε '' {p : ℝ × ℝ × ℝ | p.2.1 = 0}
      = {p : ℝ × ℝ × ℝ | p.2.1 = 0} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (triangularEquiv_snd_fst_eq_zero_iff α β γ δ ε hα hδ hε p).mpr hp
  · intro hq
    refine ⟨(triangularEquiv α β γ δ ε hα hδ hε).symm q, ?_,
      (triangularEquiv α β γ δ ε hα hδ hε).apply_symm_apply q⟩
    have h := triangularEquiv_snd_fst_eq_zero_iff α β γ δ ε hα hδ hε
      ((triangularEquiv α β γ δ ε hα hδ hε).symm q)
    rw [(triangularEquiv α β γ δ ε hα hδ hε).apply_symm_apply q] at h
    exact h.mp hq

theorem exists_coeff_triangularEquiv_symm (α β γ δ ε : ℝ) (hα : α ≠ 0) (hδ : δ ≠ 0) (hε : ε ≠ 0) :
    ∃ a b c d e : ℝ, ∀ q : ℝ × ℝ × ℝ,
      (triangularEquiv α β γ δ ε hα hδ hε).symm q
        = (a * q.1 + b * q.2.1 + c * q.2.2, d * q.2.1, e * q.2.2) := by
  refine ⟨α⁻¹, -(α⁻¹ * β * δ⁻¹), -(α⁻¹ * γ * ε⁻¹), δ⁻¹, ε⁻¹, fun q => ?_⟩
  rw [triangularEquiv_symm_apply, show α⁻¹ * (q.1 - β * (δ⁻¹ * q.2.1) - γ * (ε⁻¹ * q.2.2))
    = α⁻¹ * q.1 + -(α⁻¹ * β * δ⁻¹) * q.2.1 + -(α⁻¹ * γ * ε⁻¹) * q.2.2 by ring]

theorem exists_coeff_of_mapsTo_planes (T : (ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ × ℝ)
    (h1 : Set.MapsTo T {p : ℝ × ℝ × ℝ | p.2.2 = 0} {p : ℝ × ℝ × ℝ | p.2.2 = 0})
    (h2 : Set.MapsTo T {p : ℝ × ℝ × ℝ | p.2.1 = 0} {p : ℝ × ℝ × ℝ | p.2.1 = 0}) :
    ∃ a b c d e : ℝ, ∀ p : ℝ × ℝ × ℝ,
      T p = (a * p.1 + b * p.2.1 + c * p.2.2, d * p.2.1, e * p.2.2) := by
  have he1a : (T ((1, 0, 0) : ℝ × ℝ × ℝ)).2.1 = 0 := h2 rfl
  have he1b : (T ((1, 0, 0) : ℝ × ℝ × ℝ)).2.2 = 0 := h1 rfl
  have he2 : (T ((0, 1, 0) : ℝ × ℝ × ℝ)).2.2 = 0 := h1 rfl
  have he3 : (T ((0, 0, 1) : ℝ × ℝ × ℝ)).2.1 = 0 := h2 rfl
  refine ⟨(T (1, 0, 0)).1, (T (0, 1, 0)).1, (T (0, 0, 1)).1, (T (0, 1, 0)).2.1,
    (T (0, 0, 1)).2.2, fun p => ?_⟩
  rw [map_triple_eq_smul_add_smul_add_smul T p]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    ring
  · simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, smul_eq_mul, he1a, he3]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, he1b, he2]
    ring

theorem mapsTo_planes_iff_exists_coeff (T : (ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ × ℝ) :
    (Set.MapsTo T {p : ℝ × ℝ × ℝ | p.2.2 = 0} {p : ℝ × ℝ × ℝ | p.2.2 = 0} ∧
        Set.MapsTo T {p : ℝ × ℝ × ℝ | p.2.1 = 0} {p : ℝ × ℝ × ℝ | p.2.1 = 0}) ↔
      ∃ a b c d e : ℝ, ∀ p : ℝ × ℝ × ℝ,
        T p = (a * p.1 + b * p.2.1 + c * p.2.2, d * p.2.1, e * p.2.2) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact exists_coeff_of_mapsTo_planes T h1 h2
  · rintro ⟨a, b, c, d, e, hT⟩
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · have hp' : p.2.2 = 0 := hp
      change (T p).2.2 = 0
      rw [hT p]
      change e * p.2.2 = 0
      rw [hp', mul_zero]
    · have hp' : p.2.1 = 0 := hp
      change (T p).2.1 = 0
      rw [hT p]
      change d * p.2.1 = 0
      rw [hp', mul_zero]

theorem ne_zero_of_surjective_triangular {a b c d e : ℝ}
    (hsurj : Function.Surjective fun p : ℝ × ℝ × ℝ =>
      ((a * p.1 + b * p.2.1 + c * p.2.2, d * p.2.1, e * p.2.2) : ℝ × ℝ × ℝ)) :
    a ≠ 0 ∧ d ≠ 0 ∧ e ≠ 0 := by
  have hd : d ≠ 0 := by
    obtain ⟨p, hp⟩ := hsurj (0, 1, 0)
    have h : d * p.2.1 = 1 := congrArg (fun q : ℝ × ℝ × ℝ => q.2.1) hp
    intro hd0
    rw [hd0, zero_mul] at h
    exact zero_ne_one h
  have he : e ≠ 0 := by
    obtain ⟨p, hp⟩ := hsurj (0, 0, 1)
    have h : e * p.2.2 = 1 := congrArg (fun q : ℝ × ℝ × ℝ => q.2.2) hp
    intro he0
    rw [he0, zero_mul] at h
    exact zero_ne_one h
  refine ⟨?_, hd, he⟩
  obtain ⟨p, hp⟩ := hsurj (1, 0, 0)
  have h1 : a * p.1 + b * p.2.1 + c * p.2.2 = 1 := congrArg Prod.fst hp
  have h2 : d * p.2.1 = 0 := congrArg (fun q : ℝ × ℝ × ℝ => q.2.1) hp
  have h3 : e * p.2.2 = 0 := congrArg (fun q : ℝ × ℝ × ℝ => q.2.2) hp
  have h2' : p.2.1 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hd
    · exact h
  have h3' : p.2.2 = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h he
    · exact h
  rw [h2', h3', mul_zero, mul_zero, add_zero, add_zero] at h1
  intro ha0
  rw [ha0, zero_mul] at h1
  exact zero_ne_one h1

omit [FiniteDimensional ℝ E] in
theorem exists_mem_apply_eq_one_iff_not_le_ker {S : Submodule ℝ E} {ℓ : E →ₗ[ℝ] ℝ} :
    (∃ u ∈ S, ℓ u = 1) ↔ ¬ S ≤ LinearMap.ker ℓ := by
  constructor
  · rintro ⟨u, hu, h1⟩ hle
    have h0 : ℓ u = 0 := hle hu
    rw [h1] at h0
    exact one_ne_zero h0
  · intro h
    rw [SetLike.not_le_iff_exists] at h
    obtain ⟨u, hu, hnot⟩ := h
    have hne : ℓ u ≠ 0 := fun hz => hnot (LinearMap.mem_ker.mpr hz)
    exact ⟨(ℓ u)⁻¹ • u, S.smul_mem _ hu, by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]⟩

omit [FiniteDimensional ℝ E] in
theorem exists_mem_apply_eq_one_of_exists_mem_apply_ne_zero {S : Submodule ℝ E} {ℓ : E →ₗ[ℝ] ℝ}
    (h : ∃ u ∈ S, ℓ u ≠ 0) : ∃ u ∈ S, ℓ u = 1 := by
  obtain ⟨u, hu, hne⟩ := h
  exact ⟨(ℓ u)⁻¹ • u, S.smul_mem _ hu, by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]⟩

omit [FiniteDimensional ℝ E] in
theorem image_eq_of_mem_iff {S : Set E} {T : Set (ℝ × ℝ × ℝ)} (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ)
    (h : ∀ y : E, y ∈ S ↔ L y ∈ T) : L '' S = T := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h y).mp hy
  · intro hq
    refine ⟨L.symm q, (h (L.symm q)).mpr ?_, L.apply_symm_apply q⟩
    rw [L.apply_symm_apply]
    exact hq

omit [FiniteDimensional ℝ E] in
theorem exists_triangularEquiv_normalizing {P Q : Submodule ℝ E} {ℓ : E →ₗ[ℝ] ℝ}
    {L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ} (hPL : ∀ y : E, y ∈ P ↔ (L y).2.2 = 0)
    (hQL : ∀ y : E, y ∈ Q ↔ (L y).2.1 = 0) (hℓ : ∃ u ∈ (P ⊓ Q : Submodule ℝ E), ℓ u = 1) :
    ∃ (α β γ : ℝ) (hα : α ≠ 0),
      (∀ y : E, y ∈ P ↔
          (triangularEquiv α β γ 1 1 hα one_ne_zero one_ne_zero (L y)).2.2 = 0) ∧
        (∀ y : E, y ∈ Q ↔
            (triangularEquiv α β γ 1 1 hα one_ne_zero one_ne_zero (L y)).2.1 = 0) ∧
          (∀ y : E,
              (triangularEquiv α β γ 1 1 hα one_ne_zero one_ne_zero (L y)).2 = (L y).2) ∧
            (∀ y : E, ℓ y = (triangularEquiv α β γ 1 1 hα one_ne_zero one_ne_zero (L y)).1) := by
  obtain ⟨u, hu, hu1⟩ := hℓ
  have key : ∀ y : E, ℓ y = ℓ (L.symm (1, 0, 0)) * (L y).1 + ℓ (L.symm (0, 1, 0)) * (L y).2.1
      + ℓ (L.symm (0, 0, 1)) * (L y).2.2 := by
    intro y
    have h := linearMap_triple_apply (ℓ ∘ₗ (L.symm : (ℝ × ℝ × ℝ) →ₗ[ℝ] E)) (L y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
    exact h
  have hα : ℓ (L.symm ((1, 0, 0) : ℝ × ℝ × ℝ)) ≠ 0 := by
    have huP : (L u).2.2 = 0 := (hPL u).mp (Submodule.mem_inf.mp hu).1
    have huQ : (L u).2.1 = 0 := (hQL u).mp (Submodule.mem_inf.mp hu).2
    have h := key u
    rw [hu1, huP, huQ] at h
    intro h0
    rw [h0] at h
    simp at h
  refine ⟨ℓ (L.symm (1, 0, 0)), ℓ (L.symm (0, 1, 0)), ℓ (L.symm (0, 0, 1)), hα,
    fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · simp only [triangularEquiv_apply, one_mul]
    exact hPL y
  · simp only [triangularEquiv_apply, one_mul]
    exact hQL y
  · simp only [triangularEquiv_apply, one_mul]
  · simp only [triangularEquiv_apply]
    exact key y

theorem exists_linearEquiv_of_transverse_planes_of_transverse_functional {P Q : Submodule ℝ E}
    {ℓ : E →ₗ[ℝ] ℝ} (hP : Module.finrank ℝ P = 2) (hQ : Module.finrank ℝ Q = 2)
    (hPQ : Module.finrank ℝ (P ⊓ Q : Submodule ℝ E) = 1) (hsup : P ⊔ Q = ⊤)
    (hℓ : ∃ u ∈ (P ⊓ Q : Submodule ℝ E), ℓ u = 1) :
    ∃ L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ,
      (∀ y : E, y ∈ P ↔ (L y).2.2 = 0) ∧ (∀ y : E, y ∈ Q ↔ (L y).2.1 = 0) ∧
        (∀ y : E, y ∈ (P ⊓ Q : Submodule ℝ E) ↔ (L y).2 = 0) ∧
          (∀ y : E, ℓ y = (L y).1) := by
  obtain ⟨L, hPL, hQL⟩ := exists_linearEquiv_of_transverse_planes hP hQ hPQ hsup
  obtain ⟨α, β, γ, hα, h1, h2, _, h4⟩ := exists_triangularEquiv_normalizing hPL hQL hℓ
  exact ⟨L.trans (triangularEquiv α β γ 1 1 hα one_ne_zero one_ne_zero), h1, h2,
    mem_inf_iff_of_linearEquiv_of_transverse_planes h1 h2, h4⟩

theorem exists_linearEquiv_boundaryCrossing_normalForm {P Q : Submodule ℝ E} {ℓ : E →ₗ[ℝ] ℝ}
    (hP : Module.finrank ℝ P = 2) (hQ : Module.finrank ℝ Q = 2)
    (hPQ : Module.finrank ℝ (P ⊓ Q : Submodule ℝ E) = 1) (hsup : P ⊔ Q = ⊤)
    (hℓ : ∃ u ∈ (P ⊓ Q : Submodule ℝ E), ℓ u = 1) :
    ∃ L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ,
      L '' {y : E | 0 ≤ ℓ y} = {p : ℝ × ℝ × ℝ | 0 ≤ p.1} ∧
        L '' {y : E | ℓ y = 0} = {p : ℝ × ℝ × ℝ | p.1 = 0} ∧
          L '' {y : E | y ∈ P ∧ 0 ≤ ℓ y} = {p : ℝ × ℝ × ℝ | p.2.2 = 0 ∧ 0 ≤ p.1} ∧
            L '' {y : E | y ∈ Q ∧ 0 ≤ ℓ y} = {p : ℝ × ℝ × ℝ | p.2.1 = 0 ∧ 0 ≤ p.1} ∧
              L '' {y : E | y ∈ (P ⊓ Q : Submodule ℝ E) ∧ 0 ≤ ℓ y}
                = {p : ℝ × ℝ × ℝ | p.2 = 0 ∧ 0 ≤ p.1} := by
  obtain ⟨L, h1, h2, h3, h4⟩ :=
    exists_linearEquiv_of_transverse_planes_of_transverse_functional hP hQ hPQ hsup hℓ
  refine ⟨L, ?_, ?_, ?_, ?_, ?_⟩
  · refine image_eq_of_mem_iff L fun y => ?_
    change 0 ≤ ℓ y ↔ 0 ≤ (L y).1
    rw [h4 y]
  · refine image_eq_of_mem_iff L fun y => ?_
    change ℓ y = 0 ↔ (L y).1 = 0
    rw [h4 y]
  · refine image_eq_of_mem_iff L fun y => ?_
    change y ∈ P ∧ 0 ≤ ℓ y ↔ (L y).2.2 = 0 ∧ 0 ≤ (L y).1
    rw [h1 y, h4 y]
  · refine image_eq_of_mem_iff L fun y => ?_
    change y ∈ Q ∧ 0 ≤ ℓ y ↔ (L y).2.1 = 0 ∧ 0 ≤ (L y).1
    rw [h2 y, h4 y]
  · refine image_eq_of_mem_iff L fun y => ?_
    change y ∈ (P ⊓ Q : Submodule ℝ E) ∧ 0 ≤ ℓ y ↔ (L y).2 = 0 ∧ 0 ≤ (L y).1
    rw [h3 y, h4 y]

end DifferentialGeometry.Topology.PiecewiseLinear
