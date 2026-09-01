import DifferentialGeometry.Tensor.Alternating.Curry
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace AlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def contractionAnnihilator
    (K : Submodule ℝ (E [⋀^Fin 2]→ₗ[ℝ] ℝ)) : Submodule ℝ E where
  carrier := {v | ∀ ω ∈ K, ω.curryLeft v = 0}
  zero_mem' := by
    intro ω hω
    simp
  add_mem' := by
    intro v w hv hw ω hω
    rw [map_add, hv ω hω, hw ω hω, add_zero]
  smul_mem' := by
    intro c v hv ω hω
    rw [map_smul, hv ω hω, smul_zero]

theorem mem_contractionAnnihilator_iff
    (K : Submodule ℝ (E [⋀^Fin 2]→ₗ[ℝ] ℝ)) (v : E) :
    v ∈ contractionAnnihilator K ↔ ∀ ω ∈ K, ω.curryLeft v = 0 :=
  Iff.rfl

theorem contractionAnnihilator_span_singleton
    (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) :
    contractionAnnihilator (Submodule.span ℝ {ω}) = ω.curryLeft.ker := by
  apply le_antisymm
  · intro v hv
    exact LinearMap.mem_ker.mpr
      (hv ω (Submodule.subset_span (Set.mem_singleton ω)))
  · intro v hv ω' hω'
    let ev : (E [⋀^Fin 2]→ₗ[ℝ] ℝ) →ₗ[ℝ] (E [⋀^Fin 1]→ₗ[ℝ] ℝ) :=
      { toFun := fun η => η.curryLeft v
        map_add' := by
          intro η₁ η₂
          simp [AlternatingMap.curryLeft_add]
        map_smul' := by
          intro c η
          simp [AlternatingMap.curryLeft_smul] }
    have hspan : Submodule.span ℝ {ω} ≤ ev.ker := by
      rw [Submodule.span_le]
      intro η hη
      rw [Set.mem_singleton_iff.mp hη]
      exact LinearMap.mem_ker.mpr hv
    change ω'.curryLeft v = 0
    exact LinearMap.mem_ker.mp (hspan hω')

theorem contractionAnnihilator_eq_curryLeft_ker_of_finrank_eq_one
    (K : Submodule ℝ (E [⋀^Fin 2]→ₗ[ℝ] ℝ))
    (hK : Module.finrank ℝ K = 1) :
    ∃ ω, ω ≠ 0 ∧ K = Submodule.span ℝ {ω} ∧
      contractionAnnihilator K = ω.curryLeft.ker := by
  let _ : FiniteDimensional ℝ K := FiniteDimensional.of_finrank_eq_succ hK
  have hKne : K ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hK
    omega
  obtain ⟨ω, hωK, hω⟩ := K.ne_bot_iff.mp hKne
  have hspan : K = Submodule.span ℝ {ω} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · exact (Submodule.span_singleton_le_iff_mem ω K).mpr hωK
    · rw [finrank_span_singleton hω, hK]
  refine ⟨ω, hω, hspan, ?_⟩
  rw [hspan]
  exact contractionAnnihilator_span_singleton ω

private lemma skew_two (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (u v : E) : ω ![v, u] = -ω ![u, v] := by
  simpa using ω.map_swap (v := ![u, v]) (i := (0 : Fin 2)) (j := 1) (by decide)

private lemma diag_two (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (u : E) : ω ![u, u] = 0 := by
  exact ω.map_eq_zero_of_eq ![u, u] rfl (i := (0 : Fin 2)) (j := 1) (by decide)

private lemma basis_zero_of_coeff (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (B : Module.Basis (Fin 3) ℝ E)
    (h : ∀ i j : Fin 3, ω ![B i, B j] = 0) : ω = 0 := by
  apply Module.Basis.ext_alternating B
  intro v hv
  have h' := h (v 0) (v 1)
  have hv' : (fun i => B (v i)) = ![B (v 0), B (v 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv']
  exact h'

private lemma kernel_vec (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (B : Module.Basis (Fin 3) ℝ E) :
    ω.curryLeft (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2) = 0 := by
  have h00 := diag_two ω (B 0)
  have h11 := diag_two ω (B 1)
  have h22 := diag_two ω (B 2)
  have h10 := skew_two ω (B 0) (B 1)
  have h20 := skew_two ω (B 0) (B 2)
  have h21 := skew_two ω (B 1) (B 2)
  apply Module.Basis.ext_alternating B
  intro v hv
  have hv' : v = ![v 0] := by
    funext i
    fin_cases i
    rfl
  rw [hv']
  have hv0 : v 0 = 0 ∨ v 0 = 1 ∨ v 0 = 2 := by omega
  rcases hv0 with hv0 | hv0 | hv0 <;> rw [hv0] at hv' <;> rw [hv']
  all_goals simp only [AlternatingMap.curryLeft_apply_apply, AlternatingMap.zero_apply]
  · have hargs : Matrix.vecCons
        (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2)
        (fun i => B (![![0] 0] i)) =
        ![ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2,
          B 0] := by
      funext i
      fin_cases i <;> rfl
    rw [hargs]
    change ω (Matrix.vecCons
      (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2) ![B 0]) = 0
    rw [ω.map_vecCons_add, ω.map_vecCons_add, ω.map_vecCons_smul,
      ω.map_vecCons_smul, ω.map_vecCons_smul]
    simp only [h00, h10, h20, smul_eq_mul]
    ring
  · have hargs : Matrix.vecCons
        (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2)
        (fun i => B (![![1] 0] i)) =
        ![ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2,
          B 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hargs]
    change ω (Matrix.vecCons
      (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2) ![B 1]) = 0
    rw [ω.map_vecCons_add, ω.map_vecCons_add, ω.map_vecCons_smul,
      ω.map_vecCons_smul, ω.map_vecCons_smul]
    simp only [h11, h21, smul_eq_mul]
    ring
  · have hargs : Matrix.vecCons
        (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2)
        (fun i => B (![![2] 0] i)) =
        ![ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2,
          B 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hargs]
    change ω (Matrix.vecCons
      (ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2) ![B 2]) = 0
    rw [ω.map_vecCons_add, ω.map_vecCons_add, ω.map_vecCons_smul,
      ω.map_vecCons_smul, ω.map_vecCons_smul]
    simp only [h22, h20, smul_eq_mul]
    ring

theorem finrank_ker_curryLeft_eq_one [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 3)
    {ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ} (hω : ω ≠ 0) :
    Module.finrank ℝ ω.curryLeft.ker = 1 := by
  let B := Module.finBasisOfFinrankEq ℝ E hE
  have hω' : ¬ ∀ z : Fin 2 → E, ω z = 0 := by
    intro hz
    apply hω
    ext z
    exact hz z
  obtain ⟨z, hz⟩ := Classical.not_forall.mp hω'
  let u := z 0
  let v := z 1
  have hz' : z = ![u, v] := by
    funext i
    fin_cases i <;> rfl
  have huv : ω ![u, v] ≠ 0 := by simpa [hz'] using hz
  have hlin : LinearIndependent ℝ (fun i : Fin 2 => ω.curryLeft (![u, v] i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    fin_cases i
    · have hc' := congrArg (fun α : E [⋀^Fin 1]→ₗ[ℝ] ℝ => α ![v]) hc
      simp only [Fin.sum_univ_two, AlternatingMap.add_apply, AlternatingMap.smul_apply,
        AlternatingMap.zero_apply, AlternatingMap.curryLeft_apply_apply] at hc'
      have hvv := diag_two ω v
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hvv, smul_eq_mul, mul_zero,
        add_zero] at hc'
      exact (mul_eq_zero.mp hc').resolve_right huv
    · have hc' := congrArg (fun α : E [⋀^Fin 1]→ₗ[ℝ] ℝ => α ![u]) hc
      simp only [Fin.sum_univ_two, AlternatingMap.add_apply, AlternatingMap.smul_apply,
        AlternatingMap.zero_apply, AlternatingMap.curryLeft_apply_apply] at hc'
      have huu := diag_two ω u
      have hvu := skew_two ω u v
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, huu, hvu, smul_eq_mul, mul_zero,
        zero_add] at hc'
      exact (mul_eq_zero.mp hc').resolve_right (neg_ne_zero.mpr huv)
  let g : Fin 2 → ω.curryLeft.range :=
    fun i => ⟨ω.curryLeft (![u, v] i), ⟨![u, v] i, rfl⟩⟩
  have hg : LinearIndependent ℝ g := by
    apply LinearIndependent.of_comp (ω.curryLeft.range.subtype)
    simpa [g, Function.comp_def] using hlin
  have hspan : Module.finrank ℝ (Submodule.span ℝ (Set.range g)) = 2 := by
    simpa using finrank_span_eq_card hg
  have hmono : Module.finrank ℝ (Submodule.span ℝ (Set.range g)) ≤
      Module.finrank ℝ (ω.curryLeft.range : Type _) :=
    (Submodule.span ℝ (Set.range g)).finrank_le
  have hrange : 2 ≤ Module.finrank ℝ ω.curryLeft.range := by omega
  have hker : ω.curryLeft.ker ≠ ⊥ := by
    intro hbot
    let w := ω ![B 1, B 2] • B 0 + ω ![B 2, B 0] • B 1 + ω ![B 0, B 1] • B 2
    have hwker : w ∈ ω.curryLeft.ker := by
      rw [LinearMap.mem_ker]
      exact kernel_vec ω B
    have hwzero : w = 0 := by
      have : w ∈ (⊥ : Submodule ℝ E) := hbot ▸ hwker
      simpa using this
    have hc0 := congrArg (fun x : E => B.repr x 0) hwzero
    have hc1 := congrArg (fun x : E => B.repr x 1) hwzero
    have hc2 := congrArg (fun x : E => B.repr x 2) hwzero
    have h12 : ω ![B 1, B 2] = 0 := by
      simpa [w, B.repr_self_apply] using hc0
    have h20 : ω ![B 2, B 0] = 0 := by
      simpa [w, B.repr_self_apply] using hc1
    have h01 : ω ![B 0, B 1] = 0 := by
      simpa [w, B.repr_self_apply] using hc2
    apply hω
    apply basis_zero_of_coeff ω B
    intro i j
    fin_cases i <;> fin_cases j
    all_goals simp [diag_two, skew_two, h12, h20, h01]
  have hsum := ω.curryLeft.finrank_range_add_finrank_ker
  have hker_pos : 1 ≤ Module.finrank ℝ (ω.curryLeft.ker : Type _) :=
    (Submodule.one_le_finrank_iff).2 hker
  rw [hE] at hsum
  omega

theorem finrank_contractionAnnihilator_eq_one [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 3)
    (K : Submodule ℝ (E [⋀^Fin 2]→ₗ[ℝ] ℝ))
    (hK : Module.finrank ℝ K = 1) :
    Module.finrank ℝ (contractionAnnihilator K) = 1 := by
  obtain ⟨ω, hω, _, hann⟩ :=
    contractionAnnihilator_eq_curryLeft_ker_of_finrank_eq_one K hK
  rw [hann]
  exact finrank_ker_curryLeft_eq_one hE hω

theorem map_ker_curryLeft_compLinearEquiv
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (e : F ≃ₗ[ℝ] E) :
    Submodule.map e.toLinearMap (ω.compLinearMap e.toLinearMap).curryLeft.ker =
      ω.curryLeft.ker := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hx0 : (ω.compLinearMap e.toLinearMap).curryLeft x = 0 := hx
    apply LinearMap.mem_ker.mpr
    apply AlternatingMap.ext
    intro z
    have hz := congrArg (fun α : F [⋀^Fin 1]→ₗ[ℝ] ℝ =>
      α (fun i : Fin 1 => e.symm (z i))) hx0
    simpa [AlternatingMap.curryLeft_compLinearMap] using hz
  · intro y hy
    refine ⟨e.symm y, ?_, ?_⟩
    · have hy0 : ω.curryLeft y = 0 := hy
      apply LinearMap.mem_ker.mpr
      apply AlternatingMap.ext
      intro z
      have hzy := congrArg (fun α : E [⋀^Fin 1]→ₗ[ℝ] ℝ =>
        α (fun i : Fin 1 => e (z i))) hy0
      simpa [AlternatingMap.curryLeft_compLinearMap] using hzy
    · simp

theorem ker_curryLeft_smul_eq (ω : E [⋀^Fin 2]→ₗ[ℝ] ℝ) {c : ℝ} (hc : c ≠ 0) :
    (c • ω).curryLeft.ker = ω.curryLeft.ker := by
  apply le_antisymm
  · intro v hv
    have hv' : (c • ω).curryLeft v = 0 := hv
    have hmul : c • ω.curryLeft v = 0 := by
      simpa [AlternatingMap.curryLeft_smul] using hv'
    have : ω.curryLeft v = 0 := by
      exact (smul_eq_zero.mp hmul).resolve_left hc
    exact this
  · intro v hv
    have hv' : ω.curryLeft v = 0 := hv
    have hmul : c • ω.curryLeft v = 0 := by simp [hv']
    simpa [AlternatingMap.curryLeft_smul] using hmul

theorem map_contractionAnnihilator_compLinearEquiv
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    (K : Submodule ℝ (E [⋀^Fin 2]→ₗ[ℝ] ℝ)) (e : F ≃ₗ[ℝ] E) :
    Submodule.map e.toLinearMap
        (contractionAnnihilator
          (Submodule.map
            (AlternatingMap.domLCongr ℝ ℝ (Fin 2) ℝ e.symm).toLinearMap K)) =
      contractionAnnihilator K := by
  let e₂ := AlternatingMap.domLCongr ℝ ℝ (Fin 2) ℝ e.symm
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    intro ω hω
    have hpull : e₂ ω ∈ Submodule.map e₂.toLinearMap K := ⟨ω, hω, rfl⟩
    have hx0 := hx (e₂ ω) hpull
    apply AlternatingMap.ext
    intro z
    have hz := congrArg
      (fun α : F [⋀^Fin 1]→ₗ[ℝ] ℝ => α (fun i => e.symm (z i))) hx0
    simpa [e₂, AlternatingMap.curryLeft_compLinearMap] using hz
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    intro η hη
    rcases hη with ⟨ω, hω, rfl⟩
    apply AlternatingMap.ext
    intro z
    have hy0 := hy ω hω
    have hz := congrArg
      (fun α : E [⋀^Fin 1]→ₗ[ℝ] ℝ => α (fun i => e (z i))) hy0
    simpa [e₂, AlternatingMap.curryLeft_compLinearMap] using hz

end AlternatingMap

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def contractionAnnihilator
    (K : Submodule ℝ (E [⋀^Fin 2]→L[ℝ] ℝ)) : Submodule ℝ E :=
  AlternatingMap.contractionAnnihilator
    (Submodule.map (toAlternatingMapLinear (R := ℝ)) K)

theorem mem_contractionAnnihilator_iff
    {K : Submodule ℝ (E [⋀^Fin 2]→L[ℝ] ℝ)} {v : E} :
    v ∈ contractionAnnihilator K ↔
      ∀ ω ∈ K, ω.curryLeft v = 0 := by
  constructor
  · intro hv ω hω
    apply toAlternatingMap_injective
    exact hv ω.toAlternatingMap ⟨ω, hω, rfl⟩
  · intro hv ω hω
    rcases hω with ⟨η, hη, rfl⟩
    simpa using congrArg toAlternatingMap (hv η hη)

theorem contractionAnnihilator_span_singleton
    (ω : E [⋀^Fin 2]→L[ℝ] ℝ) :
    contractionAnnihilator (Submodule.span ℝ {ω}) = ω.curryLeft.ker := by
  rw [contractionAnnihilator]
  have hmap :
      Submodule.map (toAlternatingMapLinear (R := ℝ))
          (Submodule.span ℝ {ω}) =
        Submodule.span ℝ {ω.toAlternatingMap} := by
    rw [Submodule.map_span]
    congr 1
    ext η
    simp
  rw [hmap, AlternatingMap.contractionAnnihilator_span_singleton]
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hv
    apply toAlternatingMap_injective
    simpa using hv
  · intro hv
    simpa using congrArg toAlternatingMap hv

theorem finrank_contractionAnnihilator_eq_one [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 3)
    (K : Submodule ℝ (E [⋀^Fin 2]→L[ℝ] ℝ))
    (hK : Module.finrank ℝ K = 1) :
    Module.finrank ℝ (contractionAnnihilator K) = 1 := by
  rw [contractionAnnihilator]
  apply AlternatingMap.finrank_contractionAnnihilator_eq_one hE
  rw [← hK]
  exact (Submodule.equivMapOfInjective
    (toAlternatingMapLinear (R := ℝ)) toAlternatingMap_injective K).finrank_eq.symm

theorem map_contractionAnnihilator_compContinuousLinearEquiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Submodule ℝ (E [⋀^Fin 2]→L[ℝ] ℝ)) (e : F ≃L[ℝ] E) :
    Submodule.map e.toLinearMap
        (contractionAnnihilator
          (Submodule.map
            (e.symm.continuousAlternatingMapCongrLeft (ι := Fin 2)).toLinearMap K)) =
      contractionAnnihilator K := by
  let e₂ : (E [⋀^Fin 2]→L[ℝ] ℝ) ≃L[ℝ] (F [⋀^Fin 2]→L[ℝ] ℝ) :=
    e.symm.continuousAlternatingMapCongrLeft (ι := Fin 2)
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [mem_contractionAnnihilator_iff]
    intro ω hω
    have hpull : e₂ ω ∈ Submodule.map e₂.toLinearMap K := ⟨ω, hω, rfl⟩
    have hx0 := (mem_contractionAnnihilator_iff.mp hx) (e₂ ω) hpull
    apply ContinuousAlternatingMap.ext
    intro z
    have hz := congrArg
      (fun α : F [⋀^Fin 1]→L[ℝ] ℝ => α (fun i : Fin 1 => e.symm (z i))) hx0
    have htail : (⇑e ∘ fun i : Fin 1 => e.symm (z i)) = z := by
      funext i
      simp
    simpa [e₂, ContinuousAlternatingMap.curryLeft_compContinuousLinearMap,
      htail] using hz
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    apply mem_contractionAnnihilator_iff.mpr
    intro η hη
    rcases hη with ⟨ω, hω, rfl⟩
    apply ContinuousAlternatingMap.ext
    intro z
    have hy0 := (mem_contractionAnnihilator_iff.mp hy) ω hω
    have hz := congrArg
      (fun α : E [⋀^Fin 1]→L[ℝ] ℝ => α (fun i : Fin 1 => e (z i))) hy0
    simpa [e₂, ContinuousAlternatingMap.curryLeft_compContinuousLinearMap,
      Function.comp_def] using hz

theorem map_contractionAnnihilator_of_map_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Submodule ℝ (E [⋀^Fin 2]→L[ℝ] ℝ))
    (L : Submodule ℝ (F [⋀^Fin 2]→L[ℝ] ℝ)) (e : E ≃L[ℝ] F)
    (h : Submodule.map
      (e.continuousAlternatingMapCongrLeft (ι := Fin 2)).toLinearMap K = L) :
    Submodule.map e.toLinearMap (contractionAnnihilator K) =
      contractionAnnihilator L := by
  have hback :
      Submodule.map
          (e.symm.continuousAlternatingMapCongrLeft (ι := Fin 2)).toLinearMap L = K := by
    let e₂ : (E [⋀^Fin 2]→L[ℝ] ℝ) ≃L[ℝ] (F [⋀^Fin 2]→L[ℝ] ℝ) :=
      e.continuousAlternatingMapCongrLeft (ι := Fin 2)
    exact (Submodule.map_symm_eq_iff e₂.toLinearEquiv).2 h
  rw [← hback]
  exact map_contractionAnnihilator_compContinuousLinearEquiv L e

end ContinuousAlternatingMap
