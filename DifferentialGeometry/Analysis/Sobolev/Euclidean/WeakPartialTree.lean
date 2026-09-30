import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.WeakPartial
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialSource
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memWkp_of_weak_partial_tree
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    (u : ∀ n : ℕ, (Fin n → Fin d) → E → ℝ)
    (hLp : ∀ n α, MemLp (u n α) p (volume.restrict Ω))
    (hweak : ∀ n α i,
      DeGiorgi.HasWeakPartialDeriv i (u (n + 1) (Fin.cons i α)) (u n α) Ω) :
    ∀ k, MemWkp k p (u 0 (fun i : Fin 0 => Fin.elim0 i)) Ω := by
  have hnode : ∀ k n α, MemWkp k p (u n α) Ω := by
    intro k
    induction k with
    | zero =>
        intro n α
        exact hLp n α
    | succ k ih =>
        intro n α
        apply memWkp_succ_of_hasWeakPartialDeriv hp hΩ (hLp n α)
        · intro i
          exact ih (n + 1) (Fin.cons i α)
        · intro i
          exact hweak n α i
  intro k
  exact hnode k 0 (fun i : Fin 0 => Fin.elim0 i)

theorem ae_memWkp_of_weak_partial_tree
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    (u : ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hLp : ∀ n α, MemLp (u n α) p (μ.prod (volume.restrict Ω)))
    (hweak : ∀ n α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => u (n + 1) (Fin.cons i α) (t, x))
        (fun x => u n α (t, x)) Ω) :
    ∀ k, ∀ᵐ t ∂μ,
      MemWkp k p (fun x => u 0 (fun i : Fin 0 => Fin.elim0 i) (t, x)) Ω := by
  have hslices {f : Z × E → ℝ}
      (hf : MemLp f p (μ.prod (volume.restrict Ω))) :
      ∀ᵐ t ∂μ, MemLp (fun x => f (t, x)) p (volume.restrict Ω) := by
    by_cases hptop : p = ⊤
    · subst p
      exact hf.prodMk_left_top
    · exact hf.prodMk_left hptop
  have hnode : ∀ k n α, ∀ᵐ t ∂μ,
      MemWkp k p (fun x => u n α (t, x)) Ω := by
    intro k
    induction k with
    | zero =>
        intro n α
        exact hslices (hLp n α)
    | succ k ih =>
        intro n α
        have hchild : ∀ i : Fin d, ∀ᵐ t ∂μ,
            MemWkp k p
              (fun x => u (n + 1) (Fin.cons i α) (t, x)) Ω := by
          intro i
          exact ih (n + 1) (Fin.cons i α)
        have hchild' := ae_all_iff.mpr hchild
        have hderiv : ∀ i : Fin d, ∀ᵐ t ∂μ,
            DeGiorgi.HasWeakPartialDeriv i
              (fun x => u (n + 1) (Fin.cons i α) (t, x))
              (fun x => u n α (t, x)) Ω :=
          fun i => hweak n α i
        have hderiv' := ae_all_iff.mpr hderiv
        have hbase := hslices (hLp n α)
        filter_upwards [hbase, hchild', hderiv'] with t ht htc htd
        apply memWkp_succ_of_hasWeakPartialDeriv hp hΩ ht
          (g := fun i x => u (n + 1) (Fin.cons i α) (t, x))
        · exact htc
        · exact htd
  intro k
  exact hnode k 0 (fun i : Fin 0 => Fin.elim0 i)

theorem ae_memWkp_and_memLp_wkpNorm_of_finite_weak_partial_tree
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {Ω : Set E} (hΩ : IsOpen Ω) (K : ℕ)
    (u : ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hLp : ∀ n ≤ K, ∀ α, MemLp (u n α) p (μ.prod (volume.restrict Ω)))
    (hweak : ∀ n < K, ∀ α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => u (n + 1) (Fin.cons i α) (t, x))
        (fun x => u n α (t, x)) Ω) :
    (∀ᵐ t ∂μ,
      MemWkp K p
        (fun x => u 0 (fun i : Fin 0 => Fin.elim0 i) (t, x)) Ω) ∧
      MemLp
        (fun t =>
          (iteratedWeakSobolevNorm K p
            (fun x => u 0 (fun i : Fin 0 => Fin.elim0 i) (t, x)) Ω).toReal) p μ := by
  have hnode : ∀ k n α, n + k ≤ K → (∀ᵐ t ∂μ,
      MemWkp k p (fun x => u n α (t, x)) Ω) ∧
      MemLp
        (fun t => (iteratedWeakSobolevNorm k p
          (fun x => u n α (t, x)) Ω).toReal) p μ := by
    intro k
    induction k with
    | zero =>
        intro n α hn
        have hslice := (hLp n (by omega) α).prodMk_left hpt
        refine ⟨hslice, ?_⟩
        simpa only [wkpNorm_zero] using (hLp n (by omega) α).eLpNorm_toReal hpt
    | succ k ih =>
        intro n α hn
        let V : Z × E → ℝ := u n α
        let W : Fin d → Z × E → ℝ := fun i => u (n + 1) (Fin.cons i α)
        have hW : ∀ i, ∀ᵐ t ∂μ,
            MemWkp k p (fun x => W i (t, x)) Ω := by
          intro i
          exact (ih (n + 1) (Fin.cons i α) (by omega)).1
        have hWnorm : ∀ i, MemLp
            (fun t => (iteratedWeakSobolevNorm k p
              (fun x => W i (t, x)) Ω).toReal) p μ := by
          intro i
          exact (ih (n + 1) (Fin.cons i α) (by omega)).2
        have hstep := ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
          hΩ hp hpt (V := V) (W := W) (hLp n (by omega) α) hW hWnorm
          (hweak n (by omega) α)
        simpa only [V, W] using hstep
  exact hnode K 0 (fun i : Fin 0 => Fin.elim0 i) (by omega)

theorem ae_memWkp_and_memLp_wkpNorm_of_weak_partial_tree
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {Ω : Set E} (hΩ : IsOpen Ω)
    (u : ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hLp : ∀ n α, MemLp (u n α) p (μ.prod (volume.restrict Ω)))
    (hweak : ∀ n α i, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => u (n + 1) (Fin.cons i α) (t, x))
        (fun x => u n α (t, x)) Ω) :
    ∀ k, (∀ᵐ t ∂μ,
      MemWkp k p
        (fun x => u 0 (fun i : Fin 0 => Fin.elim0 i) (t, x)) Ω) ∧
      MemLp
        (fun t =>
          (iteratedWeakSobolevNorm k p
            (fun x => u 0 (fun i : Fin 0 => Fin.elim0 i) (t, x)) Ω).toReal) p μ := by
  intro k
  exact ae_memWkp_and_memLp_wkpNorm_of_finite_weak_partial_tree hp hpt hΩ k u
    (fun n _ => hLp n) (fun n _ => hweak n)

theorem eq_of_finite_weak_partial_trees
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω) (N : ℕ)
    (P Q : ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p (μ.prod (volume.restrict Ω)))
    (hP : ∀ m < N, ∀ β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => P (m + 1) (Fin.cons i β) (t, z)) (fun z => P m β (t, z)) Ω)
    (hQ : ∀ m < N, ∀ β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun z => Q (m + 1) (Fin.cons i β) (t, z)) (fun z => Q m β (t, z)) Ω)
    (hroot : P 0 (fun i => Fin.elim0 i) = Q 0 (fun i => Fin.elim0 i)) :
    ∀ m ≤ N, ∀ β, P m β = Q m β := by
  have hslice (V : Lp ℝ p (μ.prod (volume.restrict Ω))) :
      ∀ᵐ t ∂μ, MemLp (fun z => V (t, z)) p (volume.restrict Ω) := by
    by_cases hpt : p = ⊤
    · subst p
      exact (Lp.memLp V).prodMk_left_top
    · exact (Lp.memLp V).prodMk_left hpt
  intro m
  induction m with
  | zero =>
    intro hm β
    have he : β = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    simpa only [he] using hroot
  | succ m ih =>
    intro hm β
    obtain ⟨i, γ, rfl⟩ : ∃ (i : Fin d) (γ : Fin m → Fin d), β = Fin.cons i γ :=
      ⟨β 0, Fin.tail β, (Fin.cons_self_tail β).symm⟩
    have hprev := ih (by omega) γ
    have hqw := hQ m (by omega) γ i
    rw [← hprev] at hqw
    apply Lp.ext_curry
    filter_upwards [hP m (by omega) γ i, hqw,
      hslice (P (m + 1) (Fin.cons i γ)), hslice (Q (m + 1) (Fin.cons i γ))] with t ht hu hv hw
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ ht hu (hv.locallyIntegrable hp) (hw.locallyIntegrable hp)

theorem exists_lp_weak_partial_tree_of_finite_orders
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    (U : Z × E → ℝ)
    (h : ∀ N : ℕ, ∃ P : ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p (μ.prod (volume.restrict Ω)),
      (P 0 (fun i => Fin.elim0 i) =ᵐ[μ.prod (volume.restrict Ω)] U) ∧
      ∀ m < N, ∀ β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => P (m + 1) (Fin.cons i β) (t, z)) (fun z => P m β (t, z)) Ω) :
    ∃ P : ∀ m : ℕ, (Fin m → Fin d) → Lp ℝ p (μ.prod (volume.restrict Ω)),
      (P 0 (fun i => Fin.elim0 i) =ᵐ[μ.prod (volume.restrict Ω)] U) ∧
      ∀ m β i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => P (m + 1) (Fin.cons i β) (t, z)) (fun z => P m β (t, z)) Ω := by
  choose T hT hTw using h
  let P := fun m β => T m m β
  refine ⟨P, hT 0, ?_⟩
  intro m β i
  have hroot : T (m + 1) 0 (fun i => Fin.elim0 i) = T m 0 (fun i => Fin.elim0 i) :=
    Lp.ext ((hT (m + 1)).trans (Filter.EventuallyEq.symm (hT m)))
  have he := eq_of_finite_weak_partial_trees hp hΩ m (T (m + 1)) (T m)
    (fun k hk γ j => hTw (m + 1) k (by omega) γ j) (hTw m) hroot m le_rfl β
  have hw := hTw (m + 1) m (by omega) β i
  rw [he] at hw
  exact hw

theorem continuousOn_wkpNorm_of_finite_weak_partial_tree
    {A : Type*} [TopologicalSpace A] {s : Set A}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set E} (hΩ : IsOpen Ω) (N : ℕ)
    (U : ∀ m : ℕ, (Fin m → Fin d) → A → Lp ℝ p (volume.restrict Ω))
    (hcont : ∀ m ≤ N, ∀ β, ContinuousOn (U m β) s)
    (hweak : ∀ m < N, ∀ β i, ∀ t ∈ s, DeGiorgi.HasWeakPartialDeriv i
      (U (m + 1) (Fin.cons i β) t) (U m β t) Ω) :
    ContinuousOn (fun t => (iteratedWeakSobolevNorm N p
      (U 0 (fun i => Fin.elim0 i) t) Ω).toReal) s := by
  have hp : 1 ≤ p := Fact.out
  have hmem : ∀ k n β, n + k ≤ N → ∀ t ∈ s, MemWkp k p (U n β t) Ω := by
    intro k
    induction k with
    | zero =>
      intro n β hn t ht
      exact Lp.memLp (U n β t)
    | succ k ih =>
      intro n β hn t ht
      exact memWkp_succ_of_hasWeakPartialDeriv hp hΩ (Lp.memLp (U n β t))
        (fun i => ih (n + 1) (Fin.cons i β) (by omega) t ht) (fun i => hweak n (by omega) β i t ht)
  have hnode : ∀ k n β, n + k ≤ N → ContinuousOn
      (fun t => (iteratedWeakSobolevNorm k p (U n β t) Ω).toReal) s := by
    intro k
    induction k with
    | zero =>
      intro n β hn
      simpa only [wkpNorm_zero, Lp.norm_def] using (hcont n (by omega) β).norm
    | succ k ih =>
      intro n β hn
      have heq : EqOn (fun t => (iteratedWeakSobolevNorm (k + 1) p (U n β t) Ω).toReal)
          (fun t => ‖U n β t‖ + ∑ i : Fin d,
            (iteratedWeakSobolevNorm k p (U (n + 1) (Fin.cons i β) t) Ω).toReal) s := by
        intro t ht
        have hu := hmem (k + 1) n β hn t ht
        have he (i : Fin d) : chosenWeakPartialOrZero p i (U n β t) Ω =ᵐ[volume.restrict Ω]
            U (n + 1) (Fin.cons i β) t :=
          DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
            (chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p i)
            (hweak n (by omega) β i t ht)
            ((chosenWeakPartialOrZero_memLp_of_mem hu.memW1p i).locallyIntegrable hp)
            ((Lp.memLp (U (n + 1) (Fin.cons i β) t)).locallyIntegrable hp)
        dsimp only
        rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial]
        simp_rw [wkpNorm_congr_ae hp hΩ (he _)]
        rw [ENNReal.toReal_add (Lp.memLp (U n β t)).ne
          (ENNReal.sum_ne_top.mpr fun i _ =>
            (wkpNorm_lt_top_of_memWkp (hmem k (n + 1) (Fin.cons i β) (by omega) t ht)).ne),
          ENNReal.toReal_sum (fun i _ =>
            (wkpNorm_lt_top_of_memWkp (hmem k (n + 1) (Fin.cons i β) (by omega) t ht)).ne)]
        rfl
      exact ((hcont n (by omega) β).norm.add
        (continuousOn_finsetSum _ fun i _ => ih (n + 1) (Fin.cons i β) (by omega))).congr heq
  exact hnode N 0 (fun i => Fin.elim0 i) (by omega)

theorem tendsto_wkpNorm_sub_of_finite_weak_partial_tree
    {A : Type*} [TopologicalSpace A] {s : Set A}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set E} (hΩ : IsOpen Ω) (N : ℕ)
    (U : ∀ m : ℕ, (Fin m → Fin d) → A → Lp ℝ p (volume.restrict Ω))
    (hcont : ∀ m ≤ N, ∀ β, ContinuousOn (U m β) s)
    (hweak : ∀ m < N, ∀ β i, ∀ t ∈ s, DeGiorgi.HasWeakPartialDeriv i
      (U (m + 1) (Fin.cons i β) t) (U m β t) Ω)
    {t₀ : A} (ht₀ : t₀ ∈ s) :
    Tendsto (fun t => (iteratedWeakSobolevNorm N p
      (fun z => U 0 (fun i => Fin.elim0 i) t z - U 0 (fun i => Fin.elim0 i) t₀ z) Ω).toReal)
      (𝓝[s] t₀) (𝓝 0) := by
  have hp : 1 ≤ p := Fact.out
  have hlp (m β t) : LocallyIntegrable (U m β t) (volume.restrict Ω) :=
    (Lp.memLp (U m β t)).locallyIntegrable hp
  have hw (m) (hm : m < N) (β i) (t) (ht : t ∈ s) : DeGiorgi.HasWeakPartialDeriv i
      (U (m + 1) (Fin.cons i β) t - U (m + 1) (Fin.cons i β) t₀ : Lp ℝ p (volume.restrict Ω))
      (U m β t - U m β t₀ : Lp ℝ p (volume.restrict Ω)) Ω := by
    have hadd := DeGiorgi.HasWeakPartialDeriv.add (hweak m hm β i t ht)
      (DeGiorgi.HasWeakPartialDeriv.const_smul (hweak m hm β i t₀ ht₀) (-1))
      (hlp m β t) (by simpa only [smul_eq_mul, neg_one_mul, Pi.neg_def] using (hlp m β t₀).neg)
      (hlp (m + 1) (Fin.cons i β) t)
      (by simpa only [smul_eq_mul, neg_one_mul, Pi.neg_def] using (hlp (m + 1) (Fin.cons i β) t₀).neg)
    have hsub : DeGiorgi.HasWeakPartialDeriv i
        (fun z => U (m + 1) (Fin.cons i β) t z - U (m + 1) (Fin.cons i β) t₀ z)
        (fun z => U m β t z - U m β t₀ z) Ω := by
      simpa only [Pi.add_def, smul_eq_mul, neg_one_mul, sub_eq_add_neg] using hadd
    exact hsub.congr_ae (Filter.EventuallyEq.symm (Lp.coeFn_sub _ _))
      (Filter.EventuallyEq.symm (Lp.coeFn_sub _ _))
  have hc := continuousOn_wkpNorm_of_finite_weak_partial_tree hΩ N
    (fun m β t => U m β t - U m β t₀)
    (fun m hm β => (hcont m hm β).sub continuousOn_const) hw
  have hc' : ContinuousOn (fun t => (iteratedWeakSobolevNorm N p
      (fun z => U 0 (fun i => Fin.elim0 i) t z - U 0 (fun i => Fin.elim0 i) t₀ z) Ω).toReal) s :=
    hc.congr fun t _ => congrArg ENNReal.toReal
      (wkpNorm_congr_ae hp hΩ (Lp.coeFn_sub _ _)).symm
  have hlim := hc' t₀ ht₀
  simpa only [ContinuousWithinAt, sub_self, wkpNorm_zero_fun_zero hp hΩ, ENNReal.toReal_zero] using hlim


end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memWkp_of_finite_weak_partial_tree
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω) (K : ℕ)
    (u : ∀ n : ℕ, (Fin n → Fin d) → E → ℝ)
    (hLp : ∀ n ≤ K, ∀ α, MemLp (u n α) p (volume.restrict Ω))
    (hweak : ∀ n < K, ∀ α i,
      DeGiorgi.HasWeakPartialDeriv i (u (n + 1) (Fin.cons i α)) (u n α) Ω) :
    MemWkp K p (u 0 (fun i : Fin 0 => Fin.elim0 i)) Ω := by
  have hnode : ∀ k n α, n + k ≤ K → MemWkp k p (u n α) Ω := by
    intro k
    induction k with
    | zero =>
        intro n α hn
        exact hLp n (by omega) α
    | succ k ih =>
        intro n α hn
        apply memWkp_succ_of_hasWeakPartialDeriv hp hΩ (hLp n (by omega) α)
        · intro i
          exact ih (n + 1) (Fin.cons i α) (by omega)
        · intro i
          exact hweak n (by omega) α i
  exact hnode K 0 (fun i : Fin 0 => Fin.elim0 i) (by omega)


end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
