import DifferentialGeometry.Analysis.Calculus.CurveDerivative
import DifferentialGeometry.Geometry.Connection.ParallelTransport.InvariantSet
import DifferentialGeometry.Geometry.Connection.ParallelTransport.VectorBundle

open Bundle Set
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I]

inductive IsPiecewiseParallelOn (cov : CovariantDerivative I F V)
    (γ : ℝ → M) (Z : ∀ t : ℝ, V (γ t)) : ℝ → ℝ → Prop where
  | of_parallel {a b : ℝ}
      (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b))
      (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
        (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b))
      (hparallel : ∀ t ∈ Icc a b, cov.derivAlongWithin γ Z (Icc a b) t = 0) :
      IsPiecewiseParallelOn cov γ Z a b
  | trans {a b c : ℝ} (hab : a < b) (hbc : b < c)
      (hleft : IsPiecewiseParallelOn cov γ Z a b)
      (hright : IsPiecewiseParallelOn cov γ Z b c) :
      IsPiecewiseParallelOn cov γ Z a c

theorem IsPiecewiseParallelOn.piecewiseContMDiffOn {cov : CovariantDerivative I F V}
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {a b : ℝ}
    (hZ : cov.IsPiecewiseParallelOn γ Z a b) :
    DifferentialGeometry.Analysis.Calculus.PiecewiseContMDiffOn I ∞ γ a b := by
  induction hZ with
  | of_parallel hγ _ _ => exact .of_contMDiffOn hγ
  | trans hab hbc _ _ ihleft ihright => exact .trans hab hbc ihleft ihright

theorem IsPiecewiseParallelOn.continuousOn {cov : CovariantDerivative I F V}
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {a b : ℝ}
    (hZ : cov.IsPiecewiseParallelOn γ Z a b) :
    ContinuousOn (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b) := by
  induction hZ with
  | of_parallel _ hZ _ => exact hZ.continuousOn
  | trans hab hbc _ _ ihleft ihright =>
      rw [← Icc_union_Icc_eq_Icc hab.le hbc.le]
      exact ihleft.union_of_isClosed ihright isClosed_Icc isClosed_Icc

theorem IsPiecewiseParallelOn.congr {cov : CovariantDerivative I F V}
    {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)} {a b : ℝ}
    (hZ : cov.IsPiecewiseParallelOn γ Z a b)
    (hWZ : ∀ t ∈ Icc a b, W t = Z t) : cov.IsPiecewiseParallelOn γ W a b := by
  induction hZ with
  | of_parallel hγ hZ hparallel =>
      refine .of_parallel hγ (hZ.congr ?_) ?_
      · intro t ht
        exact congrArg (fun v => (⟨γ t, v⟩ : TotalSpace F V)) (hWZ t ht)
      · intro t ht
        rw [cov.derivAlongWithin_congr hWZ (hWZ t ht)]
        exact hparallel t ht
  | trans hab hbc _ _ ihleft ihright =>
      exact .trans hab hbc
        (ihleft fun t ht => hWZ t ⟨ht.1, ht.2.trans hbc.le⟩)
        (ihright fun t ht => hWZ t ⟨hab.le.trans ht.1, ht.2⟩)

theorem IsPiecewiseParallelOn.mono {cov : CovariantDerivative I F V}
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {a b c d : ℝ}
    (hZ : cov.IsPiecewiseParallelOn γ Z a b) (hsub : Icc c d ⊆ Icc a b) :
    cov.IsPiecewiseParallelOn γ Z c d := by
  induction hZ generalizing c d with
  | of_parallel hγ hZ hparallel =>
      exact .of_parallel (hγ.mono hsub) (hZ.mono hsub)
        (fun t ht => cov.derivAlongWithin_eq_zero_mono
          (hZ t (hsub ht)) hsub (hparallel t (hsub ht)))
  | @trans a b e hab hbe _ _ ihleft ihright =>
      by_cases hcd : c ≤ d
      · by_cases hdb : d ≤ b
        · exact ihleft fun t ht => ⟨(hsub ht).1, ht.2.trans hdb⟩
        · by_cases hbc : b ≤ c
          · exact ihright fun t ht => ⟨hbc.trans ht.1, (hsub ht).2⟩
          · have hcb : c < b := lt_of_not_ge hbc
            have hbd : b < d := lt_of_not_ge hdb
            exact .trans hcb hbd
              (ihleft fun t ht =>
                ⟨(hsub (left_mem_Icc.mpr hcd)).1.trans ht.1, ht.2⟩)
              (ihright fun t ht =>
                ⟨ht.1, ht.2.trans (hsub (right_mem_Icc.mpr hcd)).2⟩)
      · exact ihleft (by simp only [Icc_eq_empty_of_lt (lt_of_not_ge hcd), empty_subset])

theorem IsPiecewiseParallelOn.piecewise {cov : CovariantDerivative I F V}
    {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)} {a b c : ℝ}
    (hZ : cov.IsPiecewiseParallelOn γ Z a b)
    (hW : cov.IsPiecewiseParallelOn γ W b c) (hab : a < b) (hbc : b < c)
    (hZW : Z b = W b) :
    cov.IsPiecewiseParallelOn γ (fun t => if t ≤ b then Z t else W t) a c := by
  refine .trans hab hbc (hZ.congr ?_) (hW.congr ?_)
  · intro t ht
    exact if_pos ht.2
  · intro t ht
    split_ifs with htb
    · have heq : t = b := le_antisymm htb ht.1
      subst t
      exact hZW
    · rfl

theorem IsParallelSet.mem_iff_of_piecewise_parallel {cov : CovariantDerivative I F V}
    {K : Set (TotalSpace F V)} (hK : cov.IsParallelSet K)
    {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)} {a b t₀ t : ℝ}
    (hZ : cov.IsPiecewiseParallelOn γ Z a b) (ht₀ : t₀ ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    (⟨γ t, Z t⟩ : TotalSpace F V) ∈ K ↔
      (⟨γ t₀, Z t₀⟩ : TotalSpace F V) ∈ K := by
  induction hZ generalizing t₀ t with
  | of_parallel hγ hZ hparallel =>
      exact hK.mem_iff_of_parallel ht₀ ht hγ hZ hparallel
  | @trans a b c hab hbc _ _ ihleft ihright =>
      have hmiddle (s : ℝ) (hs : s ∈ Icc a c) :
          (⟨γ s, Z s⟩ : TotalSpace F V) ∈ K ↔
            (⟨γ b, Z b⟩ : TotalSpace F V) ∈ K := by
        rcases le_total s b with hsb | hbs
        · exact ihleft (right_mem_Icc.mpr hab.le) ⟨hs.1, hsb⟩
        · exact ihright (left_mem_Icc.mpr hbc.le) ⟨hbs, hs.2⟩
      exact (hmiddle t ht).trans (hmiddle t₀ ht₀).symm

theorem IsParallelSet.image_eq_of_piecewise_parallel {cov : CovariantDerivative I F V}
    {K : Set (TotalSpace F V)} (hK : cov.IsParallelSet K)
    {γ : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (T : ∀ t : ℝ, V (γ t₀) ≃L[ℝ] V (γ t))
    (hT₀ : ∀ v, T t₀ v = v)
    (hT : ∀ v, cov.IsPiecewiseParallelOn γ (fun t => T t v) a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    T t '' {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K} =
      {v : V (γ t) | (⟨γ t, v⟩ : TotalSpace F V) ∈ K} := by
  have hmem (v : V (γ t₀)) := hK.mem_iff_of_piecewise_parallel (hT v) ht₀ ht
  simp only [hT₀] at hmem
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hmem w).mpr hw
  · intro hv
    refine ⟨(T t).symm v, ?_, (T t).apply_symm_apply v⟩
    exact (hmem ((T t).symm v)).mp (by simpa only [
      (T t).apply_symm_apply, mem_ofPred_eq] using hv)

theorem isParallelSet_iff_piecewise_parallel {cov : CovariantDerivative I F V}
    {K : Set (TotalSpace F V)} : cov.IsParallelSet K ↔
      ∀ {a b t₀ t : ℝ} {γ : ℝ → M} {Z : ∀ s : ℝ, V (γ s)},
        cov.IsPiecewiseParallelOn γ Z a b → t₀ ∈ Icc a b → t ∈ Icc a b →
        ((⟨γ t, Z t⟩ : TotalSpace F V) ∈ K ↔
          (⟨γ t₀, Z t₀⟩ : TotalSpace F V) ∈ K) := by
  constructor
  · intro hK a b t₀ t γ Z hZ ht₀ ht
    exact hK.mem_iff_of_piecewise_parallel hZ ht₀ ht
  · intro h
    refine ⟨fun ht₀ hγ hZ hpar hi t ht => ?_⟩
    exact (h (.of_parallel hγ hZ hpar) ht₀ ht).mpr hi

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

private theorem parallel_section_eq_piecewise_on_Icc
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)} {a b t₀ : ℝ}
    (hW : cov.IsPiecewiseParallelOn γ W a b)
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b))
    (hZpar : ∀ t ∈ Icc a b, cov.derivAlongWithin γ Z (Icc a b) t = 0)
    (ht₀ : t₀ ∈ Icc a b) (hinit : Z t₀ = W t₀) :
    ∀ t ∈ Icc a b, Z t = W t := by
  induction hW generalizing t₀ with
  | of_parallel hγ hW hWpar =>
      exact cov.parallel_section_eq_on_Icc hcov ht₀ (hγ.of_le (by simp))
        hZ hW hZpar hWpar hinit
  | @trans a b c hab hbc _ _ ihleft ihright =>
      have hleft : Icc a b ⊆ Icc a c := fun _ ht => ⟨ht.1, ht.2.trans hbc.le⟩
      have hright : Icc b c ⊆ Icc a c := fun _ ht => ⟨hab.le.trans ht.1, ht.2⟩
      have hZleft := hZ.mono hleft
      have hZright := hZ.mono hright
      have hZpl : ∀ t ∈ Icc a b, cov.derivAlongWithin γ Z (Icc a b) t = 0 :=
        fun t ht => cov.derivAlongWithin_eq_zero_mono (hZ t (hleft ht)) hleft
          (hZpar t (hleft ht))
      have hZpr : ∀ t ∈ Icc b c, cov.derivAlongWithin γ Z (Icc b c) t = 0 :=
        fun t ht => cov.derivAlongWithin_eq_zero_mono (hZ t (hright ht)) hright
          (hZpar t (hright ht))
      have hmiddle : Z b = W b := by
        rcases le_total t₀ b with ht₀b | hbt₀
        · exact ihleft hZleft hZpl ⟨ht₀.1, ht₀b⟩ hinit b (right_mem_Icc.mpr hab.le)
        · exact ihright hZright hZpr ⟨hbt₀, ht₀.2⟩ hinit b (left_mem_Icc.mpr hbc.le)
      intro t ht
      rcases le_total t b with htb | hbt
      · exact ihleft hZleft hZpl (right_mem_Icc.mpr hab.le) hmiddle t ⟨ht.1, htb⟩
      · exact ihright hZright hZpr (left_mem_Icc.mpr hbc.le) hmiddle t ⟨hbt, ht.2⟩

theorem piecewise_parallel_section_eq_on_Icc
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {Z W : ∀ t : ℝ, V (γ t)} {a b t₀ : ℝ}
    (hZ : cov.IsPiecewiseParallelOn γ Z a b)
    (hW : cov.IsPiecewiseParallelOn γ W a b)
    (ht₀ : t₀ ∈ Icc a b) (hinit : Z t₀ = W t₀) :
    ∀ t ∈ Icc a b, Z t = W t := by
  induction hZ generalizing t₀ with
  | of_parallel _ hZ hZpar =>
      exact parallel_section_eq_piecewise_on_Icc cov hcov hW hZ hZpar ht₀ hinit
  | @trans a b c hab hbc _ _ ihleft ihright =>
      have hWleft := hW.mono (show Icc a b ⊆ Icc a c from
        fun _ ht => ⟨ht.1, ht.2.trans hbc.le⟩)
      have hWright := hW.mono (show Icc b c ⊆ Icc a c from
        fun _ ht => ⟨hab.le.trans ht.1, ht.2⟩)
      have hmiddle : Z b = W b := by
        rcases le_total t₀ b with ht₀b | hbt₀
        · exact ihleft hWleft ⟨ht₀.1, ht₀b⟩ hinit b (right_mem_Icc.mpr hab.le)
        · exact ihright hWright ⟨hbt₀, ht₀.2⟩ hinit b (left_mem_Icc.mpr hbc.le)
      intro t ht
      rcases le_total t b with htb | hbt
      · exact ihleft hWleft (right_mem_Icc.mpr hab.le) hmiddle t ⟨ht.1, htb⟩
      · exact ihright hWright (left_mem_Icc.mpr hbc.le) hmiddle t ⟨hbt, ht.2⟩

private theorem exists_piecewise_parallel_transport_from_left
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {a b : ℝ}
    (hγ : DifferentialGeometry.Analysis.Calculus.PiecewiseContMDiffOn I ∞ γ a b)
    (horder : a ≤ b) :
    ∃ T : ∀ t : ℝ, V (γ a) ≃L[ℝ] V (γ t),
      (∀ v, T a v = v) ∧
      ∀ v, cov.IsPiecewiseParallelOn γ (fun t => T t v) a b := by
  classical
  induction hγ with
  | @of_contMDiffOn a b hγ =>
      have hγp : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
          (fun p : ℝ × ℝ => γ p.1) (Icc a b ×ˢ univ) :=
        hγ.comp contMDiffOn_fst (fun _ hp => hp.1)
      obtain ⟨T, hT₀, hTf, _, hTpar⟩ :=
        cov.exists_parallel_transport_on_Icc (IP := 𝓘(ℝ, ℝ))
          (γ := fun t (_ : ℝ) => γ t) hcov (left_mem_Icc.mpr horder) hγp
      refine ⟨fun t => T t 0, hT₀ 0, fun v => .of_parallel hγ ?_ (hTpar 0 v)⟩
      let e := trivializationAt F V (γ a)
      have he : γ a ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ a)
      have h := (hTf e).comp
        ((contMDiffOn_id.prodMk (contMDiffOn_const (c := (0 : ℝ)))).prodMk
          (contMDiffOn_const (c := e.continuousLinearMapAt ℝ (γ a) v)))
        (fun t ht => ⟨ht, he⟩)
      apply (h.mdifferentiableOn (by simp)).congr
      intro t _
      dsimp only [Function.comp_apply, id_eq]
      rw [e.symmL_continuousLinearMapAt he]
  | @trans a b c hab hbc _ _ ihleft ihright =>
      obtain ⟨S, hS₀, hS⟩ := ihleft hab.le
      obtain ⟨R, hR₀, hR⟩ := ihright hbc.le
      let T (t : ℝ) : V (γ a) ≃L[ℝ] V (γ t) :=
        if t ≤ b then S t else (S b).trans (R t)
      refine ⟨T, ?_, ?_⟩
      · intro v
        simpa only [T, if_pos hab.le] using hS₀ v
      · intro v
        have h := (hS v).piecewise (hR (S b v)) hab hbc (hR₀ (S b v)).symm
        apply h.congr
        intro t _
        dsimp only [T]
        split_ifs <;> rfl

theorem exists_piecewise_parallel_transport_on_Icc
    (cov : CovariantDerivative I F V) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {a b t₀ : ℝ}
    (hγ : DifferentialGeometry.Analysis.Calculus.PiecewiseContMDiffOn I ∞ γ a b)
    (ht₀ : t₀ ∈ Icc a b) :
    ∃ T : ∀ t : ℝ, V (γ t₀) ≃L[ℝ] V (γ t),
      (∀ v, T t₀ v = v) ∧
      ∀ v, cov.IsPiecewiseParallelOn γ (fun t => T t v) a b := by
  obtain ⟨S, hS₀, hS⟩ := exists_piecewise_parallel_transport_from_left cov hcov hγ
    (ht₀.1.trans ht₀.2)
  exact ⟨fun t => (S t₀).symm.trans (S t), fun v => (S t₀).apply_symm_apply v,
    fun v => hS ((S t₀).symm v)⟩

theorem IsParallelSet.exists_piecewise_parallel_transport_on_Icc
    {cov : CovariantDerivative I F V} {K : Set (TotalSpace F V)}
    (hK : cov.IsParallelSet K) (hcov : ContMDiffCovariantDerivative cov ∞)
    {γ : ℝ → M} {a b t₀ : ℝ}
    (hγ : DifferentialGeometry.Analysis.Calculus.PiecewiseContMDiffOn I ∞ γ a b)
    (ht₀ : t₀ ∈ Icc a b) :
    ∃ T : ∀ t : ℝ, V (γ t₀) ≃L[ℝ] V (γ t),
      (∀ v, T t₀ v = v) ∧
      (∀ v, cov.IsPiecewiseParallelOn γ (fun t => T t v) a b) ∧
      ∀ t ∈ Icc a b,
        T t '' {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K} =
          {v : V (γ t) | (⟨γ t, v⟩ : TotalSpace F V) ∈ K} := by
  obtain ⟨T, hT₀, hT⟩ := cov.exists_piecewise_parallel_transport_on_Icc hcov hγ ht₀
  exact ⟨T, hT₀, hT, fun _ ht => hK.image_eq_of_piecewise_parallel ht₀ T hT₀ hT ht⟩

theorem isParallelSet_iff_image_eq_piecewise_parallel
    {cov : CovariantDerivative I F V} (hcov : ContMDiffCovariantDerivative cov ∞)
    {K : Set (TotalSpace F V)} : cov.IsParallelSet K ↔
      ∀ {a b t₀ : ℝ} {γ : ℝ → M}, t₀ ∈ Icc a b →
        ∀ T : ∀ t : ℝ, V (γ t₀) ≃L[ℝ] V (γ t),
          (∀ v, T t₀ v = v) →
          (∀ v, cov.IsPiecewiseParallelOn γ (fun t => T t v) a b) →
          ∀ t ∈ Icc a b,
            T t '' {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K} =
              {v : V (γ t) | (⟨γ t, v⟩ : TotalSpace F V) ∈ K} := by
  constructor
  · intro hK a b t₀ γ ht₀ T hT₀ hT t ht
    exact hK.image_eq_of_piecewise_parallel ht₀ T hT₀ hT ht
  · intro h
    refine ⟨?_⟩
    intro a b t₀ γ Z ht₀ hγ hZ hZpar hi t ht
    obtain ⟨T, hT₀, hT⟩ := cov.exists_piecewise_parallel_transport_on_Icc hcov
      (.of_contMDiffOn hγ) ht₀
    have heq := cov.piecewise_parallel_section_eq_on_Icc hcov
      (.of_parallel hγ hZ hZpar) (hT (Z t₀)) ht₀ (hT₀ (Z t₀)).symm
    rw [heq t ht]
    change T t (Z t₀) ∈ {v : V (γ t) | (⟨γ t, v⟩ : TotalSpace F V) ∈ K}
    rw [← h ht₀ T hT₀ hT t ht]
    exact ⟨Z t₀, hi, rfl⟩

end CovariantDerivative
