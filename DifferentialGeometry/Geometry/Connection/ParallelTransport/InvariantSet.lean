import DifferentialGeometry.Geometry.Connection.AlongCurve

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

structure IsParallelSet (cov : CovariantDerivative I F V) (K : Set (TotalSpace F V)) : Prop where
  mem_of_parallel : ∀ {a b t₀ : ℝ} {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)},
    t₀ ∈ Icc a b → ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b) →
    MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b) →
    (∀ t ∈ Icc a b, cov.derivAlongWithin γ Z (Icc a b) t = 0) →
    (⟨γ t₀, Z t₀⟩ : TotalSpace F V) ∈ K →
    ∀ t ∈ Icc a b, (⟨γ t, Z t⟩ : TotalSpace F V) ∈ K

theorem IsParallelSet.mem_iff_of_parallel {cov : CovariantDerivative I F V}
    {K : Set (TotalSpace F V)} (hK : cov.IsParallelSet K)
    {a b t₀ t : ℝ} {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    (ht₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b))
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : TotalSpace F V)) (Icc a b))
    (hZpar : ∀ t ∈ Icc a b, cov.derivAlongWithin γ Z (Icc a b) t = 0) :
    (⟨γ t, Z t⟩ : TotalSpace F V) ∈ K ↔
      (⟨γ t₀, Z t₀⟩ : TotalSpace F V) ∈ K :=
  ⟨fun h => hK.mem_of_parallel ht hγ hZ hZpar h t₀ ht₀,
    fun h => hK.mem_of_parallel ht₀ hγ hZ hZpar h t ht⟩

theorem IsParallelSet.image_eq_of_parallel {cov : CovariantDerivative I F V}
    {K : Set (TotalSpace F V)} (hK : cov.IsParallelSet K)
    {a b t₀ : ℝ} {γ : ℝ → M} (ht₀ : t₀ ∈ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b))
    (T : ∀ t : ℝ, V (γ t₀) ≃L[ℝ] V (γ t))
    (hT₀ : ∀ v, T t₀ v = v)
    (hT : ∀ v, MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, T t v⟩ : TotalSpace F V)) (Icc a b))
    (hTpar : ∀ v t, t ∈ Icc a b →
      cov.derivAlongWithin γ (fun s => T s v) (Icc a b) t = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    T t '' {v : V (γ t₀) | (⟨γ t₀, v⟩ : TotalSpace F V) ∈ K} =
      {v : V (γ t) | (⟨γ t, v⟩ : TotalSpace F V) ∈ K} := by
  have hmem (v : V (γ t₀)) :=
    hK.mem_iff_of_parallel ht₀ ht hγ (hT v) (hTpar v)
  simp only [hT₀] at hmem
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hmem w).mpr hw
  · intro hv
    refine ⟨(T t).symm v, ?_, (T t).apply_symm_apply v⟩
    exact (hmem ((T t).symm v)).mp (by simpa only [(T t).apply_symm_apply, mem_ofPred_eq] using hv)

end CovariantDerivative
