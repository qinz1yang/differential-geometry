import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyInput_CX3

set_option autoImplicit false

/-! # CH12-CX3: transfer isotopy from Φ-level finite-order closeness -/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The chart-closeness predicate has the identity map as a witness for every
positive tolerance, including on nonempty chart balls and domains. -/
theorem CkCloseInAtlas_id_CX3 (A : CkAtlas_S15 I M) (D : Set M) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) : CkCloseInAtlas_CX3 A D k ε id := by
  intro i x hx _
  have hxT := A.closedBall_sub i hx
  refine ⟨(extChartAt I (A.ctr i)).map_target hxT, ?_⟩
  have hz : chartDisplacement_CX3 (I := I) (A.ctr i) id =ᶠ[𝓝 x] (fun _ => (0 : E)) := by
    filter_upwards [(isOpen_extChartAt_target (A.ctr i)).mem_nhds hxT] with y hy
    change extChartAt I (A.ctr i) ((extChartAt I (A.ctr i)).symm y) - y = 0
    rw [(extChartAt I (A.ctr i)).right_inv hy, sub_self]
  intro j _
  rw [(hz.iteratedFDeriv ℝ j).eq_of_nhds]
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hε

section Complete
variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
  [T2Space M] [SigmaCompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M] in
theorem CkSmall_mono_CX3 {A : CkAtlas_S15 I M} {X : ∀ p : M, TangentSpace I p}
    {k l : ℕ} {ε δ : ℝ} (h : CkSmall_S15 g A X k ε) (hlk : l ≤ k) (hεδ : ε ≤ δ) :
    CkSmall_S15 g A X l δ := by
  intro i x hx
  exact ⟨((h i x hx).1).trans_le hεδ,
    fun j hj => ((h i x hx).2 j (hj.trans hlk)).trans_le hεδ⟩

/-- **H1 with the small-field premise discharged.**  `A, D, D1, D2` precede
the requested accuracy; its input tolerance precedes `Φ`.  The normal-radius
hypothesis is precisely the existing S15 hypothesis, and higher jets are only
required on `D2`.  The coordinate estimate is for `E_t`; the ambient extension
agrees with `E_t` on `D` for `0 ≤ t ≤ 1`. -/
theorem transfer_isotopy_of_Ck_close_CX3 (A : CkAtlas_S15 I M)
    {D D1 D2 : Set M} (hD : IsCompact D) (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hDD1 : D ⊆ D1) (hD12 : D1 ⊆ interior D2) (hD2A : D2 ⊆ A.cover)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
          (∀ p ∈ O, Manifold.riemannianEDist I p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ (X : ∀ p : M, TangentSpace I p) (Ψ : ℝ → ℝ → M → M) (C : Set M),
            ContMDiff I I.tangent ∞ (secBundle_S15 X) ∧ CkSmall_S15 g A X k ε ∧
            (∀ p, p ∉ D2 → X p = 0) ∧ (∀ p ∈ D1, expMapIntrinsic g hEnorm p (X p) = Φ p) ∧
            IsCompact C ∧ ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
              (fun q : (ℝ × ℝ) × M => Ψ q.1.1 q.1.2 q.2) ∧
            (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
            (∀ s t y, y ∉ C → Ψ s t y = y) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = scaledExp_S15 g hEnorm X t x) ∧
            (∀ x ∈ D, Ψ 0 1 x = Φ x) ∧
            (∀ t : ℝ, |t| ≤ 2 → ∀ i : Fin A.n,
              ∀ x ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i), ∀ j ≤ k,
                ‖iteratedFDeriv ℝ j (chartDisplacement_CX3 (I := I) (A.ctr i)
                  (scaledExp_S15 g hEnorm X t)) x‖ < ε) := by
  obtain ⟨O, hO, hD2O, ρ, hρ, χ, _, _, _, _, hfield⟩ :=
    exists_CkSmall_transfer_field_CX3 g hEnorm A hD1 hD2 hD12 k
  obtain ⟨η, hη, hiso⟩ := transfer_isotopy_of_field_S15 g hEnorm A hD
    (hDD1.trans ((hD12.trans interior_subset).trans hD2A))
  obtain ⟨δ, B, hδ, hB, hbound⟩ := transfer_isotopy_Ck_bound_CX3 g hEnorm A k
  refine ⟨O, hO, hD2O, ρ, hρ, ?_⟩
  intro ε hε
  let σ : ℝ := min η (min δ (min ε (ε / (2 * B))))
  have hσ : 0 < σ := lt_min hη (lt_min hδ (lt_min hε (by positivity)))
  have hση : σ ≤ η := min_le_left _ _
  have hσδ : σ ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hσε : σ ≤ ε := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσB : σ ≤ ε / (2 * B) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨ε', hε', hfield⟩ := hfield σ hσ
  refine ⟨ε', hε', ?_⟩
  intro Φ hΦ hdist hclose
  obtain ⟨v, _, _, hXs, hXΦ, hX0, hsmall⟩ := hfield Φ hΦ hdist hclose
  let X : ∀ p : M, TangentSpace I p := fun p => χ p • secOf_S15 v p
  obtain ⟨Ψ, C, hC, hΨ, hself, hcoc, hsupp, heq, _, _⟩ :=
    hiso X hXs (CkSmall_mono_CX3 g hsmall hk hση)
  refine ⟨X, Ψ, C, hXs, CkSmall_mono_CX3 g hsmall le_rfl hσε, hX0, hXΦ,
    hC, hΨ, hself, hcoc, hsupp, heq, ?_, ?_⟩
  · intro x hx
    rw [heq 1 ⟨zero_le_one, le_rfl⟩ x hx, one_smul]
    exact hXΦ x (hDD1 hx)
  · intro t ht i x hx j hj
    have hb := (hbound X hXs σ hσ.le hσδ hsmall t ht i x hx).2 j hj
    refine lt_of_le_of_lt hb ?_
    have := (le_div_iff₀ (mul_pos (by norm_num) hB)).mp hσB
    nlinarith

end Complete
end GC.LongTime.Ch12
