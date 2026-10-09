import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SpeedBound_S109

set_option autoImplicit false

/-! # CH12-S109 G3: `hCX3ext_S109` = `[FROZEN v3] CH12-O40 hCX3ext` at `⟨Hm.metric⟩`

Assembly: QI lemma (`K`, `ε₀`), core theorem at smallness `ε / K` and `ε₁ := ε₀`, the rebuilt flow
`Ψ := psi_S109 X G`, `C := D2`, speed from `speed_bound_S109` (`K (ε/K)² ≤ ε²`). -/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential DifferentialGeometry.Geometry.Hyperbolic

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold 𝓘(ℝ, E) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hEnorm : IsMetricNorm g)

/-- **`hCX3ext`** (`[FROZEN v3] CH12-O40`), generic form with `riemannianEDistOf g` edist clauses.
The binders `_hD : IsCompact D` and `_hV : IsOpen V` are unused (frozen shape). -/
theorem hCX3ext_edistOf_S109 [ConnectedSpace M] (A : CkAtlas_S15 𝓘(ℝ, E) M)
    {D D1 D2 V : Set M} (_hD : IsCompact D) (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hDD1 : D ⊆ D1) (hD12 : D1 ⊆ interior D2) (hD2A : D2 ⊆ A.cover) (_hV : IsOpen V)
    (hD2V : D2 ⊆ V) (k : ℕ) (hk : 1 ≤ k) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : M → M, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf g p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ (X : ∀ p : M, TangentSpace 𝓘(ℝ, E) p) (Ψ : ℝ → ℝ → M → M) (C : Set M),
            ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (secBundle_S15 X) ∧ CkSmall_S15 g A X k ε ∧
            (∀ p, p ∉ D2 → X p = 0) ∧ (∀ p ∈ D1, expMapIntrinsic g hEnorm p (X p) = Φ p) ∧
            IsCompact C ∧ ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
              (fun q : (ℝ × ℝ) × M => Ψ q.1.1 q.1.2 q.2) ∧
            (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
            (∀ s t y, y ∉ C → Ψ s t y = y) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = scaledExp_S15 g hEnorm X t x) ∧
            (∀ x ∈ D, Ψ 0 1 x = Φ x) ∧
            C ⊆ V ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : M, Ψ 0 t x = scaledExp_S15 g hEnorm X t x) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A D2 k ε (scaledExp_S15 g hEnorm X t)) ∧
            (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : M,
              let v := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Ψ r 0 p) μ
                ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
              g.inner (Ψ μ 0 p) v v ≤ ε ^ 2) ∧
            (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : M,
              riemannianEDistOf g p (Ψ μ 0 p) ≤ ENNReal.ofReal ε) := by
  obtain ⟨ε₀, hε₀, K, hK1, hQI⟩ := quasi_isometry_S109 g hEnorm A hD2 hD2A
  obtain ⟨O, hO, hD2O, ρ, hρ, hmain⟩ := hCX3ext_core_S109 g hEnorm A hD1 hD2 hD12 hD2A k hk ε₀ hε₀
  have hK0 : 0 < K := by linarith
  refine ⟨O, hO, hD2O, ρ, hρ, fun ε hε => ?_⟩
  have hεK : ε / K ≤ ε := div_le_self hε.le hK1
  obtain ⟨ε', hε', h⟩ := hmain (ε / K) (div_pos hε hK0)
  refine ⟨ε', hε', fun Φ hΦ hdist hclose => ?_⟩
  obtain ⟨X, G, hXs, hsmall, hsmall1, hX0, hXΦ, hGs, hG1, hG2, hclose2⟩ := h Φ hΦ hdist hclose
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : M,
      psi_S109 g hEnorm X G 0 t x = scaledExp_S15 g hEnorm X t x :=
    fun t ht x => psi_zero_left_S109 g hEnorm X G hG1 ht x
  have htan : ∀ q, tanLen_S15 g (secBundle_S15 X q) < ε / K :=
    fun q => tanLen_lt_of_CkSmall_S102 g A hD2A X hX0 (div_pos hε hK0) hsmall q
  have hfin : K * (ε / K) ^ 2 ≤ ε ^ 2 := by
    have : K * (ε / K) ^ 2 = ε ^ 2 / K := by field_simp
    rw [this]
    exact div_le_self (sq_nonneg ε) hK1
  refine ⟨X, psi_S109 g hEnorm X G, D2, hXs, CkSmall_mono_CX3 g hsmall le_rfl hεK, hX0, hXΦ, hD2,
    contMDiff_psi_S109 g hEnorm X hXs G hGs, psi_self_S109 g hEnorm X G hG2,
    psi_cocycle_S109 g hEnorm X G hG1, fun s t y hy => psi_fixed_S109 g hEnorm X G hX0 hG1 s t hy,
    fun t ht x _ => heq t ht x, ?_, hD2V, heq, ?_, ?_, ?_⟩
  · intro x hx
    rw [heq 1 ⟨zero_le_one, le_rfl⟩ x]
    simp only [scaledExp_S15, one_smul]
    exact hXΦ x (hDD1 hx)
  · intro t ht i x hx hxD
    obtain ⟨h1, h2⟩ := hclose2 t ht i x hx hxD
    exact ⟨h1, fun j hj => (h2 j hj).trans_le hεK⟩
  · intro μ hμ p
    have h := speed_bound_S109 g hEnorm X hXs G hGs hG2 hK0.le
      (fun μ hμ q w => hQI X hXs hX0 hsmall1 μ hμ q w) htan hμ p
    exact le_trans h hfin
  · intro μ hμ p
    exact (psi_displacement_S109 g hEnorm X G hG2 htan hμ p).trans (ENNReal.ofReal_le_ofReal hεK)

end Generic

universe u

/-- **`hCX3ext_S109` = `[FROZEN v3] CH12-O40 hCX3ext` at `⟨Hm.metric⟩`** (`withS99%`, edist clauses
`riemannianEDistOf Hm.metric`; speed clause with `Manifold`-tangent `fromTangentSpace`).  Unused
binders (frozen shape): `hD : IsCompact D`, `hV : IsOpen V`. -/
theorem hCX3ext_S109 (Hm : FiniteVolumeHyperbolicModel.{u})
    (A : CkAtlas_S15 (𝓡 3) Hm.Carrier) {D D1 D2 V : Set Hm.Carrier}
    (hD : IsCompact D) (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hDD1 : D ⊆ D1) (hD12 : D1 ⊆ interior D2) (hD2A : D2 ⊆ A.cover) (hV : IsOpen V)
    (hD2V : D2 ⊆ V) (k : ℕ) (hk : 1 ≤ k) :
    withS99% Hm as hE,
    ∃ O : Set Hm.Carrier, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : Hm.Carrier → Hm.Carrier, ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf Hm.metric p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ (X : ∀ p : Hm.Carrier, TangentSpace (𝓡 3) p) (Ψ : ℝ → ℝ → Hm.Carrier → Hm.Carrier)
            (C : Set Hm.Carrier),
            ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (secBundle_S15 X) ∧ CkSmall_S15 Hm.metric A X k ε ∧
            (∀ p, p ∉ D2 → X p = 0) ∧ (∀ p ∈ D1, expMapIntrinsic Hm.metric hE p (X p) = Φ p) ∧
            IsCompact C ∧ ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
              (fun q : (ℝ × ℝ) × Hm.Carrier => Ψ q.1.1 q.1.2 q.2) ∧
            (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
            (∀ s t y, y ∉ C → Ψ s t y = y) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = scaledExp_S15 Hm.metric hE X t x) ∧
            (∀ x ∈ D, Ψ 0 1 x = Φ x) ∧
            C ⊆ V ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : Hm.Carrier, Ψ 0 t x = scaledExp_S15 Hm.metric hE X t x) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A D2 k ε (scaledExp_S15 Hm.metric hE X t)) ∧
            (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : Hm.Carrier,
              let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Ψ r 0 p) μ
                ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
              Hm.metric.inner (Ψ μ 0 p) v v ≤ ε ^ 2) ∧
            (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : Hm.Carrier,
              riemannianEDistOf Hm.metric p (Ψ μ 0 p) ≤ ENNReal.ofReal ε) :=
  withS99% Hm as hE,
    hCX3ext_edistOf_S109 Hm.metric hE A hD hD1 hD2 hDD1 hD12 hD2A hV hD2V k hk

end GC.LongTime.Ch12
