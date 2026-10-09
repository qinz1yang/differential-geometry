import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyGlobal_S102
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyInst_S99

set_option autoImplicit false

/-! # CH12-S109 G1: `hCX3ext` without the speed clause

`Ψ s t y := E_{clamp t} (G s y)` with `G` the inverse family of S102 G1b, `C := D2`.  The core theorem
`hCX3ext_core_S109` produces `X`, `G` and the non-`Ψ` conjuncts (with an extra smallness level
`ε₁` for the speed clause of G3); `hCX3ext_noSpeed_edistOf_S109` assembles `Ψ` and all other conjuncts
of `[FROZEN v3] CH12-O40 hCX3ext`; `hCX3ext_noSpeed_S109` restates it at `⟨Hm.metric⟩` (`withS99%`). -/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential DifferentialGeometry.Geometry.Hyperbolic

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

omit [LocallyCompactSpace M] in
theorem scaledExp_zero_S109 (X : ∀ y : M, TangentSpace I y) (x : M) :
    scaledExp_S15 g hEnorm X 0 x = x := by
  simp only [scaledExp_S15, zero_smul]
  exact expMapIntrinsic_zero g hEnorm x

/-- the rebuilt two-time flow `Ψ s t = E_{clamp t} ∘ G s` (`G s = (E_{clamp s})⁻¹`). -/
def psi_S109 (X : ∀ y : M, TangentSpace I y) (G : ℝ → M → M) (s t : ℝ) (y : M) : M :=
  scaledExp_S15 g hEnorm X (clamp_S102 t) (G s y)

omit [LocallyCompactSpace M] in
theorem contMDiff_psi_S109 (X : ∀ y : M, TangentSpace I y)
    (hX : ContMDiff I I.tangent ∞ (secBundle_S15 X)) (G : ℝ → M → M)
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G q.1 q.2)) :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => psi_S109 g hEnorm X G q.1.1 q.1.2 q.2) :=
  contMDiff_scaledExp_S15 (J := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) g hEnorm
    (fun q : (ℝ × ℝ) × M => secBundle_S15 X (G q.1.1 q.2)) (fun q => clamp_S102 q.1.2)
    (hX.comp (hG.comp ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd)))
    (contMDiff_clamp_S102.comp (contMDiff_snd.comp contMDiff_fst))

omit [LocallyCompactSpace M] in
theorem psi_self_S109 (X : ∀ y : M, TangentSpace I y) (G : ℝ → M → M)
    (hG2 : ∀ μ y, scaledExp_S15 g hEnorm X (clamp_S102 μ) (G μ y) = y) (s : ℝ) (y : M) :
    psi_S109 g hEnorm X G s s y = y := hG2 s y

omit [LocallyCompactSpace M] in
theorem psi_cocycle_S109 (X : ∀ y : M, TangentSpace I y) (G : ℝ → M → M)
    (hG1 : ∀ μ x, G μ (scaledExp_S15 g hEnorm X (clamp_S102 μ) x) = x) (s t u : ℝ) (y : M) :
    psi_S109 g hEnorm X G t u (psi_S109 g hEnorm X G s t y) = psi_S109 g hEnorm X G s u y := by
  simp only [psi_S109, hG1]

omit [LocallyCompactSpace M] in
theorem psi_fixed_S109 (X : ∀ y : M, TangentSpace I y) (G : ℝ → M → M) {D2 : Set M}
    (hX0 : ∀ p, p ∉ D2 → X p = 0)
    (hG1 : ∀ μ x, G μ (scaledExp_S15 g hEnorm X (clamp_S102 μ) x) = x) (s t : ℝ) {y : M}
    (hy : y ∉ D2) : psi_S109 g hEnorm X G s t y = y := by
  have h1 : scaledExp_S15 g hEnorm X (clamp_S102 s) y = y :=
    scaledExp_zero_field_S102 g hEnorm X _ (hX0 y hy)
  have h2 : G s y = y := by
    have := hG1 s y
    rwa [h1] at this
  simp only [psi_S109, h2]
  exact scaledExp_zero_field_S102 g hEnorm X _ (hX0 y hy)

omit [LocallyCompactSpace M] in
theorem psi_zero_left_S109 (X : ∀ y : M, TangentSpace I y) (G : ℝ → M → M)
    (hG1 : ∀ μ x, G μ (scaledExp_S15 g hEnorm X (clamp_S102 μ) x) = x) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : M) :
    psi_S109 g hEnorm X G 0 t x = scaledExp_S15 g hEnorm X t x := by
  have h0 : G 0 x = x := by
    have := hG1 0 x
    rwa [clamp_zero_S102, scaledExp_zero_S109 g hEnorm] at this
  have ht' : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [psi_S109, h0, clamp_eq_self_S102 ht']

omit [LocallyCompactSpace M] in
theorem psi_zero_right_S109 (X : ∀ y : M, TangentSpace I y) (G : ℝ → M → M) (μ : ℝ) (p : M) :
    psi_S109 g hEnorm X G μ 0 p = G μ p := by
  simp only [psi_S109, clamp_zero_S102, scaledExp_zero_S109 g hEnorm]

theorem psi_displacement_S109 (X : ∀ y : M, TangentSpace I y) (G : ℝ → M → M)
    (hG2 : ∀ μ y, scaledExp_S15 g hEnorm X (clamp_S102 μ) (G μ y) = y) {ε : ℝ}
    (htan : ∀ p, tanLen_S15 g (secBundle_S15 X p) < ε) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1) (p : M) :
    riemannianEDistOf g p (psi_S109 g hEnorm X G μ 0 p) ≤ ENNReal.ofReal ε := by
  rw [psi_zero_right_S109 g hEnorm]
  have hμ' : μ ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := ⟨by linarith [hμ.1], by linarith [hμ.2]⟩
  have hq : scaledExp_S15 g hEnorm X μ (G μ p) = p := by
    have := hG2 μ p
    rwa [clamp_eq_self_S102 hμ'] at this
  rw [riemannianEDistOf_eq_riemannianEDist g hEnorm, Manifold.riemannianEDist_comm]
  have h := edist_scaledExp_le_S15 g hEnorm X μ (G μ p)
  rw [hq] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ tanLen_S15 g (secBundle_S15 X (G μ p)) := Real.sqrt_nonneg _
  have hμa : |μ| ≤ 1 := abs_le.mpr ⟨by linarith [hμ.1], hμ.2⟩
  calc |μ| * tanLen_S15 g (secBundle_S15 X (G μ p))
      ≤ 1 * tanLen_S15 g (secBundle_S15 X (G μ p)) := mul_le_mul_of_nonneg_right hμa h0
    _ ≤ ε := by rw [one_mul]; exact (htan _).le

/-- **Core.**  `X`, the inverse family `G`, and the non-`Ψ` conjuncts of `hCX3ext`; `X` is moreover
`C¹`-`ε₁`-small for a prescribed `ε₁ > 0` (used by the speed clause, G3 of S109). -/
theorem hCX3ext_core_S109 [ConnectedSpace M] (A : CkAtlas_S15 I M)
    {D1 D2 : Set M} (hD1 : IsCompact D1) (hD2 : IsCompact D2) (hD12 : D1 ⊆ interior D2)
    (hD2A : D2 ⊆ A.cover) (k : ℕ) (hk : 1 ≤ k) (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf g p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ (X : ∀ p : M, TangentSpace I p) (G : ℝ → M → M),
            ContMDiff I I.tangent ∞ (secBundle_S15 X) ∧ CkSmall_S15 g A X k ε ∧
            CkSmall_S15 g A X 1 ε₁ ∧
            (∀ p, p ∉ D2 → X p = 0) ∧ (∀ p ∈ D1, expMapIntrinsic g hEnorm p (X p) = Φ p) ∧
            ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G q.1 q.2) ∧
            (∀ μ x, G μ (scaledExp_S15 g hEnorm X (clamp_S102 μ) x) = x) ∧
            (∀ μ y, scaledExp_S15 g hEnorm X (clamp_S102 μ) (G μ y) = y) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A D2 k ε (scaledExp_S15 g hEnorm X t)) := by
  obtain ⟨O, hO, hD2O, ρ, hρ, χ, _, _, _, _, hfield⟩ :=
    exists_CkSmall_transfer_field_edistOf_S99 g hEnorm A hD1 hD2 hD12 k
  obtain ⟨δ, B, hδ, hB, hbound⟩ := transfer_isotopy_Ck_bound_CX3 g hEnorm A k
  obtain ⟨ε₀, hε₀, hinv⟩ := exists_inverse_family_S102 g hEnorm A hD2 hD2A
  refine ⟨O, hO, hD2O, ρ, hρ, fun ε hε => ?_⟩
  let σ : ℝ := min ε₀ (min δ (min ε₁ (min ε (ε / (2 * B)))))
  have hσ : 0 < σ := lt_min hε₀ (lt_min hδ (lt_min hε₁ (lt_min hε (by positivity))))
  have hσ₀ : σ ≤ ε₀ := min_le_left _ _
  have hσδ : σ ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hσ₁ : σ ≤ ε₁ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσε : σ ≤ ε :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hσB : σ ≤ ε / (2 * B) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨ε', hε', hfield⟩ := hfield σ hσ
  refine ⟨ε', hε', fun Φ hΦ hdist hclose => ?_⟩
  obtain ⟨v, _, _, hXs, hXΦ, hX0, hsmall⟩ := hfield Φ hΦ hdist hclose
  let X : ∀ p : M, TangentSpace I p := fun p => χ p • secOf_S15 v p
  obtain ⟨G, hGs, hG1, hG2⟩ := hinv X hXs hX0 (CkSmall_mono_CX3 g hsmall hk hσ₀)
  refine ⟨X, G, hXs, CkSmall_mono_CX3 g hsmall le_rfl hσε, CkSmall_mono_CX3 g hsmall hk hσ₁, hX0,
    hXΦ, hGs, hG1, hG2, ?_⟩
  intro t ht i x hx _
  have hb := hbound X hXs σ hσ.le hσδ hsmall t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    i x hx
  refine ⟨hb.1, fun j hj => lt_of_le_of_lt (hb.2 j hj) ?_⟩
  have := (le_div_iff₀ (mul_pos (by norm_num) hB)).mp hσB
  nlinarith

/-- **`hCX3ext` without the speed clause** (`[FROZEN v3] CH12-O40 hCX3ext` minus the speed conjunct),
generic form with `riemannianEDistOf g` edist clauses; `C := D2`, `Ψ := psi_S109 X G`.  The binders
`hD : IsCompact D` and `_hV : IsOpen V` are unused (kept for the frozen shape). -/
theorem hCX3ext_noSpeed_edistOf_S109 [ConnectedSpace M] (A : CkAtlas_S15 I M)
    {D D1 D2 V : Set M} (_hD : IsCompact D) (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hDD1 : D ⊆ D1) (hD12 : D1 ⊆ interior D2) (hD2A : D2 ⊆ A.cover) (_hV : IsOpen V)
    (hD2V : D2 ⊆ V) (k : ℕ) (hk : 1 ≤ k) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf g p (Φ p) < ENNReal.ofReal ρ) →
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
            C ⊆ V ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : M, Ψ 0 t x = scaledExp_S15 g hEnorm X t x) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A D2 k ε (scaledExp_S15 g hEnorm X t)) ∧
            (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : M,
              riemannianEDistOf g p (Ψ μ 0 p) ≤ ENNReal.ofReal ε) := by
  obtain ⟨O, hO, hD2O, ρ, hρ, hmain⟩ := hCX3ext_core_S109 g hEnorm A hD1 hD2 hD12 hD2A k hk 1 one_pos
  refine ⟨O, hO, hD2O, ρ, hρ, fun ε hε => ?_⟩
  obtain ⟨ε', hε', h⟩ := hmain ε hε
  refine ⟨ε', hε', fun Φ hΦ hdist hclose => ?_⟩
  obtain ⟨X, G, hXs, hsmall, _, hX0, hXΦ, hGs, hG1, hG2, hclose2⟩ := h Φ hΦ hdist hclose
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : M,
      psi_S109 g hEnorm X G 0 t x = scaledExp_S15 g hEnorm X t x :=
    fun t ht x => psi_zero_left_S109 g hEnorm X G hG1 ht x
  refine ⟨X, psi_S109 g hEnorm X G, D2, hXs, hsmall, hX0, hXΦ, hD2,
    contMDiff_psi_S109 g hEnorm X hXs G hGs, psi_self_S109 g hEnorm X G hG2,
    psi_cocycle_S109 g hEnorm X G hG1, fun s t y hy => psi_fixed_S109 g hEnorm X G hX0 hG1 s t hy,
    fun t ht x _ => heq t ht x, ?_, hD2V, heq, hclose2, ?_⟩
  · intro x hx
    rw [heq 1 ⟨zero_le_one, le_rfl⟩ x]
    simp only [scaledExp_S15, one_smul]
    exact hXΦ x (hDD1 hx)
  · intro μ hμ p
    exact psi_displacement_S109 g hEnorm X G hG2
      (fun q => tanLen_lt_of_CkSmall_S102 g A hD2A X hX0 hε hsmall q) hμ p

end Generic

universe u

/-- **`hCX3ext` without the speed clause at `⟨H.metric⟩`** (= `[FROZEN v3] CH12-O40 hCX3ext` minus
the speed conjunct; edist clauses `riemannianEDistOf Hm.metric`, as in S99). -/
theorem hCX3ext_noSpeed_S109 (Hm : FiniteVolumeHyperbolicModel.{u})
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
              riemannianEDistOf Hm.metric p (Ψ μ 0 p) ≤ ENNReal.ofReal ε) :=
  withS99% Hm as hE,
    hCX3ext_noSpeed_edistOf_S109 Hm.metric hE A hD hD1 hD2 hDD1 hD12 hD2A hV hD2V k hk

end GC.LongTime.Ch12
