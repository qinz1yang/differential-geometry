import DifferentialGeometry.Topology.Morse.ManifoldCellAttachment
import DifferentialGeometry.Topology.Morse.RegularIsotopy

namespace DifferentialGeometry.Topology.Morse

open Manifold Set ManifoldCellAttachment
open DifferentialGeometry.Analysis.ODE
open scoped Manifold ContDiff Topology

noncomputable section

private theorem morseFunction_value_at_morseChartPoint {m k : ℕ} (hk : k ≤ m + 1)
    (c : ℝ) {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) : f data.p = c := by
  rw [← data.hχ0]
  have hnorm := data.hnorm 0 (by simpa [CellAttachment.morseNorm] using (le_of_lt data.hRpos))
  rw [hnorm]
  have hsplit := CellAttachment.morseNormalForm_split hk c (0 : MorseModel (m + 1))
  rw [hsplit]
  have hpos : CellAttachment.posPart hk (0 : MorseModel (m + 1)) = 0 := by
    ext j
    simp [CellAttachment.posPart]
  have hneg : CellAttachment.negPart hk (0 : MorseModel (m + 1)) = 0 := by
    ext i
    simp [CellAttachment.negPart]
  rw [hpos, hneg]
  simp

theorem morseFunction_no_critical_at_upper_level_of_morseChart {m k : ℕ} (hk : k ≤ m + 1)
    (c ε a ε₀ : ℝ) {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hε₀ : 0 < ε₀) (haε : ε + 2 * ε₀ ≤ a)
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = data.p ∨ ¬ IsCriticalPointAt I f x)
    {x : M} (hx : f x = c + ε) : ¬ IsCriticalPointAt I f x := by
  have ha : ε ≤ a := by nlinarith only [haε, hε₀.le]
  have hmem : f x ∈ Set.Icc (c - a) (c + a) := by
    constructor <;> nlinarith only [hx, ha, hε.le]
  rcases hunique x hmem with hxp | hnc
  · exfalso
    have hpval : f data.p = c := morseFunction_value_at_morseChartPoint hk c data
    have : c = c + ε := by
      rw [hxp] at hx
      rw [hpval] at hx
      exact hx
    nlinarith only [hε, this]
  · exact hnc

theorem exists_morseRoundedSublevel_diffeomorph_upperSublevel_of_morseChart
    {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ R₀ R₁ R₁' a η ε₀ : ℝ) {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hε₀ : 0 < ε₀) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) (hδR : 40 * δ < R₁ ^ 2 - R₀ ^ 2)
    (hε₀le : 2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2))
    (hR₁₂ : R₁ < R₁') (hR₁₂R : R₁' ≤ data.R) (hR₁₂R' : R₁' ≤ data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (haε : ε + 2 * ε₀ ≤ a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = data.p ∨ ¬ IsCriticalPointAt I f x)
    (hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    (hη : r ^ 2 + δ ≤ 2 * η) (hηε₀ : 2 * ε₀ < η)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c) :=
      morseRoundedSublevelChartedSpace hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hR hR0 hbig
        hR₁₂ hR₁₂R hR₁₂R' hf hreg_f)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f (c + ε)) :=
      manifoldSublevelChartedSpace I f (c + ε) hf
        (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
          hε hε₀ haε hunique hx))
    (hchart₁ : ∀ y : SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c, hcs₁.chartAt y =
      (if h : morseRoundedFunction hk c ε r δ R₀ R₁ data y.1 = c then
        manifoldSublevelBoundaryChart I (morseRoundedFunction hk c ε r δ R₀ R₁ data) c y h
          (contMDiff_morseRoundedFunction hk c ε r δ R₀ R₁ R₁' data hf hR hR0 hR₁₂ hR₁₂R hR₁₂R')
          (fun _x hx => morseRoundedFunction_no_critical_at_level hk c ε r δ R₀ R₁ R₁' data
            hε hδ hδr hR hR0 hbig hR₁₂ hR₁₂R hR₁₂R' hreg_f hx)
        else manifoldSublevelInteriorChart I (morseRoundedFunction hk c ε r δ R₀ R₁ data) c y
          (lt_of_le_of_ne (show morseRoundedFunction hk c ε r δ R₀ R₁ data y.1 ≤ c from y.2) h)
          (contMDiff_morseRoundedFunction hk c ε r δ R₀ R₁ R₁' data hf hR hR0 hR₁₂ hR₁₂R hR₁₂R')) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f (c + ε), hcs₂.chartAt y =
      (if h : f y.1 = c + ε then
        manifoldSublevelBoundaryChart I f (c + ε) y h hf
          (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
            hε hε₀ haε hunique hx)
        else manifoldSublevelInteriorChart I f (c + ε) y
          (lt_of_le_of_ne (show f y.1 ≤ c + ε from y.2) h) hf) := by
      intro y
      rfl) :
    ∃ e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c) _ hcs₁
      (SublevelSpace f (c + ε)) _ hcs₂ (⊤ : ℕ∞),
      ∀ x : M, f x ≤ c - ε - η → ∀ hx : morseRoundedFunction hk c ε r δ R₀ R₁ data x ≤ c,
        (e ⟨x, hx⟩).1 = x ∧
        ∀ hy : f x ≤ c + ε, (e.symm ⟨x, hy⟩).1 = x := by
  classical
  letI := hcs₁
  letI := hcs₂
  let F : M → ℝ → ℝ := fun x s =>
    morseSublevelIsotopyFamily hk c ε r δ R₀ R₁ data s x
  have hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2) := by
    simpa [F] using (contMDiff_morseSublevelIsotopyFamily hk c ε r δ R₀ R₁ R₁' data hf
      hR hR0 hR₁₂ hR₁₂R hR₁₂R')
  let D : Set M := {x : M | f x ≤ c - ε - η}
  have hDcl : IsClosed D := by
    have hcont : Continuous f := hf.continuous
    have hpre : IsClosed (f ⁻¹' Set.Iic (c - ε - η)) :=
      IsClosed.preimage hcont isClosed_Iic
    simpa [D] using hpre
  have hDsep : ∀ x : M, x ∈ D → ∀ s : ℝ, s ∈ Set.Icc 0 1 → 2 * ε₀ < |F x s| := by
    intro x hx s hs
    exact morseSublevelIsotopyFamily_strip_of_deep hk c ε r δ R₀ R₁ R₁' η ε₀ data
      (le_of_lt hε) hδ hR₁₂ hR₁₂R hη hηε₀ (le_of_lt hε₀) hx s hs
  have hDsign : ∀ x : M, x ∈ D → (F x 0 ≤ 0 ↔ F x 1 ≤ 0) := by
    intro x hx
    exact morseSublevelIsotopyFamily_sign_deep hk c ε r δ R₀ R₁ R₁' η data
      (le_of_lt hε) hδ hR₁₂ hR₁₂R hη hx
  rcases exists_relDiffeomorph_sublevel_of_regularFamily (I := I) F hF ε₀ hε₀
    (isCompact_morseSublevelIsotopyFamily_strip hk c ε r δ R₀ R₁ R₁' a data hf ε₀
      hε hR hR0 hR₁₂ hR₁₂R hR₁₂R' haε hcompact)
    (fun q hq hs => no_critical_morseSublevelIsotopyFamily_strip hk c ε r δ R₀ R₁ R₁' a ε₀ data
      hε hδ hδr hR hR0 hbig hδR hε₀le hR₁₂ hR₁₂R hR₁₂R' hf haε hunique q.2 hs (x := q.1) hq)
    D hDcl hDsep hDsign with
    ⟨Φ, Ψ, hΦsm, hΨsm, hDfix, hsub_fwd, hsub_back, hbnd_fwd, hbnd_back,
      hstrict_fwd, hstrict_back, hinv_fwd, hinv_back⟩
  have hreg_round : ∀ x : M, morseRoundedFunction hk c ε r δ R₀ R₁ data x = c →
      ¬ IsCriticalPointAt I (morseRoundedFunction hk c ε r δ R₀ R₁ data) x := by
    intro x hx
    exact morseRoundedFunction_no_critical_at_level hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hR hR0 hbig
      hR₁₂ hR₁₂R hR₁₂R' hreg_f hx
  have hreg_upper : ∀ x : M, f x = c + ε → ¬ IsCriticalPointAt I f x := fun x hx =>
    morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data hε hε₀ haε hunique hx
  have hround_sm : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (morseRoundedFunction hk c ε r δ R₀ R₁ data) :=
    contMDiff_morseRoundedFunction hk c ε r δ R₀ R₁ R₁' data hf hR hR0 hR₁₂ hR₁₂R hR₁₂R'
  have hF0_le : ∀ x : M, morseRoundedFunction hk c ε r δ R₀ R₁ data x ≤ c → F x 0 ≤ 0 := by
    intro x hx
    dsimp [F, morseSublevelIsotopyFamily]
    simpa only [sub_zero, one_mul, zero_mul, add_zero] using sub_nonpos.mpr hx
  have hmap : ∀ x : M, morseRoundedFunction hk c ε r δ R₀ R₁ data x ≤ c → f (Φ x) ≤ c + ε := by
    intro x hx
    have hF1 : F (Φ x) 1 ≤ 0 := hsub_fwd x (hF0_le x hx)
    dsimp [F, morseSublevelIsotopyFamily] at hF1
    simp only [sub_self, zero_mul, one_mul, zero_add] at hF1
    simpa only [add_comm] using
      (sub_le_iff_le_add.mp (sub_nonpos.mp hF1))
  have hbnd : ∀ x : M, morseRoundedFunction hk c ε r δ R₀ R₁ data x = c → f (Φ x) = c + ε := by
    intro x hx
    have hF0 : F x 0 = 0 := by
      dsimp [F, morseSublevelIsotopyFamily]
      rw [hx]
      ring
    have hF1 : F (Φ x) 1 = 0 := hbnd_fwd x hF0
    dsimp [F, morseSublevelIsotopyFamily] at hF1
    simp only [sub_self, zero_mul, one_mul, zero_add] at hF1
    simpa only [add_comm] using
      (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hF1))
  have hstrict : ∀ x : M, morseRoundedFunction hk c ε r δ R₀ R₁ data x < c → f (Φ x) < c + ε := by
    intro x hx
    have hF0 : F x 0 < 0 := by
      dsimp [F, morseSublevelIsotopyFamily]
      simpa only [sub_zero, one_mul, zero_mul, add_zero] using sub_neg.mpr hx
    have hF1 : F (Φ x) 1 < 0 := hstrict_fwd x hF0
    dsimp [F, morseSublevelIsotopyFamily] at hF1
    simp only [sub_self, zero_mul, one_mul, zero_add] at hF1
    simpa only [add_comm] using
      (sub_lt_iff_lt_add.mp (sub_neg.mp hF1))
  have hF1_le : ∀ x : M, f x ≤ c + ε → F x 1 ≤ 0 := by
    intro x hx
    dsimp [F, morseSublevelIsotopyFamily]
    simp only [sub_self, zero_mul, one_mul, zero_add]
    apply sub_nonpos.mpr
    apply sub_le_iff_le_add.mpr
    simpa only [add_comm] using hx
  have hmap_back : ∀ x : M, f x ≤ c + ε → morseRoundedFunction hk c ε r δ R₀ R₁ data (Ψ x) ≤ c := by
    intro x hx
    have hF0 : F (Ψ x) 0 ≤ 0 := hsub_back x (hF1_le x hx)
    dsimp [F, morseSublevelIsotopyFamily] at hF0
    simp only [sub_zero, one_mul, zero_mul, add_zero] at hF0
    exact sub_nonpos.mp hF0
  have hbnd_back : ∀ x : M, f x = c + ε → morseRoundedFunction hk c ε r δ R₀ R₁ data (Ψ x) = c := by
    intro x hx
    have hF1 : F x 1 = 0 := by
      dsimp [F, morseSublevelIsotopyFamily]
      rw [hx]
      ring
    have hF0 : F (Ψ x) 0 = 0 := hbnd_back x hF1
    dsimp [F, morseSublevelIsotopyFamily] at hF0
    simp only [sub_zero, one_mul, zero_mul, add_zero] at hF0
    exact sub_eq_zero.mp hF0
  have hstrict_back : ∀ x : M, f x < c + ε → morseRoundedFunction hk c ε r δ R₀ R₁ data (Ψ x) < c := by
    intro x hx
    have hF1 : F x 1 < 0 := by
      dsimp [F, morseSublevelIsotopyFamily]
      simp only [sub_self, zero_mul, one_mul, zero_add]
      apply sub_neg.mpr
      apply sub_lt_iff_lt_add.mpr
      simpa only [add_comm] using hx
    have hF0 : F (Ψ x) 0 < 0 := hstrict_back x hF1
    dsimp [F, morseSublevelIsotopyFamily] at hF0
    simp only [sub_zero, one_mul, zero_mul, add_zero] at hF0
    exact sub_neg.mp hF0
  let toFun : SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c →
      SublevelSpace f (c + ε) :=
    fun x => ⟨Φ x.1, hmap x.1 x.2⟩
  let invFun : SublevelSpace f (c + ε) →
      SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c :=
    fun y => ⟨Ψ y.1, hmap_back y.1 y.2⟩
  let e : SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c ≃
      SublevelSpace f (c + ε) := by
    refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
    · intro x
      apply Subtype.ext
      exact hinv_fwd x.1 (hF0_le x.1 x.2)
    · intro y
      apply Subtype.ext
      exact hinv_back y.1 (hF1_le y.1 y.2)
  let d : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c) _ hcs₁
      (SublevelSpace f (c + ε)) _ hcs₂ (⊤ : ℕ∞) := by
    refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
    · simpa [toFun] using contMDiff_manifoldSublevelMap (I := I)
        (morseRoundedFunction hk c ε r δ R₀ R₁ data) f c (c + ε)
        hround_sm hf hreg_round hreg_upper Φ hΦsm hmap hbnd hstrict
        (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
    · simpa [invFun] using contMDiff_manifoldSublevelMap (I := I)
        f (morseRoundedFunction hk c ε r δ R₀ R₁ data) (c + ε) c
        hf hround_sm hreg_upper hreg_round Ψ hΨsm hmap_back hbnd_back hstrict_back
        (hcs₁ := hcs₂) (hcs₂ := hcs₁) (hchart₁ := hchart₂) (hchart₂ := hchart₁)
  refine ⟨d, ?_⟩
  intro x hx_global hx
  constructor
  · dsimp [d, e, toFun]
    exact (hDfix x hx_global).1
  · intro hy
    dsimp [d, e, invFun]
    exact (hDfix x hx_global).2

private theorem no_criticalPointAt_above_c_of_uniqueCritical {m : ℕ} {H : Type}
    [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (p : M) (c : ℝ) (hfp : f p = c) (a hlevel : ℝ)
    (hlevelpos : 0 < hlevel) (hlevela : hlevel ≤ a)
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x)
    {x : M} (hx : f x = c + hlevel) :
    ¬ IsCriticalPointAt I f x := by
  have hmem : f x ∈ Set.Icc (c - a) (c + a) := by
    constructor <;> nlinarith only [hx, hlevelpos, hlevela]
  rcases hunique x hmem with hxp | hnc
  · exfalso
    have : c = c + hlevel := by
      rw [hxp] at hx
      rw [hfp] at hx
      exact hx
    nlinarith only [this, hlevelpos]
  · exact hnc

private theorem regularFamily_f_sublevel_of_uniqueCritical
    {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (hfp : f p = c)
    (r ε a η ε₀ : ℝ)
    (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hε₀le : 2 * ε₀ < min ε (r ^ 2 / 2))
    (hr2a : r ^ 2 / 2 + 2 * ε₀ ≤ a)
    (haε : ε + 2 * ε₀ ≤ a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x)
    (hηε₀ : 2 * ε₀ < η) :
    ∃ Φ Ψ : M → M,
      ContMDiff I I (⊤ : ℕ∞) Φ ∧ ContMDiff I I (⊤ : ℕ∞) Ψ ∧
      (∀ x : M, f x ≤ c - ε - η → Φ x = x ∧ Ψ x = x) ∧
      (∀ x : M, f x ≤ c + r ^ 2 / 2 → f (Φ x) ≤ c + ε) ∧
      (∀ y : M, f y ≤ c + ε → f (Ψ y) ≤ c + r ^ 2 / 2) ∧
      (∀ x : M, f x = c + r ^ 2 / 2 → f (Φ x) = c + ε) ∧
      (∀ y : M, f y = c + ε → f (Ψ y) = c + r ^ 2 / 2) ∧
      (∀ x : M, f x < c + r ^ 2 / 2 → f (Φ x) < c + ε) ∧
      (∀ y : M, f y < c + ε → f (Ψ y) < c + r ^ 2 / 2) ∧
      (∀ x : M, f x ≤ c + r ^ 2 / 2 → Ψ (Φ x) = x) ∧
      (∀ y : M, f y ≤ c + ε → Φ (Ψ y) = y) := by
  classical
  let F : M → ℝ → ℝ := fun x s => f x - (c + r ^ 2 / 2 + s * (ε - r ^ 2 / 2))
  have hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2) := by
    have hfst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => q.1) := contMDiff_fst
    have hfs : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => f q.1) := hf.comp hfst
    have hsnd : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => q.2) := contMDiff_snd
    have hconst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => c + r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2)) := by
      simpa using ((contMDiff_const : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
        (fun _ : M × ℝ => c + r ^ 2 / 2)).add
        (hsnd.mul (contMDiff_const : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
          (fun _ : M × ℝ => ε - r ^ 2 / 2))))
    simpa [F] using hfs.sub hconst
  let D : Set M := {x : M | f x ≤ c - ε - η}
  have hDcl : IsClosed D := by
    have hcont : Continuous f := hf.continuous
    have hpre : IsClosed (f ⁻¹' Set.Iic (c - ε - η)) :=
      IsClosed.preimage hcont isClosed_Iic
    simpa [D] using hpre
  have hε₀ε : 2 * ε₀ < ε := (lt_min_iff.mp hε₀le).1
  have hε₀r : 2 * ε₀ < r ^ 2 / 2 := (lt_min_iff.mp hε₀le).2
  have ha : 0 < a := by nlinarith only [hr2a, hε₀]
  have hlevel_mem : ∀ q : M × ℝ, |F q.1 q.2| ≤ 2 * ε₀ → q.2 ∈ Set.Icc 0 1 →
      f q.1 ∈ Set.Icc (c - a) (c + a) := by
    intro q hq hs
    have hFhi : F q.1 q.2 ≤ 2 * ε₀ := (abs_le.mp hq).2
    have hFlo : -(2 * ε₀) ≤ F q.1 q.2 := (abs_le.mp hq).1
    have hlevlo : 2 * ε₀ < r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) := by
      rcases le_total ε (r ^ 2 / 2) with h | h
      · calc
          2 * ε₀ < ε := hε₀ε
          _ = (1 - q.2) * ε + q.2 * ε := by ring
          _ ≤ (1 - q.2) * (r ^ 2 / 2) + q.2 * ε :=
            add_le_add (mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hs.2)) le_rfl
          _ = r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) := by ring
      · calc
          2 * ε₀ < r ^ 2 / 2 := hε₀r
          _ = (1 - q.2) * (r ^ 2 / 2) + q.2 * (r ^ 2 / 2) := by ring
          _ ≤ (1 - q.2) * (r ^ 2 / 2) + q.2 * ε :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left h hs.1)
          _ = r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) := by ring
    have hlevhi : r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) ≤ max (r ^ 2 / 2) ε := by
      calc
        r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) =
            (1 - q.2) * (r ^ 2 / 2) + q.2 * ε := by ring
        _ ≤ (1 - q.2) * max (r ^ 2 / 2) ε + q.2 * max (r ^ 2 / 2) ε :=
          add_le_add
            (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr hs.2))
            (mul_le_mul_of_nonneg_left (le_max_right _ _) hs.1)
        _ = max (r ^ 2 / 2) ε := by ring
    have hmaxa : max (r ^ 2 / 2) ε + 2 * ε₀ ≤ a := by
      rcases le_total (r ^ 2 / 2) ε with h | h
      · rw [max_eq_right h]
        exact haε
      · rw [max_eq_left h]
        exact hr2a
    constructor
    · dsimp [F] at hFlo
      nlinarith only [hFlo, hlevlo, ha]
    · dsimp [F] at hFhi
      nlinarith only [hFhi, hlevhi, hmaxa]
  have hlevel_ne_c : ∀ q : M × ℝ, |F q.1 q.2| ≤ 2 * ε₀ → q.2 ∈ Set.Icc 0 1 →
      f q.1 ≠ c := by
    intro q hq hs
    have hFlo : -(2 * ε₀) ≤ F q.1 q.2 := (abs_le.mp hq).1
    have hlevlo : 2 * ε₀ < r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) := by
      rcases le_total ε (r ^ 2 / 2) with h | h
      · calc
          2 * ε₀ < ε := hε₀ε
          _ = (1 - q.2) * ε + q.2 * ε := by ring
          _ ≤ (1 - q.2) * (r ^ 2 / 2) + q.2 * ε :=
            add_le_add (mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hs.2)) le_rfl
          _ = r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) := by ring
      · calc
          2 * ε₀ < r ^ 2 / 2 := hε₀r
          _ = (1 - q.2) * (r ^ 2 / 2) + q.2 * (r ^ 2 / 2) := by ring
          _ ≤ (1 - q.2) * (r ^ 2 / 2) + q.2 * ε :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left h hs.1)
          _ = r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) := by ring
    dsimp [F] at hFlo
    nlinarith only [hFlo, hlevlo]
  have hstrip : IsCompact {q : M × ℝ | |F q.1 q.2| ≤ 2 * ε₀ ∧ q.2 ∈ Set.Icc 0 1} := by
    have hK : IsCompact ((f ⁻¹' Set.Icc (c - a) (c + a)) ×ˢ (Set.Icc (0 : ℝ) 1)) :=
      hcompact.prod isCompact_Icc
    have hcl : IsClosed {q : M × ℝ | |F q.1 q.2| ≤ 2 * ε₀ ∧ q.2 ∈ Set.Icc 0 1} := by
      have hcF : Continuous (fun q : M × ℝ => F q.1 q.2) := hF.continuous
      exact (isClosed_le (continuous_norm.comp hcF) continuous_const).inter
        (isClosed_Icc.preimage continuous_snd)
    refine hK.of_isClosed_subset hcl ?_
    intro q hq
    exact ⟨hlevel_mem q hq.1 hq.2, hq.2⟩
  have hreg : ∀ q : M × ℝ, |F q.1 q.2| ≤ 2 * ε₀ → q.2 ∈ Set.Icc 0 1 →
      ¬ IsCriticalPointAt I (fun x : M => F x q.2) q.1 := by
    intro q hq hs
    have hmem : f q.1 ∈ Set.Icc (c - a) (c + a) := hlevel_mem q hq hs
    rcases hunique q.1 hmem with hxp | hnc
    · exfalso
      exact (hlevel_ne_c q hq hs) (by rw [hxp]; exact hfp)
    · have hcrit_eq : IsCriticalPointAt I (fun x : M => F x q.2) q.1 ↔
          IsCriticalPointAt I f q.1 := by
        have hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : M => F x q.2) := regularFamilySliceSmooth I F hF q.2
        rw [isCriticalPointAt_iff_chart_fderiv I (fun x : M => F x q.2) hg q.1]
        rw [isCriticalPointAt_iff_chart_fderiv I f hf q.1]
        have hEq : (fun y : MorseModel (m + 1) => F ((extChartAt I q.1).symm y) q.2) =ᶠ[nhds ((extChartAt I q.1) q.1)] (fun y : MorseModel (m + 1) => f ((extChartAt I q.1).symm y) - (c + r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2))) := by
          filter_upwards with y
          simp [F]
        have hfe : fderiv ℝ (fun y : MorseModel (m + 1) => F ((extChartAt I q.1).symm y) q.2)
              ((extChartAt I q.1) q.1) =
            fderiv ℝ (fun y : MorseModel (m + 1) =>
              f ((extChartAt I q.1).symm y) - (c + r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2)))
              ((extChartAt I q.1) q.1) :=
          Filter.EventuallyEq.fderiv_eq hEq
        rw [hfe]
        have hsub := fderiv_sub_const (𝕜 := ℝ)
          (f := fun y : MorseModel (m + 1) => f ((extChartAt I q.1).symm y))
          (x := (extChartAt I q.1) q.1) (c := c + r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2))
        rw [← hsub]
      exact fun hc => hnc (hcrit_eq.mp hc)
  have hDsep : ∀ x : M, x ∈ D → ∀ s : ℝ, s ∈ Set.Icc 0 1 → 2 * ε₀ < |F x s| := by
    intro x hx s hs
    change f x ≤ c - ε - η at hx
    have hFneg : F x s ≤ -ε - η := by
      change f x - (c + r ^ 2 / 2 + s * (ε - r ^ 2 / 2)) ≤ -ε - η
      have hle : f x - c ≤ -ε - η := by linarith
      have hsum : 0 ≤ (1 - s) * (r ^ 2 / 2) + s * ε := by
        exact add_nonneg
          (mul_nonneg (sub_nonneg.mpr hs.2) (div_nonneg (sq_nonneg r) (by norm_num)))
          (mul_nonneg hs.1 hε.le)
      linarith [hle, hsum]
    have hFneg' : F x s < 0 := by nlinarith only [hFneg, hε, hε₀, hηε₀]
    have hFabs : ε + η ≤ |F x s| := by
      rw [abs_of_neg hFneg']
      linarith
    nlinarith only [hFabs, hε, hηε₀]
  have hDsign : ∀ x : M, x ∈ D → (F x 0 ≤ 0 ↔ F x 1 ≤ 0) := by
    intro x hx
    change f x ≤ c - ε - η at hx
    have h0 : F x 0 < 0 := by
      dsimp [F]
      nlinarith only [hx, sq_nonneg r, hε, hε₀, hηε₀]
    have h1 : F x 1 < 0 := by
      dsimp [F]
      nlinarith only [hx, hε, hε₀, hηε₀]
    constructor
    · intro _
      exact le_of_lt h1
    · intro _
      exact le_of_lt h0
  rcases exists_relDiffeomorph_sublevel_of_regularFamily (I := I) F hF ε₀ hε₀ hstrip hreg
    D hDcl hDsep hDsign with
    ⟨Φ, Ψ, hΦsm, hΨsm, hDfix, hsub_fwd, hsub_back, hbnd_fwd, hbnd_back,
      hstrict_fwd, hstrict_back, hinv_fwd, hinv_back⟩
  have hlevel_one : c + r ^ 2 / 2 + 1 * (ε - r ^ 2 / 2) = c + ε := by ring
  refine ⟨Φ, Ψ, hΦsm, hΨsm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hDfix x hx
  · intro x hx
    have hF1 : F (Φ x) 1 ≤ 0 := hsub_fwd x (by
      dsimp [F]
      simp only [zero_mul, add_zero]
      exact sub_nonpos.mpr hx)
    dsimp [F] at hF1
    simp only [hlevel_one] at hF1
    exact sub_nonpos.mp hF1
  · intro y hy
    have hF0 : F (Ψ y) 0 ≤ 0 := hsub_back y (by
      dsimp [F]
      simp only [hlevel_one]
      exact sub_nonpos.mpr hy)
    dsimp [F] at hF0
    simp only [zero_mul, add_zero] at hF0
    exact sub_nonpos.mp hF0
  · intro x hx
    have hF0 : F x 0 = 0 := by
      dsimp [F]
      rw [hx]
      ring
    have hF1 : F (Φ x) 1 = 0 := hbnd_fwd x hF0
    dsimp [F] at hF1
    simp only [hlevel_one] at hF1
    exact sub_eq_zero.mp hF1
  · intro y hy
    have hF1 : F y 1 = 0 := by
      dsimp [F]
      rw [hy]
      ring
    have hF0 : F (Ψ y) 0 = 0 := hbnd_back y hF1
    dsimp [F] at hF0
    simp only [zero_mul, add_zero] at hF0
    exact sub_eq_zero.mp hF0
  · intro x hx
    have hF1 : F (Φ x) 1 < 0 := hstrict_fwd x (by
      dsimp [F]
      simp only [zero_mul, add_zero]
      exact sub_neg.mpr hx)
    dsimp [F] at hF1
    simp only [hlevel_one] at hF1
    exact sub_neg.mp hF1
  · intro y hy
    have hF0 : F (Ψ y) 0 < 0 := hstrict_back y (by
      dsimp [F]
      simp only [hlevel_one]
      exact sub_neg.mpr hy)
    dsimp [F] at hF0
    simp only [zero_mul, add_zero] at hF0
    exact sub_neg.mp hF0
  · intro x hx
    exact hinv_fwd x (by
      dsimp [F]
      simp only [zero_mul, add_zero]
      exact sub_nonpos.mpr hx)
  · intro y hy
    exact hinv_back y (by
      dsimp [F]
      simp only [hlevel_one]
      exact sub_nonpos.mpr hy)


theorem exists_sublevel_diffeomorph_regularLevels_of_uniqueCriticalPoint
    {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (hfp : f p = c)
    (r ε a η ε₀ : ℝ)
    (hε : 0 < ε) (hε₀ : 0 < ε₀) (hr : 0 < r)
    (hε₀le : 2 * ε₀ < min ε (r ^ 2 / 2))
    (hr2a : r ^ 2 / 2 + 2 * ε₀ ≤ a)
    (haε : ε + 2 * ε₀ ≤ a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x)
    (hηε₀ : 2 * ε₀ < η)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f (c + r ^ 2 / 2)) :=
      manifoldSublevelChartedSpace I f (c + r ^ 2 / 2) hf (fun x hx =>
        no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a (r ^ 2 / 2)
          (by positivity) (by nlinarith only [hr2a, hε₀.le]) hunique hx))
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f (c + ε)) :=
      manifoldSublevelChartedSpace I f (c + ε) hf (fun x hx =>
        no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a ε hε
          (by nlinarith only [haε, hε₀.le]) hunique hx))
    (hchart₁ : ∀ y : SublevelSpace f (c + r ^ 2 / 2), hcs₁.chartAt y =
      (if h : f y.1 = c + r ^ 2 / 2 then
        manifoldSublevelBoundaryChart I f (c + r ^ 2 / 2) y h hf
          (fun x hx => no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a (r ^ 2 / 2)
            (by positivity) (by nlinarith only [hr2a, hε₀.le]) hunique hx)
        else manifoldSublevelInteriorChart I f (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show f y.1 ≤ c + r ^ 2 / 2 from y.2) h) hf) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f (c + ε), hcs₂.chartAt y =
      (if h : f y.1 = c + ε then
        manifoldSublevelBoundaryChart I f (c + ε) y h hf
          (fun x hx => no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a ε hε
            (by nlinarith only [haε, hε₀.le]) hunique hx)
        else manifoldSublevelInteriorChart I f (c + ε) y
          (lt_of_le_of_ne (show f y.1 ≤ c + ε from y.2) h) hf) := by
      intro y
      rfl) :
    ∃ e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace f (c + r ^ 2 / 2)) _ hcs₁
      (SublevelSpace f (c + ε)) _ hcs₂ (⊤ : ℕ∞),
      ∀ x : M, f x ≤ c - ε - η → ∀ hx : f x ≤ c + r ^ 2 / 2,
        (e ⟨x, hx⟩).1 = x ∧ ∀ hy : f x ≤ c + ε, (e.symm ⟨x, hy⟩).1 = x := by
  classical
  letI := hcs₁
  letI := hcs₂
  rcases regularFamily_f_sublevel_of_uniqueCritical f hf p c hfp r ε a η ε₀ hε hε₀ hε₀le
    hr2a haε hcompact hunique hηε₀ with
    ⟨Φ, Ψ, hΦsm, hΨsm, hDfix, hmap, hmap_back, hbnd, hbnd_back, hstrict, hstrict_back,
      hinv_fwd, hinv_back⟩
  have hreg₁ : ∀ x : M, f x = c + r ^ 2 / 2 → ¬ IsCriticalPointAt I f x := fun x hx =>
    no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a (r ^ 2 / 2)
      (by positivity) (by nlinarith only [hr2a, hε₀.le]) hunique hx
  have hreg₂ : ∀ x : M, f x = c + ε → ¬ IsCriticalPointAt I f x := fun x hx =>
    no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a ε hε
      (by nlinarith only [haε, hε₀.le]) hunique hx
  let toFun : SublevelSpace f (c + r ^ 2 / 2) → SublevelSpace f (c + ε) :=
    fun x => ⟨Φ x.1, hmap x.1 x.2⟩
  let invFun : SublevelSpace f (c + ε) → SublevelSpace f (c + r ^ 2 / 2) :=
    fun y => ⟨Ψ y.1, hmap_back y.1 y.2⟩
  let e : SublevelSpace f (c + r ^ 2 / 2) ≃ SublevelSpace f (c + ε) := by
    refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
    · intro x
      apply Subtype.ext
      exact hinv_fwd x.1 x.2
    · intro y
      apply Subtype.ext
      exact hinv_back y.1 y.2
  let d : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace f (c + r ^ 2 / 2)) _ hcs₁
      (SublevelSpace f (c + ε)) _ hcs₂ (⊤ : ℕ∞) := by
    refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
    · simpa [toFun] using contMDiff_manifoldSublevelMap (I := I)
        f f (c + r ^ 2 / 2) (c + ε) hf hf hreg₁ hreg₂ Φ hΦsm hmap hbnd hstrict
        (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
    · simpa [invFun] using contMDiff_manifoldSublevelMap (I := I)
        f f (c + ε) (c + r ^ 2 / 2) hf hf hreg₂ hreg₁ Ψ hΨsm hmap_back hbnd_back hstrict_back
        (hcs₁ := hcs₂) (hcs₂ := hcs₁) (hchart₁ := hchart₂) (hchart₂ := hchart₁)
  refine ⟨d, ?_⟩
  intro x hx_global hx
  constructor
  · dsimp [d, e, toFun]
    exact (hDfix x hx_global).1
  · intro hy
    dsimp [d, e, invFun]
    exact (hDfix x hx_global).2


private theorem morseHandleAdjunction_diffeomorph_upperSublevel_engine
    {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ θ R₀ R₀' R₁' R₁'' a η ε₀ : ℝ) {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hε₀ : 0 < ε₀) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hr : 0 < r)
    (hθ : 0 < θ) (hθr : θ < r ^ 2)
    (hR : R₀' < R₁') (hR0 : 0 ≤ R₀) (hR0lt : R₀ < data.R) (hR0' : 0 ≤ R₀')
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hbig' : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀' ^ 2)
    (hδR : 40 * δ < R₁' ^ 2 - R₀' ^ 2)
    (hε₀le : 2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2))
    (hR₁₂ : R₁' < R₁'') (hR₁₂R : R₁' ≤ data.R) (hR₁₂R'' : R₁'' ≤ data.R) (hR₁₂R''' : R₁'' ≤ data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (haε : ε + 2 * ε₀ ≤ a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = data.p ∨ ¬ IsCriticalPointAt I f x)
    (hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    (hη : r ^ 2 + δ ≤ 2 * η) (hηε₀ : 2 * ε₀ < η)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hRbig : r ^ 2 + 2 * ε + δ ≤ (data.R / 2) ^ 2)
    (hR₁big : 2 * (data.R / 2) ^ 2 - 2 * ε ≤ R₁' ^ 2)
    (hcont : Continuous f) :
    ∃ e₂ : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀' R₁' data) c) _
      (morseRoundedSublevelChartedSpace hk c ε r δ R₀' R₁' R₁'' data hε hδ hδr hR hR0' hbig'
        hR₁₂ hR₁₂R'' hR₁₂R''' hf hreg_f)
      (SublevelSpace f (c + ε)) _
      (manifoldSublevelChartedSpace I f (c + ε) hf
        (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
          hε hε₀ haε hunique hx))
      (⊤ : ℕ∞),
    ∃ e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace k (m + 1 - k)
        (morseAttachingEmbedding hk c ε r data hε
          hεr)) _
      (morseHandleAdjunctionChartedSpace hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
        hεr hεr' hR0 hR0lt
        hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f)
      (SublevelSpace f (c + ε)) _
      (manifoldSublevelChartedSpace I f (c + ε) hf
        (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
          hε hε₀ haε hunique hx))
      (⊤ : ℕ∞),
      (∀ z : Handle.AdjunctionSpace k (m + 1 - k)
          (morseAttachingEmbedding hk c ε r data hε
            hεr),
        (e z).1 = (e₂ (morseHandleAdjunctionEquivRoundedSublevel hk c ε r δ θ R₀ R₀' R₁' data
          hε hδ hθ hδr hθr hr
          hεr hεr'
          hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hcont z)).1) ∧
      (∀ x : M, f x ≤ c - ε - η → ∀ hx : f x ≤ c - ε,
        (e (Handle.lower (morseAttachingEmbedding hk c ε r data hε
          hεr)
          ⟨x, hx⟩)).1 = x) ∧
      (∀ y : M, (hydeep : f y ≤ c - ε - η) → ∀ hy : f y ≤ c + ε,
        ∀ z : Handle.AdjunctionSpace k (m + 1 - k)
            (morseAttachingEmbedding hk c ε r data hε
              hεr),
          e z = ⟨y, hy⟩ →
            z = Handle.lower (morseAttachingEmbedding hk c ε r data hε
              hεr)
              ⟨y, by
                have hsum : 0 ≤ r ^ 2 + δ := by positivity
                have hη0 : 0 ≤ η := by nlinarith only [hη, hsum]
                change f y ≤ c - ε
                nlinarith only [hydeep, hη0]⟩) := by
  classical
  let φ : Handle.AttachingRegion k (m + 1 - k) → SublevelSpace f (c - ε) :=
    morseAttachingEmbedding hk c ε r data hε
      hεr
  let h : Handle.AdjunctionSpace k (m + 1 - k) φ ≃ₜ
      SublevelSpace (morseRoundedFunction hk c ε r δ R₀' R₁' data) c :=
    morseHandleAdjunctionEquivRoundedSublevel hk c ε r δ θ R₀ R₀' R₁' data hε hδ hθ hδr hθr hr
      hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hcont
  letI : ChartedSpace (MorseHalfSpace m)
      (Handle.AdjunctionSpace k (m + 1 - k) φ) :=
    morseHandleAdjunctionChartedSpace hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr hεr
      hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀' R₁' data) c) :=
    morseRoundedSublevelChartedSpace hk c ε r δ R₀' R₁' R₁'' data hε hδ hδr hR hR0' hbig'
      hR₁₂ hR₁₂R'' hR₁₂R''' hf hreg_f
  letI : IsManifold (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀' R₁' data) c) :=
    morseRoundedSublevelIsManifold hk c ε r δ R₀' R₁' R₁'' data hε hδ hδr hR hR0' hbig'
      hR₁₂ hR₁₂R'' hR₁₂R''' hf hreg_f
  letI : ChartedSpace (MorseHalfSpace m) (SublevelSpace f (c + ε)) :=
    manifoldSublevelChartedSpace I f (c + ε) hf
      (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
        hε hε₀ haε hunique hx)
  let hD : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace k (m + 1 - k) φ) _
      (morseHandleAdjunctionChartedSpace hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr hεr
        hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀' R₁' data) c) _
      (morseRoundedSublevelChartedSpace hk c ε r δ R₀' R₁' R₁'' data hε hδ hδr hR hR0' hbig'
        hR₁₂ hR₁₂R'' hR₁₂R''' hf hreg_f)
      (⊤ : ℕ∞) :=
    morseHandleAdjunctionDiffeomorphRoundedSublevel hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr
      hθr hr hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont
      hf hreg_f
  rcases exists_morseRoundedSublevel_diffeomorph_upperSublevel_of_morseChart (m := m) (k := k)
    (hk := hk) (c := c) (ε := ε) (r := r) (δ := δ) (R₀ := R₀') (R₁ := R₁') (R₁' := R₁'')
    (a := a) (η := η) (ε₀ := ε₀) (data := data)
    hε hε₀ hδ hδr hR hR0' hbig' hδR hε₀le hR₁₂ hR₁₂R'' hR₁₂R''' hf haε hcompact hunique hreg_f
    hη hηε₀ (hcs₁ := morseRoundedSublevelChartedSpace hk c ε r δ R₀' R₁' R₁'' data hε hδ hδr
      hR hR0' hbig' hR₁₂ hR₁₂R'' hR₁₂R''' hf hreg_f) with ⟨e₂, hrel⟩
  let e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace k (m + 1 - k) φ) _
      (morseHandleAdjunctionChartedSpace hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr hεr
        hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f)
      (SublevelSpace f (c + ε)) _
      (manifoldSublevelChartedSpace I f (c + ε) hf
        (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
          hε hε₀ haε hunique hx))
      (⊤ : ℕ∞) :=
    hD.trans e₂
  have hcomm : ∀ z : Handle.AdjunctionSpace k (m + 1 - k) φ,
      (e z).1 = (e₂ (h z)).1 := by
    intro z
    change (e z).1 = (e₂.toFun (h z)).1
    rfl
  refine ⟨e₂, e, ?_, ?_, ?_⟩
  · intro z
    exact hcomm z
  · intro x hx_global hx
    have hlower : (h (Handle.lower φ ⟨x, hx⟩)).1 = x := by
      dsimp [φ, h]
      exact morseHandleAdjunctionEquivRoundedSublevel_lower_deep hk c ε r δ θ R₀ R₀' R₁' η data
        hε hδ hθ hδr hθr hr hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hcont hη
        hx hx_global
    have hmem : morseRoundedFunction hk c ε r δ R₀' R₁' data x ≤ c := by
      have hb := morseSublevelIsotopyFamily_le_neg_eta_of_deep hk c ε r δ R₀' R₁' R₁'' η data
        (le_of_lt hε) hδ hR₁₂ hR₁₂R'' hη hx_global 0 (by norm_num)
      have hF0 : morseSublevelIsotopyFamily hk c ε r δ R₀' R₁' data 0 x =
          morseRoundedFunction hk c ε r δ R₀' R₁' data x - c := by
        dsimp [morseSublevelIsotopyFamily]
        ring
      rw [hF0] at hb
      have hsum : 0 ≤ r ^ 2 + δ := by positivity
      have hη0 : 0 ≤ η := by
        have h2η : 0 ≤ 2 * η := le_trans hsum hη
        linarith only [h2η]
      linarith only [hb, hη0]
    have hfix : (e₂ ⟨x, hmem⟩).1 = x := (hrel x hx_global hmem).1
    have hH : h (Handle.lower φ ⟨x, hx⟩) = ⟨x, hmem⟩ := by
      apply Subtype.ext
      exact hlower
    change (e (Handle.lower φ ⟨x, hx⟩)).1 = x
    rw [hcomm (Handle.lower φ ⟨x, hx⟩)]
    rw [hH]
    exact hfix
  · intro y hy_global hy z hz
    have hmem : morseRoundedFunction hk c ε r δ R₀' R₁' data y ≤ c := by
      have hb := morseSublevelIsotopyFamily_le_neg_eta_of_deep hk c ε r δ R₀' R₁' R₁'' η data
        (le_of_lt hε) hδ hR₁₂ hR₁₂R'' hη hy_global 0 (by norm_num)
      have hF0 : morseSublevelIsotopyFamily hk c ε r δ R₀' R₁' data 0 y =
          morseRoundedFunction hk c ε r δ R₀' R₁' data y - c := by
        dsimp [morseSublevelIsotopyFamily]
        ring
      rw [hF0] at hb
      have hsum : 0 ≤ r ^ 2 + δ := by positivity
      have hη0 : 0 ≤ η := by
        have h2η : 0 ≤ 2 * η := le_trans hsum hη
        linarith only [h2η]
      linarith only [hb, hη0]
    have hfix : (e₂.symm ⟨y, hy⟩).1 = y := (hrel y hy_global hmem).2 hy
    have hmem_lower : f y ≤ c - ε := by
      have hsum : 0 ≤ r ^ 2 + δ := by positivity
      have hη0 : 0 ≤ η := by
        have h2η : 0 ≤ 2 * η := le_trans hsum hη
        linarith only [h2η]
      linarith only [hy_global, hη0]
    have hsymm : h.symm ⟨y, hmem⟩ = Handle.lower φ ⟨y, hmem_lower⟩ := by
      dsimp [φ]
      exact morseHandleAdjunctionEquivRoundedSublevel_symm_rel_deep hk c ε r δ θ R₀ R₀' R₁' η data
        hε hδ hθ hδr hθr hr hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hcont hη
        hy_global hmem
    have hfix' : e₂.symm ⟨y, hy⟩ = ⟨y, hmem⟩ := by
      apply Subtype.ext
      exact hfix
    have heq : h.symm (e₂.symm ⟨y, hy⟩) = Handle.lower φ ⟨y, hmem_lower⟩ := by
      rw [hfix']
      exact hsymm
    have hz' : e₂ (h z) = ⟨y, hy⟩ := by
      change e₂ (h z) = ⟨y, hy⟩
      simpa [e] using hz
    have hz'' : h z = ⟨y, hmem⟩ := by
      calc
        h z = e₂.symm (e₂ (h z)) := by simp
        _ = e₂.symm ⟨y, hy⟩ := by rw [hz']
        _ = ⟨y, hmem⟩ := hfix'
    have hfinal : z = Handle.lower φ ⟨y, hmem_lower⟩ := by
      calc
        z = h.symm (h z) := (h.symm_apply_apply z).symm
        _ = h.symm ⟨y, hmem⟩ := by rw [hz'']
        _ = Handle.lower φ ⟨y, hmem_lower⟩ := hsymm
    exact hfinal.trans (congrArg (Handle.lower φ) (by
      apply Subtype.ext
      rfl))

private theorem morseHandleAttachment_real_params (R R' a : ℝ)
    (hRpos : 0 < R) (ha : 0 < a) (haR : a ≤ R ^ 2 / 16) (hRR' : R < R') :
    ∃ ε r δ θ R₀ R₀' R₁' R₁'' η ε₀ η' R₁ : ℝ,
      0 < ε ∧ 0 < ε₀ ∧ 0 < δ ∧ δ < r ^ 2 ∧ 0 < r ∧ 0 < θ ∧ θ < r ^ 2 ∧
      R₀' < R₁' ∧ 0 ≤ R₀ ∧ R₀ < R ∧ 0 ≤ R₀' ∧
      2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2 ∧ 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀' ^ 2 ∧
      40 * δ < R₁' ^ 2 - R₀' ^ 2 ∧
      2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2) ∧
      R₁' < R₁'' ∧ R₁' ≤ R ∧ R₁'' ≤ R ∧ R₁'' ≤ R' ∧
      ε + 2 * ε₀ ≤ a ∧ r ^ 2 + δ ≤ 2 * η ∧ 2 * ε₀ < η ∧
      Real.sqrt (2 * ε + 2 * r ^ 2) ≤ R ∧
      Real.sqrt (2 * ε + 2 * r ^ 2) < R / 2 ∧
      r ^ 2 + 2 * ε + δ ≤ (R / 2) ^ 2 ∧
      2 * (R / 2) ^ 2 - 2 * ε ≤ R₁' ^ 2 ∧
      0 < η ∧ ε ≤ a ∧
      0 < η' ∧ 2 * η' ≤ r ^ 2 - θ ∧ η' < ε ∧
      R₀ < R₁ ∧ R₁ ≤ R ∧ R₁ ≤ R' ∧ 2 * R₀ < R₁ ∧
      R₀ < R₁' ∧ R₁' < R := by
  classical
  let ε := a / 4
  let s := Real.sqrt a
  let r := s / 2
  let δ := a / 20
  let θ := a / 20
  let η := a / 4
  let ε₀ := a / 200
  let η' := a / 20
  let R₀ := Real.sqrt (2 * a)
  let R₀' := R₀
  let R₁ := R
  let R₁' := 3 * R / 4
  let R₁'' := 7 * R / 8
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg a
  have hsq : s ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
  have hR2pos : 0 < R ^ 2 := sq_pos_of_pos hRpos
  have hr2 : r ^ 2 = a / 4 := by
    dsimp [r]
    rw [div_pow, hsq]
    norm_num
  have hR0sq : R₀ ^ 2 = 2 * a := by
    dsimp [R₀]
    exact Real.sq_sqrt (by positivity : 0 ≤ 2 * a)
  have h2εr : 2 * ε + 2 * r ^ 2 = a := by
    dsimp [ε]
    rw [hr2]
    ring
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδr : δ < r ^ 2 := by
    dsimp [δ]
    rw [hr2]
    linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hθr : θ < r ^ 2 := by
    dsimp [θ]
    rw [hr2]
    linarith
  have hR0 : 0 ≤ R₀ := by dsimp [R₀]; positivity
  have hR0' : 0 ≤ R₀' := by dsimp [R₀']; positivity
  have hR0lt : R₀ < R := by
    have hsq' : R₀ ^ 2 < R ^ 2 := by
      rw [hR0sq]
      linarith [haR, hR2pos]
    have habs : |R₀| < |R| := sq_lt_sq.mp hsq'
    rwa [abs_of_nonneg hR0, abs_of_nonneg (le_of_lt hRpos)] at habs
  have hR : R₀' < R₁' := by
    dsimp [R₁']
    have hsq' : R₀' ^ 2 < (3 * R / 4) ^ 2 := by
      rw [hR0sq]
      ring_nf
      linarith [haR, hR2pos]
    have habs : |R₀'| < |3 * R / 4| := sq_lt_sq.mp hsq'
    rwa [abs_of_nonneg hR0', abs_of_nonneg (by linarith : 0 ≤ 3 * R / 4)] at habs
  have hR₁₂ : R₁' < R₁'' := by
    dsimp [R₁', R₁'']
    linarith
  have hR₁₂R : R₁' ≤ R := by
    dsimp [R₁']
    linarith
  have hR₁₂R'' : R₁'' ≤ R := by
    dsimp [R₁'']
    linarith
  have hR₁₂R''' : R₁'' ≤ R' := by
    dsimp [R₁'']
    linarith
  have hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2 := by
    rw [hR0sq, hr2]
    dsimp [ε, δ]
    linarith
  have hbig' : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀' ^ 2 := by
    exact hbig
  have hδR : 40 * δ < R₁' ^ 2 - R₀' ^ 2 := by
    dsimp [δ, R₁']
    rw [hR0sq]
    ring_nf
    linarith [haR, hR2pos]
  have hε₀le₁ : min ε (r ^ 2 / 2) = r ^ 2 / 2 := by
    rw [hr2]
    dsimp [ε]
    apply min_eq_right
    linarith
  have hε₀le₂ : min (r ^ 2 / 2) ((r ^ 2 - δ) / 2) = (r ^ 2 - δ) / 2 := by
    rw [hr2]
    dsimp [δ]
    apply min_eq_right
    linarith
  have hε₀le : 2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2) := by
    rw [hε₀le₁, hε₀le₂, hr2]
    dsimp [ε₀, δ]
    linarith
  have hη : r ^ 2 + δ ≤ 2 * η := by
    rw [hr2]
    dsimp [δ, η]
    linarith
  have hηε₀ : 2 * ε₀ < η := by
    dsimp [ε₀, η]
    linarith
  have hηpos : 0 < η := by dsimp [η]; linarith
  have haε : ε + 2 * ε₀ ≤ a := by
    dsimp [ε, ε₀]
    linarith
  have hεa : ε ≤ a := by
    dsimp [ε]
    linarith
  have hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ R := by
    rw [h2εr]
    have hsq' : (Real.sqrt a) ^ 2 ≤ R ^ 2 := by
      rw [Real.sq_sqrt (le_of_lt ha)]
      linarith [haR, hR2pos]
    exact le_of_sq_le_sq hsq' (le_of_lt hRpos)
  have hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < R / 2 := by
    rw [h2εr]
    have hsq' : (Real.sqrt a) ^ 2 < (R / 2) ^ 2 := by
      rw [Real.sq_sqrt (le_of_lt ha)]
      linarith [haR, hR2pos]
    have habs : |Real.sqrt a| < |R / 2| := sq_lt_sq.mp hsq'
    rwa [abs_of_nonneg (Real.sqrt_nonneg a),
      abs_of_nonneg (by linarith : 0 ≤ R / 2)] at habs
  have hRbig : r ^ 2 + 2 * ε + δ ≤ (R / 2) ^ 2 := by
    rw [hr2]
    dsimp [ε, δ]
    ring_nf
    linarith [haR, hR2pos]
  have hR₁big : 2 * (R / 2) ^ 2 - 2 * ε ≤ R₁' ^ 2 := by
    dsimp [ε, R₁']
    ring_nf
    linarith [ha, hR2pos]
  have hη' : 0 < η' := by dsimp [η']; linarith
  have hηθ : 2 * η' ≤ r ^ 2 - θ := by
    rw [hr2]
    dsimp [η', θ]
    linarith
  have hηε : η' < ε := by
    dsimp [η', ε]
    linarith
  have hR0lt1 : R₀ < R₁ := by
    dsimp [R₁]
    exact hR0lt
  have hR1R : R₁ ≤ R := by
    dsimp [R₁]
    linarith
  have hR1R' : R₁ ≤ R' := by dsimp [R₁]; exact le_of_lt hRR'
  have h2R0lt1 : 2 * R₀ < R₁ := by
    dsimp [R₁]
    have hsq' : (2 * R₀) ^ 2 < R ^ 2 := by
      rw [mul_pow, hR0sq]
      ring_nf
      linarith [haR, hR2pos]
    have habs : |2 * R₀| < |R| := sq_lt_sq.mp hsq'
    rwa [abs_of_nonneg (mul_nonneg (by norm_num) hR0),
      abs_of_nonneg (le_of_lt hRpos)] at habs
  have hR0ltf : R₀ < R₁' := by
    dsimp [R₁']
    have hsq' : R₀ ^ 2 < (3 * R / 4) ^ 2 := by
      rw [hR0sq]
      ring_nf
      linarith [haR, hR2pos]
    have habs : |R₀| < |3 * R / 4| := sq_lt_sq.mp hsq'
    rwa [abs_of_nonneg hR0, abs_of_nonneg (by linarith : 0 ≤ 3 * R / 4)] at habs
  have hR₁₂R' : R₁' < R := by
    dsimp [R₁']
    linarith
  exact ⟨ε, r, δ, θ, R₀, R₀', R₁', R₁'', η, ε₀, η', R₁,
    hε, hε₀, hδ, hδr, hr, hθ, hθr, hR, hR0, hR0lt, hR0', hbig, hbig', hδR, hε₀le,
    hR₁₂, hR₁₂R, hR₁₂R'', hR₁₂R''', haε, hη, hηε₀, hεr, hεr', hRbig, hR₁big, hηpos, hεa,
    hη', hηθ, hηε, hR0lt1, hR1R, hR1R', h2R0lt1, hR0ltf, hR₁₂R'⟩

theorem exists_morseHandleAdjunction_diffeomorph_upperSublevel_of_morseChart
    {m k : ℕ} (hk : k ≤ m + 1)
    (c a : ℝ) {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ha : 0 < a) (haR : a ≤ data.R ^ 2 / 16) (hRR' : data.R < data.R')
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = data.p ∨ ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)] :
    ∃ ε : ℝ, ∃ hε : 0 < ε,
      ∃ r : ℝ, ∃ h : 0 < r ∧ Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R,
      ∃ η : ℝ, ∃ hηpos : 0 < η,
      ∃ hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x,
      ∃ hreg_upper : ∀ x : M, f x = c + ε → ¬ IsCriticalPointAt I f x,
      ∃ hcs : ChartedSpace (MorseHalfSpace m)
        (Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε h.2)),
      ∃ e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
        (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
        (morseModelWithCornersHalfSpace m)
        (Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε h.2)) _ hcs
        (SublevelSpace f (c + ε)) _
        (manifoldSublevelChartedSpace I f (c + ε) hf hreg_upper)
        (⊤ : ℕ∞),
        @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
          (Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε h.2)) _ hcs ∧
        @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
          (SublevelSpace f (c + ε)) _
          (manifoldSublevelChartedSpace I f (c + ε) hf hreg_upper) ∧
        @ContMDiff ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m)
          (SublevelSpace f (c - ε)) _ (manifoldSublevelChartedSpace I f (c - ε) hf hreg_f)
          (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m)
          (Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε h.2)) _ hcs
          (⊤ : ℕ∞)
          (Handle.lower (morseAttachingEmbedding hk c ε r data hε h.2)) ∧
        @ContMDiff ℝ _
          (EuclideanSpace ℝ (Fin ((k - 1) + 1)) × EuclideanSpace ℝ (Fin (((m + 1 - k - 1) + 1)))) _ _
          (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
          ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
            (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
          (Handle.StandardHandle k (m + 1 - k)) _ (Handle.standardHandleChartedSpace k (m + 1 - k))
          (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m)
          (Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε h.2)) _ hcs
          (⊤ : ℕ∞)
          (Handle.cell (morseAttachingEmbedding hk c ε r data hε h.2)) ∧
        (∀ x : M, f x ≤ c - ε - η → ∀ hx : f x ≤ c - ε,
          (e (Handle.lower (morseAttachingEmbedding hk c ε r data hε h.2) ⟨x, hx⟩)).1 = x) ∧
        (∀ y : M, (hydeep : f y ≤ c - ε - η) → ∀ hy : f y ≤ c + ε,
          ∀ z : Handle.AdjunctionSpace k (m + 1 - k)
              (morseAttachingEmbedding hk c ε r data hε h.2),
            e z = ⟨y, hy⟩ →
              z = Handle.lower (morseAttachingEmbedding hk c ε r data hε h.2)
                ⟨y, le_trans hydeep (by linarith [hηpos] : c - ε - η ≤ c - ε)⟩) := by
  classical
  rcases morseHandleAttachment_real_params data.R data.R' a data.hRpos ha haR hRR' with
    ⟨ε, r, δ, θ, R₀, R₀', R₁', R₁'', η, ε₀, η', R₁,
      hε, hε₀, hδ, hδr, hr, hθ, hθr, hR, hR0, hR0lt, hR0', hbig, hbig', hδR, hε₀le,
      hR₁₂, hR₁₂R, hR₁₂R'', hR₁₂R''', haε, hη, hηε₀, hεr, hεr', hRbig, hR₁big, hηpos, hεa,
      hη', hηθ, hηε, hR0lt1, hR1R, hR1R', h2R0lt1, hR0ltf, hR₁₂R'⟩
  have hcont : Continuous f := hf.continuous
  have hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x := by
    intro x hx
    have hfp : f data.p = c := morseFunction_value_at_morseChartPoint hk c data
    have hmem : f x ∈ Set.Icc (c - a) (c + a) := by
      constructor <;> linarith [hx, hε, hεa, ha]
    rcases hunique x hmem with hxp | hnc
    · exfalso
      have : c = c - ε := by
        rw [hxp] at hx
        rw [hfp] at hx
        exact hx
      linarith [hε, this]
    · exact hnc
  have hreg_upper : ∀ x : M, f x = c + ε → ¬ IsCriticalPointAt I f x := fun x hx =>
    no_criticalPointAt_above_c_of_uniqueCritical f data.p c
      (morseFunction_value_at_morseChartPoint hk c data) a ε hε hεa hunique hx
  rcases morseHandleAdjunction_diffeomorph_upperSublevel_engine (m := m) (k := k) (hk := hk)
    (c := c) (ε := ε) (r := r) (δ := δ) (θ := θ) (R₀ := R₀) (R₀' := R₀') (R₁' := R₁')
    (R₁'' := R₁'') (a := a) (η := η) (ε₀ := ε₀) (data := data)
    hε hε₀ hδ hδr hr hθ hθr hR hR0 hR0lt hR0' hbig hbig' hδR hε₀le hR₁₂ hR₁₂R hR₁₂R''
    hR₁₂R''' hf haε hcompact hunique hreg_f hη hηε₀ hεr hεr' hRbig hR₁big hcont with
    ⟨e₂, e, hcomm, hlower, hinj⟩
  have hmani_src : @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (Handle.AdjunctionSpace k (m + 1 - k)
        (morseAttachingEmbedding hk c ε r data hε hεr)) _
      (morseHandleAdjunctionChartedSpace hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
        hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f) :=
    morseHandleAdjunctionIsManifold hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr hεr
      hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f
  have hmani_tgt : @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (SublevelSpace f (c + ε)) _
      (manifoldSublevelChartedSpace I f (c + ε) hf hreg_upper) :=
    manifoldSublevelIsManifold I f (c + ε) hf hreg_upper
  have hlower_sm : @ContMDiff ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace f (c - ε)) _ (manifoldSublevelChartedSpace I f (c - ε) hf hreg_f)
      (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace k (m + 1 - k)
        (morseAttachingEmbedding hk c ε r data hε hεr)) _
      (morseHandleAdjunctionChartedSpace hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
        hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f)
      (⊤ : ℕ∞)
      (Handle.lower (morseAttachingEmbedding hk c ε r data hε hεr)) :=
    contMDiff_morseHandleAdjunctionLower hk c ε r δ θ η' R₀ R₁ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
      hη' hηθ hηε hεr hεr' hR0 hR0lt hR0lt1 hR1R hR1R' h2R0lt1 hbig hRbig hR0ltf hR hR0' hbig'
      hR₁big hR₁₂R hR₁₂R' hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f
  have hcell_sm : @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin ((k - 1) + 1)) × EuclideanSpace ℝ (Fin (((m + 1 - k - 1) + 1)))) _ _
      (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
      ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      (Handle.StandardHandle k (m + 1 - k)) _ (Handle.standardHandleChartedSpace k (m + 1 - k))
      (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace k (m + 1 - k)
        (morseAttachingEmbedding hk c ε r data hε hεr)) _
      (morseHandleAdjunctionChartedSpace hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
        hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f)
      (⊤ : ℕ∞)
      (Handle.cell (morseAttachingEmbedding hk c ε r data hε hεr)) :=
    contMDiff_morseHandleAdjunctionCell hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr hεr
      hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hRR' hcont hf hreg_f
  refine ⟨ε, hε, r, ⟨hr, hεr⟩, η, hηpos, hreg_f, hreg_upper,
    morseHandleAdjunctionChartedSpace hk c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
      hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f,
    e,
    ⟨hmani_src, hmani_tgt, hlower_sm, hcell_sm, hlower, hinj⟩⟩

theorem exists_morseHandleAdjunction_diffeomorph_upperSublevel_of_morseChart_zero
    {m : ℕ}
    (c a : ℝ) {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) 0 (zero_le (m + 1)) c I f)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ha : 0 < a) (haR : a ≤ data.R ^ 2 / 16) (hRR' : data.R < data.R')
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = data.p ∨ ¬ IsCriticalPointAt I f x)
    :
    ∃ ε : ℝ, ∃ hε : 0 < ε,
      ∃ r : ℝ, ∃ h : 0 < r ∧ Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R,
      ∃ η : ℝ, ∃ hηpos : 0 < η,
      ∃ hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x,
      ∃ hreg_upper : ∀ x : M, f x = c + ε → ¬ IsCriticalPointAt I f x,
      ∃ hcs : ChartedSpace (MorseHalfSpace m)
        (Handle.AdjunctionSpace 0 (m + 1) (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε h.2)),
      ∃ e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
        (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
        (morseModelWithCornersHalfSpace m)
        (Handle.AdjunctionSpace 0 (m + 1) (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε h.2)) _ hcs
        (SublevelSpace f (c + ε)) _
        (manifoldSublevelChartedSpace I f (c + ε) hf hreg_upper)
        (⊤ : ℕ∞),
        @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
          (Handle.AdjunctionSpace 0 (m + 1) (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε h.2)) _ hcs ∧
        @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
          (SublevelSpace f (c + ε)) _
          (manifoldSublevelChartedSpace I f (c + ε) hf hreg_upper) ∧
        @ContMDiff ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m)
          (SublevelSpace f (c - ε)) _ (manifoldSublevelChartedSpace I f (c - ε) hf hreg_f)
          (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m)
          (Handle.AdjunctionSpace 0 (m + 1) (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε h.2)) _ hcs
          (⊤ : ℕ∞)
          (Handle.lower (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε h.2)) ∧
        @ContMDiff ℝ _
          (EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin (((m + 1 - 1) + 1)))) _ _
          (ModelProd (EuclideanSpace ℝ (Fin 0)) (EuclideanHalfSpace ((m + 1 - 1) + 1))) _
          ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1)))
          (Handle.StandardHandle 0 (m + 1)) _ (Handle.standardHandleZeroChartedSpace (m + 1))
          (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m)
          (Handle.AdjunctionSpace 0 (m + 1) (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε h.2)) _ hcs
          (⊤ : ℕ∞)
          (Handle.cell (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε h.2)) ∧
        (∀ x : M, f x ≤ c - ε - η → ∀ hx : f x ≤ c - ε,
          (e (Handle.lower (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε h.2) ⟨x, hx⟩)).1 = x) ∧
        (∀ y : M, (hydeep : f y ≤ c - ε - η) → ∀ hy : f y ≤ c + ε,
          ∀ z : Handle.AdjunctionSpace 0 (m + 1)
              (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε h.2),
            e z = ⟨y, hy⟩ →
              z = Handle.lower (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε h.2)
                ⟨y, le_trans hydeep (by linarith [hηpos] : c - ε - η ≤ c - ε)⟩) := by
  classical
  rcases morseHandleAttachment_real_params data.R data.R' a data.hRpos ha haR hRR' with
    ⟨ε, r, δ, θ, R₀, R₀', R₁', R₁'', η, ε₀, η', R₁,
      hε, hε₀, hδ, hδr, hr, hθ, hθr, hR, hR0, hR0lt, hR0', hbig, hbig', hδR, hε₀le,
      hR₁₂, hR₁₂R, hR₁₂R'', hR₁₂R''', haε, hη, hηε₀, hεr, hεr', hRbig, hR₁big, hηpos, hεa,
      hη', hηθ, hηε, hR0lt1, hR1R, hR1R', h2R0lt1, hR0ltf, hR₁₂R'⟩
  have hcont : Continuous f := hf.continuous
  have hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x := by
    intro x hx
    have hfp : f data.p = c := morseFunction_value_at_morseChartPoint (zero_le (m + 1)) c data
    have hmem : f x ∈ Set.Icc (c - a) (c + a) := by
      constructor <;> linarith [hx, hε, hεa, ha]
    rcases hunique x hmem with hxp | hnc
    · exfalso
      have : c = c - ε := by
        rw [hxp] at hx
        rw [hfp] at hx
        exact hx
      linarith [hε, this]
    · exact hnc
  have hreg_upper : ∀ x : M, f x = c + ε → ¬ IsCriticalPointAt I f x := fun x hx =>
    no_criticalPointAt_above_c_of_uniqueCritical f data.p c
      (morseFunction_value_at_morseChartPoint (zero_le (m + 1)) c data) a ε hε hεa hunique hx
  rcases morseHandleAdjunction_diffeomorph_upperSublevel_engine (m := m) (k := 0) (hk := zero_le (m + 1))
    (c := c) (ε := ε) (r := r) (δ := δ) (θ := θ) (R₀ := R₀) (R₀' := R₀') (R₁' := R₁')
    (R₁'' := R₁'') (a := a) (η := η) (ε₀ := ε₀) (data := data)
    hε hε₀ hδ hδr hr hθ hθr hR hR0 hR0lt hR0' hbig hbig' hδR hε₀le hR₁₂ hR₁₂R hR₁₂R''
    hR₁₂R''' hf haε hcompact hunique hreg_f hη hηε₀ hεr hεr' hRbig hR₁big hcont with
    ⟨e₂, e, hcomm, hlower, hinj⟩
  have hmani_src : @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (Handle.AdjunctionSpace 0 (m + 1)
        (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε hεr)) _
      (morseHandleAdjunctionChartedSpace (zero_le (m + 1)) c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
        hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f) :=
    morseHandleAdjunctionIsManifold (zero_le (m + 1)) c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr hεr
      hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f
  have hmani_tgt : @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (SublevelSpace f (c + ε)) _
      (manifoldSublevelChartedSpace I f (c + ε) hf hreg_upper) :=
    manifoldSublevelIsManifold I f (c + ε) hf hreg_upper
  have hlower_sm : @ContMDiff ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace f (c - ε)) _ (manifoldSublevelChartedSpace I f (c - ε) hf hreg_f)
      (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace 0 (m + 1)
        (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε hεr)) _
      (morseHandleAdjunctionChartedSpace (zero_le (m + 1)) c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
        hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f)
      (⊤ : ℕ∞)
      (Handle.lower (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε hεr)) :=
    contMDiff_morseHandleAdjunctionLower (zero_le (m + 1)) c ε r δ θ η' R₀ R₁ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
      hη' hηθ hηε hεr hεr' hR0 hR0lt hR0lt1 hR1R hR1R' h2R0lt1 hbig hRbig hR0ltf hR hR0' hbig'
      hR₁big hR₁₂R hR₁₂R' hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f
  have hcell_sm : @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin (((m + 1 - 1) + 1)))) _ _
      (ModelProd (EuclideanSpace ℝ (Fin 0)) (EuclideanHalfSpace ((m + 1 - 1) + 1))) _
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1)))
      (Handle.StandardHandle 0 (m + 1)) _ (Handle.standardHandleZeroChartedSpace (m + 1))
      (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace 0 (m + 1)
        (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε hεr)) _
      (morseHandleAdjunctionChartedSpace (zero_le (m + 1)) c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
        hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f)
      (⊤ : ℕ∞)
      (Handle.cell (morseAttachingEmbedding (zero_le (m + 1)) c ε r data hε hεr)) :=
    contMDiff_morseHandleAdjunctionCell_zero c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr hεr
      hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hRR' hcont hf hreg_f
  refine ⟨ε, hε, r, ⟨hr, hεr⟩, η, hηpos, hreg_f, hreg_upper,
    morseHandleAdjunctionChartedSpace (zero_le (m + 1)) c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
      hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f,
    e,
    ⟨hmani_src, hmani_tgt, hlower_sm, hcell_sm, hlower, hinj⟩⟩

theorem exists_morseHandleAdjunction_diffeomorph_upperSublevel_of_morseChart_top
    {m : ℕ}
    (c a : ℝ) {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) (m + 1) (le_rfl : m + 1 ≤ m + 1) c I f)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (ha : 0 < a) (haR : a ≤ data.R ^ 2 / 16) (hRR' : data.R < data.R')
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = data.p ∨ ¬ IsCriticalPointAt I f x)
    :
    ∃ ε : ℝ, ∃ hε : 0 < ε,
      ∃ r : ℝ, ∃ h : 0 < r ∧ Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R,
      ∃ η : ℝ, ∃ hηpos : 0 < η,
      ∃ hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x,
      ∃ hreg_upper : ∀ x : M, f x = c + ε → ¬ IsCriticalPointAt I f x,
      ∃ hcs : ChartedSpace (MorseHalfSpace m)
        (Handle.AdjunctionSpace (m + 1) (m + 1 - (m + 1)) (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε h.2)),
      ∃ e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
        (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
        (morseModelWithCornersHalfSpace m)
        (Handle.AdjunctionSpace (m + 1) (m + 1 - (m + 1)) (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε h.2)) _ hcs
        (SublevelSpace f (c + ε)) _
        (manifoldSublevelChartedSpace I f (c + ε) hf hreg_upper)
        (⊤ : ℕ∞),
        @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
          (Handle.AdjunctionSpace (m + 1) (m + 1 - (m + 1)) (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε h.2)) _ hcs ∧
        @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
          (SublevelSpace f (c + ε)) _
          (manifoldSublevelChartedSpace I f (c + ε) hf hreg_upper) ∧
        @ContMDiff ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m)
          (SublevelSpace f (c - ε)) _ (manifoldSublevelChartedSpace I f (c - ε) hf hreg_f)
          (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m)
          (Handle.AdjunctionSpace (m + 1) (m + 1 - (m + 1)) (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε h.2)) _ hcs
          (⊤ : ℕ∞)
          (Handle.lower (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε h.2)) ∧
        @ContMDiff ℝ _
          (EuclideanSpace ℝ (Fin (((m + 1 - 1) + 1))) × EuclideanSpace ℝ (Fin 0)) _ _
          (ModelProd (EuclideanHalfSpace (((m + 1 - 1) + 1))) (EuclideanSpace ℝ (Fin 0))) _
          ((modelWithCornersEuclideanHalfSpace (((m + 1 - 1) + 1))).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))))
          (Handle.StandardHandle (m + 1) (m + 1 - (m + 1))) _ (Handle.standardHandleTopSubChartedSpace (m + 1))
          (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m)
          (Handle.AdjunctionSpace (m + 1) (m + 1 - (m + 1)) (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε h.2)) _ hcs
          (⊤ : ℕ∞)
          (Handle.cell (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε h.2)) ∧
        (∀ x : M, f x ≤ c - ε - η → ∀ hx : f x ≤ c - ε,
          (e (Handle.lower (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε h.2) ⟨x, hx⟩)).1 = x) ∧
        (∀ y : M, (hydeep : f y ≤ c - ε - η) → ∀ hy : f y ≤ c + ε,
          ∀ z : Handle.AdjunctionSpace (m + 1) (m + 1 - (m + 1))
              (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε h.2),
            e z = ⟨y, hy⟩ →
              z = Handle.lower (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε h.2)
                ⟨y, le_trans hydeep (by linarith [hηpos] : c - ε - η ≤ c - ε)⟩) := by
  classical
  rcases morseHandleAttachment_real_params data.R data.R' a data.hRpos ha haR hRR' with
    ⟨ε, r, δ, θ, R₀, R₀', R₁', R₁'', η, ε₀, η', R₁,
      hε, hε₀, hδ, hδr, hr, hθ, hθr, hR, hR0, hR0lt, hR0', hbig, hbig', hδR, hε₀le,
      hR₁₂, hR₁₂R, hR₁₂R'', hR₁₂R''', haε, hη, hηε₀, hεr, hεr', hRbig, hR₁big, hηpos, hεa,
      hη', hηθ, hηε, hR0lt1, hR1R, hR1R', h2R0lt1, hR0ltf, hR₁₂R'⟩
  have hcont : Continuous f := hf.continuous
  have hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x := by
    intro x hx
    have hfp : f data.p = c := morseFunction_value_at_morseChartPoint (le_rfl : m + 1 ≤ m + 1) c data
    have hmem : f x ∈ Set.Icc (c - a) (c + a) := by
      constructor <;> linarith [hx, hε, hεa, ha]
    rcases hunique x hmem with hxp | hnc
    · exfalso
      have : c = c - ε := by
        rw [hxp] at hx
        rw [hfp] at hx
        exact hx
      linarith [hε, this]
    · exact hnc
  have hreg_upper : ∀ x : M, f x = c + ε → ¬ IsCriticalPointAt I f x := fun x hx =>
    no_criticalPointAt_above_c_of_uniqueCritical f data.p c
      (morseFunction_value_at_morseChartPoint (le_rfl : m + 1 ≤ m + 1) c data) a ε hε hεa hunique hx
  rcases morseHandleAdjunction_diffeomorph_upperSublevel_engine (m := m) (k := m + 1) (hk := le_rfl)
    (c := c) (ε := ε) (r := r) (δ := δ) (θ := θ) (R₀ := R₀) (R₀' := R₀') (R₁' := R₁')
    (R₁'' := R₁'') (a := a) (η := η) (ε₀ := ε₀) (data := data)
    hε hε₀ hδ hδr hr hθ hθr hR hR0 hR0lt hR0' hbig hbig' hδR hε₀le hR₁₂ hR₁₂R hR₁₂R''
    hR₁₂R''' hf haε hcompact hunique hreg_f hη hηε₀ hεr hεr' hRbig hR₁big hcont with
    ⟨e₂, e, hcomm, hlower, hinj⟩
  have hmani_src : @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (Handle.AdjunctionSpace (m + 1) (m + 1 - (m + 1))
        (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε hεr)) _
      (morseHandleAdjunctionChartedSpace (le_rfl : m + 1 ≤ m + 1) c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
        hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f) :=
    morseHandleAdjunctionIsManifold (le_rfl : m + 1 ≤ m + 1) c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr hεr
      hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f
  have hmani_tgt : @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (SublevelSpace f (c + ε)) _
      (manifoldSublevelChartedSpace I f (c + ε) hf hreg_upper) :=
    manifoldSublevelIsManifold I f (c + ε) hf hreg_upper
  have hlower_sm : @ContMDiff ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace f (c - ε)) _ (manifoldSublevelChartedSpace I f (c - ε) hf hreg_f)
      (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace (m + 1) (m + 1 - (m + 1))
        (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε hεr)) _
      (morseHandleAdjunctionChartedSpace (le_rfl : m + 1 ≤ m + 1) c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
        hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f)
      (⊤ : ℕ∞)
      (Handle.lower (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε hεr)) :=
    contMDiff_morseHandleAdjunctionLower (le_rfl : m + 1 ≤ m + 1) c ε r δ θ η' R₀ R₁ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
      hη' hηθ hηε hεr hεr' hR0 hR0lt hR0lt1 hR1R hR1R' h2R0lt1 hbig hRbig hR0ltf hR hR0' hbig'
      hR₁big hR₁₂R hR₁₂R' hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f
  have hcell_sm : @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin (((m + 1 - 1) + 1))) × EuclideanSpace ℝ (Fin 0)) _ _
      (ModelProd (EuclideanHalfSpace (((m + 1 - 1) + 1))) (EuclideanSpace ℝ (Fin 0))) _
      ((modelWithCornersEuclideanHalfSpace (((m + 1 - 1) + 1))).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))))
      (Handle.StandardHandle (m + 1) (m + 1 - (m + 1))) _ (Handle.standardHandleTopSubChartedSpace (m + 1))
      (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace (m + 1) (m + 1 - (m + 1))
        (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε hεr)) _
      (morseHandleAdjunctionChartedSpace (le_rfl : m + 1 ≤ m + 1) c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
        hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f)
      (⊤ : ℕ∞)
      (Handle.cell (morseAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε hεr)) :=
    contMDiff_morseHandleAdjunctionCell_top c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr hεr
      hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hRR' hcont hf hreg_f
  refine ⟨ε, hε, r, ⟨hr, hεr⟩, η, hηpos, hreg_f, hreg_upper,
    morseHandleAdjunctionChartedSpace (le_rfl : m + 1 ≤ m + 1) c ε r δ θ R₀ R₀' R₁' R₁'' data hε hδ hθ hδr hθr hr
      hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hR₁₂ hR₁₂R'' hR₁₂R''' hcont hf hreg_f,
    e,
    ⟨hmani_src, hmani_tgt, hlower_sm, hcell_sm, hlower, hinj⟩⟩

end

end DifferentialGeometry.Topology.Morse
