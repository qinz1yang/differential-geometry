import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82PointSelection_CX11

/-!
# CH12-O30, G1a: space–time point picking for claim (C) of KL82.1

Source: corrected w-dependent local variant of KL 82.1 / Perelman II.6.5 (the point picking of
KL (45.5)–(45.6) with the age cutoff); not a verbatim transcription.  The reference PDFs named in
AGENTS.md are not on this machine; locators follow the CX11 report and the DELIVERIES records.

`kl82_select_O30` is purely order-theoretic: `P` stands for space–time points `(v, y)`,
`T` for those with `a < v ≤ top` and `y ∈ B_v(X(v), r)`, `T₀ ⊆ T` for those in a smaller ball
(margin `m`), `R` for scalar curvature and `d` for `d_v(X(v), y)`.  From one point of `T₀`
violating `R ≤ Cκ + B/(v − a)` it selects a violating point `x` of `T` whose weighted curvature
`R x (r − d x)²` is at least half of every other violating point's, and such that on the
backward age window `[time x − B/(2 R x), ·]` of the radial buffer every point of `T`
(violating or not) has `R ≤ 4 R x`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace GC.LongTime.Ch12

/-- **Space–time point picking for claim (C)** (KL (45.5)–(45.6) with the age cutoff). -/
theorem kl82_select_O30 {P : Type*} (T T₀ : Set P) (time R d : P → ℝ) {a κ C B r m : ℝ}
    (hκ : 0 < κ) (hC : 0 < C) (hB : 0 < B) (hm : 0 < m) (hT₀ : T₀ ⊆ T)
    (hT : ∀ p ∈ T, a < time p ∧ 0 ≤ d p ∧ d p < r)
    (hT₀m : ∀ p ∈ T₀, d p + m ≤ r) (hbdd : BddAbove (R '' T))
    (hseed : ∃ p ∈ T₀, C * κ + B / (time p - a) < R p) :
    ∃ x ∈ T, C * κ + B / (time x - a) < R x ∧ C * κ * m ^ 2 / 2 < R x * (r - d x) ^ 2 ∧
      (∀ p ∈ T, C * κ + B / (time p - a) < R p →
        R p * (r - d p) ^ 2 < 2 * (R x * (r - d x) ^ 2)) ∧
      ∀ p ∈ T, time x - B / (2 * R x) ≤ time p → d p ≤ d x + (r - d x) / 4 →
        R p ≤ 4 * R x := by
  classical
  set S : Set P := {p | p ∈ T ∧ C * κ + B / (time p - a) < R p} with hS
  have hbad_pos (p : P) (hp : p ∈ S) : 0 < R p := by
    have ht := (hT p hp.1).1
    have h1 : 0 < B / (time p - a) := div_pos hB (sub_pos.mpr ht)
    have h2 : 0 < C * κ := mul_pos hC hκ
    linarith [hp.2]
  have hgeom : ∀ p ∈ S, 0 < R p ∧ 0 ≤ d p ∧ d p < r := fun p hp =>
    ⟨hbad_pos p hp, (hT p hp.1).2.1, (hT p hp.1).2.2⟩
  have hQ : BddAbove (R '' S) := hbdd.mono (image_mono fun p hp => hp.1)
  have hΛ : 0 < C * κ * m ^ 2 := by positivity
  obtain ⟨p₀, hp₀, hbad₀⟩ := hseed
  have hseed' : ∃ x ∈ S, C * κ * m ^ 2 ≤ R x * (r - d x) ^ 2 := by
    refine ⟨p₀, ⟨hT₀ hp₀, hbad₀⟩, ?_⟩
    have ht := (hT p₀ (hT₀ hp₀)).1
    have h1 : 0 < B / (time p₀ - a) := div_pos hB (sub_pos.mpr ht)
    have hRC : C * κ ≤ R p₀ := by linarith
    have hmr : m ^ 2 ≤ (r - d p₀) ^ 2 :=
      pow_le_pow_left₀ hm.le (by linarith [hT₀m p₀ hp₀]) 2
    exact mul_le_mul hRC hmr (sq_nonneg _) (by linarith [mul_pos hC hκ])
  -- the selection, re-run to also export the score bound
  let score : P → ℝ := fun p => R p * (r - d p) ^ 2
  obtain ⟨K, hK⟩ := hQ
  have hne : S.Nonempty := ⟨p₀, ⟨hT₀ hp₀, hbad₀⟩⟩
  have hbddS : BddAbove (score '' S) := by
    refine ⟨K * r ^ 2, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    have hxg := hgeom x hx
    have hKpos : 0 < K := hxg.1.trans_le (hK ⟨x, hx, rfl⟩)
    exact mul_le_mul (hK ⟨x, hx, rfl⟩)
      (pow_le_pow_left₀ (sub_pos.mpr hxg.2.2).le (by linarith [hxg.2.1]) 2)
      (sq_nonneg _) hKpos.le
  obtain ⟨x₀, hx₀, hseed₀⟩ := hseed'
  have hΛsup : C * κ * m ^ 2 ≤ sSup (score '' S) :=
    hseed₀.trans (le_csSup hbddS ⟨x₀, hx₀, rfl⟩)
  have hsup : 0 < sSup (score '' S) := hΛ.trans_le hΛsup
  obtain ⟨v, hv, hvgt⟩ := exists_lt_of_lt_csSup (hne.image score)
    (show sSup (score '' S) / 2 < sSup (score '' S) by linarith)
  obtain ⟨x, hx, rfl⟩ := hv
  have hxg := hgeom x hx
  have hmargin : 0 < r - d x := sub_pos.mpr hxg.2.2
  have hscoreBound (y : P) (hy : y ∈ S) : score y < 2 * score x :=
    (le_csSup hbddS ⟨y, hy, rfl⟩).trans_lt (by linarith)
  have hxS : C * κ + B / (time x - a) < R x := hx.2
  have htx : a < time x := (hT x hx.1).1
  refine ⟨x, hx.1, hxS, by dsimp only [score] at hvgt ⊢; linarith,
    fun p hp hpbad => hscoreBound p ⟨hp, hpbad⟩, ?_⟩
  intro p hp hwin hdp
  by_cases hpS : C * κ + B / (time p - a) < R p
  · -- a violating point: the score bound and the radial buffer
    have hyg := hgeom p ⟨hp, hpS⟩
    have hbuffer : 3 * (r - d x) / 4 ≤ r - d p := by linarith
    have hbuffer2 : 9 * (r - d x) ^ 2 / 16 ≤ (r - d p) ^ 2 := by
      convert pow_le_pow_left₀ (by positivity : 0 ≤ 3 * (r - d x) / 4) hbuffer 2 using 1
      ring
    have hh := mul_le_mul_of_nonneg_left hbuffer2 hyg.1.le
    have hb := hscoreBound p ⟨hp, hpS⟩
    dsimp only [score] at hb
    have hsquare : 0 < (r - d x) ^ 2 := sq_pos_of_pos hmargin
    by_contra hn
    have hlarge : 4 * R x < R p := lt_of_not_ge hn
    have hprod := mul_pos (sub_pos.mpr hlarge) hsquare
    nlinarith
  · -- a non-violating point: the age cutoff
    have hpR : R p ≤ C * κ + B / (time p - a) := le_of_not_gt hpS
    have htp : a < time p := (hT p hp).1
    have hage : B ≤ R x * (time x - a) := by
      have h := (div_lt_iff₀ (sub_pos.mpr htx)).mp (show B / (time x - a) < R x by
        have : 0 < C * κ := mul_pos hC hκ
        linarith)
      linarith
    have hcut : B / (time p - a) * (time p - a) ≤ B := by
      rw [div_mul_cancel₀ _ (sub_pos.mpr htp).ne']
    have h2 := scalar_le_two_of_age_cutoff_CX11 hB hxg.1 hage hwin hcut
    have hCk : C * κ < R x := by
      have : 0 < B / (time x - a) := div_pos hB (sub_pos.mpr htx)
      linarith
    linarith

end GC.LongTime.Ch12
