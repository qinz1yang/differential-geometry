import DifferentialGeometry.Analysis.InnerProductSpace.ProjectedGraphRank

/-!
# All-preimage projected rank for a graph reference of any rank (TCP06; EGP07 in rank one)

Blueprint `master207B.tex`, TCP06 (`thm:fibration-actual-first-cloud`, lines 5600–5670), rank clause:
at a preimage `q` of a core point, `(TG)` gives `‖D - T L‖ ≤ e` for `D = D F_q` in the original metric,
`T = DΦ_i(a)` (its identity component gives `‖z‖ ≤ ‖T z‖`, and `‖T‖ ≤ C`) and `L = R_i Dη_i(q)` (TCP01's
Gram bound gives `(9/10)‖z‖ ≤ ‖L* z‖` and `‖L‖ ≤ 2`). FC06 (in the tree as
`ContinuousLinearMap.projected_range_surjective_of_approximation`, dimension-free) then gives: the
projection onto `im T` is onto, the normal error is at most `e`, and the nonzero singular values lie in
`[1/2, 3C]` once `e ≤ 2/5` and `e ≤ C`. The reference `F` is arbitrary (`ℝ²` for TCP06).
-/

set_option autoImplicit false

namespace ContinuousLinearMap

variable {E F H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem projected_rank_of_reference_graph (T : F →L[ℝ] H) (L : E →L[ℝ] F) (D : E →L[ℝ] H)
    {C e : ℝ} (hTlower : ∀ z, ‖z‖ ≤ ‖T z‖) (hT : ‖T‖ ≤ C)
    (hl : ∀ z, 9 / 10 * ‖z‖ ≤ ‖L.adjoint z‖) (hL : ‖L‖ ≤ 2)
    (herror : ‖D - T.comp L‖ ≤ e) (he : e ≤ 2 / 5) (heC : e ≤ C) :
    let P := T.range.orthogonalProjectionOnto.comp D
    Function.Surjective P ∧ ‖D - T.range.subtypeL.comp P‖ ≤ e ∧
      ∀ v ∈ P.kerᗮ, 1 / 2 * ‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ 3 * C * ‖v‖ := by
  obtain ⟨hs, hn, hb⟩ := projected_range_surjective_of_approximation T L D (a := 9 / 10)
    (b := C) (l := 2) (by norm_num) (by linarith) hl hTlower hT hL herror
  refine ⟨hs, hn, fun v hv => ?_⟩
  obtain ⟨h1, h2⟩ := hb v hv
  have hv0 := norm_nonneg v
  constructor
  · nlinarith
  · nlinarith

end ContinuousLinearMap
