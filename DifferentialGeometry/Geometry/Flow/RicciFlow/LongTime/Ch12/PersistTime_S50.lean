import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

/-!
# CH12-S50 / P1: right-endpoint C^2 time continuity of the normalized family

For a `MetricSmoothUpTo` family `G` on `Icc a (a+ε0)` over a compact stage, the normalized metrics
`t⁻¹ • G t` converge to `a⁻¹ • G a` in `metricDerivNorm j` (j ≤ 2), uniformly in space, as `t ↓ a`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Riemannian
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12
universe u

/-- the time-dependent normalization `t⁻¹ • G t` (junk value `G t` for `t ≤ 0`). -/
def normFamily_S50 (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric) (t : ℝ) : Q.Metric :=
  if h : 0 < t then scaleMetric t⁻¹ (inv_pos.mpr h) (G t) else G t

theorem normFamily_S50_of_pos (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric) {t : ℝ}
    (ht : 0 < t) : normFamily_S50 Q G t = scaleMetric t⁻¹ (inv_pos.mpr ht) (G t) := by
  simp [normFamily_S50, ht]

theorem metricSmoothUpTo_normFamily_S50 (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric)
    {a b : ℝ} (ha : 0 < a) (hG : Q.MetricSmoothUpTo G (Icc a b)) :
    Q.MetricSmoothUpTo (normFamily_S50 Q G) (Icc a b) := by
  intro p t ht
  obtain ⟨U, hU, hp, hUb, V, hV, htV, A, hA, hEq⟩ := hG p t ht
  have htpos : 0 < t := ha.trans_le ht.1
  refine ⟨U, hU, hp, hUb, V ∩ Ioi 0, hV.inter isOpen_Ioi, ⟨htV, htpos⟩,
    (fun z i j => z.1⁻¹ * A z i j), ?_, ?_⟩
  · intro i j
    have hinv : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞ (fun z : ℝ × Q.Carrier => z.1⁻¹)
        ((V ∩ Ioi 0) ×ˢ U) := by
      have h1 : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) {0}ᶜ := contDiffOn_inv ℝ
      have h2 := h1.contMDiffOn.comp (contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := ThreeModel)
        (M := ℝ) (N := Q.Carrier)).contMDiffOn
        (s := (V ∩ Ioi 0) ×ˢ U) (t := {0}ᶜ)
        (fun z hz => ne_of_gt hz.1.2)
      exact h2
    exact hinv.mul ((hA i j).mono (prod_mono_left inter_subset_left))
  · intro s hs x hx i j
    have hspos : 0 < s := hs.1.2
    change s⁻¹ * A (s, x) i j = _
    rw [hEq s ⟨hs.1.1, hs.2⟩ x hx i j, normFamily_S50_of_pos Q G hspos, scaleMetric_inner]

theorem exists_small_derivNorm_S50 (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric) {a ε0 : ℝ}
    (ha : 0 < a) (hε0 : 0 < ε0) (hG : Q.MetricSmoothUpTo G (Icc a (a + ε0))) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε1 : ℝ, 0 < ε1 ∧ ε1 ≤ ε0 ∧ ∀ t : ℝ, a < t → t ≤ a + ε1 → ∀ (x : Q.Carrier) (j : ℕ), j ≤ 2 →
      metricDerivNorm j (normFamily_S50 Q G t) (normFamily_S50 Q G a) (normFamily_S50 Q G a) x ≤ ε := by
  have hĜ := metricSmoothUpTo_normFamily_S50 Q G ha hG
  have hcomp : IsCompact (univ : Set Q.Carrier) := isCompact_univ
  have hj (j : ℕ) : ∀ᶠ t in 𝓝[Icc a (a + ε0)] a, ∀ x ∈ (univ : Set Q.Carrier),
      metricDerivNorm j (normFamily_S50 Q G t) (normFamily_S50 Q G a) (normFamily_S50 Q G a) x < ε := by
    have he (x : Q.Carrier) :
        {q : ℝ × Q.Carrier | metricDerivNorm j (normFamily_S50 Q G q.1) (normFamily_S50 Q G a)
          (normFamily_S50 Q G a) q.2 < ε} ∈ 𝓝[Icc a (a + ε0)] a ×ˢ 𝓝 x := by
      have h := (hĜ.metricDerivNorm_continuousOn Q (normFamily_S50 Q G a) (normFamily_S50 Q G a) j
        (a, x) ⟨⟨le_rfl, by linarith⟩, mem_univ x⟩).eventually_lt_const
        (by simpa only [metricDerivNorm_self] using hε)
      simp only [nhdsWithin_prod_eq, nhdsWithin_univ] at h
      exact h
    have hprod : ∀ᶠ q in 𝓝[Icc a (a + ε0)] a ×ˢ 𝓝ˢ (univ : Set Q.Carrier),
        metricDerivNorm j (normFamily_S50 Q G q.1) (normFamily_S50 Q G a)
          (normFamily_S50 Q G a) q.2 < ε :=
      hcomp.mem_prod_nhdsSet_of_forall (fun x _ => he x)
    exact hprod.curry.mono (fun _ ht => ht.self_of_nhdsSet)
  have hall : ∀ᶠ t in 𝓝[Icc a (a + ε0)] a, ∀ j ∈ Finset.range 3, ∀ x ∈ (univ : Set Q.Carrier),
      metricDerivNorm j (normFamily_S50 Q G t) (normFamily_S50 Q G a) (normFamily_S50 Q G a) x < ε :=
    (Filter.eventually_all_finset _).mpr (fun j _ => hj j)
  rw [nhdsWithin_Icc_eq_nhdsGE (by linarith)] at hall
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).mp hall
  refine ⟨min ((u - a) / 2) ε0, lt_min (by linarith [mem_Ioi.mp hu]) hε0, min_le_right _ _, ?_⟩
  intro t hat hta x j hj2
  have h1 : t ∈ Ico a u := ⟨hat.le, by
    have := min_le_left ((u - a) / 2) ε0
    linarith [mem_Ioi.mp hu]⟩
  exact (hsub h1 j (Finset.mem_range.mpr (by omega)) x (mem_univ x)).le

end GC.LongTime.Ch12
