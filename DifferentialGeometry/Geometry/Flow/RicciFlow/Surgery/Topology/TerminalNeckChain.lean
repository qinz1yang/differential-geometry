import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalBarrier
import DifferentialGeometry.Geometry.Neck.FiniteSelection
import DifferentialGeometry.Topology.Order.IntermediateValue

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal

private theorem exists_interval_between_levels
    {f : ℝ → ℝ} {ell A B : ℝ} (hell : 0 < ell)
    (hf : ContinuousOn f (Icc 0 ell)) (h0 : f 0 < A) (hAB : A < B) (hB : B < f ell) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < ell ∧ f a = A ∧ f b = B ∧
      ∀ t ∈ Icc a b, A ≤ f t ∧ f t ≤ B := by
  let h : ℝ × Unit → ℝ := fun p => f p.1
  have hh : ContinuousOn h (Icc 0 ell ×ˢ univ) := hf.comp continuous_fst.continuousOn (fun _ ht => ht.1)
  obtain ⟨b, hb, _, hfb, hbefore, hball⟩ :=
    hh.exists_first_level_of_compact hell.le (by intro _; exact h0.trans hAB)
      ⟨(), hB.le⟩
  have hbend : b < ell := lt_of_le_of_ne hb.2 (fun heq => hB.ne' (heq ▸ hfb))
  have hfb' : f b = B := hfb
  obtain ⟨a, ha, hfa, hafter⟩ :=
    (hf.mono (Icc_subset_Icc le_rfl hb.2)).exists_eq_and_forall_gt hb.1.le h0.le
      (hAB.trans_eq hfb'.symm)
  have hapos : 0 < a := lt_of_le_of_ne ha.1 (fun heq => h0.ne (heq ▸ hfa))
  refine ⟨a, b, hapos, ha.2, hbend, hfa, hfb', ?_⟩
  intro t ht
  constructor
  · rcases lt_or_eq_of_le ht.1 with hat | rfl
    · exact (hafter t ⟨hat, ht.2⟩).le
    · exact hfa.ge
  · rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hbefore t ⟨ha.1.trans ht.1, htb⟩ ()).le
    · exact hfb'.le


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_neck_chain_along_minimizer
    (L : G.TerminalLimitMetric) {eps δ α q C1 C2 A B ell : ℝ}
    (hδ : 0 < δ) (hα : α ≤ 1 / 20000) (hreserve : 13000 * δ ≤ α)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (hq : 0 < q) (hC2 : 1 ≤ C2)
    (hell : 0 < ell) (gamma : ℝ → G.terminalRegularOpen)
    (hcontinuous : ContinuousOn gamma (Icc 0 ell))
    (hmin : ∀ t ∈ Icc 0 ell, ∀ v ∈ Icc 0 ell,
      riemannianEDistOf L.metric (gamma t) (gamma v) = ENNReal.ofReal |t - v|)
    (hcanonical : ∀ t ∈ Ioo 0 ell, ∀ time ∈ Ioo a s, q < G.flow.scalar time (gamma t).val →
      ∃ W : CanonicalWitness G.flow eps C1 C2 (gamma t).val time, W.capTubeHasNeckChart eps)
    (hbase : 2 * C2 * metricScalarAt L.metric (gamma 0) < A)
    (hAq : q < A) (hAB : A < B)
    (hend : 2 * C2 * B ≤ metricScalarAt L.metric (gamma ell))
    (N : ℕ) (hratio : (2 : ℝ) ^ N * A ≤ B) :
    ∃ u v : ℝ, 0 < u ∧ u < v ∧ v < ell ∧
      metricScalarAt L.metric (gamma u) = A ∧ metricScalarAt L.metric (gamma v) = B ∧
      (∀ t ∈ Icc u v, A ≤ metricScalarAt L.metric (gamma t) ∧ metricScalarAt L.metric (gamma t) ≤ B) ∧
      ∃ neck : ∀ x ∈ gamma '' Icc u v, SpatialNeck L.metric α x,
      (∃ (rho : ℝ≥0) (_ : 0 < rho) (S : Set G.terminalRegularOpen)
          (hSC : S ⊆ gamma '' Icc u v),
        S.Finite ∧ gamma u ∈ S ∧ gamma v ∈ S ∧
        S.Pairwise (fun p q => (rho : ℝ≥0∞) < riemannianEDistOf L.metric p q) ∧
        ∀ x ∈ gamma '' Icc u v, ∃ p : G.terminalRegularOpen, ∃ hp : p ∈ S,
          x ∈ (neck p (hSC hp)).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) ∧
      ∃ n : ℕ, N ≤ n ∧ ∃ p : Fin (n + 1) → gamma '' Icc u v,
        (p 0).val = gamma u ∧ (p (Fin.last n)).val = gamma v ∧ Function.Injective p ∧
        (∀ i : Fin n,
          ((neck (p i.castSucc) (p i.castSucc).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            (neck (p i.succ) (p i.succ).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty) ∧
        ∀ i j : Fin (n + 1), i.val + 1 < j.val →
          Disjoint ((neck (p i) (p i).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))
            ((neck (p j) (p j).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  classical
  have hA : 0 < A := hq.trans hAq
  have hB : 0 < B := hA.trans hAB
  have hscalarContinuous : ContinuousOn (fun t => metricScalarAt L.metric (gamma t)) (Icc 0 ell) :=
    (metricScalar_smooth L.metric).continuous.comp_continuousOn hcontinuous
  have hzero : metricScalarAt L.metric (gamma 0) < A := by
    by_cases hh : 0 ≤ metricScalarAt L.metric (gamma 0)
    · nlinarith
    · exact (lt_of_not_ge hh).trans hA
  have hlast : B < metricScalarAt L.metric (gamma ell) := by nlinarith
  obtain ⟨u, v, hu, huv, hv, hRu, hRv, hband⟩ :=
    exists_interval_between_levels hell hscalarContinuous hzero hAB hlast
  have hnecks : ∀ x ∈ gamma '' Icc u v, Nonempty (SpatialNeck L.metric α x) := by
    rintro x ⟨t, ht, rfl⟩
    have ht0 : 0 < t := hu.trans_le ht.1
    have htell : t < ell := ht.2.trans_lt hv
    exact L.nonempty_spatialNeck_of_canonical_along_minimizer
      hδ (hα.trans_lt (by norm_num)) hreserve hepsδ hfit hq (by linarith) ht0 htell hmin
      (hcanonical t ⟨ht0, htell⟩) (hAq.trans_le (hband t ht).1)
      (hbase.trans_le (hband t ht).1)
      ((mul_le_mul_of_nonneg_left (hband t ht).2 (by linarith : 0 ≤ 2 * C2)).trans hend)
  let neck : ∀ x ∈ gamma '' Icc u v, SpatialNeck L.metric α x :=
    fun x hx => Classical.choice (hnecks x hx)
  have hpre : IsPreconnected (gamma '' Icc u v) := isPreconnected_Icc.image gamma
    (hcontinuous.mono (Icc_subset_Icc hu.le hv.le))
  have hcompact : IsCompact (gamma '' Icc u v) :=
    isCompact_Icc.image_of_continuousOn (hcontinuous.mono (Icc_subset_Icc hu.le hv.le))
  have hends : ({gamma u, gamma v} : Set G.terminalRegularOpen) ⊆ gamma '' Icc u v := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · subst x
      exact ⟨u, ⟨le_rfl, huv.le⟩, rfl⟩
    · have h := Set.mem_singleton_iff.mp h
      subst x
      exact ⟨v, ⟨huv.le, le_rfl⟩, rfl⟩
  obtain ⟨rho, hrho, S, hSC, hendsS, hS, hsep, hcover, _⟩ :=
    exists_finite_connected_spatial_neck_cover_containing L.metric hcompact hpre
      (Set.toFinite {gamma u, gamma v}) hends neck
  let left : gamma '' Icc u v := ⟨gamma u, u, ⟨le_rfl, huv.le⟩, rfl⟩
  let right : gamma '' Icc u v := ⟨gamma v, v, ⟨huv.le, le_rfl⟩, rfl⟩
  obtain ⟨n, hn, p, hp0, hpn, hinj, hmeet, hdisj⟩ :=
    exists_long_spatial_neck_chain_of_scalar_ratio hpre neck hα left right N (by
      change (2 : ℝ) ^ N * metricScalarAt L.metric (gamma u) ≤ metricScalarAt L.metric (gamma v)
      rw [hRu, hRv]
      exact hratio)
  exact ⟨u, v, hu, huv, hv, hRu, hRv, hband, neck, ⟨rho, hrho, S, hSC, hS, hendsS (by simp), hendsS (by simp), hsep, hcover⟩, n, hn, p,
    congrArg Subtype.val hp0, congrArg Subtype.val hpn, hinj, hmeet, hdisj⟩


theorem exists_eventually_neck_chains_along_scalar_escape
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ i, (P i).IncomingSlab (a i) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric) (gamma : ∀ i, ℝ → (G i).terminalRegularOpen)
    (ell Q q : ℕ → ℝ) (hell : ∀ i, 0 < ell i) (hQ : ∀ i, 0 < Q i)
    (hq : ∀ i, 0 < q i) (hqQ : ∀ i, q i ≤ Q i)
    {eps δ α C1 C2 : ℝ}
    (hδ : 0 < δ) (hα : α ≤ 1 / 20000) (hreserve : 13000 * δ ≤ α)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (hC2 : 1 ≤ C2)
    (hcontinuous : ∀ i, ContinuousOn (gamma i) (Icc 0 (ell i)))
    (hmin : ∀ i, ∀ t ∈ Icc 0 (ell i), ∀ v ∈ Icc 0 (ell i),
      riemannianEDistOf (L i).metric (gamma i t) (gamma i v) = ENNReal.ofReal |t - v|)
    (hcanonical : ∀ i, ∀ t ∈ Ioo 0 (ell i), ∀ time ∈ Ioo (a i) (s i),
      q i < (G i).flow.scalar time (gamma i t).val →
      ∃ W : CanonicalWitness (G i).flow eps C1 C2 (gamma i t).val time, W.capTubeHasNeckChart eps)
    (hbase : ∀ i, metricScalarAt (L i).metric (gamma i 0) ≤ Q i)
    (hhigh : Filter.Tendsto (fun i => metricScalarAt (L i).metric (gamma i (ell i)) / Q i)
      Filter.atTop Filter.atTop) (N : ℕ) :
    let A := fun i => (2 * C2 + 2) * Q i
    let B := fun i => (2 : ℝ) ^ (N + 1) * A i
    ∀ᶠ i in Filter.atTop,
    ∃ u v : ℝ, 0 < u ∧ u < v ∧ v < (ell i) ∧
      metricScalarAt (L i).metric ((gamma i) u) = (A i) ∧ metricScalarAt (L i).metric ((gamma i) v) = (B i) ∧
      (∀ t ∈ Icc u v, (A i) ≤ metricScalarAt (L i).metric ((gamma i) t) ∧ metricScalarAt (L i).metric ((gamma i) t) ≤ (B i)) ∧
      ∃ neck : ∀ x ∈ (gamma i) '' Icc u v, SpatialNeck (L i).metric α x,
      (∃ (rho : ℝ≥0) (_ : 0 < rho) (S : Set (G i).terminalRegularOpen)
          (hSC : S ⊆ (gamma i) '' Icc u v),
        S.Finite ∧ (gamma i) u ∈ S ∧ (gamma i) v ∈ S ∧
        S.Pairwise (fun p q => (rho : ℝ≥0∞) < riemannianEDistOf (L i).metric p q) ∧
        ∀ x ∈ (gamma i) '' Icc u v, ∃ p : (G i).terminalRegularOpen, ∃ hp : p ∈ S,
          x ∈ (neck p (hSC hp)).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) ∧
      ∃ n : ℕ, N ≤ n ∧ ∃ p : Fin (n + 1) → (gamma i) '' Icc u v,
        (p 0).val = (gamma i) u ∧ (p (Fin.last n)).val = (gamma i) v ∧ Function.Injective p ∧
        (∀ i : Fin n,
          ((neck (p i.castSucc) (p i.castSucc).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            (neck (p i.succ) (p i.succ).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty) ∧
        ∀ i j : Fin (n + 1), i.val + 1 < j.val →
          Disjoint ((neck (p i) (p i).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1))
            ((neck (p j) (p j).property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  dsimp only
  let A := fun i => (2 * C2 + 2) * Q i
  let B := fun i => (2 : ℝ) ^ (N + 1) * A i
  filter_upwards [hhigh.eventually_ge_atTop (2 * C2 * (2 : ℝ) ^ (N + 1) * (2 * C2 + 2))] with i hi
  apply (L i).exists_neck_chain_along_minimizer hδ hα hreserve hepsδ hfit (hq i) hC2
    (hell i) (gamma i) (hcontinuous i) (hmin i) (hcanonical i)
  · have hh := mul_le_mul_of_nonneg_left (hbase i) (by linarith : 0 ≤ 2 * C2)
    change 2 * C2 * metricScalarAt (L i).metric (gamma i 0) < (2 * C2 + 2) * Q i
    nlinarith [hQ i]
  · nlinarith [hqQ i, hQ i]
  · have hA : 0 < A i := mul_pos (by linarith) (hQ i)
    have hpow : (1 : ℝ) < (2 : ℝ) ^ (N + 1) := one_lt_pow₀ (by norm_num) (by omega)
    exact lt_mul_of_one_lt_left hA hpow
  · have hmul := (le_div_iff₀ (hQ i)).mp hi
    nlinarith
  · have hA : 0 ≤ A i := le_of_lt (mul_pos (by linarith) (hQ i))
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ N)) hA

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
