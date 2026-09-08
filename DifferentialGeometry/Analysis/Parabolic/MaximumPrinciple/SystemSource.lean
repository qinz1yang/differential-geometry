import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.SystemRank
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Operator.MetricFamilyJointRegularity

set_option autoImplicit false

noncomputable section

open Bundle Set CovariantDerivative Filter
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PositiveSystem

open DifferentialGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem finrank_range_le_at_later_time_of_contMDiffOn
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    {T : ℝ}
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico 0 T ×ˢ (Set.univ : Set M)))
    (hcovsmooth : ∀ q ∈ Ioo 0 T, ContMDiffCovariantDerivative (cov q) ∞)
    (hcov : ∀ q ∈ Ioo 0 T, (cov q).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hApos : ∀ q ∈ Ico 0 T, ∀ z, (A q z).IsPositive)
    (hA : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ico 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (hX : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Ico 0 T ×ˢ (Set.univ : Set M)))
    (reaction : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q ∈ Ioo 0 T, ∀ z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t < T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R, 0 ≤ R →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ Icc s t, ∀ z ∈ Kset,
          ∀ B C : V z →L[ℝ] V z,
            (B : V z →ₗ[ℝ] V z).IsSymmetric →
            (C : V z →ₗ[ℝ] V z).IsSymmetric →
            ‖B‖ ≤ R → ‖C‖ ≤ R →
            ‖reaction q z B - reaction q z C‖ ≤ L * ‖B - C‖)
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z,
      HasDerivAt (fun r ↦ A r z)
        (rawBundleEndomorphismConnLap (I := I) (g q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
            (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) q)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t < T) (x y : M) :
    Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z => VectorBundle.finiteDimensional ℝ F V z
  have hT : 0 < T := (hs.trans_lt hst).trans ht
  have hspread : ∀ {a b : ℝ}, 0 < a → a < b → b < T → ∀ z w,
      Module.finrank ℝ (A a z).range ≤ Module.finrank ℝ (A b w).range := by
    intro a b ha hab hb z w
    let D := (RealTimeInterval.closedOpen 0 T hT).timeShift a
    let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
      { metric := fun q => g (q + a)
        connection := fun q => LeviCivita (g (q + a))
        metricCompatible := fun q => by
          rw [LeviCivita_eq_leviCivitaConnectionOfMetric]
          exact leviCivitaConnectionOfMetric_isMetricCompatible (g (q + a)) }
    have hshift : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × M => (p.1 + a, p.2)) :=
      (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
    have hgshift : MetricFamilySmoothOn (I := I) (M := M) D G.metric := by
      apply metricFamilySmoothOn_of_contMDiffOn
      exact hg.comp hshift.contMDiffOn (fun p hp => ⟨hp.1, hp.2⟩)
    have hshiftmem {q : ℝ} (hq : q ∈ Ico 0 (T - a)) : q + a ∈ Ioo 0 T := by
      constructor <;> linarith [hq.1, hq.2]
    have hAshift := hA.comp hshift.continuous.continuousOn
      (s := Ico 0 (T - a) ×ˢ (Set.univ : Set M))
      (fun p hp => ⟨⟨(hshiftmem hp.1).1.le, (hshiftmem hp.1).2⟩, hp.2⟩)
    have hXshift := hX.comp hshift.continuous.continuousOn
      (s := Ico 0 (T - a) ×ˢ (Set.univ : Set M))
      (fun p hp => ⟨⟨(hshiftmem hp.1).1.le, (hshiftmem hp.1).2⟩, hp.2⟩)
    have hlip : ∀ {c d : ℝ}, 0 ≤ c → c < d → d < T - a →
        ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
          ∃ Klip : NNReal, ∀ q ∈ Ioc c d, ∀ v ∈ Kset,
            LipschitzOnWith Klip (reaction (q + a) v)
              {B : V v →L[ℝ] V v | B.IsPositive ∧ ‖B‖ ≤ 2 * R} := by
      intro c d hc hcd hd K hK R
      obtain ⟨L, hL, hLbound⟩ := hreactionLip
        (s := c + a) (t := d + a) (by linarith) (by linarith) (by linarith)
        hK (max (2 * R) 0) (le_max_right _ _)
      let Klip : NNReal := ⟨L, hL⟩
      refine ⟨Klip, ?_⟩
      intro q hq v hv
      apply LipschitzOnWith.of_dist_le_mul
      intro B hB C hC
      rw [dist_eq_norm, dist_eq_norm]
      have hcoe : (Klip : ℝ) = L := rfl
      rw [hcoe]
      exact hLbound (q + a) ⟨by linarith [hq.1], by linarith [hq.2]⟩ v hv
          B C hB.1.isSymmetric hC.1.isSymmetric
          (hB.2.trans (le_max_left _ _)) (hC.2.trans (le_max_left _ _))
    have hevol : ∀ q ∈ Ioo 0 (T - a), ∀ v,
        HasDerivAt (fun r => A (r + a) v)
          (rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov (q + a))
              (fun w => A (q + a) w) v +
            HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
              (cov (q + a)) (cov (q + a)) (fun w => A (q + a) w) v (X (q + a) v) +
            reaction (q + a) v (A (q + a) v)) q := by
      intro q hq v
      have hq' : q + a ∈ Ioo 0 T := by constructor <;> linarith [hq.1, hq.2]
      simpa only [Function.comp_def, id_eq, one_smul, G] using
        (hevolution (q + a) hq' v).scomp q ((hasDerivAt_id q).add_const a)
    have hmain := finrank_range_le_at_later_time_of_continuous_endomorphism_on_Ioo
      G (fun q => cov (q + a))
      (fun q hq => hcovsmooth (q + a) (hshiftmem hq))
      (fun q hq => hcov (q + a) (hshiftmem hq))
      (fun q => A (q + a))
      (fun q hq v => hApos (q + a) ⟨(hshiftmem hq).1.le, (hshiftmem hq).2⟩ v)
      hAshift (fun q => X (q + a)) (fun q => reaction (q + a))
      (fun q hq v => hreactionNull (q + a) (hshiftmem hq) v)
      hlip hgshift (fun q hq => hshiftmem hq) hXshift (fun _ _ => rfl) hevol
      (s := 0) (t := b - a) le_rfl (sub_pos.mpr hab) (by linarith) z w
    have hmain' : Module.finrank ℝ (A (0 + a) z).range ≤
        Module.finrank ℝ (A (b - a + a) w).range := hmain
    rw [zero_add, sub_add_cancel] at hmain'
    exact hmain'
  rcases hs.eq_or_lt with rfl | hspos
  · have hAcont : ContinuousWithinAt (fun q => A q x) (Ico 0 T) 0 := by
      have hc : ContinuousOn (fun q : ℝ =>
          (TotalSpace.mk' (F →L[ℝ] F) x (A q x) :
            TotalSpace (F →L[ℝ] F) (fun z => V z →L[ℝ] V z))) (Ico 0 T) :=
        hA.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun q hq => ⟨hq, mem_univ x⟩)
      exact (FiberBundle.totalSpaceMk_isInducing (F →L[ℝ] F)
        (fun z => V z →L[ℝ] V z) x).continuousWithinAt_iff.mpr
          (hc 0 ⟨le_rfl, hT⟩)
    have hlower := hAcont.eventually_finrank_range_ge
    have hev : ∀ᶠ q in 𝓝[Ioo 0 t] 0,
        Module.finrank ℝ (A 0 x).range ≤ Module.finrank ℝ (A q x).range :=
      hlower.filter_mono (nhdsWithin_mono 0 (show Ioo 0 t ⊆ Ico 0 T from
        fun q hq => ⟨hq.1.le, hq.2.trans ht⟩))
    let _ : (𝓝[Ioo 0 t] (0 : ℝ)).NeBot := left_nhdsWithin_Ioo_neBot hst
    have hmem : ∀ᶠ q in 𝓝[Ioo 0 t] (0 : ℝ), q ∈ Ioo 0 t := self_mem_nhdsWithin
    obtain ⟨q, hq, hqrank⟩ := (hmem.and hev).exists
    exact hqrank.trans (hspread hq.1 hq.2 ht x y)
  · exact hspread hspos hst ht x y

theorem finrank_range_spatially_constant_and_locally_constant_of_contMDiffOn
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    {T : ℝ} (hT : 0 < T)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico 0 T ×ˢ (Set.univ : Set M)))
    (hcovsmooth : ∀ q ∈ Ioo 0 T, ContMDiffCovariantDerivative (cov q) ∞)
    (hcov : ∀ q ∈ Ioo 0 T, (cov q).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hApos : ∀ q ∈ Ico 0 T, ∀ z, (A q z).IsPositive)
    (hA : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ico 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (hX : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Ico 0 T ×ˢ (Set.univ : Set M)))
    (reaction : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q ∈ Ioo 0 T, ∀ z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t < T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R, 0 ≤ R →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ Icc s t, ∀ z ∈ Kset,
          ∀ B C : V z →L[ℝ] V z,
            (B : V z →ₗ[ℝ] V z).IsSymmetric →
            (C : V z →ₗ[ℝ] V z).IsSymmetric →
            ‖B‖ ≤ R → ‖C‖ ≤ R →
            ‖reaction q z B - reaction q z C‖ ≤ L * ‖B - C‖)
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z,
      HasDerivAt (fun r ↦ A r z)
        (rawBundleEndomorphismConnLap (I := I) (g q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
            (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) q)
 :
    (∀ t ∈ Ioo 0 T, ∀ x y,
      Module.finrank ℝ (A t x).range = Module.finrank ℝ (A t y).range) ∧
    (∀ x, MonotoneOn (fun t => Module.finrank ℝ (A t x).range) (Ioo 0 T)) ∧
    (∀ t ∈ Ioo 0 T, ∀ x,
      ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
        Module.finrank ℝ (A s x).range = Module.finrank ℝ (A t x).range) ∧
    ∃ δ ∈ Ioo 0 T, ∃ q : ℕ, ∀ t ∈ Ioc 0 δ, ∀ x,
      Module.finrank ℝ (A t x).range = q := by
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z => VectorBundle.finiteDimensional ℝ F V z
  have hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t < T → ∀ x y,
      Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
    intro s t hs hst ht x y
    exact finrank_range_le_at_later_time_of_contMDiffOn
      g cov hg hcovsmooth hcov A hApos hA X hX reaction hreactionNull hreactionLip
      hevolution hs hst ht x y
  have hrank {u : ℝ} (hu : u ∈ Ioo 0 T) :=
    rank_spatially_constant_and_locally_constant_from_left_of_spreading
      (rank := fun t x => Module.finrank ℝ (A t x).range) hu.1
      (fun t ht x =>
        (ContinuousAt.eventually_finrank_range_ge
          (hevolution t ⟨ht.1, ht.2.trans_lt hu.2⟩ x).continuousAt).filter_mono inf_le_left)
      (fun hs hst ht x y => hspread hs hst (ht.trans_lt hu.2) x y)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht x y
    exact (hrank ht).1 t ⟨ht.1, le_rfl⟩ x y
  · intro x s hs t ht hst
    rcases hst.eq_or_lt with rfl | hst
    · exact le_rfl
    · exact hspread hs.1.le hst ht.2 x x
  · intro t ht x
    exact (hrank ht).2.2.1 t ⟨ht.1, le_rfl⟩ x
  · have hh : T / 2 ∈ Ioo 0 T := ⟨half_pos hT, half_lt_self hT⟩
    obtain ⟨δ, hδ, q, hq⟩ := (hrank hh).2.2.2
    exact ⟨δ, ⟨hδ.1, hδ.2.trans_lt hh.2⟩, q, hq⟩

theorem rank_finite_interval_partition_of_contMDiffOn
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    {T : ℝ}
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico 0 T ×ˢ (Set.univ : Set M)))
    (hcovsmooth : ∀ q ∈ Ioo 0 T, ContMDiffCovariantDerivative (cov q) ∞)
    (hcov : ∀ q ∈ Ioo 0 T, (cov q).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hApos : ∀ q ∈ Ico 0 T, ∀ z, (A q z).IsPositive)
    (hA : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Ico 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (hX : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Ico 0 T ×ˢ (Set.univ : Set M)))
    (reaction : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q ∈ Ioo 0 T, ∀ z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t < T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R, 0 ≤ R →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ Icc s t, ∀ z ∈ Kset,
          ∀ B C : V z →L[ℝ] V z,
            (B : V z →ₗ[ℝ] V z).IsSymmetric →
            (C : V z →ₗ[ℝ] V z).IsSymmetric →
            ‖B‖ ≤ R → ‖C‖ ≤ R →
            ‖reaction q z B - reaction q z C‖ ≤ L * ‖B - C‖)
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z,
      HasDerivAt (fun r ↦ A r z)
        (rawBundleEndomorphismConnLap (I := I) (g q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
            (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    ∃ Q : Finset ℕ,
      Icc a b = ⋃ q ∈ Q, {t | t ∈ Icc a b ∧ ∀ x,
        Module.finrank ℝ (A t x).range = q} ∧
      (Q : Set ℕ).PairwiseDisjoint
        (fun q => {t | t ∈ Icc a b ∧ ∀ x,
          Module.finrank ℝ (A t x).range = q}) ∧
      ∀ q ∈ Q, {t | t ∈ Icc a b ∧ ∀ x,
        Module.finrank ℝ (A t x).range = q}.Nonempty ∧
        ∃ l u : ℝ, a ≤ l ∧ l ≤ u ∧ u ≤ b ∧
          ({t | t ∈ Icc a b ∧ ∀ x,
            Module.finrank ℝ (A t x).range = q} = Icc a u ∧
              (∀ x, Module.finrank ℝ (A a x).range = q) ∨
            {t | t ∈ Icc a b ∧ ∀ x,
              Module.finrank ℝ (A t x).range = q} = Ioc l u ∧
              ¬ ∀ x, Module.finrank ℝ (A a x).range = q) := by
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z => VectorBundle.finiteDimensional ℝ F V z
  have hbpos : 0 < b := ha.trans_le hab
  apply rank_finite_interval_partition_of_spreading
    (rank := fun t x => Module.finrank ℝ (A t x).range) hbpos
  · intro t ht x
    exact (ContinuousAt.eventually_finrank_range_ge
      (hevolution t ⟨ht.1, ht.2.trans_lt hb⟩ x).continuousAt).filter_mono inf_le_left
  · intro s t hs hst ht x y
    exact finrank_range_le_at_later_time_of_contMDiffOn
      g cov hg hcovsmooth hcov A hApos hA X hX reaction hreactionNull hreactionLip
      hevolution hs hst (ht.trans_lt hb) x y
  · exact ha
  · exact hab
  · exact le_rfl

theorem finrank_range_le_at_later_time_of_contMDiffOn_on_Icc
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    {T : ℝ}
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcovsmooth : ∀ q ∈ Ioo 0 T, ContMDiffCovariantDerivative (cov q) ∞)
    (hcov : ∀ q ∈ Ioo 0 T, (cov q).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hA : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (hX : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (reaction : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q ∈ Ioo 0 T, ∀ z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R, 0 ≤ R →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ Icc s t, ∀ z ∈ Kset,
          ∀ B C : V z →L[ℝ] V z,
            (B : V z →ₗ[ℝ] V z).IsSymmetric →
            (C : V z →ₗ[ℝ] V z).IsSymmetric →
            ‖B‖ ≤ R → ‖C‖ ≤ R →
            ‖reaction q z B - reaction q z C‖ ≤ L * ‖B - C‖)
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z,
      HasDerivAt (fun r ↦ A r z)
        (rawBundleEndomorphismConnLap (I := I) (g q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
            (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) q)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) (x y : M) :
    Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z => VectorBundle.finiteDimensional ℝ F V z
  let _ : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := ∞)
  have hT : 0 < T := (hs.trans_lt hst).trans_le ht
  have hmid : T / 2 ∈ Ioo 0 T := ⟨half_pos hT, half_lt_self hT⟩
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    { metric := g
      connection := fun q => LeviCivita (g q)
      metricCompatible := fun q => by
        rw [LeviCivita_eq_leviCivitaConnectionOfMetric]
        exact leviCivitaConnectionOfMetric_isMetricCompatible (g q) }
  let A' : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯ :=
    fun q => if q ∈ Icc 0 T then A q else 0
  have hAeq : ∀ q ∈ Icc 0 T, A' q = A q := fun _ hq => if_pos hq
  have hAsymm' : ∀ q z,
      ((A' q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric := by
    intro q z
    by_cases hq : q ∈ Icc 0 T
    · rw [hAeq q hq]
      exact (hApos q hq z).isSymmetric
    · simp only [A', if_neg hq]
      change (0 : V z →ₗ[ℝ] V z).IsSymmetric
      exact LinearMap.IsSymmetric.zero
  have hApos' : ∀ q ∈ Icc 0 T, ∀ z, (A' q z).IsPositive := by
    intro q hq z
    rw [hAeq q hq]
    exact hApos q hq z
  have hAcont' : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) p.2 (A' p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (Icc 0 T ×ˢ (Set.univ : Set M)) := by
    apply hA.congr
    intro p hp
    exact congrArg (fun B : Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯ =>
      (TotalSpace.mk' (F →L[ℝ] F) p.2 (B p.2) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) (hAeq p.1 hp.1)
  let cov' : ℝ → CovariantDerivative I F V :=
    fun q => if q ∈ Ioo 0 T then cov q else cov (T / 2)
  let _ : ∀ q, ContMDiffCovariantDerivative (cov' q) ∞ := by
    intro q
    dsimp only [cov']
    split_ifs with hq
    · exact hcovsmooth q hq
    · exact hcovsmooth (T / 2) hmid
  have hcov' : ∀ q, (cov' q).IsMetricCompatible := by
    intro q
    dsimp only [cov']
    split_ifs with hq
    · exact hcov q hq
    · exact hcov (T / 2) hmid
  let reaction' : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z :=
    fun q z => if q ∈ Ioo 0 T then reaction q z else fun _ => 0
  have hnull : ∀ q z, satisfiesNullEigenvectorCondition (reaction' q z) := by
    intro q z
    by_cases hq : q ∈ Ioo 0 T
    · simpa only [reaction', if_pos hq] using hreactionNull q hq z
    · intro B hB v hv
      simp only [reaction', if_neg hq, zero_apply, inner_zero_left, le_refl]
  have hlip : ∀ {a b : ℝ}, 0 ≤ a → a < b → b ≤ T →
      ∀ {K : Set M}, IsCompact K → ∀ R, ∃ Klip : NNReal,
        ∀ q ∈ Ioc a b, ∀ z ∈ K, LipschitzOnWith Klip (reaction' q z)
          {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R} := by
    intro a b ha hab hb K hK R
    obtain ⟨L, hL, hbound⟩ := hreactionLip ha hab.le hb hK (max (2 * R) 0)
      (le_max_right _ _)
    let Klip : NNReal := ⟨L, hL⟩
    refine ⟨Klip, ?_⟩
    intro q hq z hz
    by_cases hqT : q ∈ Ioo 0 T
    · simp only [reaction', if_pos hqT]
      apply LipschitzOnWith.of_dist_le_mul
      intro B hB C hC
      rw [dist_eq_norm, dist_eq_norm]
      have hcoe : (Klip : ℝ) = L := rfl
      rw [hcoe]
      exact hbound q ⟨hq.1.le, hq.2⟩ z hz B C hB.1.isSymmetric hC.1.isSymmetric
        (hB.2.trans (le_max_left _ _)) (hC.2.trans (le_max_left _ _))
    · simpa only [reaction', if_neg hqT] using
        (LipschitzWith.const (0 : V z →L[ℝ] V z)).weaken
          (show (0 : NNReal) ≤ Klip from zero_le) |>.lipschitzOnWith
  have hevol : ∀ q ∈ Ioo 0 T, ∀ z,
      HasDerivAt (fun r => A' r z)
        (rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov' q)
            (fun w => A' q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
            (cov' q) (cov' q) (fun w => A' q w) z (X q z) +
          reaction' q z (A' q z)) q := by
    intro q hq z
    have hq' : q ∈ Icc 0 T := ⟨hq.1.le, hq.2.le⟩
    have hev : (fun r => A' r z) =ᶠ[𝓝 q] (fun r => A r z) := by
      filter_upwards [isOpen_Ioo.mem_nhds hq] with r hr
      rw [hAeq r ⟨hr.1.le, hr.2.le⟩]
    simpa only [G, hAeq q hq', cov', reaction', if_pos hq] using
      (hevolution q hq z).congr_of_eventuallyEq hev
  have hbound : ∀ {a b : ℝ}, 0 ≤ a → a < b → b ≤ T → ∀ {K : Set M},
      IsCompact K → ∃ R, ∀ q ∈ Icc a b, ∀ z ∈ K, ‖A' q z‖ ≤ R := by
    intro a b ha hab hb K hK
    obtain ⟨R, -, hR⟩ := (isCompact_Icc.prod hK).exists_hom_bundle_opNorm_bound
      (hAcont'.mono fun p hp => ⟨⟨ha.trans hp.1.1, hp.1.2.trans hb⟩, mem_univ p.2⟩)
    exact ⟨R, fun q hq z hz => hR (q, z) ⟨hq, hz⟩⟩
  have hmain := finrank_range_le_at_later_time_of_interior_evolution
    G cov' hcov' hT A' hAsymm' hApos'
    (fun k hk => hAcont'.lowerKyFanSum_bundle (fun p => hAsymm' p.1 p.2) hk)
    hbound X reaction' hnull hlip
    (fun rho hrho => gradient_norm_sq_continuousOn_of_contMDiffOn g hg hrho)
    (fun rho hrho => G.heatOperatorWithDrift_continuousOn_of_contMDiffOn
      hg (uniqueDiffOn_Icc hT) (fun _ _ => rfl) X hX hrho)
    (fun _ _ => rfl)
    (fun q hq z => (hevol q hq z).differentiableAt)
    (fun q hq z => (hevol q hq z).deriv) hs hst ht x y
  rw [hAeq s ⟨hs, hst.le.trans ht⟩, hAeq t ⟨hs.trans hst.le, ht⟩] at hmain
  exact hmain

theorem finrank_range_spatially_constant_and_locally_constant_of_contMDiffOn_on_Icc
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    {T : ℝ} (hT : 0 < T)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcovsmooth : ∀ q ∈ Ioo 0 T, ContMDiffCovariantDerivative (cov q) ∞)
    (hcov : ∀ q ∈ Ioo 0 T, (cov q).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hA : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (hX : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (reaction : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q ∈ Ioo 0 T, ∀ z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R, 0 ≤ R →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ Icc s t, ∀ z ∈ Kset,
          ∀ B C : V z →L[ℝ] V z,
            (B : V z →ₗ[ℝ] V z).IsSymmetric →
            (C : V z →ₗ[ℝ] V z).IsSymmetric →
            ‖B‖ ≤ R → ‖C‖ ≤ R →
            ‖reaction q z B - reaction q z C‖ ≤ L * ‖B - C‖)
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z,
      HasDerivAt (fun r ↦ A r z)
        (rawBundleEndomorphismConnLap (I := I) (g q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
            (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) q)
 :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (A t x).range = Module.finrank ℝ (A t y).range) ∧
    (∀ x, MonotoneOn (fun t => Module.finrank ℝ (A t x).range) (Ioc 0 T)) ∧
    (∀ t ∈ Ioc 0 T, ∀ x,
      ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
        Module.finrank ℝ (A s x).range = Module.finrank ℝ (A t x).range) ∧
    ∃ δ ∈ Ioc 0 T, ∃ q : ℕ, ∀ t ∈ Ioc 0 δ, ∀ x,
      Module.finrank ℝ (A t x).range = q := by
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z => VectorBundle.finiteDimensional ℝ F V z
  apply rank_spatially_constant_and_locally_constant_from_left_of_spreading
    (rank := fun t x => Module.finrank ℝ (A t x).range) hT
  · intro t ht x
    have hc : ContinuousOn (fun q : ℝ =>
        (TotalSpace.mk' (F →L[ℝ] F) x (A q x) :
          TotalSpace (F →L[ℝ] F) (fun z => V z →L[ℝ] V z))) (Icc 0 T) :=
      hA.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun q hq => ⟨hq, mem_univ x⟩)
    have hAx : ContinuousWithinAt (fun q => A q x) (Icc 0 T) t :=
      (FiberBundle.totalSpaceMk_isInducing (F →L[ℝ] F)
        (fun z => V z →L[ℝ] V z) x).continuousWithinAt_iff.mpr
          (hc t ⟨ht.1.le, ht.2⟩)
    exact hAx.eventually_finrank_range_ge
  · intro s t hs hst ht x y
    exact finrank_range_le_at_later_time_of_contMDiffOn_on_Icc
      g cov hg hcovsmooth hcov A hApos hA X hX reaction hreactionNull hreactionLip
      hevolution hs hst ht x y

theorem rank_finite_interval_partition_of_contMDiffOn_on_Icc
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    {T : ℝ}
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcovsmooth : ∀ q ∈ Ioo 0 T, ContMDiffCovariantDerivative (cov q) ∞)
    (hcov : ∀ q ∈ Ioo 0 T, (cov q).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hA : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (hX : ContinuousOn
      (fun p : ℝ × M => (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (reaction : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q ∈ Ioo 0 T, ∀ z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R, 0 ≤ R →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ Icc s t, ∀ z ∈ Kset,
          ∀ B C : V z →L[ℝ] V z,
            (B : V z →ₗ[ℝ] V z).IsSymmetric →
            (C : V z →ₗ[ℝ] V z).IsSymmetric →
            ‖B‖ ≤ R → ‖C‖ ≤ R →
            ‖reaction q z B - reaction q z C‖ ≤ L * ‖B - C‖)
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z,
      HasDerivAt (fun r ↦ A r z)
        (rawBundleEndomorphismConnLap (I := I) (g q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
            (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ T) :
    ∃ Q : Finset ℕ,
      Icc a b = ⋃ q ∈ Q, {t | t ∈ Icc a b ∧ ∀ x,
        Module.finrank ℝ (A t x).range = q} ∧
      (Q : Set ℕ).PairwiseDisjoint
        (fun q => {t | t ∈ Icc a b ∧ ∀ x,
          Module.finrank ℝ (A t x).range = q}) ∧
      ∀ q ∈ Q, {t | t ∈ Icc a b ∧ ∀ x,
        Module.finrank ℝ (A t x).range = q}.Nonempty ∧
        ∃ l u : ℝ, a ≤ l ∧ l ≤ u ∧ u ≤ b ∧
          ({t | t ∈ Icc a b ∧ ∀ x,
            Module.finrank ℝ (A t x).range = q} = Icc a u ∧
              (∀ x, Module.finrank ℝ (A a x).range = q) ∨
            {t | t ∈ Icc a b ∧ ∀ x,
              Module.finrank ℝ (A t x).range = q} = Ioc l u ∧
              ¬ ∀ x, Module.finrank ℝ (A a x).range = q) := by
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z => VectorBundle.finiteDimensional ℝ F V z
  have hT : 0 < T := (ha.trans_le hab).trans_le hb
  apply rank_finite_interval_partition_of_spreading
    (rank := fun t x => Module.finrank ℝ (A t x).range) hT
  · intro t ht x
    have hc : ContinuousOn (fun q : ℝ =>
        (TotalSpace.mk' (F →L[ℝ] F) x (A q x) :
          TotalSpace (F →L[ℝ] F) (fun z => V z →L[ℝ] V z))) (Icc 0 T) :=
      hA.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun q hq => ⟨hq, mem_univ x⟩)
    have hAx : ContinuousWithinAt (fun q => A q x) (Icc 0 T) t :=
      (FiberBundle.totalSpaceMk_isInducing (F →L[ℝ] F)
        (fun z => V z →L[ℝ] V z) x).continuousWithinAt_iff.mpr
          (hc t ⟨ht.1.le, ht.2⟩)
    exact hAx.eventually_finrank_range_ge
  · intro s t hs hst ht x y
    exact finrank_range_le_at_later_time_of_contMDiffOn_on_Icc
      g cov hg hcovsmooth hcov A hApos hA X hX reaction hreactionNull hreactionLip
      hevolution hs hst ht x y
  · exact ha
  · exact hab
  · exact hb

end PositiveSystem
