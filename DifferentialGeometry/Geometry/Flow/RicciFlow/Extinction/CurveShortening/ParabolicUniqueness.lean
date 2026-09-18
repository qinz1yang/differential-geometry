import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalUniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicReparametrizationExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.GaugeNormalizationUniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TimeTranslation
import DifferentialGeometry.Geometry.Metric.Family.TimeShift

noncomputable section

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem curveShorteningLocalUniqueness_of_parabolic_short_time
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hparabolic : ∀ (s T : ℝ), a ≤ s → s < T → T ≤ b →
      ∀ d₁ d₂ : CurveMap M,
        d₁.SmoothOn (I := I) (Icc s T) → d₁.ImmersedOn (I := I) (Icc s T) →
        d₂.SmoothOn (I := I) (Icc s T) → d₂.ImmersedOn (I := I) (Icc s T) →
        (∀ x t, t ∈ Icc s T → d₁.velocity (I := I) (Icc s T) x t =
          d₁.speed B.family.metric x t ^ (-2 : ℤ) • d₁.Dx B.family.metric d₁.X x t) →
        (∀ x t, t ∈ Icc s T → d₂.velocity (I := I) (Icc s T) x t =
          d₂.speed B.family.metric x t ^ (-2 : ℤ) • d₂.Dx B.family.metric d₂.X x t) →
        (∀ z, d₁ z s = d₂ z s) →
        ∃ δ > 0, ∀ z t, t ∈ Icc s (min T (s + δ)) → d₁ z t = d₂ z t) :
    curveShorteningLocalUniqueness (I := I) (M := M) B := by
  apply curveShorteningLocalUniqueness_of_short_time B
  intro s T has hsT hTb c₁ c₂ hc₁ hc₂ hstart
  have hJD : Icc s T ⊆ D.regular :=
    (Icc_subset_Icc has hTb).trans B.regular
  obtain ⟨τ₁, hτ₁, hτ₁T, P, hPinitial, hd₁⟩ :=
    hc₁.exists_reparametrization_parabolic_equation_on_Icc hsT B.smooth hJD
  obtain ⟨τ₂, hτ₂, hτ₂T, Q, hQinitial, hd₂⟩ :=
    hc₂.exists_reparametrization_parabolic_equation_on_Icc hsT B.smooth hJD
  let d₁ : CurveMap M := fun z t => c₁ (P.map t z) t
  let d₂ : CurveMap M := fun z t => c₂ (Q.map t z) t
  have hd₁sm : d₁.SmoothOn (I := I) (Icc s (s + τ₁)) := hd₁.1
  have hd₂sm : d₂.SmoothOn (I := I) (Icc s (s + τ₂)) := hd₂.1
  have restrict_equation {d : CurveMap M} {r q : ℝ} (hr : 0 < r) (hrq : r < q)
      (hsm : d.SmoothOn (I := I) (Icc s (s + q)))
      (heq : ∀ x t, t ∈ Icc s (s + q) →
        d.velocity (I := I) (Icc s (s + q)) x t =
          d.speed B.family.metric x t ^ (-2 : ℤ) • d.Dx B.family.metric d.X x t) :
      ∀ x t, t ∈ Icc s (s + r) →
        d.velocity (I := I) (Icc s (s + r)) x t =
          d.speed B.family.metric x t ^ (-2 : ℤ) • d.Dx B.family.metric d.X x t := by
    intro x t ht
    rw [CurveMap.velocity_Icc_of_lt hr hrq hsm ht]
    exact heq x t ⟨ht.1, ht.2.trans (add_le_add (le_refl s) hrq.le)⟩
  let η := min τ₁ τ₂ / 2
  have hη : 0 < η := half_pos (lt_min hτ₁ hτ₂)
  have hητ₁ : η < τ₁ :=
    (half_lt_self (lt_min hτ₁ hτ₂)).trans_le (min_le_left τ₁ τ₂)
  have hητ₂ : η < τ₂ :=
    (half_lt_self (lt_min hτ₁ hτ₂)).trans_le (min_le_right τ₁ τ₂)
  have hηT : s + η ≤ T := (add_le_add (le_refl s) hητ₁.le).trans hτ₁T
  have hsub₁ : Icc s (s + η) ⊆ Icc s (s + τ₁) :=
    Icc_subset_Icc le_rfl (add_le_add (le_refl s) hητ₁.le)
  have hsub₂ : Icc s (s + η) ⊆ Icc s (s + τ₂) :=
    Icc_subset_Icc le_rfl (add_le_add (le_refl s) hητ₂.le)
  have hdstart : ∀ z, d₁ z s = d₂ z s := by
    intro z
    change c₁ (P.map s z) s = c₂ (Q.map s z) s
    rw [hPinitial z, hQinitial z]
    exact hstart z
  obtain ⟨δ, hδ, hagree⟩ := hparabolic s (s + η) has (lt_add_of_pos_right s hη)
    (hηT.trans hTb) d₁ d₂
    (hd₁sm.mono (prod_mono Subset.rfl hsub₁))
    (fun x t ht => hd₁.2.1 x t (hsub₁ ht))
    (hd₂sm.mono (prod_mono Subset.rfl hsub₂))
    (fun x t ht => hd₂.2.1 x t (hsub₂ ht))
    (restrict_equation hη hητ₁ hd₁sm hd₁.2.2)
    (restrict_equation hη hητ₂ hd₂sm hd₂.2.2) hdstart
  let ε := min η δ / 2
  have hε : 0 < ε := half_pos (lt_min hη hδ)
  have hεη : ε < η :=
    (half_lt_self (lt_min hη hδ)).trans_le (min_le_left η δ)
  have hεδ : ε ≤ δ :=
    (half_lt_self (lt_min hη hδ)).le.trans (min_le_right η δ)
  have hετ₁ : ε < τ₁ := hεη.trans hητ₁
  have hετ₂ : ε < τ₂ := hεη.trans hητ₂
  have hεT : s + ε ≤ T := (add_le_add (le_refl s) hεη.le).trans hηT
  have hsubε₁ : Icc s (s + ε) ⊆ Icc s (s + τ₁) :=
    Icc_subset_Icc le_rfl (add_le_add (le_refl s) hετ₁.le)
  have hsubε₂ : Icc s (s + ε) ⊆ Icc s (s + τ₂) :=
    Icc_subset_Icc le_rfl (add_le_add (le_refl s) hετ₂.le)
  have hagreeε : ∀ z t, t ∈ Icc s (s + ε) → d₁ z t = d₂ z t := by
    intro z t ht
    exact hagree z t ⟨ht.1, le_min
      (ht.2.trans (add_le_add (le_refl s) hεη.le))
      (ht.2.trans (add_le_add (le_refl s) hεδ))⟩
  have hnormal₁ := hc₁.mono_Icc le_rfl hεT (lt_add_of_pos_right s hε)
  have hnormal₂ := hc₂.mono_Icc le_rfl hεT (lt_add_of_pos_right s hε)
  have hmaps : (P.restrict hsubε₁).map s = (Q.restrict hsubε₂).map s := by
    ext z
    exact (hPinitial z).trans (hQinitial z).symm
  have hnormal := hnormal₁.eqOn_of_parabolic_reparametrizations B.smooth
    ((Icc_subset_Icc le_rfl hεT).trans hJD) hnormal₂
    (restrict_equation hε hετ₁ hd₁sm hd₁.2.2)
    (P.restrict hsubε₁) (Q.restrict hsubε₂)
    (fun _ _ _ => rfl) hagreeε hmaps
  refine ⟨ε, hε, ?_⟩
  intro z t ht
  exact hnormal z t ⟨ht.1, ht.2.trans (min_le_right T (s + ε))⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem parabolic_short_time_uniqueness_of_zero_start
    (hzero : ∀ (D₀ : RealTimeInterval) (g₀ : ℝ → SmoothRiemannianMetric I M)
      (T : ℝ), 0 < T → MetricFamilySmoothOn D₀ g₀ → Icc 0 T ⊆ D₀.regular →
      ∀ d₁ d₂ : CurveMap M,
        d₁.SmoothOn (I := I) (Icc 0 T) → d₁.ImmersedOn (I := I) (Icc 0 T) →
        d₂.SmoothOn (I := I) (Icc 0 T) → d₂.ImmersedOn (I := I) (Icc 0 T) →
        (∀ x t, t ∈ Icc 0 T → d₁.velocity (I := I) (Icc 0 T) x t =
          d₁.speed g₀ x t ^ (-2 : ℤ) • d₁.Dx g₀ d₁.X x t) →
        (∀ x t, t ∈ Icc 0 T → d₂.velocity (I := I) (Icc 0 T) x t =
          d₂.speed g₀ x t ^ (-2 : ℤ) • d₂.Dx g₀ d₂.X x t) →
        (∀ z, d₁ z 0 = d₂ z 0) →
        ∃ δ > 0, ∀ z t, t ∈ Icc 0 (min T δ) → d₁ z t = d₂ z t)
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    {a b : ℝ} (hab : a < b) (hG : MetricFamilySmoothOn D g)
    (hJD : Icc a b ⊆ D.regular)
    (c₁ c₂ : CurveMap M)
    (hc₁ : c₁.SmoothOn (I := I) (Icc a b))
    (hi₁ : c₁.ImmersedOn (I := I) (Icc a b))
    (hc₂ : c₂.SmoothOn (I := I) (Icc a b))
    (hi₂ : c₂.ImmersedOn (I := I) (Icc a b))
    (heq₁ : ∀ x t, t ∈ Icc a b → c₁.velocity (I := I) (Icc a b) x t =
      c₁.speed g x t ^ (-2 : ℤ) • c₁.Dx g c₁.X x t)
    (heq₂ : ∀ x t, t ∈ Icc a b → c₂.velocity (I := I) (Icc a b) x t =
      c₂.speed g x t ^ (-2 : ℤ) • c₂.Dx g c₂.X x t)
    (hstart : ∀ z, c₁ z a = c₂ z a) :
    ∃ δ > 0, ∀ z t, t ∈ Icc a (min b (a + δ)) → c₁ z t = c₂ z t := by
  let d₁ : CurveMap M := fun z t => c₁ z (t + a)
  let d₂ : CurveMap M := fun z t => c₂ z (t + a)
  let g₀ : ℝ → SmoothRiemannianMetric I M := fun t => g (t + a)
  have hT : 0 < b - a := sub_pos.mpr hab
  have hmap : MapsTo (fun t : ℝ => t + a) (Icc 0 (b - a)) (Icc a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hreg : Icc (0 : ℝ) (b - a) ⊆ (D.timeShift a).regular :=
    fun _ ht => hJD (hmap ht)
  have hds₁ : d₁.SmoothOn (I := I) (Icc 0 (b - a)) :=
    CurveMap.smoothOn_time_translate hc₁ a hmap
  have hds₂ : d₂.SmoothOn (I := I) (Icc 0 (b - a)) :=
    CurveMap.smoothOn_time_translate hc₂ a hmap
  have hdi₁ : d₁.ImmersedOn (I := I) (Icc 0 (b - a)) := by
    intro x t ht
    exact hi₁ x (t + a) (hmap ht)
  have hdi₂ : d₂.ImmersedOn (I := I) (Icc 0 (b - a)) := by
    intro x t ht
    exact hi₂ x (t + a) (hmap ht)
  have hde₁ := CurveMap.parabolic_equation_time_translate hc₁ heq₁ a hmap
    (uniqueDiffOn_Icc hT)
  have hde₂ := CurveMap.parabolic_equation_time_translate hc₂ heq₂ a hmap
    (uniqueDiffOn_Icc hT)
  have hdstart : ∀ z, d₁ z 0 = d₂ z 0 := by
    intro z
    simpa only [d₁, d₂, zero_add] using hstart z
  obtain ⟨δ, hδ, hagree⟩ := hzero (D.timeShift a) g₀ (b - a) hT
    (hG.timeShift a) hreg d₁ d₂ hds₁ hdi₁ hds₂ hdi₂ hde₁ hde₂ hdstart
  refine ⟨δ, hδ, ?_⟩
  intro z t ht
  have htshift : t - a ∈ Icc (0 : ℝ) (min (b - a) δ) := by
    refine ⟨sub_nonneg.mpr ht.1, le_min ?_ ?_⟩
    · exact sub_le_sub_right (ht.2.trans (min_le_left _ _)) a
    · have hta : t ≤ a + δ := ht.2.trans (min_le_right _ _)
      linarith
  simpa only [d₁, d₂, sub_add_cancel] using hagree z (t - a) htshift

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

section
noncomputable section

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

theorem curveShorteningLocalUniqueness_of_compact
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    curveShorteningLocalUniqueness (I := I) (M := M) B := by
  apply curveShorteningLocalUniqueness_of_parabolic_short_time B
  intro s T has hsT hTb c₁ c₂ hc₁ hi₁ hc₂ hi₂ heq₁ heq₂ hstart
  apply parabolic_short_time_uniqueness_of_zero_start (I := I) (M := M) ?_
    hsT B.smooth ((Icc_subset_Icc has hTb).trans B.regular)
    c₁ c₂ hc₁ hi₁ hc₂ hi₂ heq₁ heq₂ hstart
  intro D₀ g₀ T₀ hT₀ hG₀ hJD₀ d₁ d₂ hd₁ hi₁ hd₂ hi₂ hde₁ hde₂ hdstart
  obtain ⟨δ, hδ, hδT, heq⟩ := exists_initial_interval_eq_of_parametric_curves_of_compact
    g₀ hT₀ hG₀ hJD₀ hd₁ hd₂ hi₁ hi₂ hde₁ hde₂ hdstart
  refine ⟨δ, hδ, ?_⟩
  simpa only [min_eq_right hδT] using heq

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
end
