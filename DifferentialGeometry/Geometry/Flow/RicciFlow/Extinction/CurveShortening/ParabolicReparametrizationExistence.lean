import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SobolevExistence
import DifferentialGeometry.Geometry.Metric.Family.AddCircle
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ReparametrizationExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicReparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Connection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Periodicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicReconstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Reparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TimeTranslation
import DifferentialGeometry.Geometry.Metric.Family.TimeShift

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem CurveMap.IsSolutionOn.exists_reparametrization_parabolic_equation
    {c : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M}
    {D : RealTimeInterval} {b : ℝ} (hb : 0 < b)
    (hc : c.IsSolutionOn (I := I) g (Icc 0 b))
    (hG : MetricFamilySmoothOn D g) (hJD : Icc (0 : ℝ) b ⊆ D.regular) :
    ∃ τ > 0, τ ≤ b ∧ ∃ P : CircleReparametrization (Icc 0 τ),
      (∀ z, P.map 0 z = z) ∧
        let d : CurveMap M := fun z t => c (P.map t z) t
        d.SmoothOn (I := I) (Icc 0 τ) ∧ d.ImmersedOn (I := I) (Icc 0 τ) ∧
          ∀ x t, t ∈ Icc 0 τ → d.velocity (I := I) (Icc 0 τ) x t =
            d.speed g x t ^ (-2 : ℤ) • d.Dx g d.X x t := by
  have hspeed := CurveMap.Field.smoothOn_speed g hG hJD c hc.smooth hc.immersed
  have hperiodic : ∀ t ∈ Icc (0 : ℝ) b,
      Function.Periodic (fun x => c.speed g x t) 1 := by
    intro t ht x
    exact c.speed_add_period g t x
      ((c.smooth_slice hc.smooth ht).mdifferentiableAt (x := x + 1) (by simp))
  obtain ⟨h, hGsmooth, hmetric⟩ :=
    AddCircle.exists_metricFamilySmoothOn_extension_of_periodic_sq hspeed hperiodic
      (fun x t ht => (c.speed_pos g hc.immersed x t ht).ne')
  let q₀ : SmoothImmersion (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) :=
    { map := id
      smooth := AddCircle.contMDiff_coe
      immersed := by
        intro x
        change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (fun y : ℝ => (y : AddCircle (1 : ℝ))) x 1 ≠ 0
        erw [← AddCircle.parameterTangent_coe]
        exact AddCircle.parameterTangent_ne_zero _ }
  have hzero : (0 : ℝ) ∈ D.regular := hJD ⟨le_rfl, hb.le⟩
  obtain ⟨T, hT, q, hqsm, -, hqinitial, hqequation⟩ :=
    SmoothImmersion.exists_parametric_solution_of_compact q₀ h hzero (hGsmooth D)
  have hq₀ : ∀ z, q z 0 = z := hqinitial
  let L := min (T / 2) b
  have hL : 0 < L := lt_min (half_pos hT) hb
  have hLT : L < T := (min_le_left (T / 2) b).trans_lt (half_lt_self hT)
  have hLb : L ≤ b := min_le_right (T / 2) b
  have hqsmall : q.SmoothOn (I := 𝓘(ℝ, ℝ)) (Icc 0 L) :=
    hqsm.mono (prod_mono Subset.rfl (Icc_subset_Icc le_rfl hLT.le))
  have htop := CurveMap.SmoothOn.exists_reparametrization_of_initial_identity hL hqsmall hq₀
  simp only [zero_add] at htop
  obtain ⟨τ, hτ, hτL, P₀, hP⟩ := htop
  let P : CircleReparametrization (Icc 0 τ) :=
    { map := P₀.map
      smooth := by simpa only [zero_add] using P₀.smooth
      smooth_inverse := by simpa only [zero_add] using P₀.smooth_inverse }
  have hτT : τ < T := hτL.trans_lt hLT
  have hτb : τ ≤ b := hτL.trans hLb
  have hsubT : Icc (0 : ℝ) τ ⊆ Icc 0 T := Icc_subset_Icc le_rfl hτT.le
  have hsubb : Icc (0 : ℝ) τ ⊆ Icc 0 b := Icc_subset_Icc le_rfl hτb
  have hPinitial : ∀ z, P.map 0 z = z :=
    fun z => (hP 0 ⟨le_rfl, hτ.le⟩ z).trans (hq₀ z)
  let ψ : CurveMap (AddCircle (1 : ℝ)) := fun z t => P.map t z
  have hqτ : ∀ x t, t ∈ Icc (0 : ℝ) τ →
      q.velocity (I := 𝓘(ℝ, ℝ)) (Icc 0 τ) x t =
        q.speed h x t ^ (-2 : ℤ) • q.Dx h q.X x t := by
    intro x t ht
    have hvel : q.velocity (I := 𝓘(ℝ, ℝ)) (Icc 0 τ) x t =
        q.velocity (I := 𝓘(ℝ, ℝ)) (Icc 0 T) x t := by
      simpa only [zero_add] using
        (CurveMap.velocity_Icc_of_lt (c := q) (t₀ := 0) (σ := τ) (τ := T)
          hτ hτT (by simpa only [zero_add] using hqsm)
          (x := x) (t := t) (by simpa only [zero_add] using ht))
    exact hvel.trans (hqequation x t (hsubT ht))
  have hparametric : ∀ x t, t ∈ Icc 0 τ →
      ψ.velocity (I := 𝓘(ℝ, ℝ)) (Icc 0 τ) x t =
        ψ.speed h x t ^ (-2 : ℤ) • ψ.Dx h ψ.X x t := by
    intro x t ht
    apply CurveMap.velocity_eq_parametric_acceleration_of_eqOn
      (I := 𝓘(ℝ, ℝ)) (c := ψ) (d := q) (g := h)
      (fun z s hs => hP s hs z) ht
    exact hqτ x t ht
  have hinner : ∀ (y t : ℝ), t ∈ Icc (0 : ℝ) τ →
      (h t).inner (y : AddCircle (1 : ℝ))
          (AddCircle.parameterTangent (y : AddCircle (1 : ℝ)))
          (AddCircle.parameterTangent (y : AddCircle (1 : ℝ))) =
        (g t).inner (c.lift y t) (c.X (I := I) y t) (c.X (I := I) y t) := by
    intro y t ht
    refine (hmetric t (hsubb ht) y).trans ?_
    exact Real.sq_sqrt (DifferentialGeometry.metric_inner_self_nonneg (g t) _ _)
  refine ⟨τ, hτ, hτb, P, hPinitial, ?_⟩
  exact (hc.mono_Icc le_rfl hτb hτ).parabolic_equation_reparam
    P h (uniqueDiffOn_Icc hτ) hinner hparametric

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem CurveMap.IsSolutionOn.exists_reparametrization_parabolic_equation_on_Icc
    {c : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M}
    {D : RealTimeInterval} {a b : ℝ} (hab : a < b)
    (hc : c.IsSolutionOn (I := I) g (Icc a b))
    (hG : MetricFamilySmoothOn D g) (hJD : Icc a b ⊆ D.regular) :
    ∃ τ > 0, a + τ ≤ b ∧ ∃ P : CircleReparametrization (Icc a (a + τ)),
      (∀ z, P.map a z = z) ∧
        let d : CurveMap M := fun z t => c (P.map t z) t
        d.SmoothOn (I := I) (Icc a (a + τ)) ∧
          d.ImmersedOn (I := I) (Icc a (a + τ)) ∧
            ∀ x t, t ∈ Icc a (a + τ) → d.velocity (I := I) (Icc a (a + τ)) x t =
              d.speed g x t ^ (-2 : ℤ) • d.Dx g d.X x t := by
  let c₀ : CurveMap M := fun z t => c z (t + a)
  let g₀ : ℝ → SmoothRiemannianMetric I M := fun t => g (t + a)
  have hforward : MapsTo (fun t : ℝ => t + a) (Icc 0 (b - a)) (Icc a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hc₀ : c₀.IsSolutionOn (I := I) g₀ (Icc 0 (b - a)) :=
    hc.time_translate a hforward (uniqueDiffOn_Icc (sub_pos.mpr hab))
  have hJD₀ : Icc (0 : ℝ) (b - a) ⊆ (D.timeShift a).regular :=
    fun _ ht => hJD (hforward ht)
  obtain ⟨τ, hτ, hτb, P₀, hP₀, he⟩ :=
    hc₀.exists_reparametrization_parabolic_equation (sub_pos.mpr hab)
      (hG.timeShift a) hJD₀
  let e : CurveMap M := fun z t => c₀ (P₀.map t z) t
  have hesm : e.SmoothOn (I := I) (Icc 0 τ) := he.1
  have heim : e.ImmersedOn (I := I) (Icc 0 τ) := he.2.1
  have heeq : ∀ x t, t ∈ Icc (0 : ℝ) τ →
      e.velocity (I := I) (Icc 0 τ) x t =
        e.speed g₀ x t ^ (-2 : ℤ) • e.Dx g₀ e.X x t := he.2.2
  have hbackward : MapsTo (fun t : ℝ => t + -a) (Icc a (a + τ)) (Icc 0 τ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  let P : CircleReparametrization (Icc a (a + τ)) :=
    P₀.compTime (contDiff_id.add contDiff_const).contDiffOn hbackward
  have hPinitial : ∀ z, P.map a z = z := by
    intro z
    simpa only [P, CircleReparametrization.compTime, id_eq, add_neg_cancel] using hP₀ z
  let d : CurveMap M := fun z t => c (P.map t z) t
  have hde : d = fun z t => e z (t + -a) := by
    funext z t
    simp only [d, e, c₀, P, CircleReparametrization.compTime, id_eq, neg_add_cancel_right]
  refine ⟨τ, hτ, by linarith, P, hPinitial, ?_⟩
  change d.SmoothOn (I := I) (Icc a (a + τ)) ∧
    d.ImmersedOn (I := I) (Icc a (a + τ)) ∧
      ∀ x t, t ∈ Icc a (a + τ) → d.velocity (I := I) (Icc a (a + τ)) x t =
        d.speed g x t ^ (-2 : ℤ) • d.Dx g d.X x t
  rw [hde]
  refine ⟨CurveMap.smoothOn_time_translate hesm (-a) hbackward, ?_, ?_⟩
  · intro x t ht
    exact heim x (t + -a) (hbackward ht)
  · intro x t ht
    have htime := (e.time_slice_contMDiffWithinAt (Icc 0 τ) hesm x
      (t + -a) (hbackward ht)).mdifferentiableWithinAt (by simp)
    rw [CurveMap.velocity_time_translate (-a) hbackward htime
      ((uniqueDiffOn_Icc (by linarith : a < a + τ)) t ht)]
    have h := heeq x (t + -a) (hbackward ht)
    change e.velocity (I := I) (Icc 0 τ) x (t + -a) =
      e.speed (fun s => g (s + a)) x (t + -a) ^ (-2 : ℤ) •
        e.Dx (fun s => g (s + a)) e.X x (t + -a) at h
    simp only [CurveMap.speed, CurveMap.Dx, CurveMap.X, CurveMap.lift,
      neg_add_cancel_right] at h ⊢
    exact h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
