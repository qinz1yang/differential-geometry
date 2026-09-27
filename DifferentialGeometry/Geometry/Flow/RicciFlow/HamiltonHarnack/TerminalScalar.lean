import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [NeZero (Module.finrank ℝ E)]

private local instance scalarTerminalIsManifoldOne : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

variable {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
  (hS : IsSolutionOn S)
  (hcomplete : ∀ t ∈ D.regular,
    RiemannianMetricComplete (I := I) (S.base.metric t))
  (hcurv : ∀ c d : ℝ, Set.Icc c d ⊆ D.regular →
    ∃ C : ℝ, ∀ t ∈ Set.Icc c d, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
  (hR : ∀ t ∈ D.regular, ∀ x : M,
    metricAlgebraicCurvatureTensorAt (I := I) (S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))

include hS hcomplete hcurv hR

private theorem scalar_trace_finite_left
    {a t : ℝ} (hat : a < t) (hregular : Set.Ioc a t ⊆ D.regular) (x : M) :
    0 ≤ deriv (fun s : ℝ => S.scalar s x) t + S.scalar t x / (t - a) := by
  have hlimit := hamilton_finite_origin_matrix_limit
    (q := deriv (fun s : ℝ => S.scalar s x) t)
    (c := 2 * S.scalar t x) (sub_pos.mpr hat) (fun α hα => by
      let clock : HarnackClock := ⟨a + α, t, by linarith [hα.2]⟩
      have hclock : Set.Icc clock.origin clock.time ⊆ D.regular := by
        intro s hs
        exact hregular ⟨(lt_add_of_pos_right a hα.1).trans_le hs.1, hs.2⟩
      have h := hamilton_trace_harnack (I := I) S hS hcomplete hcurv hR
        clock hclock x (0 : TangentSpace I x)
      have hRicZero : metricRicci (I := I) (S.base.metric t) x
          (vec2 (0 : TangentSpace I x) 0) = 0 :=
        (metricRicci (I := I) (S.base.metric t) x).map_coord_zero
          (i := 0) (by simp [vec2])
      change 0 ≤ deriv (fun s : ℝ => S.scalar s x) t +
        S.scalar t x / (t - (a + α)) + _ + _ at h
      rw [hRicZero] at h
      have h' : 0 ≤ deriv (fun s : ℝ => S.scalar s x) t +
          S.scalar t x / (t - (a + α)) := by simpa using h
      convert h' using 1
      field_simp
      ring)
  convert hlimit using 1
  field_simp

theorem hamilton_scalar_le_terminal
    {a b t : ℝ} (hat : a < t) (htb : t ≤ b)
    (hb : b ∈ D.carrier)
    (hregular : Set.Ioo a b ⊆ D.regular) (x : M) :
    S.scalar t x ≤ (b - a) * S.scalar b x / (t - a) := by
  have hcarrier : Set.Icc t b ⊆ D.carrier := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hsb | rfl
    · exact D.regular_subset (hregular ⟨hat.trans_le hs.1, hsb⟩)
    · exact hb
  have hcont : ContinuousOn (fun s : ℝ => S.scalar s x) (Set.Icc t b) := by
    have hmap : Continuous (fun s : ℝ => (s, x)) :=
      continuous_id.prodMk continuous_const
    simpa only [Function.comp_def] using hS.scalarCont.comp hmap.continuousOn
      (fun s hs => ⟨hcarrier hs, Set.mem_univ x⟩)
  have hmono := hamilton_shifted_scalar_monotoneOn
    (R := fun s : ℝ => S.scalar s x)
    (dR := fun s : ℝ => deriv (fun r : ℝ => S.scalar r x) s)
    hat.le ((continuousOn_id.sub continuousOn_const).mul hcont)
    (fun s hs => by
      have hsreg : s ∈ D.regular := hregular ⟨hat.trans hs.1, hs.2⟩
      exact ((hS.scalarTime (K := D.carrier) (D.regular_subset hsreg)
        subset_rfl x).differentiableAt (D.regular_mem_nhds hsreg)).hasDerivAt)
    (fun s hs => scalar_trace_finite_left S hS hcomplete hcurv hR
      (hat.trans hs.1) (fun r hr => hregular ⟨hr.1, hr.2.trans_lt hs.2⟩) x)
  have hscaled := hamilton_shifted_scalar_two_time htb hmono
  exact (le_div_iff₀ (sub_pos.mpr hat)).2 (by simpa only [mul_comm] using hscaled)

theorem hamilton_scalar_le_terminal_bound
    {a b t C : ℝ} (hat : a < t) (htb : t ≤ b)
    (hb : b ∈ D.carrier)
    (hregular : Set.Ioo a b ⊆ D.regular)
    (x : M) (hbound : S.scalar b x ≤ C) :
    S.scalar t x ≤ (b - a) * C / (t - a) := by
  exact (hamilton_scalar_le_terminal S hS hcomplete hcurv hR hat htb
    hb hregular x).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr (hat.le.trans htb)))
      (sub_nonneg.mpr hat.le))

theorem hamilton_ancient_scalar_le_terminal
    {b t : ℝ} (htb : t ≤ b) (hb : b ∈ D.carrier)
    (hregular : Set.Iio b ⊆ D.regular) (x : M) :
    S.scalar t x ≤ S.scalar b x := by
  rcases htb.eq_or_lt with rfl | hlt
  · exact le_rfl
  apply hamilton_ancient_two_time_limit hlt
  intro a hat
  have h := hamilton_scalar_le_terminal S hS hcomplete hcurv hR
    hat htb hb (fun _ hu => hregular hu.2) x
  have hab : 0 < b - a := sub_pos.mpr (hat.trans_le htb)
  have h' := (le_div_iff₀ (sub_pos.mpr hat)).mp h
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hab).mpr
  nlinarith [h']


end DifferentialGeometry.PDE.RicciFlow

end
