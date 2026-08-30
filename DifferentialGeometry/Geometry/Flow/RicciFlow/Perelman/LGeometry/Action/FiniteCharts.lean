import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.KineticChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ScalarCompact
import DifferentialGeometry.Geometry.Operator.MetricFamilyGramWeak
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ChartTimeH1
import DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision
import DifferentialGeometry.Topology.UniformConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology Interval

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M]
variable {D : RealTimeInterval}

def lSegLen {m : ℕ} (t : Fin (m + 1) → Real) (i : Fin m) : Real :=
  t i.succ - t i.castSucc

omit [CompactSpace M] in
theorem exists_chartH1_fin
    [I.Boundaryless]
    (a b : Real) {m : ℕ} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (Kman : Fin m → Set M)
    (hKc : ∀ i, IsCompact (Kman i))
    (hKsrc : ∀ i, Kman i ⊆ (chartAt H (p i)).source)
    (gamma : Real → M) (hgamma : ContinuousOn gamma (Icc a b))
    (hgammaK : ∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
      (interior (Kman i)))
    (alpha : ℕ → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Icc a b))
    (hunif : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha n s.1) (fun s ↦ gamma s.1) atTop) :
    ∃ (N : ℕ) (Kcoord : Fin m → Set E)
      (u : (i : Fin m) → ℕ → timeH1 E (lSegLen t i)),
      (∀ i, IsCompact (Kcoord i)) ∧
      (∀ i, Kcoord i ⊆ interior (extChartAt I (p i)).target) ∧
      (∀ i n, MapsTo (alpha (n + N)) (Icc (t i.castSucc) (t i.succ))
        (chartAt H (p i)).source) ∧
      (∀ i n, EqOn (u i n).toFun
        (fun r ↦ extChartAt I (p i) (alpha (n + N) (t i.castSucc + r)))
        (Icc (0 : Real) (lSegLen t i))) ∧
      (∀ i n (r : Icc (0 : Real) (lSegLen t i)),
        (u i n).toFun r.1 ∈ Kcoord i) := by
  classical
  have hab : a ≤ b := by
    rw [← ht0, ← htlast]
    exact htmono (Fin.zero_le _)
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hpieceSub (i : Fin m) :
      Icc (t i.castSucc) (t i.succ) ⊆ Icc a b :=
    Icc_subset_Icc (hleft i) (hright i)
  have hconv (i : Fin m) : TendstoUniformly
      (fun n (s : Icc (t i.castSucc) (t i.succ)) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) atTop := by
    let incl : Icc (t i.castSucc) (t i.succ) → Icc a b :=
      fun s ↦ ⟨s.1, hpieceSub i s.2⟩
    with_unfolding_all exact hunif.comp incl
  have hevent (i : Fin m) : ∀ᶠ n in atTop,
      MapsTo (alpha n) (Icc (t i.castSucc) (t i.succ))
        (interior (Kman i)) := by
    have hgammaCont : Continuous
        (fun s : Icc (t i.castSucc) (t i.succ) ↦ gamma s.1) :=
      (hgamma.mono (hpieceSub i)).domRestrict
    have hmap : MapsTo
        (fun s : Icc (t i.castSucc) (t i.succ) ↦ gamma s.1) univ
        (interior (Kman i)) := by
      intro s _
      exact hgammaK i s.2
    have hev := DifferentialGeometry.eventually_mapsTo_of_tendstoUniformly
      (hconv i) isCompact_univ hgammaCont.continuousOn isOpen_interior hmap
    filter_upwards [hev] with n hn
    intro s hs
    exact hn (mem_univ (⟨s, hs⟩ : Icc (t i.castSucc) (t i.succ)))
  have hall : ∀ᶠ n in atTop, ∀ i, MapsTo (alpha n)
      (Icc (t i.castSucc) (t i.succ)) (interior (Kman i)) :=
    Filter.eventually_all.mpr hevent
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  have htail (i : Fin m) (n : ℕ) : MapsTo (alpha (n + N))
      (Icc (t i.castSucc) (t i.succ)) (interior (Kman i)) :=
    hN (n + N) (Nat.le_add_left N n) i
  let Kcoord : Fin m → Set E := fun i ↦ extChartAt I (p i) '' Kman i
  have hKcoordC (i : Fin m) : IsCompact (Kcoord i) :=
    (hKc i).image_of_continuousOn
      ((continuousOn_extChartAt (I := I) (p i)).mono (by
        simpa only [extChartAt_source] using hKsrc i))
  have hKcoordChart (i : Fin m) :
      Kcoord i ⊆ interior (extChartAt I (p i)).target := by
    rw [interior_eq_iff_isOpen.mpr (isOpen_extChartAt_target (I := I) (p i))]
    rintro _ ⟨x, hx, rfl⟩
    exact (extChartAt I (p i)).map_source (by
      rw [extChartAt_source]
      exact hKsrc i hx)
  have hsrc (i : Fin m) (n : ℕ) : MapsTo (alpha (n + N))
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source :=
    (htail i n).mono_right (interior_subset.trans (hKsrc i))
  have hshift (i : Fin m) : MapsTo (fun r : Real ↦ t i.castSucc + r)
      (Icc (0 : Real) (lSegLen t i)) (Icc a b) := by
    intro r hr
    change r ∈ Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    exact ⟨by linarith [hleft i, hr.1], by linarith [hr.2, hright i]⟩
  have hshiftPiece (i : Fin m) : MapsTo (fun r : Real ↦ t i.castSucc + r)
      (Icc (0 : Real) (lSegLen t i)) (Icc (t i.castSucc) (t i.succ)) := by
    intro r hr
    change r ∈ Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hlocalMD (i : Fin m) (n : ℕ) : ContMDiffOn 𝓘(Real, Real) I 1
      (fun r : Real ↦ alpha (n + N) (t i.castSucc + r))
      (Icc (0 : Real) (lSegLen t i)) :=
    (halpha (n + N)).comp
      (contMDiff_const.add contMDiff_id).contMDiffOn (hshift i)
  have hlocalSrc (i : Fin m) (n : ℕ) : MapsTo
      (fun r : Real ↦ alpha (n + N) (t i.castSucc + r))
      (Icc (0 : Real) (lSegLen t i)) (chartAt H (p i)).source :=
    (hsrc i n).comp (hshiftPiece i)
  let u : (i : Fin m) → ℕ → timeH1 E (lSegLen t i) := fun i n ↦
    chartTimeH1 I (sub_nonneg.mpr (hseg i)) (p i)
      (fun r ↦ alpha (n + N) (t i.castSucc + r))
      (hlocalMD i n) (hlocalSrc i n)
  have hrep (i : Fin m) (n : ℕ) : EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha (n + N) (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)) := by
    with_unfolding_all
      exact chartTimeH1_toFun I (sub_nonneg.mpr (hseg i)) (p i)
        (fun r ↦ alpha (n + N) (t i.castSucc + r))
        (hlocalMD i n) (hlocalSrc i n)
  refine ⟨N, Kcoord, u, hKcoordC, hKcoordChart, hsrc, hrep, ?_⟩
  intro i n r
  rw [hrep i n r.2]
  refine ⟨alpha (n + N) (t i.castSucc + r.1), ?_, rfl⟩
  exact interior_subset (htail i n (hshiftPiece i r.2))

theorem lChartH1_fin
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) {m : ℕ} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (alpha : ℕ → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Icc a b))
    (hLag : ∀ n, IntervalIntegrable (lRegLag S T (alpha n)) volume a b)
    (u : (i : Fin m) → ℕ → timeH1 E (lSegLen t i))
    (hsrc : ∀ i n, MapsTo (alpha n) (Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i n, EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKchart : ∀ i, K i ⊆ interior (extChartAt I (p i)).target)
    (huK : ∀ i n (r : Icc (0 : Real) (lSegLen t i)),
      (u i n).toFun r.1 ∈ K i)
    {A : Real} (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ (phi : ℕ → ℕ)
      (uLim : (i : Fin m) → timeH1 E (lSegLen t i)),
      StrictMono phi ∧
        (∀ i (z : timeL2 E (lSegLen t i)),
          Tendsto (fun n ↦ inner Real (u i (phi n)).deriv z) atTop
            (nhds (inner Real (uLim i).deriv z))) ∧
        (∀ i, TendstoUniformly
          (fun n (r : Icc (0 : Real) (lSegLen t i)) ↦
            (u i (phi n)).toFun r.1)
          (fun r ↦ (uLim i).toFun r.1) atTop) := by
  classical
  have hab : a ≤ b := by
    rw [← ht0, ← htlast]
    exact htmono (Fin.zero_le _)
  let kin : ℕ → Real := fun n ↦ ∫ s in a..b, (1 / 2 : Real) *
    (S.base.metric (T - s ^ 2)).inner (alpha n s)
      (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)
  let pot : ℕ → Real := fun n ↦
    ∫ s in a..b, 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)
  have hcarrier : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hreg s (by simpa only [uIcc_of_le hab] using hs))
  have hpotInt (n : ℕ) : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s)) volume a b :=
    lScalar_int (I := I) S hSc T a b (alpha n) hcarrier (by
      simpa only [uIcc_of_le hab] using (halpha n).continuousOn)
  have hkinInt (n : ℕ) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s)
          (lVelocity (I := I) (alpha n) s)) volume a b := by
    simpa only [lRegLag, add_sub_cancel_right] using (hLag n).sub (hpotInt n)
  have hsplit (n : ℕ) : lRegAction S T (alpha n) a b = kin n + pot n := by
    simpa only [lRegAction, lRegLag, kin, pot] using
      intervalIntegral.integral_add (hkinInt n) (hpotInt n)
  obtain ⟨C, hC⟩ := lScalar_lower (I := I) S hSc T a b hcarrier
  have hpotLower (n : ℕ) : C * (b - a) ≤ pot n := by
    have hmono := intervalIntegral.integral_mono_on hab
      intervalIntegrable_const (hpotInt n) (fun s hs ↦
        hC s (by simpa only [uIcc_of_le hab] using hs) (alpha n s))
    rw [intervalIntegral.integral_const] at hmono
    simpa only [pot, smul_eq_mul, mul_comm] using hmono
  let B : Real := A - C * (b - a)
  have hkinBound (n : ℕ) : kin n ≤ B := by
    have ha := hact n
    rw [hsplit n] at ha
    dsimp only [B]
    linarith [ha, hpotLower n]
  have hkinNonneg (n : ℕ) :
      ∀ᵐ s ∂volume.restrict (Ioc a b), 0 ≤ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s)
          (lVelocity (I := I) (alpha n) s) := by
    apply Eventually.of_forall
    intro s
    apply mul_nonneg (by norm_num)
    let v := lVelocity (I := I) (alpha n) s
    by_cases hv : v = 0
    · change 0 ≤ (S.base.metric (T - s ^ 2)).inner (alpha n s) v v
      rw [hv]
      simp
    · exact ((S.base.metric (T - s ^ 2)).pos (alpha n s) v hv).le
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hdiff (i : Fin m) (n : ℕ) :
      ∀ᵐ r ∂timeMeasure (lSegLen t i),
        MDifferentiableAt (modelWithCornersSelf Real Real) I
          (alpha n) (t i.castSucc + r) := by
    have hmem : ∀ᵐ r ∂timeMeasure (lSegLen t i),
        r ∈ Ioo (0 : Real) (lSegLen t i) := by
      unfold timeMeasure
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with r hr
    change r ∈ Ioo (0 : Real) (t i.succ - t i.castSucc) at hr
    have hsIoo : t i.castSucc + r ∈ Ioo a b := by
      constructor <;> linarith [hr.1, hr.2, hleft i, hright i]
    have hsWithin := halpha n (t i.castSucc + r) ⟨hsIoo.1.le, hsIoo.2.le⟩
    exact (hsWithin.contMDiffAt
      (Icc_mem_nhds hsIoo.1 hsIoo.2)).mdifferentiableAt (by norm_num)
  have hpiece (i : Fin m) (n : ℕ) :
      (∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha n s)
          (lVelocity (I := I) (alpha n) s)
          (lVelocity (I := I) (alpha n) s)) ≤ B := by
    have hmono :
        (∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
          (S.base.metric (T - s ^ 2)).inner (alpha n s)
            (lVelocity (I := I) (alpha n) s)
            (lVelocity (I := I) (alpha n) s)) ≤ kin n := by
      exact intervalIntegral.integral_mono_interval (hleft i) (hseg i) (hright i)
        (hkinNonneg n) (hkinInt n)
    exact hmono.trans (hkinBound n)
  have hchart (i : Fin m) (n : ℕ) :
      (∫ r in (0 : Real)..lSegLen t i, (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (u i n).toFun r) ((u i n).deriv r))
        ((u i n).deriv r)) ≤ B := by
    have heq :
        (∫ r in (0 : Real)..lSegLen t i,
          (1 / 2 : Real) * inner Real
            (chartGramOp (I := I) S.family (p i)
              (T - (t i.castSucc + r) ^ 2, (u i n).toFun r) ((u i n).deriv r))
            ((u i n).deriv r)) =
          ∫ s in t i.castSucc..t i.succ, (1 / 2 : Real) *
            (S.base.metric (T - s ^ 2)).inner (alpha n s)
              (lVelocity (I := I) (alpha n) s)
              (lVelocity (I := I) (alpha n) s) := by
      simpa only [lSegLen, smul_apply, real_inner_smul_left] using
        (lKinetic_local S T (alpha n) (p i) (t i.castSucc) (t i.succ)
          (hseg i) (u i n) (hsrc i n) (hrep i n) (hdiff i n)).symm
    rw [heq]
    exact hpiece i n
  have hτc (i : Fin m) : ContinuousOn
      (fun r : Real ↦ T - (t i.castSucc + r) ^ 2)
      (Icc (0 : Real) (lSegLen t i)) :=
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτreg (i : Fin m) : MapsTo
      (fun r : Real ↦ T - (t i.castSucc + r) ^ 2)
      (Icc (0 : Real) (lSegLen t i)) D.regular := by
    intro r hr
    change r ∈ Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    apply hreg (t i.castSucc + r)
    exact ⟨by linarith [hleft i, hr.1], by linarith [hr.2, hright i]⟩
  exact chartH1_fin (I := I) hMet p
    (fun i ↦ lSegLen t i) (fun i ↦ by
      change 0 ≤ t i.succ - t i.castSucc
      exact sub_nonneg.mpr (hseg i))
    (fun i r ↦ T - (t i.castSucc + r) ^ 2) hτc hτreg K hKc hKchart
    u (fun _ ↦ B) huK hchart

end DifferentialGeometry.PDE.RicciFlow.Perelman
