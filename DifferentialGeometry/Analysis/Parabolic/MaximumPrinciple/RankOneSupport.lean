import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Basic
import DifferentialGeometry.Geometry.Operator.LaplacianMinimum

import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Operator.GradientRegularity
import DifferentialGeometry.Topology.VectorBundle.Compactness
import Mathlib.LinearAlgebra.QuadraticForm.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

structure FirstNull
    {Z : Type*} (q : Real -> Z -> Real) (a b : Real) where
  time : Real
  direction : Z
  time_mem : time ∈ Set.Ioc a b
  nonnegative_until :
    forall t, t ∈ Set.Icc a time -> forall z, 0 <= q t z
  null : q time direction = 0

theorem exists_first_null
    {Z : Type*} [TopologicalSpace Z]
    (q : Real -> Z -> Real) (a b : Real) (K : Set Z)
    (hK : IsCompact K)
    (hcont : ContinuousOn (fun p : Real × Z => q p.1 p.2)
      (Set.Icc a b ×ˢ K))
    (hinit : forall z, 0 < q a z)
    (hout : forall t, t ∈ Set.Icc a b -> forall z, z ∉ K -> 0 < q t z)
    (hfail : exists t, t ∈ Set.Icc a b ∧ exists z, q t z <= 0) :
    Nonempty (FirstNull q a b) := by
  classical
  let slab : Set (Real × Z) := Set.Icc a b ×ˢ K
  let bad : Set (Real × Z) :=
    slab ∩ (fun p : Real × Z => q p.1 p.2) ⁻¹' Set.Iic 0
  have hslab : IsCompact slab := isCompact_Icc.prod hK
  have hcontSlab : ContinuousOn (fun p : Real × Z => q p.1 p.2) slab := by
    simpa [slab] using hcont
  have hbadCompact : IsCompact bad := by
    simpa [bad] using
      hcontSlab.lowerSemicontinuousOn.isCompact_inter_preimage_Iic hslab 0
  obtain ⟨tbad, htbad, zbad, hzbad⟩ := hfail
  have hzbadK : zbad ∈ K := by
    by_contra hz
    exact not_lt_of_ge hzbad (hout tbad htbad zbad hz)
  have hbadNonempty : bad.Nonempty :=
    ⟨(tbad, zbad), ⟨⟨htbad, hzbadK⟩, hzbad⟩⟩
  obtain ⟨p, hpbad, hpmin⟩ :=
    hbadCompact.exists_isMinOn hbadNonempty continuous_fst.continuousOn
  let t := p.1
  let z := p.2
  have ht : t ∈ Set.Icc a b := hpbad.1.1
  have hzK : z ∈ K := hpbad.1.2
  have hqnonpos : q t z <= 0 := hpbad.2
  have hta : t ≠ a := by
    intro h
    have := hinit z
    rw [h] at hqnonpos
    linarith
  have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
  have hnonnegative :
      forall s, s ∈ Set.Icc a t -> forall w, 0 <= q s w := by
    intro s hs w
    by_cases hwK : w ∈ K
    · by_contra hnot
      have hneg : q s w < 0 := lt_of_not_ge hnot
      rcases lt_or_eq_of_le hs.2 with hst | rfl
      · have hsab : s ∈ Set.Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
        have hswbad : (s, w) ∈ bad :=
          ⟨⟨hsab, hwK⟩, le_of_lt hneg⟩
        have hts : t <= s := hpmin hswbad
        exact (not_lt_of_ge hts) hst
      · obtain ⟨r, hrab, hrt, hrneg⟩ :=
          let hwcont : ContinuousOn (fun u : Real => q u w) (Set.Icc a b) :=
            hcont.comp (continuous_id.prodMk continuous_const).continuousOn
              (fun _u hu => ⟨hu, hwK⟩)
          DifferentialGeometry.PDE.RicciFlow.exists_left_neg_of_continuousOn
            (a := a) (b := t) (c := b) hat ht.2
            hwcont hneg
        have hrbad : (r, w) ∈ bad :=
          ⟨⟨hrab, hwK⟩, le_of_lt hrneg⟩
        have htr : t <= r := hpmin hrbad
        exact (not_lt_of_ge htr) hrt
    · exact (hout s ⟨hs.1, hs.2.trans ht.2⟩ w hwK).le
  have hqnonneg : 0 <= q t z := hnonnegative t ⟨le_of_lt hat, le_rfl⟩ z
  refine Nonempty.intro
    { time := t
      direction := z
      time_mem := ⟨hat, ht.2⟩
      nonnegative_until := hnonnegative
      null := le_antisymm hqnonpos hqnonneg }

theorem exists_first_null_of_compact_representatives
    {Z : Type*} [TopologicalSpace Z]
    (q : Real -> Z -> Real) (a b : Real) (K : Set Z)
    (hK : IsCompact K)
    (hcont : ContinuousOn (fun p : Real × Z => q p.1 p.2)
      (Set.Icc a b ×ˢ K))
    (hinit : forall z, 0 < q a z)
    (hrepresent : forall t, t ∈ Set.Icc a b -> forall z, q t z <= 0 ->
      exists w, w ∈ K ∧ q t w <= 0 ∧ (q t z < 0 -> q t w < 0))
    (hfail : exists t, t ∈ Set.Icc a b ∧ exists z, q t z <= 0) :
    Nonempty (FirstNull q a b) := by
  classical
  let slab : Set (Real × Z) := Set.Icc a b ×ˢ K
  let bad : Set (Real × Z) :=
    slab ∩ (fun p : Real × Z => q p.1 p.2) ⁻¹' Set.Iic 0
  have hslab : IsCompact slab := isCompact_Icc.prod hK
  have hcontSlab : ContinuousOn (fun p : Real × Z => q p.1 p.2) slab := by
    simpa [slab] using hcont
  have hbadCompact : IsCompact bad := by
    simpa [bad] using
      hcontSlab.lowerSemicontinuousOn.isCompact_inter_preimage_Iic hslab 0
  obtain ⟨tbad, htbad, zbad, hzbad⟩ := hfail
  obtain ⟨wbad, hwbadK, hwbadNonpos, _⟩ :=
    hrepresent tbad htbad zbad hzbad
  have hbadNonempty : bad.Nonempty :=
    ⟨(tbad, wbad), ⟨⟨htbad, hwbadK⟩, hwbadNonpos⟩⟩
  obtain ⟨p, hpbad, hpmin⟩ :=
    hbadCompact.exists_isMinOn hbadNonempty continuous_fst.continuousOn
  let t := p.1
  let z := p.2
  have ht : t ∈ Set.Icc a b := hpbad.1.1
  have hqnonpos : q t z <= 0 := hpbad.2
  have hta : t ≠ a := by
    intro h
    have := hinit z
    rw [h] at hqnonpos
    linarith
  have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
  have hnonnegative :
      forall s, s ∈ Set.Icc a t -> forall w, 0 <= q s w := by
    intro s hs w
    by_contra hnot
    have hneg : q s w < 0 := lt_of_not_ge hnot
    have hsab : s ∈ Set.Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
    obtain ⟨w', hw'K, _, hw'neg⟩ :=
      hrepresent s hsab w (le_of_lt hneg)
    have hneg' : q s w' < 0 := hw'neg hneg
    rcases lt_or_eq_of_le hs.2 with hst | rfl
    · have hswbad : (s, w') ∈ bad :=
        ⟨⟨hsab, hw'K⟩, le_of_lt hneg'⟩
      have hts : t <= s := hpmin hswbad
      exact (not_lt_of_ge hts) hst
    · obtain ⟨r, hrab, hrt, hrneg⟩ :=
        let hwcont : ContinuousOn (fun u : Real => q u w') (Set.Icc a b) :=
          hcont.comp (continuous_id.prodMk continuous_const).continuousOn
            (fun _u hu => ⟨hu, hw'K⟩)
        DifferentialGeometry.PDE.RicciFlow.exists_left_neg_of_continuousOn
          (a := a) (b := t) (c := b) hat ht.2 hwcont hneg'
      have hrbad : (r, w') ∈ bad :=
        ⟨⟨hrab, hw'K⟩, le_of_lt hrneg⟩
      have htr : t <= r := hpmin hrbad
      exact (not_lt_of_ge htr) hrt
  have hqnonneg : 0 <= q t z :=
    hnonnegative t ⟨le_of_lt hat, le_rfl⟩ z
  refine Nonempty.intro
    { time := t
      direction := z
      time_mem := ⟨hat, ht.2⟩
      nonnegative_until := hnonnegative
      null := le_antisymm hqnonpos hqnonneg }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [I.Boundaryless]

private theorem timeDeriv_nonpos
    {phi : Real -> Real} {a c b t d : Real}
    (hac : a < c) (hct : c < t) (htb : t <= b)
    (hmin : IsLocalMinOn phi (Set.Icc c t) t)
    (hderiv : HasDerivWithinAt phi d (Set.Ioc a b) t) :
    d <= 0 := by
  have hsubset : Set.Icc c t ⊆ Set.Ioc a b := by
    intro y hy
    exact ⟨lt_of_lt_of_le hac hy.1, hy.2.trans htb⟩
  have hderiv_c : HasDerivWithinAt phi d (Set.Icc c t) t :=
    hderiv.mono hsubset
  have hdir : c - t ∈ posTangentConeAt (Set.Icc c t) t := by
    have hseg : segment Real t c ⊆ Set.Icc c t := by
      rw [segment_symm, segment_eq_Icc (le_of_lt hct)]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonnegative :=
    hmin.hasFDerivWithinAt_nonneg hderiv_c.hasFDerivWithinAt hdir
  change 0 <= (c - t) * d at hnonnegative
  exact nonpos_of_mul_nonneg_right hnonnegative (sub_neg.mpr hct)

theorem strict_rank_one_support_of_compact_representatives
    {ZModel : Type*} {Z : M -> Type*}
    [TopologicalSpace (Bundle.TotalSpace ZModel Z)]
    (cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (G : Real -> SmoothRiemannianMetric I M)
    (q : Real -> forall x, Z x -> Real)
    (a b eta : Real) (K : Set (Bundle.TotalSpace ZModel Z))
    (heta : 0 < eta)
    (hK : IsCompact K)
    (hcont : ContinuousOn
      (fun p : Real × Bundle.TotalSpace ZModel Z => q p.1 p.2.proj p.2.2)
      (Set.Icc (a + eta) b ×ˢ K))
    (hearly : forall t, t ∈ Set.Ioc a (a + eta) ->
      forall x z, 0 < q t x z)
    (hrepresent : forall t, t ∈ Set.Icc (a + eta) b ->
      forall z : Bundle.TotalSpace ZModel Z,
        q t z.proj z.2 <= 0 ->
          exists w, w ∈ K ∧ q t w.proj w.2 <= 0 ∧
            (q t z.proj z.2 < 0 -> q t w.proj w.2 < 0))
    (hmc : forall t,
      IsMetricCompatibleGen (I := I) (cov t) (G t))
    (hsupport : forall t, t ∈ Set.Ioc (a + eta) b ->
      (forall x z, 0 <= q t x z) ->
      forall x z, q t x z = 0 ->
      exists (extension : Real -> forall y, Z y) (f : Real -> M -> Real)
          (timeDeriv : Real),
        extension t x = z ∧
        f t x = q t x (extension t x) ∧
        (∀ᶠ p in nhdsWithin (t, x) (Set.Ioc a b ×ˢ Set.univ),
          q p.1 p.2 (extension p.1 p.2) <= f p.1 p.2) ∧
        HasDerivWithinAt (fun s : Real => f s x) timeDeriv
          (Set.Ioc a b) t ∧
        MDifferentiableAt I 𝓘(Real, Real) (f t) x ∧
        (∀ᶠ y in nhds x,
          MDifferentiableAt I 𝓘(Real, Real) (f t) y) ∧
        MDiffAt (T% fun y : M =>
          gradientFun (I := I) (G t) (f t) y) x ∧
        0 < timeDeriv -
          laplacian (I := I) (cov t) (G t) (f t) x) :
    forall t, t ∈ Set.Ioc a b -> forall x z, 0 < q t x z := by
  let qTotal : Real -> Bundle.TotalSpace ZModel Z -> Real :=
    fun t z => q t z.proj z.2
  intro t ht x z
  by_cases htcut : t <= a + eta
  · exact hearly t ⟨ht.1, htcut⟩ x z
  by_contra hnot
  have hfail : exists s, s ∈ Set.Icc (a + eta) b ∧
      exists w, qTotal s w <= 0 :=
    ⟨t, ⟨le_of_not_ge htcut, ht.2⟩,
      Bundle.TotalSpace.mk' ZModel x z, le_of_not_gt hnot⟩
  have hac : a < a + eta := by linarith
  have hinit : forall w, 0 < qTotal (a + eta) w := by
    intro w
    exact hearly (a + eta) ⟨hac, le_rfl⟩ w.proj w.2
  have hcontTotal : ContinuousOn
      (fun p : Real × Bundle.TotalSpace ZModel Z => qTotal p.1 p.2)
      (Set.Icc (a + eta) b ×ˢ K) := by
    exact hcont
  have hrepresentTotal : forall s, s ∈ Set.Icc (a + eta) b ->
      forall w, qTotal s w <= 0 ->
        exists w', w' ∈ K ∧ qTotal s w' <= 0 ∧
          (qTotal s w < 0 -> qTotal s w' < 0) := by
    intro s hs w hw
    exact hrepresent s hs w hw
  obtain ⟨d⟩ := exists_first_null_of_compact_representatives
    qTotal (a + eta) b K hK hcontTotal hinit hrepresentTotal hfail
  have hnonnegative : forall y w, 0 <= q d.time y w := by
    intro y w
    exact d.nonnegative_until d.time
      ⟨le_of_lt d.time_mem.1, le_rfl⟩
      (Bundle.TotalSpace.mk' ZModel y w)
  have hnull : q d.time d.direction.proj d.direction.2 = 0 := by
    exact d.null
  obtain ⟨extension, f, dt, hextension, hvalue, hupper, htime,
      hdiff, hdiffNear, hgrad, hstrict⟩ :=
    hsupport d.time d.time_mem hnonnegative d.direction.proj d.direction.2 hnull
  have hzero : f d.time d.direction.proj = 0 := by
    rw [hvalue, hextension]
    exact hnull
  have hupperTime :
      ∀ᶠ s in nhdsWithin d.time (Set.Ioc a b),
        q s d.direction.proj (extension s d.direction.proj) <=
          f s d.direction.proj := by
    have hmap : Filter.Tendsto
        (fun s : Real => (s, d.direction.proj))
        (nhdsWithin d.time (Set.Ioc a b))
        (nhdsWithin (d.time, d.direction.proj)
          (Set.Ioc a b ×ˢ Set.univ)) := by
      rw [nhdsWithin_prod_eq, nhdsWithin_univ]
      exact Filter.Tendsto.prodMk Filter.tendsto_id tendsto_const_nhds
    exact hmap hupper
  have htimeMin :
      IsLocalMinOn (fun s : Real => f s d.direction.proj)
        (Set.Icc (a + eta) d.time) d.time := by
    have hsubset : Set.Icc (a + eta) d.time ⊆ Set.Ioc a b := by
      intro s hs
      exact ⟨hac.trans_le hs.1, hs.2.trans d.time_mem.2⟩
    unfold IsLocalMinOn IsMinFilter
    filter_upwards [hupperTime.filter_mono
        (nhdsWithin_mono d.time hsubset),
        self_mem_nhdsWithin] with s hupperS hs
    rw [hzero]
    have hqnonnegative := d.nonnegative_until s hs
      (Bundle.TotalSpace.mk' ZModel d.direction.proj
        (extension s d.direction.proj))
    exact hqnonnegative.trans hupperS
  have hdt : dt <= 0 :=
    timeDeriv_nonpos hac d.time_mem.1 d.time_mem.2 htimeMin htime
  have hupperSpace :
      ∀ᶠ y in nhds d.direction.proj,
        q d.time y (extension d.time y) <= f d.time y := by
    have htDomain : d.time ∈ Set.Ioc a b :=
      ⟨hac.trans d.time_mem.1, d.time_mem.2⟩
    have hmap : Filter.Tendsto
        (fun y : M => (d.time, y))
        (nhds d.direction.proj)
        (nhdsWithin (d.time, d.direction.proj)
          (Set.Ioc a b ×ˢ Set.univ)) := by
      rw [nhdsWithin_prod_eq, nhdsWithin_univ]
      exact Filter.Tendsto.prodMk
        (tendsto_const_nhdsWithin htDomain) Filter.tendsto_id
    exact hmap hupper
  have hmin : IsLocalMin (f d.time) d.direction.proj := by
    unfold IsLocalMin IsMinFilter
    filter_upwards [hupperSpace] with y hupperY
    rw [hzero]
    exact (hnonnegative y (extension d.time y)).trans hupperY
  have hlap : 0 <= laplacian (I := I) (cov d.time) (G d.time)
      (f d.time) d.direction.proj :=
    laplacian_nonneg_at_spatial_min_of_metricCompatible
      (I := I) (cov d.time) (G d.time) (hmc d.time)
      hmin hdiff hdiffNear hgrad
  linarith

theorem strict_rank_one_support
    {ZModel : Type*} {Z : M -> Type*}
    [TopologicalSpace (Bundle.TotalSpace ZModel Z)]
    (cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (G : Real -> SmoothRiemannianMetric I M)
    (q : Real -> forall x, Z x -> Real)
    (a b eta : Real) (K : Set (Bundle.TotalSpace ZModel Z))
    (heta : 0 < eta)
    (hK : IsCompact K)
    (hcont : ContinuousOn
      (fun p : Real × Bundle.TotalSpace ZModel Z => q p.1 p.2.proj p.2.2)
      (Set.Icc (a + eta) b ×ˢ K))
    (hearly : forall t, t ∈ Set.Ioc a (a + eta) ->
      forall x z, 0 < q t x z)
    (hout : forall t, t ∈ Set.Icc (a + eta) b ->
      forall z : Bundle.TotalSpace ZModel Z,
        z ∉ K -> 0 < q t z.proj z.2)
    (hmc : forall t,
      IsMetricCompatibleGen (I := I) (cov t) (G t))
    (hsupport : forall t, t ∈ Set.Ioc (a + eta) b ->
      (forall x z, 0 <= q t x z) ->
      forall x z, q t x z = 0 ->
      exists (extension : Real -> forall y, Z y) (f : Real -> M -> Real)
          (timeDeriv : Real),
        extension t x = z ∧
        f t x = q t x (extension t x) ∧
        (∀ᶠ p in nhdsWithin (t, x) (Set.Ioc a b ×ˢ Set.univ),
          q p.1 p.2 (extension p.1 p.2) <= f p.1 p.2) ∧
        HasDerivWithinAt (fun s : Real => f s x) timeDeriv
          (Set.Ioc a b) t ∧
        MDifferentiableAt I 𝓘(Real, Real) (f t) x ∧
        (∀ᶠ y in nhds x,
          MDifferentiableAt I 𝓘(Real, Real) (f t) y) ∧
        MDiffAt (T% fun y : M =>
          gradientFun (I := I) (G t) (f t) y) x ∧
        0 < timeDeriv -
          laplacian (I := I) (cov t) (G t) (f t) x) :
    forall t, t ∈ Set.Ioc a b -> forall x z, 0 < q t x z := by
  apply strict_rank_one_support_of_compact_representatives
    cov G q a b eta K heta hK hcont hearly ?_ hmc hsupport
  intro t ht z hz
  by_cases hzK : z ∈ K
  · exact ⟨z, hzK, hz, fun hneg => hneg⟩
  · exact False.elim ((not_lt_of_ge hz) (hout t ht z hzK))

private theorem exists_norm_eq_one_of_nonpos
    {V₀ : Type*} [NormedAddCommGroup V₀] [NormedSpace ℝ V₀]
    (Q : QuadraticForm ℝ V₀) (z : V₀) (hz : z ≠ 0) (hQ : Q z ≤ 0) :
    ∃ w : V₀, ‖w‖ = 1 ∧ Q w ≤ 0 ∧ (Q z < 0 → Q w < 0) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hc : 0 < ‖z‖⁻¹ * ‖z‖⁻¹ := mul_pos (inv_pos.mpr hn) (inv_pos.mpr hn)
  refine ⟨‖z‖⁻¹ • z, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    exact inv_mul_cancel₀ (ne_of_gt hn)
  · rw [QuadraticMap.map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le hQ
  · intro h
    rw [QuadraticMap.map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc h


variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]

theorem strict_rank_one_support_quadraticForm
    (G : ℝ → SmoothRiemannianMetric I M)
    (Q : ℝ → ∀ x, QuadraticForm ℝ (V x))
    (a b η : ℝ) (K : Set M) (hη : 0 < η) (hK : IsCompact K)
    (hcont : ContinuousOn
      (fun p : ℝ × TotalSpace F V => Q p.1 p.2.proj p.2.2)
      (Icc (a + η) b ×ˢ {z | z.proj ∈ K ∧ ‖z.2‖ = 1}))
    (hearly : ∀ t ∈ Ioc a (a + η), ∀ x z, z ≠ 0 → 0 < Q t x z)
    (hout : ∀ t ∈ Icc (a + η) b, ∀ x, x ∉ K → ∀ z, z ≠ 0 → 0 < Q t x z)
    (hsupport : ∀ t ∈ Ioc (a + η) b, (∀ x z, 0 ≤ Q t x z) →
      ∀ x z, z ≠ 0 → Q t x z = 0 →
      ∃ (extension : ℝ → ∀ y, V y) (f : ℝ → M → ℝ) (timeDeriv : ℝ),
        extension t x = z ∧
        ContinuousWithinAt
          (fun p : ℝ × M => (⟨p.2, extension p.1 p.2⟩ : TotalSpace F V))
          (Ioc a b ×ˢ univ) (t, x) ∧
        f t x = 0 ∧
        (∀ᶠ p in nhdsWithin (t, x) (Ioc a b ×ˢ univ),
          Q p.1 p.2 (extension p.1 p.2) ≤ f p.1 p.2) ∧
        HasDerivWithinAt (fun s => f s x) timeDeriv (Ioc a b) t ∧
        MDifferentiableAt I 𝓘(ℝ, ℝ) (f t) x ∧
        (∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ, ℝ) (f t) y) ∧
        MDiffAt (T% fun y : M => gradientFun (I := I) (G t) (f t) y) x ∧
        0 < timeDeriv - laplacian (I := I) (LeviCivita (G t)) (G t) (f t) x) :
    ∀ t ∈ Ioc a b, ∀ x z, z ≠ 0 → 0 < Q t x z := by
  classical
  let q : ℝ → ∀ x, V x → ℝ := fun t x z => if z = 0 then 1 else Q t x z
  let C : Set (TotalSpace F V) := {z | z.proj ∈ K ∧ ‖z.2‖ = 1}
  have hC : IsCompact C := hK.bundle_norm_eq (F := F) (V := V) 1
  have hq (t : ℝ) (x : M) (z : V x) (hz : z ≠ 0) : q t x z = Q t x z := if_neg hz
  have hncont : Continuous (fun z : TotalSpace F V => ‖z.2‖) := by
    have hi : Continuous (fun z : TotalSpace F V => inner ℝ z.2 z.2) :=
      continuous_id.inner_bundle continuous_id
    simpa only [← norm_eq_sqrt_real_inner] using hi.sqrt
  have hpos := strict_rank_one_support_of_compact_representatives
    (ZModel := F) (Z := V) (fun t => LeviCivita (G t)) G q a b η C hη hC
    (hcont.congr (by
      intro p hp
      apply hq
      intro hz
      have hn := hp.2.2
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn))
    (by
      intro t ht x z
      by_cases hz : z = 0
      · simp only [q, hz, if_pos rfl, zero_lt_one]
      · rw [hq t x z hz]
        exact hearly t ht x z hz)
    (by
      intro t ht z hnonpos
      have hz : z.2 ≠ 0 := by
        intro hz
        have hf : (1 : ℝ) ≤ 0 := by simpa only [q, hz, if_pos rfl] using hnonpos
        linarith
      rw [hq t z.proj z.2 hz] at hnonpos
      have hx : z.proj ∈ K := by
        by_contra hx
        exact (not_lt_of_ge hnonpos) (hout t ht z.proj hx z.2 hz)
      obtain ⟨w, hw, hwQ, hwneg⟩ := exists_norm_eq_one_of_nonpos (Q t z.proj) z.2 hz hnonpos
      have hw0 : w ≠ 0 := by
        intro hzero
        rw [hzero, norm_zero] at hw
        exact zero_ne_one hw
      refine ⟨⟨z.proj, w⟩, ⟨hx, hw⟩, ?_, ?_⟩
      · exact (hq t z.proj w hw0).symm ▸ hwQ
      · intro hneg
        rw [hq t z.proj w hw0]
        exact hwneg ((hq t z.proj z.2 hz) ▸ hneg))
    (fun t => leviCivitaConnectionOfMetric_isMetricCompatible (G t))
    (by
      intro t ht hnonneg x z hzero
      have hz : z ≠ 0 := by
        intro hz
        simp only [q, hz, if_pos rfl, one_ne_zero] at hzero
      have hQzero : Q t x z = 0 := (hq t x z hz) ▸ hzero
      have hQnonneg : ∀ y w, 0 ≤ Q t y w := by
        intro y w
        by_cases hw : w = 0
        · simp [hw]
        · exact (hq t y w hw) ▸ hnonneg y w
      obtain ⟨extension, f, dt, hext, hextcont, hfzero, hupper, hdt, hdiff, hdiffNear,
        hgrad, hstrict⟩ := hsupport t ht hQnonneg x z hz hQzero
      have hn : ContinuousWithinAt (fun p : ℝ × M => ‖extension p.1 p.2‖)
          (Ioc a b ×ˢ univ) (t, x) := hncont.continuousAt.comp_continuousWithinAt hextcont
      have hnormpos : 0 < ‖extension t x‖ := by rw [hext]; exact norm_pos_iff.mpr hz
      have hnear : ∀ᶠ p in nhdsWithin (t, x) (Ioc a b ×ˢ univ), extension p.1 p.2 ≠ 0 := by
        have hp := hn.preimage_mem_nhdsWithin (Ioi_mem_nhds hnormpos)
        filter_upwards [hp] with p hp
        exact norm_pos_iff.mp hp
      refine ⟨extension, f, dt, hext, ?_, ?_, hdt, hdiff, hdiffNear, hgrad, hstrict⟩
      · rw [hext, hq t x z hz, hQzero, hfzero]
      · filter_upwards [hupper, hnear] with p hp hz
        rw [hq p.1 p.2 _ hz]
        exact hp)
  intro t ht x z hz
  exact (hq t x z hz) ▸ hpos t ht x z


theorem strict_rank_one_support_bilinForm
    (G : ℝ → SmoothRiemannianMetric I M)
    (B : ℝ → ∀ x, LinearMap.BilinForm ℝ (V x))
    (a b η : ℝ) (K : Set M) (hη : 0 < η) (hK : IsCompact K)
    (hcont : ContinuousOn
      (fun p : ℝ × TotalSpace F V => B p.1 p.2.proj p.2.2 p.2.2)
      (Icc (a + η) b ×ˢ {z | z.proj ∈ K ∧ ‖z.2‖ = 1}))
    (hearly : ∀ t ∈ Ioc a (a + η), ∀ x z, z ≠ 0 → 0 < B t x z z)
    (hout : ∀ t ∈ Icc (a + η) b, ∀ x, x ∉ K → ∀ z, z ≠ 0 → 0 < B t x z z)
    (hsupport : ∀ t ∈ Ioc (a + η) b, (∀ x z, 0 ≤ B t x z z) →
      ∀ x z, z ≠ 0 → B t x z z = 0 →
      ∃ (extension : ℝ → ∀ y, V y) (f : ℝ → M → ℝ) (timeDeriv : ℝ),
        extension t x = z ∧
        ContinuousWithinAt
          (fun p : ℝ × M => (⟨p.2, extension p.1 p.2⟩ : TotalSpace F V))
          (Ioc a b ×ˢ univ) (t, x) ∧
        f t x = 0 ∧
        (∀ᶠ p in nhdsWithin (t, x) (Ioc a b ×ˢ univ),
          B p.1 p.2 (extension p.1 p.2) (extension p.1 p.2) ≤ f p.1 p.2) ∧
        HasDerivWithinAt (fun s => f s x) timeDeriv (Ioc a b) t ∧
        MDifferentiableAt I 𝓘(ℝ, ℝ) (f t) x ∧
        (∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(ℝ, ℝ) (f t) y) ∧
        MDiffAt (T% fun y : M => gradientFun (I := I) (G t) (f t) y) x ∧
        0 < timeDeriv - laplacian (I := I) (LeviCivita (G t)) (G t) (f t) x) :
    ∀ t ∈ Ioc a b, ∀ x z, z ≠ 0 → 0 < B t x z z := by
  exact strict_rank_one_support_quadraticForm G
    (fun t x => (B t x).toQuadraticMap) a b η K hη hK hcont hearly hout hsupport


theorem strict_rank_one_support_bilinForm_of_contMDiffAt
    (G : ℝ → SmoothRiemannianMetric I M)
    (B : ℝ → ∀ x, LinearMap.BilinForm ℝ (V x))
    (a b η : ℝ) (K : Set M) (hη : 0 < η) (hK : IsCompact K)
    (hcont : ContinuousOn
      (fun p : ℝ × TotalSpace F V => B p.1 p.2.proj p.2.2 p.2.2)
      (Icc (a + η) b ×ˢ {z | z.proj ∈ K ∧ ‖z.2‖ = 1}))
    (hearly : ∀ t ∈ Ioc a (a + η), ∀ x z, z ≠ 0 → 0 < B t x z z)
    (hout : ∀ t ∈ Icc (a + η) b, ∀ x, x ∉ K → ∀ z, z ≠ 0 → 0 < B t x z z)
    (hsupport : ∀ t ∈ Ioc (a + η) b, (∀ x z, 0 ≤ B t x z z) →
      ∀ x z, z ≠ 0 → B t x z z = 0 →
      ∃ (extension : ℝ → ∀ y, V y) (f : ℝ → M → ℝ),
        extension t x = z ∧
        ContinuousWithinAt
          (fun p : ℝ × M => (⟨p.2, extension p.1 p.2⟩ : TotalSpace F V))
          (Ioc a b ×ˢ univ) (t, x) ∧
        f t x = 0 ∧
        (∀ᶠ p in nhdsWithin (t, x) (Ioc a b ×ˢ univ),
          B p.1 p.2 (extension p.1 p.2) (extension p.1 p.2) ≤ f p.1 p.2) ∧
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
          (fun p : ℝ × M => f p.1 p.2) (t, x) ∧
        0 < deriv (fun s => f s x) t - laplacian (I := I) (LeviCivita (G t)) (G t) (f t) x) :
    ∀ t ∈ Ioc a b, ∀ x z, z ≠ 0 → 0 < B t x z z := by
  apply strict_rank_one_support_bilinForm G B a b η K hη hK hcont hearly hout
  intro t ht hnonneg x z hz hzero
  obtain ⟨extension, f, hext, hextcont, hfzero, hupper, hf, hstrict⟩ :=
    hsupport t ht hnonneg x z hz hzero
  have hfs : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (f t) x :=
    hf.comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  have hft : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 (fun s => f s x) t :=
    hf.comp t (contMDiffAt_id.prodMk contMDiffAt_const)
  have htime : DifferentiableAt ℝ (fun s => f s x) t :=
    (contMDiffAt_iff_contDiffAt.mp hft).differentiableAt (by norm_num)
  refine ⟨extension, f, deriv (fun s => f s x) t, hext, hextcont, hfzero, hupper,
    htime.hasDerivAt.hasDerivWithinAt, hfs.mdifferentiableAt (by norm_num), ?_,
    (gradientFun_contMDiffAt_one (G t) hfs).mdifferentiableAt one_ne_zero, hstrict⟩
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (by norm_num : (2 : WithTop ℕ∞) ≠ ∞)).mp hfs
  filter_upwards [hnear] with y hy
  exact hy.mdifferentiableAt (by norm_num)

end DifferentialGeometry.Analysis.Parabolic
