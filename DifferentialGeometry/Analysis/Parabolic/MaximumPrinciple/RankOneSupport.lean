import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Basic
import DifferentialGeometry.Geometry.Operator.LaplacianMinimum

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

private structure FirstNull
    {Z : Type*} (q : Real -> Z -> Real) (a b : Real) where
  time : Real
  direction : Z
  time_mem : time ∈ Set.Ioc a b
  nonnegative_until :
    forall t, t ∈ Set.Icc a time -> forall z, 0 <= q t z
  null : q time direction = 0

private theorem exists_firstNull
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

private theorem exists_firstNull_of_compact_representatives
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
  obtain ⟨d⟩ := exists_firstNull_of_compact_representatives
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

end DifferentialGeometry.Analysis.Parabolic
