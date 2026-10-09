import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition

set_option autoImplicit false
namespace DifferentialGeometry.CheegerGromovCompactness
open Analysis Filter Topology
open scoped ContDiff
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem tendstoUniformlyOn_iteratedFDeriv_comp_moving_finite
    {K : Set E} {V K' : Set F} {p : ℕ}
    {A : ℕ → F → G} {Ainf : F → G} {B : ℕ → E → F} {Binf : E → F}
    (hV : IsOpen V) (hK' : IsCompact K') (hK'V : K' ⊆ V)
    (hA : MapCPConvergenceOn K' p A Ainf)
    (hAc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (p : ℕ∞) Ainf V)
    (hB : TendstoUniformlyOn B Binf atTop K)
    (hBK' : ∀ᶠ k in atTop, Set.MapsTo (B k) K K')
    (hBinfK' : Set.MapsTo Binf K K') (r : ℕ) (hr : r ≤ p) :
    TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ r (A k) (B k x))
      (fun x => iteratedFDeriv ℝ r Ainf (Binf x)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hAder :
      TendstoUniformlyOn
        (fun k y => iteratedFDeriv ℝ r (A k) y)
        (fun y => iteratedFDeriv ℝ r Ainf y) atTop K' :=
    hA.tendstoUniformlyOn_iteratedFDeriv hV hK'V hAc hAinfc hr
  have hDcont : ContinuousOn (fun y => iteratedFDeriv ℝ r Ainf y) K' :=
    ((ContinuousOn.continuousOn_iteratedFDeriv hAinfc hV
      (by exact_mod_cast hr)).mono hK'V)
  have hDuc : UniformContinuousOn (fun y => iteratedFDeriv ℝ r Ainf y) K' :=
    hK'.uniformContinuousOn_of_continuous hDcont
  have hDcomp :
      TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ r Ainf (B k x))
        (fun x => iteratedFDeriv ℝ r Ainf (Binf x)) atTop K :=
    UniformContinuousOn.comp_tendstoUniformlyOn_eventually hBK' hBinfK' hDuc hB
  rw [Metric.tendstoUniformlyOn_iff] at hAder hDcomp
  obtain ⟨NA, hNA⟩ := eventually_atTop.mp (hAder (ε / 2) (by positivity))
  obtain ⟨NB, hNB⟩ := eventually_atTop.mp (hDcomp (ε / 2) (by positivity))
  obtain ⟨NM, hNM⟩ := eventually_atTop.mp hBK'
  rw [eventually_atTop]
  refine ⟨max (max NA NB) NM, fun k hk x hx => ?_⟩
  have hkA : NA ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hk)
  have hkB : NB ≤ k := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hk)
  have hkM : NM ≤ k := le_trans (le_max_right _ _) hk
  have hBxK' : B k x ∈ K' := hNM k hkM hx
  calc
    dist (iteratedFDeriv ℝ r Ainf (Binf x))
        (iteratedFDeriv ℝ r (A k) (B k x))
        ≤ dist (iteratedFDeriv ℝ r Ainf (Binf x))
              (iteratedFDeriv ℝ r Ainf (B k x))
          + dist (iteratedFDeriv ℝ r Ainf (B k x))
              (iteratedFDeriv ℝ r (A k) (B k x)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        exact add_lt_add (hNB k hkB x hx) (hNA k hkA (B k x) hBxK')
    _ = ε := by ring

theorem MapCPConvergenceOn.comp_finite
    {U K : Set E} {V : Set F} {p : ℕ} (hU : IsOpen U) (hV : IsOpen V)
    [ProperSpace F]
    {B : ℕ → E → F} {Binf : E → F} {A : ℕ → F → G} {Ainf : F → G}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hB : MapCPConvergenceOn K p B Binf)
    (hA : ∀ S : Set F, IsCompact S → S ⊆ V → MapCPConvergenceOn S p A Ainf)
    (hBc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (B k) U)
    (hBinfc : ContDiffOn ℝ (p : ℕ∞) Binf U)
    (hAc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (p : ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V) (hmapk : ∀ k, Set.MapsTo (B k) U V) :
    MapCPConvergenceOn K p (fun k x => A k (B k x)) (fun x => Ainf (Binf x)) := by
  have hBinf_cont : ContinuousOn Binf U := hBinfc.continuousOn
  have hBKcpt : IsCompact (Binf '' K) := hK.image_of_continuousOn (hBinf_cont.mono hKU)
  have hBKV : Binf '' K ⊆ V := by
    rintro y ⟨x, hx, rfl⟩
    exact hmap (hKU hx)
  obtain ⟨δ₀, hδ₀pos, hδ₀V⟩ := hBKcpt.exists_cthickening_subset_open hV hBKV
  set K' : Set F := Metric.cthickening δ₀ (Binf '' K) with hK'def
  have hK'compact : IsCompact K' := hBKcpt.cthickening
  have hK'V : K' ⊆ V := hδ₀V
  have hB0 : TendstoUniformlyOn B Binf atTop K :=
    tendstoUniformlyOn_of_cPConvergence (hB.mono_order (Nat.zero_le p))
  rw [Metric.tendstoUniformlyOn_iff] at hB0
  obtain ⟨NB, hNB⟩ := eventually_atTop.mp (hB0 δ₀ hδ₀pos)
  have hBK' : ∀ᶠ k in atTop, Set.MapsTo (B k) K K' := by
    rw [eventually_atTop]
    refine ⟨NB, fun k hk x hx => ?_⟩
    have hclose : dist (Binf x) (B k x) < δ₀ := hNB k hk x hx
    exact Metric.mem_cthickening_of_dist_le (B k x) (Binf x) δ₀ (Binf '' K)
      ⟨x, hx, rfl⟩ (by rw [dist_comm]; exact le_of_lt hclose)
  have hBinfK' : Set.MapsTo Binf K K' := by
    intro x hx
    exact Metric.self_subset_cthickening _ ⟨x, hx, rfl⟩
  refine mapCPConvergenceOn_of_tendstoUniformlyOn hU hKU
    (fun k => ContDiffOn.comp (hAc k)
      (hBc k) (hmapk k))
    (ContDiffOn.comp hAinfc
      hBinfc hmap) ?_
  intro r hr
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let l : Filter (ℕ × E) := atTop ×ˢ Filter.principal K
  let p₁ : ℕ × E → FormalMultilinearSeries ℝ F G :=
    fun q => ftaylorSeries ℝ (A q.1) (B q.1 q.2)
  let p₂ : ℕ × E → FormalMultilinearSeries ℝ F G :=
    fun q => ftaylorSeries ℝ Ainf (Binf q.2)
  let q₁ : ℕ × E → FormalMultilinearSeries ℝ E F :=
    fun q => ftaylorSeries ℝ (B q.1) q.2
  let q₂ : ℕ × E → FormalMultilinearSeries ℝ E F :=
    fun q => ftaylorSeries ℝ Binf q.2
  have hAeval : ∀ i : ℕ, i ≤ p →
      TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ i (A k) (B k x))
        (fun x => iteratedFDeriv ℝ i Ainf (Binf x)) atTop K :=
    fun i hi => tendstoUniformlyOn_iteratedFDeriv_comp_moving_finite hV hK'compact hK'V
      (hA K' hK'compact hK'V) hAc hAinfc (tendstoUniformlyOn_of_cPConvergence (hB.mono_order (Nat.zero_le p)))
      hBK' hBinfK' i hi
  have hBder : ∀ i : ℕ, i ≤ p →
      TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ i (B k) x)
        (fun x => iteratedFDeriv ℝ i Binf x) atTop K :=
    fun i hi => hB.tendstoUniformlyOn_iteratedFDeriv hU hKU
      hBc
      hBinfc hi
  have hcompLittle :
      (fun q : ℕ × E =>
        iteratedFDeriv ℝ r (fun x => A q.1 (B q.1 x)) q.2 -
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) q.2)
        =o[l] (fun _ : ℕ × E => (1 : ℝ)) := by
    have htaylor :
        (fun q : ℕ × E =>
          iteratedFDeriv ℝ r (fun x => A q.1 (B q.1 x)) q.2 -
            iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) q.2)
          =ᶠ[l] fun q =>
            (p₁ q).taylorComp (q₁ q) r - (p₂ q).taylorComp (q₂ q) r := by
      change ∀ᶠ q in atTop ×ˢ Filter.principal K,
        (fun q : ℕ × E =>
          iteratedFDeriv ℝ r (fun x => A q.1 (B q.1 x)) q.2 -
            iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) q.2)
          q = ((p₁ q).taylorComp (q₁ q) r - (p₂ q).taylorComp (q₂ q) r)
      rw [eventually_prod_principal_iff]
      refine Eventually.of_forall fun k x hx => ?_
      have hxU : x ∈ U := hKU hx
      have hBkV : B k x ∈ V := hmapk k hxU
      have hBinfV : Binf x ∈ V := hmap hxU
      dsimp [p₁, p₂, q₁, q₂]
      have hcur :
          iteratedFDeriv ℝ r (fun x => A k (B k x)) x =
            (ftaylorSeries ℝ (A k) (B k x)).taylorComp (ftaylorSeries ℝ (B k) x) r := by
        simpa [Function.comp_def] using
          (iteratedFDeriv_comp
          ((hAc k).contDiffAt (hV.mem_nhds hBkV))
          ((hBc k).contDiffAt (hU.mem_nhds hxU))
          (by exact_mod_cast hr : (r : WithTop ℕ∞) ≤ (p : ℕ∞)))
      have hlim :
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) x =
            (ftaylorSeries ℝ Ainf (Binf x)).taylorComp (ftaylorSeries ℝ Binf x) r := by
        simpa [Function.comp_def] using
          (iteratedFDeriv_comp
          (hAinfc.contDiffAt (hV.mem_nhds hBinfV))
          (hBinfc.contDiffAt (hU.mem_nhds hxU))
          (by exact_mod_cast hr : (r : WithTop ℕ∞) ≤ (p : ℕ∞)))
      rw [hcur, hlim]
    refine htaylor.trans_isLittleO ?_
    refine FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO ?hp ?hpf ?hq1 ?hq2 ?hqf
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y ∈ K', ‖iteratedFDeriv ℝ i Ainf y‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK'compact.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hAinfc hV
            (by exact_mod_cast hi.trans hr)).norm.mono hK'V)
        exact ⟨C, fun y hy => hC ⟨y, hy, rfl⟩⟩
      exact isBoundedUnder_prod_principal_of_eventually_forall_le
        ⟨C + 1, TendstoUniformlyOn.eventually_norm_le (hAeval i (hi.trans hr))
          (fun x hx => hC (Binf x) (hBinfK' hx))⟩
    · intro i hi
      exact TendstoUniformlyOn.isLittleO_sub_const (hAeval i (hi.trans hr))
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i Binf x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hBinfc hU
            (by exact_mod_cast hi.trans hr)).norm.mono hKU)
        exact ⟨C, fun x hx => hC ⟨x, hx, rfl⟩⟩
      exact isBoundedUnder_prod_principal_of_eventually_forall_le
        ⟨C + 1, TendstoUniformlyOn.eventually_norm_le (hBder i (hi.trans hr)) hC⟩
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i Binf x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hBinfc hU
            (by exact_mod_cast hi.trans hr)).norm.mono hKU)
        exact ⟨C, fun x hx => hC ⟨x, hx, rfl⟩⟩
      exact isBoundedUnder_prod_principal_of_forall_le
        ⟨C, fun _ x hx => hC x hx⟩
    · intro i hi
      exact TendstoUniformlyOn.isLittleO_sub_const (hBder i (hi.trans hr))
  have htend : Tendsto
      (fun q : ℕ × E =>
        iteratedFDeriv ℝ r (fun x => A q.1 (B q.1 x)) q.2 -
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) q.2)
      l (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp hcompLittle
  rw [Metric.tendsto_nhds] at htend
  have htail : ∀ᶠ (x : ℕ × E) in atTop ×ˢ Filter.principal K,
      dist
        (iteratedFDeriv ℝ r (fun x_1 => A x.1 (B x.1 x_1)) x.2 -
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) x.2) 0 < ε :=
    htend ε hε
  rw [eventually_prod_principal_iff] at htail
  exact htail.mono fun k hk x hx => by
    simpa [dist_eq_norm, norm_sub_rev] using hk x hx

theorem mapCPConvergenceOn_comp_of_eventually_contDiffOn
    [LocallyCompactSpace E] [ProperSpace F]
    {U : Set E} {V : Set F} {p : ℕ}
    {B : ℕ → E → F} {Binf : E → F} {A : ℕ → F → G} {Ainf : F → G}
    (hU : IsOpen U) (hV : IsOpen V)
    (hB : ∀ L : Set E, IsCompact L → L ⊆ U → MapCPConvergenceOn L p B Binf)
    (hA : ∀ S : Set F, IsCompact S → S ⊆ V → MapCPConvergenceOn S p A Ainf)
    (hBc : ∀ L : Set E, IsCompact L → L ⊆ U →
      ∀ᶠ i in atTop, ContDiffOn ℝ (p : ℕ∞) (B i) L)
    (hBinfc : ContDiffOn ℝ (p : ℕ∞) Binf U)
    (hAc : ∀ S : Set F, IsCompact S → S ⊆ V →
      ∀ᶠ i in atTop, ContDiffOn ℝ (p : ℕ∞) (A i) S)
    (hAinfc : ContDiffOn ℝ (p : ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    MapCPConvergenceOn K p (fun i x => A i (B i x)) (fun x => Ainf (Binf x)) := by
  obtain ⟨W, hW, hKW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  have hWsub : W ⊆ U := subset_closure.trans hWU
  have himage : IsCompact (Binf '' closure W) :=
    hWc.image_of_continuousOn (hBinfc.continuousOn.mono hWU)
  have himageV : Binf '' closure W ⊆ V := by
    rintro y ⟨x, hx, rfl⟩
    exact hmap (hWU hx)
  obtain ⟨T, hT, hBT, hTV, hTc⟩ :=
    exists_open_between_and_isCompact_closure himage hV himageV
  have hTsub : T ⊆ V := subset_closure.trans hTV
  obtain ⟨δ, hδ, hδT⟩ := himage.exists_thickening_subset_open hT hBT
  have hBzero := tendstoUniformlyOn_of_cPConvergence
    ((hB (closure W) hWc hWU).mono_order (Nat.zero_le p))
  have hmaps : ∀ᶠ i in atTop, Set.MapsTo (B i) (closure W) T := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hBzero) δ hδ] with i hi
    intro x hx
    apply hδT
    rw [Metric.mem_thickening_iff]
    exact ⟨Binf x, ⟨x, hx, rfl⟩, by simpa only [dist_comm] using hi x hx⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((hBc (closure W) hWc hWU).and (hAc (closure T) hTc hTV)).and hmaps)
  have hshift : StrictMono (fun i : ℕ => i + N) :=
    fun _ _ hij => Nat.add_lt_add_right hij N
  have hshifted : MapCPConvergenceOn K p
      (fun i x => A (i + N) (B (i + N) x)) (fun x => Ainf (Binf x)) := by
    apply MapCPConvergenceOn.comp_finite hW hT hK hKW
      ((hB K hK hKU).comp_subseq hshift)
    · intro S hS hST
      exact (hA S hS (hST.trans hTsub)).comp_subseq hshift
    · intro i
      exact ((hN (i + N) (Nat.le_add_left N i)).1.1).mono subset_closure
    · exact hBinfc.mono hWsub
    · intro i
      exact ((hN (i + N) (Nat.le_add_left N i)).1.2).mono subset_closure
    · exact hAinfc.mono hTsub
    · intro x hx
      exact hBT ⟨x, subset_closure hx, rfl⟩
    · intro i x hx
      exact (hN (i + N) (Nat.le_add_left N i)).2 (subset_closure hx)
  intro ε hε
  obtain ⟨M, hM⟩ := hshifted ε hε
  refine ⟨M + N, fun i hi r hr x hx => ?_⟩
  have hNi : N ≤ i := by omega
  have hMi : M ≤ i - N := by omega
  simpa only [Nat.sub_add_cancel hNi] using hM (i - N) hMi r hr x hx

end DifferentialGeometry.CheegerGromovCompactness
