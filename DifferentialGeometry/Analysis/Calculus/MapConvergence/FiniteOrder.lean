import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition

/-!
# Finite-order `C^p` convergence of maps

The closure lemmas in `MapConvergence/Composition.lean` assume that every map involved is
`C^∞`.  This file proves the same closure properties for `MapCPConvergenceOn K p` when the
approximating maps and their limits are only `C^p` on an open neighbourhood of the compact set.

The smoothness hypotheses are written `ContDiffOn ℝ (p : ℕ∞) f U`, matching
`mapCPConvergenceOn_of_tendstoUniformlyOn` and
`MapCPConvergenceOn.tendstoUniformlyOn_iteratedFDeriv`.

The composition argument follows `MapCPConvergenceOn.comp_cInf`: Faà di Bruno
(`iteratedFDeriv_comp`) writes the `r`-th derivative of a composition as a Taylor-series
composition, and `FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO` reduces the
convergence to that of the individual derivatives of order `≤ r ≤ p`.  The outer derivatives are
evaluated at moving points; this is controlled by the uniform continuity of
`iteratedFDeriv ℝ i Ainf` (`i ≤ p`) on a compact set `K'`.
-/

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Topology

variable {E F G P Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- A constant sequence converges in every `C^p` sense to its value. -/
theorem MapCPConvergenceOn.const_seq {K : Set E} {p : ℕ} (Φ : E → F) :
    MapCPConvergenceOn K p (fun _ => Φ) Φ := by
  intro ε hε
  exact ⟨0, fun _ _ _ _ _ _ => by simpa [mapDerivNorm, sub_self] using hε.le⟩

/-- If every term of the sequence agrees with the limit near each point of `K`, the sequence
converges in `C^p` on `K`. -/
theorem MapCPConvergenceOn.of_eventuallyEq {K : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F} (h : ∀ x ∈ K, ∀ k, Φ k =ᶠ[𝓝 x] Φinf) :
    MapCPConvergenceOn K p Φ Φinf := by
  intro ε hε
  refine ⟨0, fun k _ r _ x hx => ?_⟩
  have heq : (fun y => Φ k y - Φinf y) =ᶠ[𝓝 x] fun y => Φinf y - Φinf y := by
    filter_upwards [h x hx k] with y hy
    rw [hy]
  have hval : mapDerivNorm r (Φ k) Φinf x = mapDerivNorm r Φinf Φinf x := by
    simp only [mapDerivNorm]
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ heq r).eq_of_nhds]
  rw [hval]
  simpa [mapDerivNorm, sub_self] using hε.le

/-- Finite-order version of `MapCPConvergenceOn.prodMk`. -/
theorem MapCPConvergenceOn.prodMk_of_contDiffOn {U K : Set E} {p : ℕ}
    (hU : IsOpen U) (hKU : K ⊆ U)
    {u : ℕ → E → P} {uinf : E → P} {v : ℕ → E → Q} {vinf : E → Q}
    (hu : MapCPConvergenceOn K p u uinf) (hv : MapCPConvergenceOn K p v vinf)
    (huc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (u k) U) (huinfc : ContDiffOn ℝ (p : ℕ∞) uinf U)
    (hvc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (v k) U) (hvinfc : ContDiffOn ℝ (p : ℕ∞) vinf U) :
    MapCPConvergenceOn K p (fun k y => (u k y, v k y)) (fun y => (uinf y, vinf y)) := by
  intro ε hε
  obtain ⟨k1, hk1⟩ := hu ε hε
  obtain ⟨k2, hk2⟩ := hv ε hε
  refine ⟨max k1 k2, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hcu : ContDiffAt ℝ r (fun y => u k y - uinf y) x :=
    (((huc k).sub huinfc).contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr)
  have hcv : ContDiffAt ℝ r (fun y => v k y - vinf y) x :=
    (((hvc k).sub hvinfc).contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr)
  have heq : (fun y => (u k y, v k y) - (uinf y, vinf y))
      = fun y => (u k y - uinf y, v k y - vinf y) := by
    funext y; simp [Prod.mk_sub_mk]
  have hkey : mapDerivNorm r (fun y => (u k y, v k y)) (fun y => (uinf y, vinf y)) x
      = max (mapDerivNorm r (u k) uinf x) (mapDerivNorm r (v k) vinf x) := by
    simp only [mapDerivNorm]
    rw [heq, iteratedFDeriv_prodMk hcu hcv le_rfl, ContinuousMultilinearMap.opNorm_prod]
  rw [hkey]
  exact max_le (hk1 k (le_trans (le_max_left k1 k2) hk) r hr x hx)
    (hk2 k (le_trans (le_max_right k1 k2) hk) r hr x hx)

/-- Sums of `C^p`-convergent sequences of `C^p` maps converge in `C^p`. -/
theorem MapCPConvergenceOn.add_of_contDiffOn {U K : Set E} {p : ℕ}
    (hU : IsOpen U) (hKU : K ⊆ U)
    {u : ℕ → E → F} {uinf : E → F} {v : ℕ → E → F} {vinf : E → F}
    (hu : MapCPConvergenceOn K p u uinf) (hv : MapCPConvergenceOn K p v vinf)
    (huc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (u k) U) (huinfc : ContDiffOn ℝ (p : ℕ∞) uinf U)
    (hvc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (v k) U) (hvinfc : ContDiffOn ℝ (p : ℕ∞) vinf U) :
    MapCPConvergenceOn K p (fun k y => u k y + v k y) (fun y => uinf y + vinf y) := by
  intro ε hε
  obtain ⟨k1, hk1⟩ := hu (ε / 2) (by positivity)
  obtain ⟨k2, hk2⟩ := hv (ε / 2) (by positivity)
  refine ⟨max k1 k2, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hcu : ContDiffAt ℝ r (fun y => u k y - uinf y) x :=
    (((huc k).sub huinfc).contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr)
  have hcv : ContDiffAt ℝ r (fun y => v k y - vinf y) x :=
    (((hvc k).sub hvinfc).contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr)
  have heq : (fun y => u k y + v k y - (uinf y + vinf y))
      = (fun y => u k y - uinf y) + fun y => v k y - vinf y := by
    funext y; simp only [Pi.add_apply]; abel
  have hkey : mapDerivNorm r (fun y => u k y + v k y) (fun y => uinf y + vinf y) x
      = ‖iteratedFDeriv ℝ r (fun y => u k y - uinf y) x
          + iteratedFDeriv ℝ r (fun y => v k y - vinf y) x‖ := by
    simp only [mapDerivNorm]
    rw [heq, iteratedFDeriv_add_apply hcu hcv]
  rw [hkey]
  calc ‖iteratedFDeriv ℝ r (fun y => u k y - uinf y) x
          + iteratedFDeriv ℝ r (fun y => v k y - vinf y) x‖
      ≤ mapDerivNorm r (u k) uinf x + mapDerivNorm r (v k) vinf x := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 :=
        add_le_add (hk1 k (le_trans (le_max_left k1 k2) hk) r hr x hx)
          (hk2 k (le_trans (le_max_right k1 k2) hk) r hr x hx)
    _ = ε := by ring

/-- Finite sums of `C^p`-convergent sequences of `C^p` maps converge in `C^p`. -/
theorem MapCPConvergenceOn.sum_of_contDiffOn {ι : Type*} (s : Finset ι) {U K : Set E} {p : ℕ}
    (hU : IsOpen U) (hKU : K ⊆ U) {Φ : ι → ℕ → E → F} {Φinf : ι → E → F}
    (h : ∀ i ∈ s, MapCPConvergenceOn K p (Φ i) (Φinf i))
    (hc : ∀ i ∈ s, ∀ k, ContDiffOn ℝ (p : ℕ∞) (Φ i k) U)
    (hic : ∀ i ∈ s, ContDiffOn ℝ (p : ℕ∞) (Φinf i) U) :
    MapCPConvergenceOn K p (fun k y => ∑ i ∈ s, Φ i k y) (fun y => ∑ i ∈ s, Φinf i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        MapCPConvergenceOn.const_seq (K := K) (p := p) (fun _ : E => (0 : F))
  | insert a t hat ih =>
      have ha : a ∈ insert a t := Finset.mem_insert_self a t
      have hsub : ∀ i ∈ t, i ∈ insert a t := fun i hi => Finset.mem_insert_of_mem hi
      have ih' := ih (fun i hi => h i (hsub i hi)) (fun i hi => hc i (hsub i hi))
        (fun i hi => hic i (hsub i hi))
      simp only [Finset.sum_insert hat]
      exact (h a ha).add_of_contDiffOn hU hKU ih' (hc a ha) (hic a ha)
        (fun k => ContDiffOn.sum fun i hi => hc i (hsub i hi) k)
        (ContDiffOn.sum fun i hi => hic i (hsub i hi))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Finite-order version of
`MapCInfConvergenceOnCompacts.tendstoUniformlyOn_iteratedFDeriv_comp_moving`: the derivatives of
order `r ≤ p` of `A k`, evaluated at the moving points `B k x`, converge uniformly on `K`. -/
theorem MapCPConvergenceOn.tendstoUniformlyOn_iteratedFDeriv_comp_moving_of_contDiffOn
    {K : Set E} {V K' : Set F} {p : ℕ}
    {A : ℕ → F → G} {Ainf : F → G} {B : ℕ → E → F} {Binf : E → F}
    (hV : IsOpen V) (hK' : IsCompact K') (hK'V : K' ⊆ V)
    (hA : MapCPConvergenceOn K' p A Ainf)
    (hAc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (p : ℕ∞) Ainf V)
    (hB : TendstoUniformlyOn B Binf atTop K)
    (hBK' : ∀ᶠ k in atTop, Set.MapsTo (B k) K K')
    (hBinfK' : Set.MapsTo Binf K K') {r : ℕ} (hr : r ≤ p) :
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
    (ContinuousOn.continuousOn_iteratedFDeriv hAinfc hV (by exact_mod_cast hr)).mono hK'V
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
    _ < ε / 2 + ε / 2 := add_lt_add (hNB k hkB x hx) (hNA k hkA (B k x) hBxK')
    _ = ε := by ring

/-- Finite-order composition: if `B k → Binf` in `C^p` on the compact set `K`, `A k → Ainf` in
`C^p` on the compact set `K'`, all maps are `C^p` on open neighbourhoods `U ⊇ K`, `V ⊇ K'`, and
`B k` (eventually) and `Binf` send `K` into `K'`, then `A k ∘ B k → Ainf ∘ Binf` in `C^p`
on `K`. -/
theorem MapCPConvergenceOn.comp_of_contDiffOn
    {U K : Set E} {V K' : Set F} {p : ℕ} (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKU : K ⊆ U) (hK' : IsCompact K') (hK'V : K' ⊆ V)
    {B : ℕ → E → F} {Binf : E → F} {A : ℕ → F → G} {Ainf : F → G}
    (hB : MapCPConvergenceOn K p B Binf) (hA : MapCPConvergenceOn K' p A Ainf)
    (hBc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (B k) U) (hBinfc : ContDiffOn ℝ (p : ℕ∞) Binf U)
    (hAc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (A k) V) (hAinfc : ContDiffOn ℝ (p : ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V) (hmapk : ∀ k, Set.MapsTo (B k) U V)
    (hBK' : ∀ᶠ k in atTop, Set.MapsTo (B k) K K') (hBinfK' : Set.MapsTo Binf K K') :
    MapCPConvergenceOn K p (fun k x => A k (B k x)) (fun x => Ainf (Binf x)) := by
  have hB0 : TendstoUniformlyOn B Binf atTop K :=
    tendstoUniformlyOn_of_cPConvergence (hB.mono_order (Nat.zero_le p))
  refine mapCPConvergenceOn_of_tendstoUniformlyOn hU hKU
    (fun k => (hAc k).comp (hBc k) (hmapk k)) (hAinfc.comp hBinfc hmap) ?_
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
    fun i hi => hA.tendstoUniformlyOn_iteratedFDeriv_comp_moving_of_contDiffOn hV hK' hK'V
      hAc hAinfc hB0 hBK' hBinfK' hi
  have hBder : ∀ i : ℕ, i ≤ p →
      TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ i (B k) x)
        (fun x => iteratedFDeriv ℝ i Binf x) atTop K :=
    fun i hi => hB.tendstoUniformlyOn_iteratedFDeriv hU hKU hBc hBinfc hi
  have hBinfBound : ∀ i : ℕ, i ≤ p → ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i Binf x‖ ≤ C := by
    intro i hi
    obtain ⟨C, hC⟩ := hK.bddAbove_image
      ((ContinuousOn.continuousOn_iteratedFDeriv hBinfc hU
        (by exact_mod_cast hi)).norm.mono hKU)
    exact ⟨C, fun x hx => hC ⟨x, hx, rfl⟩⟩
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
      have hrp : (r : WithTop ℕ∞) ≤ ((p : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hr
      dsimp [p₁, p₂, q₁, q₂]
      have hcur :
          iteratedFDeriv ℝ r (fun x => A k (B k x)) x =
            (ftaylorSeries ℝ (A k) (B k x)).taylorComp (ftaylorSeries ℝ (B k) x) r := by
        simpa [Function.comp_def] using
          (iteratedFDeriv_comp
            ((hAc k).contDiffAt (hV.mem_nhds hBkV))
            ((hBc k).contDiffAt (hU.mem_nhds hxU)) hrp)
      have hlim :
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) x =
            (ftaylorSeries ℝ Ainf (Binf x)).taylorComp (ftaylorSeries ℝ Binf x) r := by
        simpa [Function.comp_def] using
          (iteratedFDeriv_comp
            (hAinfc.contDiffAt (hV.mem_nhds hBinfV))
            (hBinfc.contDiffAt (hU.mem_nhds hxU)) hrp)
      rw [hcur, hlim]
    refine htaylor.trans_isLittleO ?_
    refine FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO ?hp ?hpf ?hq1 ?hq2 ?hqf
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y ∈ K', ‖iteratedFDeriv ℝ i Ainf y‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK'.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hAinfc hV
            (by exact_mod_cast hi.trans hr)).norm.mono hK'V)
        exact ⟨C, fun y hy => hC ⟨y, hy, rfl⟩⟩
      exact isBoundedUnder_prod_principal_of_eventually_forall_le
        ⟨C + 1, TendstoUniformlyOn.eventually_norm_le (hAeval i (hi.trans hr))
          (fun x hx => hC (Binf x) (hBinfK' hx))⟩
    · intro i hi
      exact TendstoUniformlyOn.isLittleO_sub_const (hAeval i (hi.trans hr))
    · intro i hi
      obtain ⟨C, hC⟩ := hBinfBound i (hi.trans hr)
      exact isBoundedUnder_prod_principal_of_eventually_forall_le
        ⟨C + 1, TendstoUniformlyOn.eventually_norm_le (hBder i (hi.trans hr)) hC⟩
    · intro i hi
      obtain ⟨C, hC⟩ := hBinfBound i (hi.trans hr)
      exact isBoundedUnder_prod_principal_of_forall_le ⟨C, fun _ x hx => hC x hx⟩
    · intro i hi
      exact TendstoUniformlyOn.isLittleO_sub_const (hBder i (hi.trans hr))
  have htend : Tendsto
      (fun q : ℕ × E =>
        iteratedFDeriv ℝ r (fun x => A q.1 (B q.1 x)) q.2 -
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) q.2)
      l (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp hcompLittle
  rw [Metric.tendsto_nhds] at htend
  have htail : ∀ᶠ (q : ℕ × E) in atTop ×ˢ Filter.principal K,
      dist
        (iteratedFDeriv ℝ r (fun y => A q.1 (B q.1 y)) q.2 -
          iteratedFDeriv ℝ r (fun y => Ainf (Binf y)) q.2) 0 < ε :=
    htend ε hε
  rw [eventually_prod_principal_iff] at htail
  exact htail.mono fun k hk x hx => by
    simpa [dist_eq_norm, norm_sub_rev] using hk x hx

/-- Finite-order composition with a fixed globally `C^p` outer map. -/
theorem MapCPConvergenceOn.comp_contDiff_left [ProperSpace F]
    {U K : Set E} {p : ℕ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {B : ℕ → E → F} {Binf : E → F} (hB : MapCPConvergenceOn K p B Binf)
    (hBc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (B k) U) (hBinfc : ContDiffOn ℝ (p : ℕ∞) Binf U)
    {Ψ : F → G} (hΨ : ContDiff ℝ (p : ℕ∞) Ψ) :
    MapCPConvergenceOn K p (fun k x => Ψ (B k x)) (fun x => Ψ (Binf x)) := by
  have hBKcpt : IsCompact (Binf '' K) :=
    hK.image_of_continuousOn (hBinfc.continuousOn.mono hKU)
  have hK'c : IsCompact (Metric.cthickening 1 (Binf '' K)) := hBKcpt.cthickening
  have hB0 : TendstoUniformlyOn B Binf atTop K :=
    tendstoUniformlyOn_of_cPConvergence (hB.mono_order (Nat.zero_le p))
  rw [Metric.tendstoUniformlyOn_iff] at hB0
  have hBK' : ∀ᶠ k in atTop, Set.MapsTo (B k) K (Metric.cthickening 1 (Binf '' K)) := by
    filter_upwards [hB0 1 one_pos] with k hk x hx
    exact Metric.mem_cthickening_of_dist_le (B k x) (Binf x) 1 (Binf '' K)
      ⟨x, hx, rfl⟩ (by rw [dist_comm]; exact (hk x hx).le)
  have hBinfK' : Set.MapsTo Binf K (Metric.cthickening 1 (Binf '' K)) :=
    fun x hx => Metric.self_subset_cthickening _ ⟨x, hx, rfl⟩
  exact MapCPConvergenceOn.comp_of_contDiffOn (A := fun _ => Ψ) hU isOpen_univ hK hKU hK'c
    (Set.subset_univ _) hB (MapCPConvergenceOn.const_seq Ψ) hBc hBinfc
    (fun _ => hΨ.contDiffOn) hΨ.contDiffOn (Set.mapsTo_univ _ _)
    (fun _ => Set.mapsTo_univ _ _) hBK' hBinfK'

/-- Finite-order composition with a fixed `C^p` inner map. -/
theorem MapCPConvergenceOn.comp_contDiffOn_right
    {U K : Set E} {V : Set F} {p : ℕ} (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKU : K ⊆ U) {T : E → F} (hT : ContDiffOn ℝ (p : ℕ∞) T U)
    (hTmap : Set.MapsTo T U V) {A : ℕ → F → G} {Ainf : F → G}
    (hA : MapCPConvergenceOn (T '' K) p A Ainf)
    (hAc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (A k) V) (hAinfc : ContDiffOn ℝ (p : ℕ∞) Ainf V) :
    MapCPConvergenceOn K p (fun k x => A k (T x)) (fun x => Ainf (T x)) :=
  MapCPConvergenceOn.comp_of_contDiffOn (B := fun _ => T) hU hV hK hKU
    (hK.image_of_continuousOn (hT.continuousOn.mono hKU))
    (Set.image_subset_iff.mpr fun _ hx => hTmap (hKU hx))
    (MapCPConvergenceOn.const_seq T) hA (fun _ => hT) hT hAc hAinfc hTmap (fun _ => hTmap)
    (Eventually.of_forall fun _ => Set.mapsTo_image T K) (Set.mapsTo_image T K)

end CheegerGromovCompactness
end DifferentialGeometry
