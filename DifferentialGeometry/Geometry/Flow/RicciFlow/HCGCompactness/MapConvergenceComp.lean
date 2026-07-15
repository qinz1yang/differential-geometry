import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergenceDeriv
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Composition for `MapCInfConvOnCompacts`

This file is the Step-B analysis layer for composition convergence.  The first
lemmas expose a basic projection that the composition proof needs: the project
definition controls derivatives of the difference `Φₖ - Φ∞`, and under the
localized smoothness hypotheses this is equivalent to uniform convergence of the
individual iterated derivatives on compact subsets of the open domain.
-/

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology
open scoped ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Extract uniform convergence of a fixed iterated derivative from `MapCPConvOn`
on an open domain.  The `ContDiffOn` hypotheses let `iteratedFDeriv` commute with
subtraction at points of the compact set. -/
theorem MapCPConvOn.tendstoUniformlyOn_iteratedFDeriv
    {U K : Set E} {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (hU : IsOpen U) (hKU : K ⊆ U) (h : MapCPConvOn K p Φ Φinf)
    (hΦ : ∀ k, ContDiffOn ℝ (p : ℕ∞) (Φ k) U)
    (hΦinf : ContDiffOn ℝ (p : ℕ∞) Φinf U) {r : ℕ} (hr : r ≤ p) :
    TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ r (Φ k) x)
      (fun x => iteratedFDeriv ℝ r Φinf x) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨k0, hk0⟩ := h (ε / 2) (by positivity)
  rw [eventually_atTop]
  refine ⟨k0, fun k hk x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hsub : iteratedFDeriv ℝ r (fun y => Φ k y - Φinf y) x
      = iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r Φinf x := by
    exact iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := r) (x := x)
      (((hΦ k).contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr))
      ((hΦinf.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr))
  have hb := hk0 k hk r hr x hx
  rw [mapDerivNorm, hsub] at hb
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hb (by linarith)

/-- `C^p` convergence is stable under any reindexing tending to infinity. -/
theorem MapCPConvOn.comp_tendsto_atTop {K : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCPConvOn K p Φ Φinf)
    {τ : ℕ → ℕ} (hτ : Tendsto τ atTop atTop) :
    MapCPConvOn K p (fun k => Φ (τ k)) Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hτ.eventually_ge_atTop k0)
  exact ⟨N, fun k hk r hr x hx => hk0 (τ k) (hN k hk) r hr x hx⟩

/-- `C^∞`-on-compacts convergence is stable under any reindexing tending to infinity. -/
theorem MapCInfConvOnCompacts.comp_tendsto_atTop {U : Set E}
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCInfConvOnCompacts U Φ Φinf)
    {τ : ℕ → ℕ} (hτ : Tendsto τ atTop atTop) :
    MapCInfConvOnCompacts U (fun k => Φ (τ k)) Φinf :=
  fun K hK hKU p => (h K hK hKU p).comp_tendsto_atTop hτ

/-- The fixed-order derivative projection for `MapCInfConvOnCompacts`. -/
theorem MapCInfConvOnCompacts.tendstoUniformlyOn_iteratedFDeriv
    {U K : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (h : MapCInfConvOnCompacts U Φ Φinf)
    (hΦ : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (Φ k) U)
    (hΦinf : ContDiffOn ℝ (∞ : WithTop ℕ∞) Φinf U) (r : ℕ) :
    TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ r (Φ k) x)
      (fun x => iteratedFDeriv ℝ r Φinf x) atTop K := by
  exact (h K hK hKU r).tendstoUniformlyOn_iteratedFDeriv hU hKU
    (fun k => (hΦ k).of_le (by exact_mod_cast le_top))
    (hΦinf.of_le (by exact_mod_cast le_top)) le_rfl

/-- Localized version of `mapCPConvOn_of_tendstoUniformly` on an open domain. -/
theorem mapCPConvOn_of_tendstoUniformlyOn {U K : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F} (hU : IsOpen U) (hKU : K ⊆ U)
    (hΦ : ∀ k, ContDiffOn ℝ (p : ℕ∞) (Φ k) U)
    (hΦinf : ContDiffOn ℝ (p : ℕ∞) Φinf U)
    (htu : ∀ r : ℕ, r ≤ p →
      TendstoUniformlyOn (fun k x => iteratedFDeriv ℝ r (Φ k) x)
        (fun x => iteratedFDeriv ℝ r Φinf x) atTop K) :
    MapCPConvOn K p Φ Φinf := by
  intro ε hε
  have key : ∀ r : ℕ, r ≤ p →
      ∀ᶠ k in atTop, ∀ x ∈ K, mapDerivNorm r (Φ k) Φinf x ≤ ε := by
    intro r hr
    have h := (Metric.tendstoUniformlyOn_iff.mp (htu r hr)) ε hε
    filter_upwards [h] with k hk x hx
    have hxU : x ∈ U := hKU hx
    have hsub : iteratedFDeriv ℝ r (fun y => Φ k y - Φinf y) x
        = iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r Φinf x := by
      exact iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := r) (x := x)
        (((hΦ k).contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr))
        ((hΦinf.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr))
    have hdist := hk x hx
    rw [dist_eq_norm, ← norm_sub_rev] at hdist
    rw [mapDerivNorm, hsub]
    exact hdist.le
  have hfin : ∀ᶠ k in atTop, ∀ r ∈ Set.Iic p, ∀ x ∈ K,
      mapDerivNorm r (Φ k) Φinf x ≤ ε :=
    (Set.finite_Iic p).eventually_all.2 (fun r hr => key r (Set.mem_Iic.mp hr))
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp hfin
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (Set.mem_Iic.mpr hr) x hx⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Uniform convergence on `K` is little-`o(1)` on the product filter
`atTop × principal K`, in the additive difference form consumed by the
Taylor-composition estimates. -/
theorem TendstoUniformlyOn.isLittleO_sub_const
    {K : Set E} {Fseq : ℕ → E → F} {Flim : E → F}
    (h : TendstoUniformlyOn Fseq Flim atTop K) :
    (fun q : ℕ × E => Fseq q.1 q.2 - Flim q.2)
      =o[atTop ×ˢ Filter.principal K] (fun _ : ℕ × E => (1 : ℝ)) := by
  rw [Asymptotics.isLittleO_one_iff ℝ]
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [eventually_prod_principal_iff]
  exact ((Metric.tendstoUniformlyOn_iff.mp h) ε hε).mono fun k hk x hx => by
    simpa [dist_eq_norm, norm_sub_rev] using hk x hx

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A uniform pointwise bound over the compact variable gives boundedness along
the product filter `atTop × principal K`. -/
theorem isBoundedUnder_prod_principal_of_forall_le {K : Set E} {u : ℕ × E → ℝ}
    (h : ∃ C : ℝ, ∀ k x, x ∈ K → u (k, x) ≤ C) :
    (atTop ×ˢ Filter.principal K).IsBoundedUnder (· ≤ ·) u := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rw [eventually_map, eventually_prod_principal_iff]
  exact Eventually.of_forall fun k x hx => hC k x hx

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Eventual uniform bounds over `x ∈ K` give boundedness along
`atTop × principal K`. -/
theorem isBoundedUnder_prod_principal_of_eventually_forall_le {K : Set E} {u : ℕ × E → ℝ}
    (h : ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, u (k, x) ≤ C) :
    (atTop ×ˢ Filter.principal K).IsBoundedUnder (· ≤ ·) u := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rw [eventually_map, eventually_prod_principal_iff]
  exact hC

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A uniformly convergent family is eventually uniformly norm-bounded if its
limit is uniformly norm-bounded. -/
theorem TendstoUniformlyOn.eventually_norm_le
    {K : Set E} {Fseq : ℕ → E → F} {Flim : E → F}
    (h : TendstoUniformlyOn Fseq Flim atTop K)
    {C : ℝ} (hC : ∀ x ∈ K, ‖Flim x‖ ≤ C) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ‖Fseq k x‖ ≤ C + 1 := by
  have h1 := (Metric.tendstoUniformlyOn_iff.mp h) 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h1] with k hk x hx
  have hdist : dist (Flim x) (Fseq k x) < 1 := hk x hx
  have htri : ‖Fseq k x‖ ≤ ‖Flim x‖ + dist (Flim x) (Fseq k x) := by
    calc
      ‖Fseq k x‖ ≤ ‖Flim x‖ + ‖Fseq k x - Flim x‖ := by
        simpa [dist_zero_right, dist_eq_norm, add_comm, add_left_comm, add_assoc]
          using dist_triangle (Fseq k x) (Flim x) (0 : F)
      _ = ‖Flim x‖ + dist (Flim x) (Fseq k x) := by
        rw [dist_eq_norm, norm_sub_rev]
  nlinarith [hC x hx, hdist.le]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Moving-evaluation derivative convergence.  If `Aₖ → A∞` in `C^∞` on a fixed
compact `K' ⊆ V`, `Bₖ → B∞` uniformly on `K`, and the moving points `Bₖ x`,
`B∞ x` stay in `K'`, then each fixed derivative of `Aₖ` evaluated at `Bₖ x`
converges uniformly on `K`. -/
theorem MapCInfConvOnCompacts.tendstoUniformlyOn_iteratedFDeriv_comp_moving
    {K : Set E} {V K' : Set F}
    {A : ℕ → F → G} {Ainf : F → G} {B : ℕ → E → F} {Binf : E → F}
    (hV : IsOpen V) (hK' : IsCompact K') (hK'V : K' ⊆ V)
    (hA : MapCInfConvOnCompacts V A Ainf)
    (hAc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf V)
    (hB : TendstoUniformlyOn B Binf atTop K)
    (hBK' : ∀ᶠ k in atTop, Set.MapsTo (B k) K K')
    (hBinfK' : Set.MapsTo Binf K K') (r : ℕ) :
    TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ r (A k) (B k x))
      (fun x => iteratedFDeriv ℝ r Ainf (Binf x)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hAder :
      TendstoUniformlyOn
        (fun k y => iteratedFDeriv ℝ r (A k) y)
        (fun y => iteratedFDeriv ℝ r Ainf y) atTop K' :=
    hA.tendstoUniformlyOn_iteratedFDeriv hV hK' hK'V hAc hAinfc r
  have hDcont : ContinuousOn (fun y => iteratedFDeriv ℝ r Ainf y) K' :=
    ((ContinuousOn.continuousOn_iteratedFDeriv hAinfc hV
      (by exact_mod_cast le_top)).mono hK'V)
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

/-- **Composition preserves `C^∞` convergence on compact subsets.**  This same-index
version assumes the moving inner maps send the whole open source domain into the
open target domain, so the composed maps are genuinely smooth on `U`.  The fixed
compact corral for the moving evaluation points is derived internally from
order-`0` convergence of `Bₖ` to `B∞`. -/
theorem MapCInfConvOnCompacts.comp
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    [ProperSpace F]
    {B : ℕ → E → F} {Binf : E → F} {A : ℕ → F → G} {Ainf : F → G}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hA : MapCInfConvOnCompacts V A Ainf)
    (hBc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Binf U)
    (hAc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V) (hmapk : ∀ k, Set.MapsTo (B k) U V) :
    MapCInfConvOnCompacts U (fun k x => A k (B k x)) (fun x => Ainf (Binf x)) := by
  intro K hK hKU p
  have hBinf_cont : ContinuousOn Binf U := hBinfc.continuousOn
  have hBKcpt : IsCompact (Binf '' K) := hK.image_of_continuousOn (hBinf_cont.mono hKU)
  have hBKV : Binf '' K ⊆ V := by
    rintro y ⟨x, hx, rfl⟩
    exact hmap (hKU hx)
  obtain ⟨δ₀, hδ₀pos, hδ₀V⟩ := hBKcpt.exists_cthickening_subset_open hV hBKV
  set K' : Set F := Metric.cthickening δ₀ (Binf '' K) with hK'def
  have hK'cpt : IsCompact K' := hBKcpt.cthickening
  have hK'V : K' ⊆ V := hδ₀V
  have hB0 : TendstoUniformlyOn B Binf atTop K :=
    tendstoUniformlyOn_of_cPConv (hB K hK hKU 0)
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
  refine mapCPConvOn_of_tendstoUniformlyOn hU hKU
    (fun k => ContDiffOn.comp ((hAc k).of_le (by exact_mod_cast le_top))
      ((hBc k).of_le (by exact_mod_cast le_top)) (hmapk k))
    (ContDiffOn.comp (hAinfc.of_le (by exact_mod_cast le_top))
      (hBinfc.of_le (by exact_mod_cast le_top)) hmap) ?_
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
  have hAeval : ∀ i : ℕ,
      TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ i (A k) (B k x))
        (fun x => iteratedFDeriv ℝ i Ainf (Binf x)) atTop K :=
    fun i => hA.tendstoUniformlyOn_iteratedFDeriv_comp_moving hV hK'cpt hK'V
      hAc hAinfc (tendstoUniformlyOn_of_cPConv (hB K hK hKU 0)) hBK' hBinfK' i
  have hBder : ∀ i : ℕ,
      TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ i (B k) x)
        (fun x => iteratedFDeriv ℝ i Binf x) atTop K :=
    fun i => hB.tendstoUniformlyOn_iteratedFDeriv hU hK hKU hBc hBinfc i
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
          (by exact_mod_cast le_top : (r : WithTop ℕ∞) ≤ ∞))
      have hlim :
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) x =
            (ftaylorSeries ℝ Ainf (Binf x)).taylorComp (ftaylorSeries ℝ Binf x) r := by
        simpa [Function.comp_def] using
          (iteratedFDeriv_comp
          (hAinfc.contDiffAt (hV.mem_nhds hBinfV))
          (hBinfc.contDiffAt (hU.mem_nhds hxU))
          (by exact_mod_cast le_top : (r : WithTop ℕ∞) ≤ ∞))
      rw [hcur, hlim]
    refine htaylor.trans_isLittleO ?_
    refine FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO ?hp ?hpf ?hq1 ?hq2 ?hqf
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y ∈ K', ‖iteratedFDeriv ℝ i Ainf y‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK'cpt.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hAinfc hV
            (by exact_mod_cast le_top)).norm.mono hK'V)
        exact ⟨C, fun y hy => hC ⟨y, hy, rfl⟩⟩
      exact isBoundedUnder_prod_principal_of_eventually_forall_le
        ⟨C + 1, TendstoUniformlyOn.eventually_norm_le (hAeval i)
          (fun x hx => hC (Binf x) (hBinfK' hx))⟩
    · intro i hi
      exact TendstoUniformlyOn.isLittleO_sub_const (hAeval i)
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i Binf x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hBinfc hU
            (by exact_mod_cast le_top)).norm.mono hKU)
        exact ⟨C, fun x hx => hC ⟨x, hx, rfl⟩⟩
      exact isBoundedUnder_prod_principal_of_eventually_forall_le
        ⟨C + 1, TendstoUniformlyOn.eventually_norm_le (hBder i) hC⟩
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i Binf x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hBinfc hU
            (by exact_mod_cast le_top)).norm.mono hKU)
        exact ⟨C, fun x hx => hC ⟨x, hx, rfl⟩⟩
      exact isBoundedUnder_prod_principal_of_forall_le
        ⟨C, fun _ x hx => hC x hx⟩
    · intro i hi
      exact TendstoUniformlyOn.isLittleO_sub_const (hBder i)
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

end HCGCompactness
end DifferentialGeometry
