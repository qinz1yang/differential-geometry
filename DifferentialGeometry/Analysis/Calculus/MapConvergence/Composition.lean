import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Pi
import DifferentialGeometry.Analysis.Calculus.Inverse.RingBounds
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Analysis
open Filter Topology
open scoped ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem MapCPConvergenceOn.tendstoUniformlyOn_iteratedFDeriv
    {U K : Set E} {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (hU : IsOpen U) (hKU : K ⊆ U) (h : MapCPConvergenceOn K p Φ Φinf)
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

theorem MapCPConvergenceOn.comp_tendsto_atTop {K : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCPConvergenceOn K p Φ Φinf)
    {τ : ℕ → ℕ} (hτ : Tendsto τ atTop atTop) :
    MapCPConvergenceOn K p (fun k => Φ (τ k)) Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hτ.eventually_ge_atTop k0)
  exact ⟨N, fun k hk r hr x hx => hk0 (τ k) (hN k hk) r hr x hx⟩

theorem MapCInfConvergenceOnCompacts.comp_tendsto_atTop {U : Set E}
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCInfConvergenceOnCompacts U Φ Φinf)
    {τ : ℕ → ℕ} (hτ : Tendsto τ atTop atTop) :
    MapCInfConvergenceOnCompacts U (fun k => Φ (τ k)) Φinf :=
  fun K hK hKU p => (h K hK hKU p).comp_tendsto_atTop hτ

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem mapCInf_pair_tail
    {U : Set E} {Φ : ℕ → ℕ → E → G} {Φinf : E → G}
    (hconv : ∀ kn ln : ℕ → ℕ,
      Tendsto kn atTop atTop → Tendsto ln atTop atTop →
        MapCInfConvergenceOnCompacts U (fun n => Φ (kn n) (ln n)) Φinf)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (p : ℕ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ j ≤ p, ∀ x ∈ K,
      mapDerivNorm j (Φ k l) Φinf x ≤ ε := by
  classical
  intro ε hε
  by_contra hbad
  push Not at hbad
  choose k hk hbad using hbad
  choose l hl hbad using hbad
  choose j hj hbad using hbad
  choose x hx hbad using hbad
  have hk_top : Tendsto k atTop atTop :=
    tendsto_atTop_mono hk tendsto_id
  have hl_top : Tendsto l atTop atTop :=
    tendsto_atTop_mono hl tendsto_id
  obtain ⟨N, hN⟩ := hconv k l hk_top hl_top K hK hKU p ε hε
  exact not_lt_of_ge
    (hN N le_rfl (j N) (hj N) (x N) (hx N)) (hbad N)

theorem exists_three_tail {P : Nat → Nat → Nat → Prop}
    (h : ∀ an bn cn : Nat → Nat,
      Tendsto an atTop atTop → Tendsto bn atTop atTop →
        Tendsto cn atTop atTop →
          ∀ᶠ m in atTop, P (an m) (bn m) (cn m)) :
    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N, ∀ c ≥ N, P a b c := by
  classical
  by_contra hbad
  push Not at hbad
  choose a ha hbad using hbad
  choose b hb hbad using hbad
  choose c hc hbad using hbad
  have ha_top : Tendsto a atTop atTop :=
    tendsto_atTop_mono ha tendsto_id
  have hb_top : Tendsto b atTop atTop :=
    tendsto_atTop_mono hb tendsto_id
  have hc_top : Tendsto c atTop atTop :=
    tendsto_atTop_mono hc tendsto_id
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h a b c ha_top hb_top hc_top)
  exact hbad N (hN N le_rfl)

theorem MapCInfConvergenceOnCompacts.eventually_mapsTo
    {U : Set E} {Φ : Nat → E → F} {Φinf : E → F}
    (hconv : MapCInfConvergenceOnCompacts U Φ Φinf)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hΦinf : ContinuousOn Φinf K)
    {V : Set F} (hV : IsOpen V) (hmap : Set.MapsTo Φinf K V) :
    ∀ᶠ n in atTop, Set.MapsTo (Φ n) K V := by
  have hKimage : IsCompact (Φinf '' K) :=
    hK.image_of_continuousOn hΦinf
  have hKV : Φinf '' K ⊆ V := Set.image_subset_iff.mpr hmap
  obtain ⟨delta, hdelta, hthick⟩ :=
    hKimage.exists_thickening_subset_open hV hKV
  have htu := tendstoUniformlyOn_of_cPConvergence (hconv K hK hKU 0)
  rw [Metric.tendstoUniformlyOn_iff] at htu
  filter_upwards [htu delta hdelta] with n hn
  intro x hx
  apply hthick
  rw [Metric.mem_thickening_iff]
  exact ⟨Φinf x, ⟨x, hx, rfl⟩, by
    simpa only [dist_comm] using hn x hx⟩

theorem MapCInfConvergenceOnCompacts.three_tail
    {U : Set E} {Φ : ℕ → ℕ → ℕ → E → F} {Φinf : E → F}
    (hconv : ∀ an bn cn : ℕ → ℕ,
      Tendsto an atTop atTop → Tendsto bn atTop atTop →
        Tendsto cn atTop atTop →
      MapCInfConvergenceOnCompacts U
        (fun n => Φ (an n) (bn n) (cn n)) Φinf)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (p : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, ∀ c ≥ N,
      ∀ r ≤ p, ∀ x ∈ K, mapDerivNorm r (Φ a b c) Φinf x ≤ ε := by
  classical
  by_contra hbad
  push Not at hbad
  choose a ha hbad using hbad
  choose b hb hbad using hbad
  choose c hc hbad using hbad
  choose r hr hbad using hbad
  choose x hx hbad using hbad
  have ha_top : Tendsto a atTop atTop :=
    tendsto_atTop_mono ha tendsto_id
  have hb_top : Tendsto b atTop atTop :=
    tendsto_atTop_mono hb tendsto_id
  have hc_top : Tendsto c atTop atTop :=
    tendsto_atTop_mono hc tendsto_id
  have hΦ := hconv a b c ha_top hb_top hc_top
  obtain ⟨N, hN⟩ := hΦ K hK hKU p ε hε
  exact not_lt_of_ge
    (hN N le_rfl (r N) (hr N) (x N) (hx N)) (hbad N)

theorem exists_cInf_finite
    {ι : Type*} [Finite ι]
    (U : ι → Set E) (Φ : ι → ℕ → E → F)
    (Q : ι → (E → F) → Prop)
    (hstep : ∀ i (τ : ℕ → ℕ), StrictMono τ →
      ∃ (σ : ℕ → ℕ) (Φinf : E → F), StrictMono σ ∧
        MapCInfConvergenceOnCompacts (U i)
          (fun n => Φ i (τ (σ n))) Φinf ∧ Q i Φinf) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∀ i, ∃ Φinf : E → F,
        MapCInfConvergenceOnCompacts (U i) (fun n => Φ i (ψ n)) Φinf ∧ Q i Φinf := by
  classical
  let := Fintype.ofFinite ι
  have aux : ∀ s : Finset ι,
      ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
        ∀ i ∈ s, ∃ Φinf : E → F,
          MapCInfConvergenceOnCompacts (U i) (fun n => Φ i (ψ n)) Φinf ∧ Q i Φinf := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨id, strictMono_id, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨τ, hτ, hconv⟩ := ih
        obtain ⟨σ, Φa, hσ, hΦa, hQa⟩ := hstep a τ hτ
        refine ⟨τ ∘ σ, hτ.comp hσ, ?_⟩
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact ⟨Φa, by simpa only [Function.comp_apply] using hΦa, hQa⟩
        · obtain ⟨Φinf, hΦinf, hQinf⟩ := hconv i hi
          exact ⟨Φinf, by
            simpa only [Function.comp_apply] using
              hΦinf.comp_tendsto_atTop hσ.tendsto_atTop, hQinf⟩
  obtain ⟨ψ, hψ, hconv⟩ := aux Finset.univ
  exact ⟨ψ, hψ, fun i => hconv i (Finset.mem_univ i)⟩

theorem MapCInfConvergenceOnCompacts.tendstoUniformlyOn_iteratedFDeriv
    {U K : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (h : MapCInfConvergenceOnCompacts U Φ Φinf)
    (hΦ : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (Φ k) U)
    (hΦinf : ContDiffOn ℝ (∞ : WithTop ℕ∞) Φinf U) (r : ℕ) :
    TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ r (Φ k) x)
      (fun x => iteratedFDeriv ℝ r Φinf x) atTop K := by
  exact (h K hK hKU r).tendstoUniformlyOn_iteratedFDeriv hU hKU
    (fun k => (hΦ k).of_le (by exact_mod_cast le_top))
    (hΦinf.of_le (by exact_mod_cast le_top)) le_rfl

theorem mapCPConvergenceOn_of_tendstoUniformlyOn {U K : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F} (hU : IsOpen U) (hKU : K ⊆ U)
    (hΦ : ∀ k, ContDiffOn ℝ (p : ℕ∞) (Φ k) U)
    (hΦinf : ContDiffOn ℝ (p : ℕ∞) Φinf U)
    (htu : ∀ r : ℕ, r ≤ p →
      TendstoUniformlyOn (fun k x => iteratedFDeriv ℝ r (Φ k) x)
        (fun x => iteratedFDeriv ℝ r Φinf x) atTop K) :
    MapCPConvergenceOn K p Φ Φinf := by
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
theorem isBoundedUnder_prod_principal_of_forall_le {K : Set E} {u : ℕ × E → ℝ}
    (h : ∃ C : ℝ, ∀ k x, x ∈ K → u (k, x) ≤ C) :
    (atTop ×ˢ Filter.principal K).IsBoundedUnder (· ≤ ·) u := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rw [eventually_map, eventually_prod_principal_iff]
  exact Eventually.of_forall fun k x hx => hC k x hx

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem isBoundedUnder_prod_principal_of_eventually_forall_le {K : Set E} {u : ℕ × E → ℝ}
    (h : ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, u (k, x) ≤ C) :
    (atTop ×ˢ Filter.principal K).IsBoundedUnder (· ≤ ·) u := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rw [eventually_map, eventually_prod_principal_iff]
  exact hC

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
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
theorem MapCInfConvergenceOnCompacts.tendstoUniformlyOn_iteratedFDeriv_comp_moving
    {K : Set E} {V K' : Set F}
    {A : ℕ → F → G} {Ainf : F → G} {B : ℕ → E → F} {Binf : E → F}
    (hV : IsOpen V) (hK' : IsCompact K') (hK'V : K' ⊆ V)
    (hA : MapCInfConvergenceOnCompacts V A Ainf)
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

theorem MapCPConvergenceOn.comp_cInf
    {U K : Set E} {V : Set F} {p : ℕ} (hU : IsOpen U) (hV : IsOpen V)
    [ProperSpace F]
    {B : ℕ → E → F} {Binf : E → F} {A : ℕ → F → G} {Ainf : F → G}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hB : MapCPConvergenceOn K p B Binf)
    (hA : MapCInfConvergenceOnCompacts V A Ainf)
    (hBc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Binf U)
    (hAc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf V)
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
    fun i => hA.tendstoUniformlyOn_iteratedFDeriv_comp_moving hV hK'compact hK'V
      hAc hAinfc (tendstoUniformlyOn_of_cPConvergence (hB.mono_order (Nat.zero_le p)))
      hBK' hBinfK' i
  have hBder : ∀ i : ℕ, i ≤ p →
      TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ i (B k) x)
        (fun x => iteratedFDeriv ℝ i Binf x) atTop K :=
    fun i hi => hB.tendstoUniformlyOn_iteratedFDeriv hU hKU
      (fun k => (hBc k).of_le (by exact_mod_cast le_top))
      (hBinfc.of_le (by exact_mod_cast le_top)) hi
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
        obtain ⟨C, hC⟩ := hK'compact.bddAbove_image
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
        ⟨C + 1, TendstoUniformlyOn.eventually_norm_le (hBder i (hi.trans hr)) hC⟩
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i Binf x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hBinfc hU
            (by exact_mod_cast le_top)).norm.mono hKU)
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

theorem MapCInfConvergenceOnCompacts.comp
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    [ProperSpace F]
    {B : ℕ → E → F} {Binf : E → F} {A : ℕ → F → G} {Ainf : F → G}
    (hB : MapCInfConvergenceOnCompacts U B Binf)
    (hA : MapCInfConvergenceOnCompacts V A Ainf)
    (hBc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Binf U)
    (hAc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V) (hmapk : ∀ k, Set.MapsTo (B k) U V) :
    MapCInfConvergenceOnCompacts U (fun k x => A k (B k x)) (fun x => Ainf (Binf x)) := by
  intro K hK hKU p
  exact MapCPConvergenceOn.comp_cInf hU hV hK hKU (hB K hK hKU p) hA
    hBc hBinfc hAc hAinfc hmap hmapk

theorem MapCInfConvergenceOnCompacts.comp_of_finiteDimensional
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    [FiniteDimensional Real F]
    {B : Nat → E → F} {Binf : E → F}
    {A : Nat → F → G} {Ainf : F → G}
    (hB : MapCInfConvergenceOnCompacts U B Binf)
    (hA : MapCInfConvergenceOnCompacts V A Ainf)
    (hBc : ∀ k, ContDiffOn Real ∞ (B k) U)
    (hBinfc : ContDiffOn Real ∞ Binf U)
    (hAc : ∀ k, ContDiffOn Real ∞ (A k) V)
    (hAinfc : ContDiffOn Real ∞ Ainf V)
    (hmap : Set.MapsTo Binf U V)
    (hmapk : ∀ k, Set.MapsTo (B k) U V) :
    MapCInfConvergenceOnCompacts U (fun k x => A k (B k x))
      (fun x => Ainf (Binf x)) := by
  let : ProperSpace F := FiniteDimensional.proper Real F
  exact hB.comp hU hV hA hBc hBinfc hAc hAinfc hmap hmapk

theorem MapCInfConvergenceOnCompacts.const_arg
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    [ProperSpace F]
    {A : Nat → F → G} {Ainf : F → G} {y₀ : F}
    (hy₀ : y₀ ∈ V) (hA : MapCInfConvergenceOnCompacts V A Ainf)
    (hAc : ∀ k, ContDiffOn Real ∞ (A k) V)
    (hAinfc : ContDiffOn Real ∞ Ainf V) :
    MapCInfConvergenceOnCompacts U (fun k _ => A k y₀) (fun _ => Ainf y₀) := by
  have hconst : MapCInfConvergenceOnCompacts U
      (fun _ : Nat => fun _ : E => y₀) (fun _ : E => y₀) :=
    by
      intro K _ _ p ε hε
      exact ⟨0, fun k _ r _ x _ => by
        simpa [mapDerivNorm, sub_self] using hε.le⟩
  exact hconst.comp hU hV hA
    (fun _ => contDiffOn_const) contDiffOn_const hAc hAinfc
    (fun _ _ => hy₀) (fun _ _ _ => hy₀)

section BasicClosures

variable {E' P Q : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem mapCInfConvergence_const {U : Set E'} (Φ : E' → P) :
    MapCInfConvergenceOnCompacts U (fun _ : ℕ => Φ) Φ := by
  intro K _ _ p ε hε
  exact ⟨0, fun k _ r _ x _ => by
    simpa [mapDerivNorm, sub_self] using hε.le⟩

theorem MapCInfConvergenceOnCompacts.precomp
    {D : Set E'} {U : Set P} (hD : IsOpen D) (hU : IsOpen U)
    [ProperSpace P]
    {A : Nat → P → Q} {Ainf : P → Q}
    (hA : MapCInfConvergenceOnCompacts U A Ainf)
    {f : E' → P} (hf : ContDiffOn ℝ (∞ : WithTop ℕ∞) f D)
    (hmap : Set.MapsTo f D U)
    (hAc : ∀ n, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A n) U)
    (hAinfC : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf U) :
    MapCInfConvergenceOnCompacts D
      (fun n x => A n (f x)) (fun x => Ainf (f x)) :=
  MapCInfConvergenceOnCompacts.comp hD hU (mapCInfConvergence_const f) hA
    (fun _ => hf) hf hAc hAinfC hmap (fun _ => hmap)

theorem MapCPConvergenceOn.prodMk {U K : Set E'} {p : ℕ} (hU : IsOpen U) (hKU : K ⊆ U)
    {u : ℕ → E' → P} {uinf : E' → P} {v : ℕ → E' → Q} {vinf : E' → Q}
    (hu : MapCPConvergenceOn K p u uinf) (hv : MapCPConvergenceOn K p v vinf)
    (huc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U)
    (hvc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) vinf U) :
    MapCPConvergenceOn K p (fun k y => (u k y, v k y)) (fun y => (uinf y, vinf y)) := by
  intro ε hε
  obtain ⟨k1, hk1⟩ := hu ε hε
  obtain ⟨k2, hk2⟩ := hv ε hε
  refine ⟨max k1 k2, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hle : ((r : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcu : ContDiffAt ℝ (r : ℕ∞) (fun y => u k y - uinf y) x :=
    (((huc k).sub huinfc).contDiffAt (hU.mem_nhds hxU)).of_le hle
  have hcv : ContDiffAt ℝ (r : ℕ∞) (fun y => v k y - vinf y) x :=
    (((hvc k).sub hvinfc).contDiffAt (hU.mem_nhds hxU)).of_le hle
  have heq : (fun y => (u k y, v k y) - (uinf y, vinf y))
      = fun y => (u k y - uinf y, v k y - vinf y) := by
    funext y; simp [Prod.mk_sub_mk]
  have hkey : mapDerivNorm r (fun y => (u k y, v k y)) (fun y => (uinf y, vinf y)) x
      = max (mapDerivNorm r (u k) uinf x) (mapDerivNorm r (v k) vinf x) := by
    simp only [mapDerivNorm]
    rw [heq, iteratedFDeriv_prodMk hcu hcv le_rfl,
      ContinuousMultilinearMap.opNorm_prod]
  rw [hkey]
  exact max_le (hk1 k (le_trans (le_max_left k1 k2) hk) r hr x hx)
    (hk2 k (le_trans (le_max_right k1 k2) hk) r hr x hx)

theorem mapCInfConvergence_prodMk {U : Set E'} (hU : IsOpen U)
    {u : ℕ → E' → P} {uinf : E' → P} {v : ℕ → E' → Q} {vinf : E' → Q}
    (hu : MapCInfConvergenceOnCompacts U u uinf) (hv : MapCInfConvergenceOnCompacts U v vinf)
    (huc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U)
    (hvc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) vinf U) :
    MapCInfConvergenceOnCompacts U (fun k y => (u k y, v k y)) (fun y => (uinf y, vinf y)) := by
  intro K hK hKU p
  exact MapCPConvergenceOn.prodMk hU hKU (hu K hK hKU p) (hv K hK hKU p)
    huc huinfc hvc hvinfc

theorem mapCInfConvergence_pi {ι : Type*} [Fintype ι] {U : Set E'} (hU : IsOpen U)
    {v : ι → ℕ → E' → Q} {vinf : ι → E' → Q}
    (hv : ∀ i, MapCInfConvergenceOnCompacts U (v i) (vinf i))
    (hvc : ∀ i k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (v i k) U)
    (hvinfc : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (vinf i) U) :
    MapCInfConvergenceOnCompacts U (fun k y i => v i k y) (fun y i => vinf i y) := by
  intro K hK hKU p ε hε
  choose k0 hk0 using fun i => hv i K hK hKU p ε hε
  refine ⟨Finset.univ.sup k0, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hle : ((r : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcd : ∀ i, ContDiffAt ℝ ((r : ℕ∞) : WithTop ℕ∞) (fun y => v i k y - vinf i y) x :=
    fun i => (((hvc i k).sub (hvinfc i)).contDiffAt (hU.mem_nhds hxU)).of_le hle
  have heq : (fun y => (fun i => v i k y) - fun i => vinf i y)
      = fun y (i : ι) => v i k y - vinf i y := rfl
  have hkey : mapDerivNorm r (fun y i => v i k y) (fun y i => vinf i y) x
      = ‖fun i => iteratedFDeriv ℝ r (fun y => v i k y - vinf i y) x‖ := by
    simp only [mapDerivNorm]
    rw [heq, iteratedFDeriv_pi hcd le_rfl, ContinuousMultilinearMap.opNorm_pi]
  rw [hkey, pi_norm_le_iff_of_nonneg hε.le]
  intro i
  exact hk0 i k (le_trans (Finset.le_sup (Finset.mem_univ i)) hk) r hr x hx

theorem mapCInf_apply {ι : Type*} [Fintype ι]
    {U : Set E'} (hU : IsOpen U)
    {u : ℕ → E' → (ι → Q)} {uinf : E' → (ι → Q)}
    (hu : MapCInfConvergenceOnCompacts U u uinf)
    (huc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U) (i : ι) :
    MapCInfConvergenceOnCompacts U (fun k x ↦ u k x i) (fun x ↦ uinf x i) := by
  intro K hK hKU p epsilon hepsilon
  obtain ⟨k0, hk0⟩ := hu K hK hKU p epsilon hepsilon
  refine ⟨k0, fun k hk r hr x hx ↦ ?_⟩
  have hxU : x ∈ U := hKU hx
  have hle : ((r : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hcd : ∀ j : ι, ContDiffAt ℝ (r : ℕ∞)
      (fun y ↦ u k y j - uinf y j) x := by
    intro j
    exact (((contDiffOn_pi.mp (huc k) j).sub
      (contDiffOn_pi.mp huinfc j)).contDiffAt (hU.mem_nhds hxU)).of_le hle
  have hbase := hk0 k hk r hr x hx
  simp only [mapDerivNorm] at hbase ⊢
  change ‖iteratedFDeriv ℝ r (fun y j ↦ u k y j - uinf y j) x‖ ≤ epsilon at hbase
  rw [iteratedFDeriv_pi hcd le_rfl, ContinuousMultilinearMap.opNorm_pi] at hbase
  exact (norm_le_pi_norm (fun j ↦
    iteratedFDeriv ℝ r (fun y ↦ u k y j - uinf y j) x) i).trans hbase

theorem mapCInfConvergence_clm {F' G' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {U : Set E'} (hU : IsOpen U) (L : F' →L[ℝ] G')
    {u : ℕ → E' → F'} {uinf : E' → F'}
    (hu : MapCInfConvergenceOnCompacts U u uinf)
    (huc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U) :
    MapCInfConvergenceOnCompacts U (fun k y => L (u k y)) (fun y => L (uinf y)) := by
  intro K hK hKU p ε hε
  have hL1 : (0 : ℝ) < ‖L‖ + 1 := by positivity
  obtain ⟨k0, hk0⟩ := hu K hK hKU p (ε / (‖L‖ + 1)) (div_pos hε hL1)
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hle : ((r : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcd : ContDiffAt ℝ ((r : ℕ∞) : WithTop ℕ∞) (fun y => u k y - uinf y) x :=
    (((huc k).sub huinfc).contDiffAt (hU.mem_nhds hxU)).of_le hle
  have heq : (fun y => L (u k y) - L (uinf y)) = ⇑L ∘ fun y => u k y - uinf y := by
    funext y; simp [Function.comp_apply, map_sub]
  have hbase : ‖iteratedFDeriv ℝ r (fun y => u k y - uinf y) x‖ ≤ ε / (‖L‖ + 1) :=
    hk0 k hk r hr x hx
  simp only [mapDerivNorm]
  rw [heq, ContinuousLinearMap.iteratedFDeriv_comp_left L hcd le_rfl]
  calc ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ r (fun y => u k y - uinf y) x)‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ r (fun y => u k y - uinf y) x‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ (‖L‖ + 1) * (ε / (‖L‖ + 1)) := by
        refine mul_le_mul (by linarith [norm_nonneg L]) hbase (norm_nonneg _) hL1.le
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hL1)

theorem MapCInfConvergenceOnCompacts.pullbackForm
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [ProperSpace ((W →L[ℝ] W →L[ℝ] ℝ) × (V →L[ℝ] W))]
    {U : Set E'} (hU : IsOpen U)
    {B : ℕ → E' → W →L[ℝ] W →L[ℝ] ℝ} {Binf : E' → W →L[ℝ] W →L[ℝ] ℝ}
    {D : ℕ → E' → V →L[ℝ] W} {Dinf : E' → V →L[ℝ] W}
    (hB : MapCInfConvergenceOnCompacts U B Binf)
    (hD : MapCInfConvergenceOnCompacts U D Dinf)
    (hBc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (B k) U)
    (hBinfC : ContDiffOn ℝ (∞ : WithTop ℕ∞) Binf U)
    (hDc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (D k) U)
    (hDinfC : ContDiffOn ℝ (∞ : WithTop ℕ∞) Dinf U) :
    MapCInfConvergenceOnCompacts U
      (fun k z => pullbackForm (B k z, D k z))
      (fun z => pullbackForm (Binf z, Dinf z)) := by
  have hpair : MapCInfConvergenceOnCompacts U
      (fun k z => (B k z, D k z)) (fun z => (Binf z, Dinf z)) :=
    mapCInfConvergence_prodMk hU hB hD hBc hBinfC hDc hDinfC
  apply MapCInfConvergenceOnCompacts.comp hU isOpen_univ hpair
    (mapCInfConvergence_const (U := Set.univ)
      (_root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm (E := V) (F := W)))
  · exact fun k => (hBc k).prodMk (hDc k)
  · exact hBinfC.prodMk hDinfC
  · exact fun _ => pullbackForm.contDiff.contDiffOn
  · exact pullbackForm.contDiff.contDiffOn
  · exact fun _ _ => Set.mem_univ _
  · exact fun _ _ _ => Set.mem_univ _

theorem MapCInfConvergenceOnCompacts.pullbackForm_comp_fderiv
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup W] [NormedSpace Real W] [ProperSpace W]
    [ProperSpace ((W →L[Real] W →L[Real] Real) × (V →L[Real] W))]
    {U : Set V} {D : Set W} (hU : IsOpen U) (hD : IsOpen D)
    {A : Nat → V → W} {Ainf : V → W}
    {B : Nat → W → (W →L[Real] W →L[Real] Real)}
    {Binf : W → (W →L[Real] W →L[Real] Real)}
    (hA : MapCInfConvergenceOnCompacts U A Ainf)
    (hB : MapCInfConvergenceOnCompacts D B Binf)
    (hAc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (A n) U)
    (hAinfC : ContDiffOn Real (∞ : WithTop ℕ∞) Ainf U)
    (hBc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (B n) D)
    (hBinfC : ContDiffOn Real (∞ : WithTop ℕ∞) Binf D)
    (hmapInf : Set.MapsTo Ainf U D)
    (hmap : ∀ n, Set.MapsTo (A n) U D) :
    MapCInfConvergenceOnCompacts U
      (fun n z ↦ _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (B n (A n z), fderiv Real (A n) z))
      (fun z ↦ _root_.DifferentialGeometry.CheegerGromovCompactness.pullbackForm
        (Binf (Ainf z), fderiv Real Ainf z)) := by
  have hBA : MapCInfConvergenceOnCompacts U
      (fun n z ↦ B n (A n z)) (fun z ↦ Binf (Ainf z)) :=
    MapCInfConvergenceOnCompacts.comp hU hD hA hB hAc hAinfC hBc hBinfC
      hmapInf hmap
  have hDA : MapCInfConvergenceOnCompacts U
      (fun n z ↦ fderiv Real (A n) z) (fun z ↦ fderiv Real Ainf z) :=
    hA.fderivOn hU hAc hAinfC
  have hBAc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ B n (A n z)) U := by
    intro n
    simpa only [Function.comp_def] using
      ContDiffOn.comp (hBc n) (hAc n) (hmap n)
  have hBAinfC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ Binf (Ainf z)) U := by
    simpa only [Function.comp_def] using
      ContDiffOn.comp hBinfC hAinfC hmapInf
  have hDAc : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ fderiv Real (A n) z) U := by
    intro n z hz
    exact (((hAc n).contDiffAt (hU.mem_nhds hz)).fderiv_right
      (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt
  have hDAinfC : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun z ↦ fderiv Real Ainf z) U := by
    intro z hz
    exact ((hAinfC.contDiffAt (hU.mem_nhds hz)).fderiv_right
      (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt
  exact hBA.pullbackForm hU hDA hBAc hBAinfC hDAc hDAinfC

end BasicClosures

theorem MapCInfConvergenceOnCompacts.ringInv
    {E R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R] [HasSummableGeomSeries R]
    [ProperSpace R]
    {U : Set E} (hU : IsOpen U)
    {A : ℕ → E → R} {Ainf : E → R}
    (hA : MapCInfConvergenceOnCompacts U A Ainf)
    (hAc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A k) U)
    (hAinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf U)
    (hunit : ∀ k x, x ∈ U → IsUnit (A k x))
    (hunitInf : ∀ x, x ∈ U → IsUnit (Ainf x)) :
    MapCInfConvergenceOnCompacts U
      (fun k x => Ring.inverse (A k x))
      (fun x => Ring.inverse (Ainf x)) := by
  apply MapCInfConvergenceOnCompacts.comp hU Units.isOpen hA
    (mapCInfConvergence_const (U := {y : R | IsUnit y}) Ring.inverse)
    hAc hAinfc
    (fun _ => contDiffOn_ringInverse (𝕜 := ℝ) (∞ : WithTop ℕ∞))
    (contDiffOn_ringInverse (𝕜 := ℝ) (∞ : WithTop ℕ∞))
  · exact fun x hx => hunitInf x hx
  · exact fun k x hx => hunit k x hx

end CheegerGromovCompactness
end DifferentialGeometry
