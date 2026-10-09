import DifferentialGeometry.Topology.Manifold.SmoothApproximation.NoncompactTarget
import DifferentialGeometry.Analysis.Calculus.MapConvergence.EventualCongruence

/-!
# Smooth approximation near a compact set of a noncompact source (LFR48, tier T1)

The approximation tools W1a, W1 (lane W-1), Codex X89 and the relative forms of lane W-2b all assume
a COMPACT source manifold. LFR48 (A:29037) approximates a `C^s` comparison embedding defined on an
open subset of a noncompact limit manifold, near a compact buffer, by a smooth map that still sends
the marked point to the marked point.

* `MapCPConvergenceOn.add_const_seq`: adding constants `c j → 0` preserves `C^p` convergence of `C^p`
  maps (used for the pointed correction).
* `exists_smooth_seq_chart_tendsto_near_isCompact`: for `h` of class `C^k` on an open `U` of a
  Hausdorff boundaryless manifold `A` (no compactness), a compact `C ⊆ U` and a point `x₀ ∈ C`, there
  are an open `W` with `C ⊆ W ⊆ U` and maps `hs j` into a boundaryless metric manifold `B`, smooth on
  `W`, with `hs j x₀ = h x₀` for every `j`, `hs j → h` uniformly on `W`, and chartwise `C^k`
  convergence (with eventual chart capture) on every compact chart piece over `W`.

Route: local embeddings with smooth retractions near the compact sets `C ⊆ A` and `h(C) ⊆ B`
(`Geometry.exists_contMDiff_embedding_retraction_near_isCompact`); the Euclidean map
`F = e_B ∘ h ∘ r_A` is `C^k` near `e_A(C)`; one cutoff and one mollification; the constant shift
`G(e_A x₀) − g_j(e_A x₀)`; then `hs j = r_B ∘ g_j ∘ e_A` after a fixed index shift that captures the
compact image `G(closure O)` in the retraction domain.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

/-- Adding constants `c j → 0` to a `C^p`-convergent sequence of `C^p` maps keeps the convergence. -/
theorem MapCPConvergenceOn.add_const_seq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {p : ℕ} {Φ : ℕ → E → F}
    {Φinf : E → F} (h : MapCPConvergenceOn K p Φ Φinf) (hΦ : ∀ j, ContDiff ℝ (p : ℕ∞) (Φ j))
    (hΦinf : ContDiff ℝ (p : ℕ∞) Φinf) {c : ℕ → F} (hc : Tendsto c atTop (𝓝 0)) :
    MapCPConvergenceOn K p (fun j y => Φ j y + c j) Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨k1, hk1⟩ := eventually_atTop.mp (hc.eventually (Metric.ball_mem_nhds 0 (half_pos hε)))
  refine ⟨max k0 k1, fun k hk r hr x hx => ?_⟩
  have h0 := hk0 k (le_of_max_le_left hk) r hr x hx
  have hck : ‖c k‖ < ε / 2 := by simpa using hk1 k (le_of_max_le_right hk)
  have hfun : (fun y => Φ k y + c k - Φinf y) =
      (fun y => Φ k y - Φinf y) + fun _ => c k := by
    funext y
    simp only [Pi.add_apply]
    abel
  unfold mapDerivNorm at h0 ⊢
  rw [hfun]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [norm_iteratedFDeriv_zero] at h0 ⊢
    calc ‖Φ k x - Φinf x + c k‖ ≤ ‖Φ k x - Φinf x‖ + ‖c k‖ := norm_add_le _ _
      _ ≤ ε := by linarith
  · have hdiff : ContDiffAt ℝ r (fun y => Φ k y - Φinf y) x :=
      (((hΦ k).sub hΦinf).of_le (by exact_mod_cast hr)).contDiffAt
    rw [iteratedFDeriv_add_apply hdiff contDiffAt_const, iteratedFDeriv_const_of_ne hr0.ne',
      Pi.zero_apply, add_zero]
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A] [T2Space A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {B : Type*} [MetricSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

/-- **LFR48 T1: pointed smooth approximation near a compact set of a noncompact source.** Let `h`
be `C^k` on an open set `U` of a Hausdorff boundaryless manifold `A`, `C ⊆ U` compact and `x₀ ∈ C`.
There are an open `W` with `C ⊆ W ⊆ U` and maps `hs j : A → B`, smooth on `W`, with `hs j x₀ = h x₀`,
`hs j → h` uniformly on `W`, and, for all charts `φ_p` of `A`, `ψ_q` of `B` and every compact `K` in
the target of `φ_p` over `W` with `h (φ_p⁻¹ K) ⊆ source ψ_q`: eventually `hs j (φ_p⁻¹ K) ⊆ source ψ_q`
and `ψ_q ∘ hs j ∘ φ_p⁻¹ → ψ_q ∘ h ∘ φ_p⁻¹` in `C^k` on `K`. -/
theorem exists_smooth_seq_chart_tendsto_near_isCompact (k : ℕ) {U : Set A} (hU : IsOpen U)
    {h : A → B} (hh : ContMDiffOn I J k h U) {C : Set A} (hC : IsCompact C) (hCU : C ⊆ U)
    {x₀ : A} (hx₀ : x₀ ∈ C) :
    ∃ W : Set A, IsOpen W ∧ C ⊆ W ∧ W ⊆ U ∧ ∃ hs : ℕ → A → B,
      (∀ j, ContMDiffOn I J ∞ (hs j) W) ∧ (∀ j, hs j x₀ = h x₀) ∧
      TendstoUniformlyOn hs h atTop W ∧
      ∀ (p : A) (q : B) (K : Set E), IsCompact K →
        K ⊆ (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' W →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => hs j ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K k (fun j y => extChartAt J q (hs j ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y))) := by
  classical
  obtain ⟨Ns, n, es, rs, Vs, hCNs, hes, -, -, -, hVs, hesVs, hrs, hrsid⟩ :=
    DifferentialGeometry.Geometry.exists_contMDiff_embedding_retraction_near_isCompact
      (I := I) hC ⟨x₀, hx₀⟩
  have hhC : IsCompact (h '' C) := hC.image_of_continuousOn (hh.continuousOn.mono hCU)
  obtain ⟨Nt, m, et, rt, Vt, hCNt, het, -, -, -, hVt, hetVt, hrt, hrtid⟩ :=
    DifferentialGeometry.Geometry.exists_contMDiff_embedding_retraction_near_isCompact
      (I := J) hhC ⟨h x₀, mem_image_of_mem h hx₀⟩
  -- the open set where all data are defined
  let S : Set A := (Ns : Set A) ∩ (U ∩ h ⁻¹' (Nt : Set B))
  have hS : IsOpen S := Ns.isOpen.inter (hh.continuousOn.isOpen_inter_preimage hU Nt.isOpen)
  have hCS : C ⊆ S := fun x hx => ⟨hCNs hx, hCU hx, hCNt (mem_image_of_mem h hx)⟩
  let Vs' : Set (EuclideanSpace ℝ (Fin n)) := Vs ∩ rs ⁻¹' S
  have hVs' : IsOpen Vs' := hrs.continuousOn.isOpen_inter_preimage hVs hS
  have hesS : ∀ x ∈ S, es x ∈ Vs' := by
    intro x hx
    refine ⟨hesVs ⟨x, hx.1, rfl⟩, ?_⟩
    change rs (es x) ∈ S
    rw [hrsid x hx.1]
    exact hx
  -- the Euclidean map and its cutoff
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) := fun z => et (h (rs z))
  have hF : ContDiffOn ℝ k F Vs' := by
    have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) J k (h ∘ rs) Vs' :=
      hh.comp ((hrs.mono inter_subset_left).of_le (by exact_mod_cast le_top))
        (fun z hz => hz.2.2.1)
    exact contMDiffOn_iff_contDiffOn.mp ((het.of_le (by exact_mod_cast le_top)).comp_contMDiffOn h1)
  have hesC : IsCompact (es '' C) := hC.image hes.continuous
  have hesCVs' : es '' C ⊆ Vs' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hesS x (hCS hx)
  obtain ⟨χ, hχ, hχc, hχone, hχU, -⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hesC hVs' hesCVs'
  obtain ⟨O1, hO1, hCO1, hO1one⟩ := mem_nhdsSet_iff_exists.mp hχone
  let G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) := fun z => χ z • F z
  have hG : ContDiff ℝ k G := by
    apply contDiffOn_univ.mp
    exact DifferentialGeometry.Analysis.contDiffOn_cutoff_smul hVs'
      (hχ.of_le (by exact_mod_cast le_top)) hχU (by simpa only [univ_inter] using hF)
  have hGc : HasCompactSupport G := hχc.smul_right
  have hGF : ∀ z ∈ O1, G z = F z := by
    intro z hz
    have hz1 : χ z = 1 := by simpa using hO1one hz
    simp only [G, hz1, one_smul]
  -- mollification and the pointed shift
  obtain ⟨-, -, -, -, g, hg, -, hconv⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_approx_supported_in_open_of_contDiff k hG hGc
      isOpen_univ (subset_univ _)
  have hgk : ∀ j, ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) (g j) := fun j =>
    (hg j).of_le (by exact_mod_cast le_top)
  have hgG : MapCPConvergenceOn univ k g G :=
    mapCPConvergenceOn_of_tendstoUniformly hgk hG fun j hj => (hconv j hj).tendstoUniformlyOn
  let c : ℕ → EuclideanSpace ℝ (Fin m) := fun j => G (es x₀) - g j (es x₀)
  have hc : Tendsto c atTop (𝓝 0) := by
    have h1 := (tendstoUniformlyOn_of_cPConvergence (hgG.mono_order (Nat.zero_le k))).tendsto_at
      (mem_univ (es x₀))
    have h2 := (tendsto_const_nhds (x := G (es x₀))).sub h1
    rw [sub_self] at h2
    exact h2
  let g' : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) := fun j z => g j z + c j
  have hg'G : MapCPConvergenceOn univ k g' G := MapCPConvergenceOn.add_const_seq hgG hgk hG hc
  have hg'sm : ∀ j, ContDiff ℝ ∞ (g' j) := fun j => (hg j).add contDiff_const
  have hg'k : ∀ j, ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) (g' j) := fun j =>
    (hg'sm j).of_le (by exact_mod_cast le_top)
  have hg'x₀ : ∀ j, g' j (es x₀) = G (es x₀) := by
    intro j
    simp only [g', c]
    abel
  -- a relatively compact buffer in the Euclidean source
  obtain ⟨O2, hO2, hCO2, hO2sub, hO2c⟩ :=
    exists_open_between_and_isCompact_closure hesC (hVs'.inter hO1) (subset_inter hesCVs' hCO1)
  let W : Set A := S ∩ es ⁻¹' O2
  have hW : IsOpen W := hS.inter (hO2.preimage hes.continuous)
  have hCW : C ⊆ W := fun x hx => ⟨hCS hx, hCO2 (mem_image_of_mem es hx)⟩
  have hWU : W ⊆ U := fun x hx => hx.1.2.1
  have hGVt : ∀ z ∈ closure O2, G z ∈ Vt := by
    intro z hz
    have hz' := hO2sub hz
    rw [hGF z hz'.2]
    have hrz : rs z ∈ S := hz'.1.2
    exact hetVt ⟨h (rs z), hrz.2.2, rfl⟩
  have hfixW : ∀ x ∈ W, rt (G (es x)) = h x := by
    intro x hx
    have hx1 : es x ∈ O1 := (hO2sub (subset_closure hx.2)).2
    rw [hGF _ hx1]
    change rt (et (h (rs (es x)))) = h x
    rw [hrsid x hx.1.1, hrtid (h x) hx.1.2.2]
  -- capture of the compact image in the retraction domain after a fixed index shift
  have hKt : IsCompact (G '' closure O2) := hO2c.image hG.continuous
  have hKtV : G '' closure O2 ⊆ Vt := by
    rintro _ ⟨z, hz, rfl⟩
    exact hGVt z hz
  obtain ⟨δ, hδ, hδV⟩ := hKt.exists_cthickening_subset_open hVt hKtV
  have hunif : TendstoUniformly g' G atTop :=
    tendstoUniformlyOn_univ.mp
      (tendstoUniformlyOn_of_cPConvergence (hg'G.mono_order (Nat.zero_le k)))
  obtain ⟨a, ha⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hunif δ hδ)
  have hcap : ∀ j, ∀ z ∈ closure O2,
      g' (j + a) z ∈ Metric.cthickening δ (G '' closure O2) := by
    intro j z hz
    apply Metric.mem_cthickening_of_dist_le _ (G z) _ _ (mem_image_of_mem G hz)
    rw [dist_comm]
    exact (ha (j + a) (Nat.le_add_left a j) z).le
  let hs : ℕ → A → B := fun j x => rt (g' (j + a) (es x))
  refine ⟨W, hW, hCW, hWU, hs, ?_, ?_, ?_, ?_⟩
  · -- smoothness on `W`
    intro j x hx
    have hz : g' (j + a) (es x) ∈ Vt := hδV (hcap j (es x) (subset_closure hx.2))
    have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) J ∞ rt (g' (j + a) (es x)) :=
      (hrt _ hz).contMDiffAt (hVt.mem_nhds hz)
    exact (h1.comp x ((hg'sm (j + a)).contMDiff.contMDiffAt.comp x
      hes.contMDiffAt)).contMDiffWithinAt
  · -- the marked point
    intro j
    change rt (g' (j + a) (es x₀)) = h x₀
    rw [hg'x₀]
    exact hfixW x₀ (hCW hx₀)
  · -- uniform convergence on `W`
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hcomp : IsCompact (Metric.cthickening δ (G '' closure O2)) := hKt.cthickening
    have huc : UniformContinuousOn rt (Metric.cthickening δ (G '' closure O2)) :=
      hcomp.uniformContinuousOn_of_continuous (hrt.continuousOn.mono hδV)
    obtain ⟨η, hη, hηε⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
    obtain ⟨b, hb⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hunif η hη)
    rw [eventually_atTop]
    refine ⟨b, fun j hj x hx => ?_⟩
    have hxz : es x ∈ closure O2 := subset_closure hx.2
    rw [← hfixW x hx]
    exact hηε _ (Metric.self_subset_cthickening _ (mem_image_of_mem G hxz)) _ (hcap j _ hxz)
      (hb (j + a) (hj.trans (Nat.le_add_right j a)) (es x))
  · -- chartwise `C^k` convergence
    intro p q K hK hKW hKm
    let Up : Set E := (extChartAt I p).target ∩
      (extChartAt I p).symm ⁻¹' (W ∩ h ⁻¹' (extChartAt J q).source)
    have hWq : IsOpen (W ∩ h ⁻¹' (extChartAt J q).source) :=
      (hh.continuousOn.mono hWU).isOpen_inter_preimage hW (isOpen_extChartAt_source q)
    have hUp : IsOpen Up := (continuousOn_extChartAt_symm p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) hWq
    have hKUp : K ⊆ Up := fun y hy => ⟨(hKW hy).1, (hKW hy).2, hKm hy⟩
    let Wt : Set (EuclideanSpace ℝ (Fin m)) := Vt ∩ rt ⁻¹' (extChartAt J q).source
    have hWt : IsOpen Wt :=
      hrt.continuousOn.isOpen_inter_preimage hVt (isOpen_extChartAt_source q)
    let T : E → EuclideanSpace ℝ (Fin n) := fun y => es ((extChartAt I p).symm y)
    let inner : E → EuclideanSpace ℝ (Fin m) := fun y => G (T y)
    let approx : ℕ → E → EuclideanSpace ℝ (Fin m) := fun j y => g' (j + a) (T y)
    let outer : EuclideanSpace ℝ (Fin m) → E' := fun z => extChartAt J q (rt z)
    have houter : ContDiffOn ℝ ∞ outer Wt := by
      apply contMDiffOn_iff_contDiffOn.mp
      apply (contMDiffOn_extChartAt (x := q)).comp (hrt.mono inter_subset_left)
      intro z hz
      simpa only [extChartAt_source] using hz.2
    have hT : ContDiffOn ℝ ∞ T (extChartAt I p).target :=
      contMDiffOn_iff_contDiffOn.mp (hes.comp_contMDiffOn (contMDiffOn_extChartAt_symm p))
    have hTk : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) T (extChartAt I p).target :=
      hT.of_le (by exact_mod_cast le_top)
    have hinner : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) inner (extChartAt I p).target :=
      hG.comp_contDiffOn hTk
    have happ (j : ℕ) : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) (approx j)
        (extChartAt I p).target :=
      (hg'k (j + a)).comp_contDiffOn hTk
    have hmap : MapsTo inner Up Wt := by
      intro y hy
      have hx : (extChartAt I p).symm y ∈ W := hy.2.1
      refine ⟨hGVt _ (subset_closure hx.2), ?_⟩
      change rt (G (es ((extChartAt I p).symm y))) ∈ (extChartAt J q).source
      rw [hfixW _ hx]
      exact hy.2.2
    have hshift : StrictMono (fun j : ℕ => j + a) := fun j l hjl => Nat.add_lt_add_right hjl a
    have hconv' : ∀ L : Set E, IsCompact L → L ⊆ Up → MapCPConvergenceOn L k approx inner := by
      intro L hL hLU
      have h1 := MapCPConvergenceOn.comp_contDiffOn_right (isOpen_extChartAt_target p)
        isOpen_univ hL (hLU.trans inter_subset_left) hTk (mapsTo_univ _ _)
        (hg'G.mono_set (subset_univ _)) (fun j => (hg'k j).contDiffOn) hG.contDiffOn
      exact h1.comp_subseq hshift
    have hcapture : ∀ᶠ j in atTop, MapsTo (approx j) K Wt :=
      TendstoUniformlyOn.eventually_mapsTo_of_isCompact
        (tendstoUniformlyOn_of_cPConvergence ((hconv' K hK hKUp).mono_order (Nat.zero_le k)))
        hK (hinner.continuousOn.mono (hKUp.trans inter_subset_left)) hWt (hmap.mono_left hKUp)
    have hcompose : MapCPConvergenceOn K k (fun j y => outer (approx j y))
        (fun y => outer (inner y)) :=
      mapCPConvergenceOn_comp_of_eventually_contDiffOn hUp hWt hconv'
        (fun S _ _ => MapCPConvergenceOn.const_seq outer)
        (fun L _ hLU => Eventually.of_forall fun j => (happ j).mono (hLU.trans inter_subset_left))
        (hinner.mono inter_subset_left)
        (fun S _ hSW => Eventually.of_forall fun _ =>
          (houter.of_le (by exact_mod_cast le_top)).mono hSW)
        (houter.of_le (by exact_mod_cast le_top)) hmap hK hKUp
    constructor
    · filter_upwards [hcapture] with j hj
      intro y hy
      exact (hj hy).2
    · refine hcompose.congr_eventually hUp hKUp (Eventually.of_forall fun j y _ => rfl) ?_
      intro y hy
      change extChartAt J q (h ((extChartAt I p).symm y)) =
        extChartAt J q (rt (G (es ((extChartAt I p).symm y))))
      rw [hfixW _ hy.2.1]

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
