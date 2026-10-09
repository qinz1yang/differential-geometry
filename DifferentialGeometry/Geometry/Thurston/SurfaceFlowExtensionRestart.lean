import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Time
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.FiniteGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Compact
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness

/-!
# Restarting a flow from a smooth endpoint family

Chapter 7, surface lemma U1, route (a), step a1 (lane U1E2), tier T4 of route E2 (review 17 §3.2).
Dimension free. Let `S` be a Ricci flow on `[0, Tm)` on a closed manifold and `k` a family of
metrics, jointly smooth on `(0, Tm + ε) × M`, equal to the flow on `[0, Tm)`. The family `k` is
not claimed to be a Ricci flow after `Tm`.

* `extendsPastEndpoint_of_smooth_endpoint_family`: `S` extends past `Tm`. A short-time flow
  `r` is started at `k Tm` (`exists_completeBoundedCurvatureSolutionOn_of_compact`); the pieces
  `k` on `[Tm/3, Tm]` and `r (· - Tm)` on `[Tm, Tm + c]` (`c` below the lifetime of `r`)
  are glued by `exists_isSolutionOn_finite_gluing` (joint smoothness on the closed pieces, the
  equation inside, `k Tm = r 0`); the glued flow, started at `Tm/2`, agrees with `S` on
  `[Tm/2, Tm)` and is joined to `S` by `extend_construction_of_restart`, and
  `isSolutionOn_of_metric_extension` gives the solution property. No uniqueness theorem is used.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open Bundle Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

theorem extendsPastEndpoint_of_smooth_endpoint_family {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) {ε : ℝ} (hε : 0 < ε) (k : ℝ → SmoothRiemannianMetric I M)
    (hk : ∀ t ∈ Ico 0 Tm, k t = S.family.metric t)
    (hksmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (k p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ioo 0 (Tm + ε) ×ˢ (univ : Set M))) :
    ExtendsPastEndpoint (I := I) hTm S := by
  obtain ⟨d, hd, Q, hQ0, -, hQjoint, hQpde⟩ :=
    exists_completeBoundedCurvatureSolutionOn_of_compact (I := I) (M := M) (k Tm)
  set r := Q.solution.base.metric with hr
  set c : ℝ := min (d / 2) ε with hc
  have hc0 : 0 < c := lt_min (by linarith) hε
  have hcd : c < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hcε : c ≤ ε := min_le_right _ _
  let time : Fin 3 → ℝ := ![Tm / 3, Tm, Tm + c]
  have htime : StrictMono time := by
    refine Fin.strictMono_iff_lt_succ.mpr (fun i => ?_)
    fin_cases i
    · change Tm / 3 < Tm
      linarith
    · change Tm < Tm + c
      linarith
  let g : Fin 2 → ℝ → SmoothRiemannianMetric I M := ![k, fun t => r (t - Tm)]
  have hsmooth : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (g i q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc (time i.castSucc) (time i.succ) ×ˢ (univ : Set M)) := by
    intro i
    fin_cases i
    · refine hksmooth.mono (prod_mono (fun t ht => ⟨?_, ?_⟩) subset_rfl)
      · have : Tm / 3 ≤ t := ht.1
        linarith
      · have : t ≤ Tm := ht.2
        linarith
    · have hshift : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
          (fun p : ℝ × M => ((p.1 - Tm, p.2) : ℝ × M)) :=
        (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
      refine hQjoint.comp hshift.contMDiffOn (fun q hq => ⟨⟨?_, ?_⟩, mem_univ _⟩)
      · have : Tm ≤ q.1 := hq.1.1
        linarith
      · have : q.1 ≤ Tm + c := hq.1.2
        linarith
  have hleft := ricciFlowPDE_Ici_of_solution (I := I) hS
  have hpde : ∀ i, ∀ t ∈ Ioo (time i.castSucc) (time i.succ),
      ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (g i s).inner x v w)
        (-2 * ricciTensor (I := I) (g i t) x v w) t := by
    intro i
    fin_cases i
    · intro t ht x v w
      have ht1 : Tm / 3 < t := ht.1
      have ht2 : t < Tm := ht.2
      have ht0 : 0 < t := by linarith
      have h := (hleft t ⟨ht0.le, ht2⟩ x v w).hasDerivAt (Ici_mem_nhds ht0)
      change HasDerivAt (fun s => (k s).inner x v w) (-2 * ricciTensor (I := I) (k t) x v w) t
      rw [hk t ⟨ht0.le, ht2⟩]
      refine h.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht0 ht2] with s hs
      rw [hk s ⟨hs.1.le, hs.2⟩]
      rfl
    · intro t ht x v w
      have ht1 : Tm < t := ht.1
      have ht2 : t < Tm + c := ht.2
      have hpos : 0 < t - Tm := by linarith
      have h := (hQpde (t - Tm) ⟨hpos.le, by linarith⟩ x v w).hasDerivAt (Ici_mem_nhds hpos)
      exact h.comp_sub_const t Tm
  have hmatch : ∀ i : Fin 1, g i.castSucc (time i.succ.castSucc) =
      g i.succ (time i.succ.castSucc) := by
    intro i
    fin_cases i
    change k Tm = r (Tm - Tm)
    rw [sub_self]
    exact hQ0.symm
  obtain ⟨G, hGeq, hGsmooth, hGsol⟩ :=
    exists_isSolutionOn_finite_gluing 1 time htime g hsmooth hpde hmatch
  have hGpde : ∀ t ∈ Ioo (Tm / 3) (Tm + c), ∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s => (G s).inner x v w) (-2 * ricciTensor (I := I) (G t) x v w) t := by
    intro t ht x v w
    have h := metricDerivAt (I := I) _ hGsol ⟨t, ht⟩ x v w
    rwa [show ((⟨t, ht⟩ : RealTimeInterval.RegularTime _) : ℝ) = t from rfl,
      SolutionOn.ricciAt, SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor] at h
  have hGgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Tensor.Coordinates.chartGramMatrix (I := I) (G p.1) x₀ p.2 i j)
        (Icc (Tm / 3) (Tm + c) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => chartGramMatrix_joint_contMDiffOn_of_pullback G _ hGsmooth G id contMDiff_id
      (fun t _ x u v => by rw [mfderiv_id]; rfl) x₀ i j
  set TT : ℝ := Tm + c - Tm / 2 with hTT
  let rr : ℝ → SmoothRiemannianMetric I M := fun u => G (Tm / 2 + u)
  have hshift : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => ((Tm / 2 + p.1, p.2) : ℝ × M)) :=
    (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
  have hrr_gram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Tensor.Coordinates.chartGramMatrix (I := I) (rr p.1) x₀ p.2 i j)
        (Ico 0 TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    refine (hGgram x₀ i j).comp hshift.contMDiffOn (fun q hq => ⟨⟨?_, ?_⟩, hq.2⟩)
    · have : 0 ≤ q.1 := hq.1.1
      change Tm / 3 ≤ Tm / 2 + q.1
      linarith
    · have : q.1 < TT := hq.1.2
      change Tm / 2 + q.1 ≤ Tm + c
      linarith
  have hrr_pde : ∀ t ∈ Ico (0 : ℝ) TT, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun u : ℝ => (rr u).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (rr t) x v w) (Ici 0) t := by
    intro t ht x v w
    have ht1 : 0 ≤ t := ht.1
    have ht2 : t < TT := ht.2
    exact ((hGpde (Tm / 2 + t) ⟨by linarith, by linarith⟩ x v w).comp_const_add
      (Tm / 2) t).hasDerivWithinAt
  have hagree_overlap : ∀ s ∈ Ico (Tm / 2) Tm, rr (s - Tm / 2) = S.base.metric s := by
    intro s hs
    have hs1 : Tm / 2 ≤ s := hs.1
    have hs2 : s < Tm := hs.2
    change G (Tm / 2 + (s - Tm / 2)) = S.base.metric s
    rw [add_sub_cancel, hGeq 0 s ⟨by change Tm / 3 ≤ s; linarith, hs2.le⟩]
    exact hk s ⟨by linarith, hs2⟩
  obtain ⟨ε₁, hε₁, g_ext, hagree, hsmooth_ext, hcont_ext, hpde_ext⟩ :=
    extend_construction_of_restart (I := I) S.base.metric hleft
      (fun x₀ i j => chartGram_smooth_of_solution (I := I) hS x₀ i j)
      (fun x₀ i j => chartGram_cont_of_solution (I := I) hS x₀ i j)
      (t_star := Tm / 2) (TT := TT) (by linarith) (by linarith) (by linarith) rr
      (fun x₀ i j => (hrr_gram x₀ i j).mono (prod_mono Ioo_subset_Ico_self subset_rfl))
      (fun x₀ i j => (hrr_gram x₀ i j).continuousOn) hrr_pde hagree_overlap
  have hwide : 0 < Tm + ε₁ := by linarith
  let Shat : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 (Tm + ε₁) hwide) :=
    { base := { metric := g_ext } }
  refine ⟨ε₁, hε₁, hwide, Shat, ?_, ?_⟩
  · exact isSolutionOn_of_metric_extension hwide hTm g_ext S hS hagree hsmooth_ext hcont_ext
      hpde_ext
  · intro t ht
    have hteq : g_ext t = S.base.metric t := hagree t ht.2
    refine ⟨?_, ?_, ?_⟩
    · change S.base.metric t = g_ext t
      exact hteq.symm
    · change S.base.connection t = (SolutionFamily.connection { metric := g_ext }) t
      simp only [SolutionFamily.connection]
      congr 1
      exact hteq.symm
    · change S.base.ricci t = SolutionFamily.ricci { metric := g_ext } t
      simp only [SolutionFamily.ricci]
      congr 1
      exact hteq.symm

end GC.Geometry
