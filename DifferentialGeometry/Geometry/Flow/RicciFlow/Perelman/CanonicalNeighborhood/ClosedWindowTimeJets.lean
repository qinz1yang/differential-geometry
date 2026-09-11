import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabChartBootstrap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialJetTimeContinuity
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.UniformSpace.HeineCantor


set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem derivWithin_time_eq_fderivWithin
    {f : ℝ × E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hf : ContDiffOn ℝ ∞ f (J ×ˢ V))
    {t : ℝ} (ht : t ∈ J) {x : E} (hx : x ∈ V) :
    derivWithin (fun s => f (s, x)) J t =
      fderivWithin ℝ f (J ×ˢ V) (t, x) (1, 0) := by
  have hd := (hf.differentiableOn (by simp) (t, x) ⟨ht, hx⟩).hasFDerivWithinAt
  have hparam : HasDerivWithinAt (fun s : ℝ => (s, x)) (1, 0) J t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have hmaps : MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ V) := fun _ hs => ⟨hs, hx⟩
  exact (hd.comp_hasDerivWithinAt t hparam hmaps).derivWithin (hJ t ht)


theorem contDiffOn_iteratedDerivWithin_time
    {f : ℝ × E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ V)) (k : ℕ) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => iteratedDerivWithin k (fun s => f (s, q.2)) J q.1)
      (J ×ˢ V) := by
  induction k with
  | zero => simpa only [iteratedDerivWithin_zero] using hf
  | succ k hk =>
    have hd := (hk.fderivWithin (hJ.prod hV.uniqueDiffOn) (m := ∞) (by simp)).clm_apply
      (contDiffOn_const (c := (1, (0 : E))))
    apply hd.congr
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [iteratedDerivWithin_succ]
    exact derivWithin_time_eq_fderivWithin hJ hk ht hx


theorem hasDerivWithinAt_iteratedDerivWithin_time
    {f : ℝ × E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ V)) (k : ℕ)
    {t : ℝ} (ht : t ∈ J) {x : E} (hx : x ∈ V) :
    HasDerivWithinAt (iteratedDerivWithin k (fun s => f (s, x)) J)
      (iteratedDerivWithin (k + 1) (fun s => f (s, x)) J t) J t := by
  have hk := contDiffOn_iteratedDerivWithin_time hJ hV hf k
  have hd := (hk.differentiableOn (by simp) (t, x) ⟨ht, hx⟩).hasFDerivWithinAt
  have hparam : HasDerivWithinAt (fun s : ℝ => (s, x)) (1, 0) J t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have hmaps : MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ V) := fun _ hs => ⟨hs, hx⟩
  have h := hd.comp_hasDerivWithinAt t hparam hmaps
  have heq := derivWithin_time_eq_fderivWithin hJ hk ht hx
  rw [iteratedDerivWithin_succ]
  exact h.congr_deriv heq.symm

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem tendstoUniformlyOn_of_joint_continuous
    {P : Type*} [TopologicalSpace P] {f : P → E → F}
    {J : Set P} {K : Set E} (hK : IsCompact K)
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ K)) {p : P} (hp : p ∈ J) :
    TendstoUniformlyOn f (f p) (𝓝[J] p) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  obtain ⟨V, hV, hsmall⟩ := hK.mem_uniformity_of_prod hf hp (Metric.dist_mem_uniformity heps)
  filter_upwards [hV] with q hq
  intro x hx
  have hh : dist (f q x) (f p x) < eps := hsmall q hq x hx
  simpa only [dist_comm] using hh


theorem mapCInf_of_joint_smooth_on_closed
    {G : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V))
    (tau : ℕ → ℝ) (htau : ∀ n, tau n ∈ J) {t : ℝ} (ht : t ∈ J)
    (htend : Tendsto tau atTop (𝓝 t)) :
    DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
      (fun n => G (tau n)) (G t) := by
  intro K hK hKV m
  have hf (s : ℝ) (hs : s ∈ J) : ContDiffOn ℝ ∞ (G s) V :=
    hG.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨hs, hy⟩)
  have hm : (m : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  apply DifferentialGeometry.CheegerGromovCompactness.mapCPConvergenceOn_of_tendstoUniformlyOn hV hKV
    (fun n => (hf (tau n) (htau n)).of_le hm)
    ((hf t ht).of_le hm)
  intro r _hr
  let : NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    ContinuousMultilinearMap.normedAddCommGroup
  let : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    ContinuousMultilinearMap.normedSpace
  have hjoint := (KappaSolutions.spatial_iteratedFDeriv_contDiffOn
    (G := G) hJ hV hG r).continuousOn
  have hu := tendstoUniformlyOn_of_joint_continuous hK
    (hjoint.mono (Set.prod_mono Subset.rfl hKV)) ht
  exact hu.seq_tendstoUniformlyOn tau
    (tendsto_nhdsWithin_iff.mpr ⟨htend, Filter.Eventually.of_forall htau⟩)

end Calculus

open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
  [BoundarylessManifold I M]


theorem solution_chartGram_timeJets_contDiffOn_closed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) (p : M) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      ∀ k : ℕ, ∀ i j : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun q : ℝ × E => iteratedDerivWithin k
          (fun s => chartGramOnE (I := I) (S.base.metric s) p i j q.2) (Icc c b) q.1)
          (Icc c b ×ˢ V) := by
  obtain ⟨V, hV, hpV, hVt, hgram⟩ :=
    solution_chartGram_contDiffOn_closed S hS hac hcb hslab hreg p
  exact ⟨V, hV, hpV, hVt, fun k i j =>
    contDiffOn_iteratedDerivWithin_time (uniqueDiffOn_Icc hcb) hV (hgram i j) k⟩


theorem solution_chartGram_mixedJets_contDiffOn_closed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) (p : M) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      ∀ r k : ℕ, ∀ i j : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun q : ℝ × E => iteratedFDeriv ℝ r
          (fun y => iteratedDerivWithin k
            (fun s => chartGramOnE (I := I) (S.base.metric s) p i j y) (Icc c b) q.1) q.2)
          (Icc c b ×ˢ V) := by
  obtain ⟨V, hV, hpV, hVt, hjets⟩ :=
    solution_chartGram_timeJets_contDiffOn_closed S hS hac hcb hslab hreg p
  exact ⟨V, hV, hpV, hVt, fun r k i j =>
    KappaSolutions.spatial_iteratedFDeriv_contDiffOn
      (G := fun s y => iteratedDerivWithin k
        (fun u => chartGramOnE (I := I) (S.base.metric u) p i j y) (Icc c b) s)
      (uniqueDiffOn_Icc hcb) hV (hjets k i j) r⟩


theorem solution_chartGram_timeJets_mapCInf_of_time_sequence
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) (p : M) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      ∀ tau : ℕ → ℝ, (∀ n, tau n ∈ Icc c b) → ∀ t ∈ Icc c b,
        Tendsto tau atTop (𝓝 t) → ∀ k : ℕ, ∀ i j : Fin (Module.finrank ℝ E),
          DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
            (fun n y => iteratedDerivWithin k
              (fun s => chartGramOnE (I := I) (S.base.metric s) p i j y) (Icc c b) (tau n))
            (fun y => iteratedDerivWithin k
              (fun s => chartGramOnE (I := I) (S.base.metric s) p i j y) (Icc c b) t) := by
  obtain ⟨V, hV, hpV, hVt, htime⟩ :=
    solution_chartGram_timeJets_contDiffOn_closed S hS hac hcb hslab hreg p
  refine ⟨V, hV, hpV, hVt, ?_⟩
  intro tau htau t ht htend k i j
  exact mapCInf_of_joint_smooth_on_closed
    (G := fun s y => iteratedDerivWithin k
      (fun u => chartGramOnE (I := I) (S.base.metric u) p i j y) (Icc c b) s)
    (uniqueDiffOn_Icc hcb) hV (htime k i j) tau htau ht htend

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
