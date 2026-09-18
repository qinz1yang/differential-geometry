import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabJetBootstrap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalJointSpatialJets
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local instance slabChartBootstrapC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
local instance slabChartBootstrapC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [CompleteSpace E] [T2Space M] in
private theorem chartGramPi_jets_continuousOn
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {J : Set ℝ} {V : Set E}
    (hVt : V ⊆ (extChartAt I p).target) (r : ℕ)
    (hjets : ∀ i j : Fin (Module.finrank ℝ E), ContinuousOn
      (fun q : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (I := I) (g q.1) p i j) q.2)
      (J ×ˢ V)) :
    ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ r
      (chartGramPi (I := I) (g q.1) p) q.2) (J ×ˢ V) := by
  let L₁ : (∀ _ : Fin (Module.finrank ℝ E), E [×r]→L[ℝ] ℝ) ≃ₗᵢ[ℝ]
      E [×r]→L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    ContinuousMultilinearMap.piₗᵢ _ _
  let L₂ : (∀ _ : Fin (Module.finrank ℝ E),
      E [×r]→L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)) ≃ₗᵢ[ℝ]
      E [×r]→L[ℝ] (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
    ContinuousMultilinearMap.piₗᵢ _ _
  have hrows : ContinuousOn (fun q i => L₁ (fun j => iteratedFDeriv ℝ r
      (chartGramOnE (I := I) (g q.1) p i j) q.2)) (J ×ˢ V) := by
    exact continuousOn_pi.mpr fun i => L₁.continuous.comp_continuousOn
      (continuousOn_pi.mpr fun j => hjets i j)
  have hmatrix := L₂.continuous.comp_continuousOn hrows
  refine hmatrix.congr fun q hq => ?_
  have hentryCD (i j : Fin (Module.finrank ℝ E)) : ContDiffAt ℝ (r : WithTop ℕ∞)
      (chartGramOnE (I := I) (g q.1) p i j) q.2 :=
    ((chartGramOnE_contDiffOn (I := I) (g q.1) p i j).contDiffAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds (hVt hq.2))).of_le
        (by exact_mod_cast le_top)
  have hrowCD (i : Fin (Module.finrank ℝ E)) : ContDiffAt ℝ (r : WithTop ℕ∞)
      (fun z j => chartGramOnE (I := I) (g q.1) p i j z) q.2 :=
    contDiffAt_pi' fun j => hentryCD i j
  rw [show chartGramPi (I := I) (g q.1) p =
      (fun z i j => chartGramOnE (I := I) (g q.1) p i j z) from rfl,
    iteratedFDeriv_pi hrowCD le_rfl]
  simp only [L₁, L₂, ContinuousMultilinearMap.piₗᵢ_apply]
  apply congrArg ContinuousMultilinearMap.pi
  funext i
  exact iteratedFDeriv_pi (fun j => hentryCD i j) le_rfl

omit [CompleteSpace E] in
theorem chartGram_contDiffOn_of_spatialJets
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {a b : ℝ} {V : Set E}
    (hab : a < b) (hV : IsOpen V) (hVt : V ⊆ (extChartAt I p).target)
    (hjets : ∀ r : ℕ, ∀ i j : Fin (Module.finrank ℝ E), ContinuousOn
      (fun q : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (I := I) (g q.1) p i j) q.2)
      (Icc a b ×ˢ V))
    (hpde : ∀ t ∈ Ioo a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (I := I) (g t) x v w) t) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => chartGramPi (I := I) (g q.1) p q.2)
      (Icc a b ×ˢ V) := by
  let G : ℝ → E → (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
    fun t => chartGramPi (I := I) (g t) p
  let Ω : Set (MatJet E (Module.finrank ℝ E)) := {z | (Matrix.of z.1).det ≠ 0}
  have hstatic (t : ℝ) : ContDiffOn ℝ ∞ (G t) V :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j =>
      (chartGramOnE_contDiffOn (I := I) (g t) p i j).mono hVt
  have hdet : Continuous (fun z : MatJet E (Module.finrank ℝ E) => (Matrix.of z.1).det) :=
    (contDiff_det_of_entries (fun z : MatJet E (Module.finrank ℝ E) => Matrix.of z.1)
      (fun i j => contDiff_jetVal i j)).continuous
  have hΩ : IsOpen Ω := by
    simpa only [Ω, Set.mem_ofPred_eq] using
      (isOpen_ne_fun hdet (continuous_const : Continuous
        (fun _ : MatJet E (Module.finrank ℝ E) => (0 : ℝ))))
  have hΦ : ContDiffOn ℝ ∞ (jetRicciFlow (chartModelBasis E)) Ω :=
    fun z hz => (contDiffAt_jetRicciFlow (chartModelBasis E) hz).contDiffWithinAt
  have hmap : MapsTo (fun q : ℝ × E => jet2 (G q.1) q.2) (Icc a b ×ˢ V) Ω := by
    rintro ⟨t, y⟩ ⟨_, hy⟩
    have hbase : (extChartAt I p).symm y ∈
        (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      have hs := (extChartAt I p).map_target (hVt hy)
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hs
    have heq : Matrix.of (jet2 (G t) y).1 =
        chartGramMatrix (I := I) (g t) p ((extChartAt I p).symm y) := by
      ext i j
      rfl
    change (Matrix.of (jet2 (G t) y).1).det ≠ 0
    rw [heq]
    exact (chartGramMatrix_det_pos (I := I) (g t) p hbase).ne'
  have htime : ∀ t ∈ Ioo a b, ∀ y ∈ V,
      HasDerivAt (fun s => G s y) (jetRicciFlow (chartModelBasis E) (jet2 (G t) y)) t := by
    intro t ht y hy
    have hyt := hVt hy
    have hyint : y ∈ interior (extChartAt I p).target :=
      (isOpen_extChartAt_target (I := I) p).interior_eq.symm ▸ hyt
    have hsrc := (extChartAt I p).map_target hyt
    have hxy := (extChartAt I p).right_inv hyt
    have hbase : (extChartAt I p).symm y ∈
        (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source_eq_chartAt_source (I := I)]
      exact hsrc
    have hgood : (extChartAt I p).symm y ∈ chartLeviCivitaGoodSet (I := I) p :=
      mem_chartLeviCivitaGoodSet_iff.mpr ⟨hsrc, hbase, by simpa only [hxy] using hyint⟩
    have hAt := (hstatic t).contDiffAt (hV.mem_nhds hy)
    have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (G t) z := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact ((hstatic t).contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)
    have hG2 : DifferentiableAt ℝ (fun z => fderiv ℝ (G t) z) y :=
      (hAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
    have hmetric := hpde t ht ((extChartAt I p).symm y)
      (chartBasisVecFiber (I := I) p i ((extChartAt I p).symm y))
      (chartBasisVecFiber (I := I) p j ((extChartAt I p).symm y))
    have hentry := chartGramEntryPDE_of_metricPDE (I := I) g p hgood hxy i j
      (sL := Ioo a b) hmetric.hasDerivWithinAt
    have hflow := jetRicciFlow_chartGram (I := I) (g t) p hyint
      (hAt.differentiableAt (by simp)) hG1 hG2 i j
    exact (hentry.hasDerivAt (isOpen_Ioo.mem_nhds ht)).congr_deriv hflow.symm
  exact contDiffOn_of_closed_jet_pde hab hV hΩ (fun t _ => hstatic t) hΦ hmap
    (fun r => chartGramPi_jets_continuousOn g p hVt r (hjets r)) htime

theorem solution_metricCLMSection_contMDiffOn_closed
    [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.base.metric p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc c b ×ˢ (Set.univ : Set M)) := by
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on (I := I) S.base.metric (Icc c b)
  intro x i j
  have hjets := solution_chartGram_jets_continuousOn_closed S hS hac hcb hslab hreg x
  have hmetric : ∀ t ∈ Ioo c b, ∀ y : M, ∀ v w : TangentSpace I y,
      HasDerivAt (fun s => (S.base.metric s).inner y v w)
        (-2 * ricciTensor (I := I) (S.base.metric t) y v w) t := by
    intro t ht y v w
    have hd := metricDerivAt S hS ⟨t, hreg ⟨hac.trans ht.1, ht.2⟩⟩ y v w
    have hr := metricRicciAt_apply_eq_ricciTensor (I := I) (S.base.metric t) y v w
    dsimp only [SolutionOn.ricciAt, SolutionFamily.ricciAt] at hd
    erw [hr] at hd
    exact hd
  have hG := chartGram_contDiffOn_of_spatialJets S.base.metric x hcb
    (isOpen_extChartAt_target x) Subset.rfl hjets hmetric
  have hentry := contDiffOn_pi.mp (contDiffOn_pi.mp hG i) j
  have hsource {y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
      y ∈ (extChartAt I x).source := by
    rwa [extChartAt_source_eq_chartAt_source, ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
  have harg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : ℝ × M => (p.1, extChartAt I x p.2))
      (Icc c b ×ˢ (trivializationAt E (TangentSpace I) x).baseSet) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffOn_fst.prodMk ((contMDiffOn_extChartAt (I := I) (x := x)).comp contMDiffOn_snd
      (fun p hp => by
        simpa only [Set.mem_preimage, trivializationAt_baseSet_eq_chartAt_source] using hp.2))
  have hh := hentry.contMDiffOn.comp harg (fun p hp => ⟨hp.1,
    (extChartAt I x).map_source (hsource hp.2)⟩)
  apply hh.congr
  intro p hp
  change chartGramMatrix (S.base.metric p.1) x p.2 i j =
    chartGramMatrix (S.base.metric p.1) x ((extChartAt I x).symm (extChartAt I x p.2)) i j
  rw [(extChartAt I x).left_inv (hsource hp.2)]


theorem solution_chartGram_contDiffOn_closed
    [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) (p : M) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I p p ∈ W ∧ W ⊆ (extChartAt I p).target ∧
      ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
        (fun q : ℝ × E => chartGramOnE (I := I) (S.base.metric q.1) p i j q.2)
        (Icc c b ×ˢ W) := by
  refine ⟨(extChartAt I p).target, isOpen_extChartAt_target p,
    (extChartAt I p).map_source (mem_extChartAt_source p), Subset.rfl, ?_⟩
  exact fun i j => chartGramOnE_joint_contDiffOn S.base.metric (Icc c b)
    (solution_metricCLMSection_contMDiffOn_closed S hS hac hcb hslab hreg) p i j

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
