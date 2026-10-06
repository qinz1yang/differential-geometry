import DifferentialGeometry.Geometry.HarmonicMap.MinimalGraphDifference
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientGraphHessian
import DifferentialGeometry.Analysis.Elliptic.Planar.PowerPullback
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval

namespace DifferentialGeometry.Geometry

/-- The two original graph germs give a punctured equation for the literal
root-height difference. All coefficient fields are defined from the same root
height before the two germs are used; no equation is an input. -/
theorem chartLeadingPlaneProjection_root_pair_height_difference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    (htension : ∀ z ∈ s, diskMapTension g U z = 0)
    {a : ℂ} {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (N : E)
    (hunit : chartGramBilin g p (U a) N N = 1)
    (hprojN : chartLeadingPlaneProjection g p (U a) b N = 0)
    (hsplit : ∀ v : E,
      v = (chartModelBasis E).equivFunL.symm
          (fun i => (2 : ℝ) *
            (chartLeadingPlaneProjection g p (U a) b v * b i).re) +
        (chartGramBilin g p (U a) N v) • N)
    (L : ℂ →L[ℝ] E)
    (hL : ∀ v, L v = (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (v * b i).re))
    {m : ℕ} (hm : 1 ≤ m)
    (eRoot e₁ e₂ : OpenPartialHomeomorph ℂ ℂ)
    (he₁source : e₁.source ⊆ s) (he₂source : e₂.source ⊆ s)
    (he₁ : (e₁ : ℂ → ℂ) = fun z => chartLeadingPlaneProjection g p (U a) b
      (extChartAt 𝓘(ℝ, E) p (U z)))
    (he₂ : (e₂ : ℂ → ℂ) = fun z => chartLeadingPlaneProjection g p (U a) b
      (extChartAt 𝓘(ℝ, E) p (U z)))
    (he₁inverse : ContDiffOn ℝ ∞ e₁.symm e₁.target)
    (he₂inverse : ContDiffOn ℝ ∞ e₂.symm e₂.target)
    (hpower : ∀ v ∈ eRoot.target,
      chartLeadingPlaneProjection g p (U a) b (extChartAt 𝓘(ℝ, E) p (U (eRoot.symm v))) =
        chartLeadingPlaneProjection g p (U a) b (extChartAt 𝓘(ℝ, E) p (U a)) +
          v ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) :
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => chartLeadingPlaneProjection g p (U a) b (X z)
    let c := F a
    let H : ℂ → ℝ := fun v => chartGramBilin g p (U a) N (X (eRoot.symm v) - X a)
    let Q := chartGramBilin g p (U a)
    let proj := chartLeadingPlaneProjection g p (U a) b
    let dirs : Fin 2 → ℂ := ![1, Complex.I]
    let Y : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) → E := fun q =>
      extChartAt 𝓘(ℝ, E) p (U a) + L (q.1.1 - c) + q.1.2 • N
    let V : (ℂ →L[ℝ] ℝ) → Fin 2 → E := fun l i => L (dirs i) + l (dirs i) • N
    let G : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q i j =>
      chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y q)) (V q.2 i) (V q.2 j)
    let A : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q =>
      Analysis.planarConductivity (G q 0 0) (G q 1 1) (G q 0 1)
    let theta : (ℂ →L[ℝ] ℝ) → E →L[ℝ] ℝ := fun l => Q N - l.comp proj
    let Phi : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) → ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → ℝ :=
      fun T q => ∑ i : Fin 2, ∑ j : Fin 2,
        A q i j * (T (dirs i) (dirs j) +
          theta q.2 (chartChristoffelContraction g p (V q.2 i) (V q.2 j) (Y q)))
    let R : ℂ → (ℂ →L[ℝ] ℝ) := Analysis.complexPowerNormalizedGradient m H
    let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
    let T2 : ℂ → ℂ → (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := fun zeta w =>
      (fderiv ℝ R (zeta * w)).comp
        (ContinuousLinearMap.mul ℝ ℂ (((zeta * w) ^ m)⁻¹))
    let Jet : Type := ℝ × (ℂ →L[ℝ] ℝ)
    let J1 : ℂ → Jet := fun w => (H w, R w)
    let J2 : ℂ → ℂ → Jet := fun zeta w => (H (zeta * w), R (zeta * w))
    let J : ℂ → ℂ → ℝ → Jet := fun zeta w t => (1 - t) • J2 zeta w + t • J1 w
    let PhiRoot : ℂ → ℂ → Jet → ℝ := fun zeta w j =>
      Phi (T2 zeta w) ((P w, j.1), j.2)
    let duals : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]
    let betaRoot : ℂ → ℂ → Fin 2 → ℝ := fun zeta w i =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (PhiRoot zeta w) (J zeta w t) (0, duals i)
    let cRoot : ℂ → ℂ → ℝ := fun zeta w =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (PhiRoot zeta w) (J zeta w t) (1, 0)
    let A1 : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w => A ((P w, H w), R w)
    let K : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w => if w = 0 then 1 else
      Analysis.planarComplexMulMatrix ((w ^ m)⁻¹) * A1 w *
        Analysis.planarComplexMulMatrix (w ^ m)
    let bTilde : ℂ → ℂ → ℂ := fun zeta w =>
      star (w ^ m) * ((betaRoot zeta w 0 : ℂ) + (betaRoot zeta w 1 : ℂ) * Complex.I) -
        ((m : ℂ) / w) * Analysis.planarMatrixSpin (K w)
    let cTilde : ℂ → ℂ → ℝ := fun zeta w => ‖w ^ m‖ ^ 2 * cRoot zeta w
    let W : ℂ → ℂ → ℝ := fun zeta w => H w - H (zeta * w)
    ∀ zeta w : ℂ, zeta ^ (m + 1) = 1 → w ≠ 0 →
      w ∈ eRoot.target → zeta * w ∈ eRoot.target →
      eRoot.symm w ∈ e₁.source → eRoot.symm (zeta * w) ∈ e₂.source →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Y ((P w, (J zeta w t).1), (J zeta w t).2) ∈
          (extChartAt 𝓘(ℝ, E) p).target) →
      Analysis.planarScalarOperator K
        (fun v => ![(bTilde zeta v).re, (bTilde zeta v).im])
        (cTilde zeta) (W zeta) w = 0 := by
  classical
  intro X F c H Q proj dirs Y V G A theta Phi R P T2 Jet J1 J2 J PhiRoot duals
    betaRoot cRoot A1 K bTilde cTilde W zeta w hzeta hw0 hw hwz hw₁ hw₂ hphysical
  have hzeta0 : zeta ≠ 0 := by
    intro hz
    simp [hz] at hzeta
  have hwz0 : zeta * w ≠ 0 := mul_ne_zero hzeta0 hw0
  have hPz (v : ℂ) : P (zeta * v) = P v := by
    simp only [P, mul_pow, hzeta, one_mul]
  have hpower' (v : ℂ) (hv : v ∈ eRoot.target) : F (eRoot.symm v) = P v :=
    hpower v hv
  have hinverse (eg : OpenPartialHomeomorph ℂ ℂ) (heg : (eg : ℂ → ℂ) = F)
      (v : ℂ) (hv : v ∈ eRoot.target) (hvg : eRoot.symm v ∈ eg.source) :
      eg.symm (P v) = eRoot.symm v := by
    rw [← hpower' v hv, ← heg]
    exact eg.left_inv hvg
  have hinv₁ : e₁.symm (P w) = eRoot.symm w := hinverse e₁ he₁ w hw hw₁
  have hinv₂ : e₂.symm (P w) = eRoot.symm (zeta * w) := by
    rw [← hPz w]
    exact hinverse e₂ he₂ (zeta * w) hwz hw₂
  have hy₁ : P w ∈ e₁.target := by
    have hy := e₁.map_source hw₁
    have heval : e₁ (eRoot.symm w) = F (eRoot.symm w) := congrFun he₁ _
    rw [heval, hpower' w hw] at hy
    exact hy
  have hy₂ : P w ∈ e₂.target := by
    have hy := e₂.map_source hw₂
    have heval : e₂ (eRoot.symm (zeta * w)) = F (eRoot.symm (zeta * w)) :=
      congrFun he₂ _
    rw [heval, hpower' (zeta * w) hwz, hPz w] at hy
    exact hy
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart z hz)).comp z
      (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  let h₁ : ℂ → ℝ := fun y => Q N (X (e₁.symm y) - X a)
  let h₂ : ℂ → ℝ := fun y => Q N (X (e₂.symm y) - X a)
  let f : ℂ → ℝ := fun y => h₁ y - h₂ y
  have hXe₁ : ContDiffOn ℝ ∞ (fun y => X (e₁.symm y)) e₁.target :=
    hX.comp he₁inverse (fun y hy => he₁source (e₁.symm.map_source hy))
  have hXe₂ : ContDiffOn ℝ ∞ (fun y => X (e₂.symm y)) e₂.target :=
    hX.comp he₂inverse (fun y hy => he₂source (e₂.symm.map_source hy))
  have hh₁ : ContDiffOn ℝ ∞ h₁ e₁.target :=
    (Q N).contDiff.comp_contDiffOn (hXe₁.sub contDiffOn_const)
  have hh₂ : ContDiffOn ℝ ∞ h₂ e₂.target :=
    (Q N).contDiff.comp_contDiffOn (hXe₂.sub contDiffOn_const)
  have hheight₁ : h₁ (P w) = H w := by simp only [h₁, hinv₁]; rfl
  have hheight₂ : h₂ (P w) = H (zeta * w) := by simp only [h₂, hinv₂]; rfl
  have hgrad₁ : fderiv ℝ h₁ (P w) = R w := by
    rw [← hpower' w hw]
    exact chartLeadingPlaneProjection_graph_fderiv_eq_normalized_gradient
      g p U a b N m eRoot e₁ he₁ hpower hh₁ w hw hw0 hw₁
  have hgrad₂ : fderiv ℝ h₂ (P w) = R (zeta * w) := by
    rw [← hPz w, ← hpower' (zeta * w) hwz]
    exact chartLeadingPlaneProjection_graph_fderiv_eq_normalized_gradient
      g p U a b N m eRoot e₂ he₂ hpower hh₂ (zeta * w) hwz hwz0 hw₂
  have hsecond : fderiv ℝ (fderiv ℝ h₂) (P w) = T2 zeta w := by
    rw [← hPz w, ← hpower' (zeta * w) hwz]
    exact (chartLeadingPlaneProjection_graph_second_fderiv_eq_normalized_gradient
      g p U a b N m eRoot e₂ he₂ hpower hh₂ (zeta * w) hwz hwz0 hw₂).2.2.1
  have hposition (v : ℂ) (hv : v ∈ eRoot.target) :
      X (eRoot.symm v) = X a + L (P v - c) + H v • N := by
    have hsplitv := hsplit (X (eRoot.symm v) - X a)
    rw [← hL] at hsplitv
    have hprojv : proj (X (eRoot.symm v) - X a) = P v - c := by
      rw [map_sub]
      exact congrArg (fun z : ℂ => z - c) (hpower' v hv)
    change X (eRoot.symm v) - X a =
      L (proj (X (eRoot.symm v) - X a)) + H v • N at hsplitv
    rw [hprojv] at hsplitv
    calc
      X (eRoot.symm v) = X a + (X (eRoot.symm v) - X a) := by abel
      _ = X a + L (P v - c) + H v • N := by rw [hsplitv, add_assoc]
  have hsegment_at (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (1 - t) • X (e₂.symm (P w)) + t • X (e₁.symm (P w)) ∈
        (extChartAt 𝓘(ℝ, E) p).target := by
    have hYt : Y ((P w, (J zeta w t).1), (J zeta w t).2) =
        (1 - t) • X (e₂.symm (P w)) + t • X (e₁.symm (P w)) := by
      rw [hinv₁, hinv₂, hposition w hw, hposition (zeta * w) hwz, hPz w]
      let v := X a + L (P w - c)
      have hv : (1 - t) • v + t • v = v := by
        rw [← add_smul, sub_add_cancel, one_smul]
      change v + ((1 - t) * H (zeta * w) + t * H w) • N =
        (1 - t) • (v + H (zeta * w) • N) + t • (v + H w • N)
      calc
        _ = ((1 - t) • v + t • v) +
            (((1 - t) * H (zeta * w)) • N + (t * H w) • N) := by
          rw [hv, add_smul]
        _ = _ := by
          simp only [smul_add, smul_smul]
          abel
    exact hYt ▸ hphysical t ht
  have hnearsegment : ∀ᶠ y in 𝓝 (P w), ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • X (e₂.symm y) + t • X (e₁.symm y) ∈
        (extChartAt 𝓘(ℝ, E) p).target := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hc₁ : ContinuousAt (fun y => X (e₁.symm y)) (P w) :=
      (hXe₁.contDiffAt (e₁.open_target.mem_nhds hy₁)).continuousAt
    have hc₂ : ContinuousAt (fun y => X (e₂.symm y)) (P w) :=
      (hXe₂.contDiffAt (e₂.open_target.mem_nhds hy₂)).continuousAt
    have hjoint : ContinuousAt
        (fun z : ℂ × ℝ => (1 - z.2) • X (e₂.symm z.1) + z.2 • X (e₁.symm z.1))
        (P w, t) :=
      ((continuousAt_const.sub continuousAt_snd).smul
        (hc₂.comp_of_eq (show ContinuousAt (Prod.fst : ℂ × ℝ → ℂ) (P w, t) from
          continuousAt_fst) rfl)).add
        (continuousAt_snd.smul
          (hc₁.comp_of_eq (show ContinuousAt (Prod.fst : ℂ × ℝ → ℂ) (P w, t) from
            continuousAt_fst) rfl))
    exact hjoint ((isOpen_extChartAt_target p).mem_nhds (hsegment_at t ht))
  have hOevent : ∀ᶠ y in 𝓝 (P w), y ∈ e₁.target ∧ y ∈ e₂.target ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        (1 - t) • X (e₂.symm y) + t • X (e₁.symm y) ∈
          (extChartAt 𝓘(ℝ, E) p).target := by
    filter_upwards [e₁.open_target.mem_nhds hy₁, e₂.open_target.mem_nhds hy₂,
      hnearsegment] with y hy₁ hy₂ hy
    exact ⟨hy₁, hy₂, hy⟩
  obtain ⟨O, hOsub, hO, hyO⟩ := _root_.mem_nhds_iff.mp hOevent
  have hO₁ : O ⊆ e₁.target := fun y hy => (hOsub hy).1
  have hO₂ : O ⊆ e₂.target := fun y hy => (hOsub hy).2.1
  have hsegment : ∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • X (e₂.symm y) + t • X (e₁.symm y) ∈
        (extChartAt 𝓘(ℝ, E) p).target := fun y hy => (hOsub hy).2.2
  have hbase := chartLeadingPlaneProjection_two_graphs_height_difference
    g hs hU hconformal htension hchart N hunit hprojN hsplit
    e₁ e₂ he₁source he₂source he₁ he₂ he₁inverse he₂inverse hO hO₁ hO₂ hsegment
  simp only [← hL] at hbase
  obtain ⟨_, _, hf, _, _, _, _, _, hbase⟩ := hbase
  obtain ⟨_, _, _, _, _, _, _, _, hbase⟩ := hbase (P w) hyO
  let BaseJ : ℂ → ℝ → Jet := fun y t =>
    (1 - t) • (h₂ y, fderiv ℝ h₂ y) + t • (h₁ y, fderiv ℝ h₁ y)
  let BasePhi : ℂ → Jet → ℝ := fun y j =>
    Phi (fderiv ℝ (fderiv ℝ h₂) y) ((y, j.1), j.2)
  let BaseBeta : ℂ → Fin 2 → ℝ := fun y i =>
    ∫ t in (0 : ℝ)..1, fderiv ℝ (BasePhi y) (BaseJ y t) (0, duals i)
  let BaseC : ℂ → ℝ := fun y =>
    ∫ t in (0 : ℝ)..1, fderiv ℝ (BasePhi y) (BaseJ y t) (1, 0)
  change Analysis.planarScalarOperator
    (fun y => A ((y, h₁ y), fderiv ℝ h₁ y)) BaseBeta BaseC f (P w) = 0 at hbase
  have hBaseJ : BaseJ (P w) = J zeta w := by
    funext t
    simp only [BaseJ, hheight₁, hheight₂, hgrad₁, hgrad₂]
    rfl
  -- This is equality on EVERY jet, not just equality on the integration segment.
  have hBasePhi : BasePhi (P w) = PhiRoot zeta w := by
    funext j
    simp only [BasePhi, hsecond]
    rfl
  have hBaseBeta : BaseBeta (P w) = betaRoot zeta w := by
    funext i
    simp only [BaseBeta, hBasePhi, hBaseJ]
    rfl
  have hBaseC : BaseC (P w) = cRoot zeta w := by
    simp only [BaseC, hBasePhi, hBaseJ]
    rfl
  have hbaseglobal : Analysis.planarScalarOperator (fun _ => A1 w)
      (fun _ => betaRoot zeta w) (fun _ => cRoot zeta w) f (P w) = 0 := by
    simpa only [Analysis.planarScalarOperator, hheight₁, hgrad₁, hBaseBeta, hBaseC]
      using hbase
  let beta : ℂ := (betaRoot zeta w 0 : ℂ) + (betaRoot zeta w 1 : ℂ) * Complex.I
  have hbetavec : (![beta.re, beta.im] : Fin 2 → ℝ) = betaRoot zeta w := by
    funext i
    fin_cases i <;> simp [beta]
  have hKw : K w = Analysis.planarComplexMulMatrix ((w ^ m)⁻¹) * A1 w *
      Analysis.planarComplexMulMatrix (w ^ m) := by simp [K, hw0]
  have hfAt : ContDiffAt ℝ 2 f (P w) :=
    (hf.contDiffAt (hO.mem_nhds hyO)).of_le (by norm_num)
  have hpull := Analysis.planarScalarOperator_normalized_power_pullback hm c hw0
    (A1 w) beta (cRoot zeta w) hfAt
  dsimp only at hpull
  rw [← hKw] at hpull
  change Analysis.planarScalarOperator (fun _ => K w)
      (fun _ => ![(bTilde zeta w).re, (bTilde zeta w).im])
      (fun _ => cTilde zeta w) (fun z => f (P z)) w =
    ‖w ^ m‖ ^ 2 * Analysis.planarScalarOperator (fun _ => A1 w)
      (fun _ => ![beta.re, beta.im]) (fun _ => cRoot zeta w) f (P w) at hpull
  rw [hbetavec, hbaseglobal, mul_zero] at hpull
  have hRootCont₁ : ContinuousAt (eRoot.symm : ℂ → ℂ) w :=
    eRoot.continuousOn_invFun.continuousAt (eRoot.open_target.mem_nhds hw)
  have hRootCont₂ : ContinuousAt (fun v => eRoot.symm (zeta * v)) w :=
    (eRoot.continuousOn_invFun.continuousAt (eRoot.open_target.mem_nhds hwz)).comp
      (continuousAt_const.mul continuousAt_id)
  have hWnear : W zeta =ᶠ[𝓝 w] (fun v => f (P v)) := by
    filter_upwards [eRoot.open_target.mem_nhds hw,
      (continuousAt_const.mul continuousAt_id) (eRoot.open_target.mem_nhds hwz),
      hRootCont₁ (e₁.open_source.mem_nhds hw₁),
      hRootCont₂ (e₂.open_source.mem_nhds hw₂)] with v hv hvz hv₁ hv₂
    have hinv₁v : e₁.symm (P v) = eRoot.symm v := hinverse e₁ he₁ v hv hv₁
    have hinv₂v : e₂.symm (P v) = eRoot.symm (zeta * v) := by
      rw [← hPz v]
      exact hinverse e₂ he₂ (zeta * v) hvz hv₂
    simp only [f, h₁, h₂, hinv₁v, hinv₂v]
    rfl
  simpa only [Analysis.planarScalarOperator, hWnear.fderiv_eq,
    hWnear.fderiv.fderiv_eq, hWnear.eq_of_nhds] using hpull

end DifferentialGeometry.Geometry
