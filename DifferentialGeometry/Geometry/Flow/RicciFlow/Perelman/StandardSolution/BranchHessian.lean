import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.LocalCostBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Smoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Algebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.MinimizerNonnegativity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinNonconjugacy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem lMinVec_reg_min_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M)
    {Z : TangentSpace I x} {tau : ℝ}
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hbdd : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt tau) = lExp S T x Z tau ∧
        lRegularizedAction S T alpha 0 (Real.sqrt tau) = r})
    (delta : ℝ → M)
    (hdelta : ContMDiff 𝓘(ℝ, ℝ) I 1 delta)
    (hd0 : delta 0 = lRegularizedCurve S T x Z 0)
    (hdb : delta (Real.sqrt tau) = lRegularizedCurve S T x Z (Real.sqrt tau)) :
    lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) ≤
      lRegularizedAction S T delta 0 (Real.sqrt tau) := by
  have hvec := (mem_lMinDomain S T x Z tau).1 hmin
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hcost :
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
        lRegularizedCostC1 S T 0 (Real.sqrt tau) x (lExp S T x Z tau) := by
    calc
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
          lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 tau :=
        (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T (lRegularizedCurve S T x Z) tau htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau := hvec.2
      _ = lRegularizedCostC1 S T 0 (Real.sqrt tau) x (lExp S T x Z tau) :=
        lCost_eq_regularity (I := I) S T x (lExp S T x Z tau) tau htau.le
  rw [hcost]
  exact lRegularizedCostC1_le_bdd (I := I) S T 0 (Real.sqrt tau) x
    (lExp S T x Z tau) hbdd delta hdelta
    (hd0.trans (lRegularizedCurve_zero S T x Z)) hdb

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem lRayIndex_nonneg_on_of_min
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x)
    {b : ℝ} (hb : 0 < b)
    (hbdom : b ∈ lRegularizedDomain S T x Z)
    (hmin : ∀ delta : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta 0 = lRegularizedCurve S T x Z 0 →
      delta b = lRegularizedCurve S T x Z b →
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b ≤
        lRegularizedAction S T delta 0 b)
    (Q : ∀ s, TangentSpace I (lRegularizedCurve S T x Z s))
    {Ω : Set ℝ} (hΩ : IsOpen Ω)
    (hseg : Icc (0 : ℝ) b ⊆ Ω)
    (hQ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun s : ℝ ↦
        (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _))
          (lRegularizedCurve S T x Z s) (Q s) : TangentBundle I M)) Ω)
    (hQ0 : Q 0 = 0) (hQb : Q b = 0) :
    0 ≤ lRegularizedIndex S T (lRegularizedCurve S T x Z) Q Q 0 b := by
  obtain ⟨rho, a, d, ha, hbd, hrho, hrhoEq,
      _hrhoDeriv, _hrhoDom, hrhoΩ⟩ :=
    exists_lRegularizedDomain_smoothGerm_in S T x Z hb hbdom Ω hΩ hseg
  let alpha : ℝ → M := lRegularizedCurve S T x Z
  let gamma : ℝ → M := fun s ↦ alpha (rho s)
  let Qg : ∀ s, TangentSpace I (gamma s) := fun s ↦ Q (rho s)
  have hrhoM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hQg : ContMDiff 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun s : ℝ ↦
        (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _))
          (gamma s) (Qg s) : TangentBundle I M)) := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      ((fun s : ℝ ↦
        (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _))
          (lRegularizedCurve S T x Z s) (Q s) : TangentBundle I M)) ∘ rho) univ
    exact hQ.comp
      ((hrhoM.of_le (by decide :
        (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffOn)
      (fun s _hs ↦ hrhoΩ s)
  have hrhoGerm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      rho =ᶠ[𝓝 s] id := by
    filter_upwards [Ioo_mem_nhds
      (ha.trans_le hs.1) (hs.2.trans_lt hbd)] with r hr
    exact hrhoEq ⟨hr.1.le, hr.2.le⟩
  have hgammaGerm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      gamma =ᶠ[𝓝 s] alpha := by
    filter_upwards [hrhoGerm s hs] with r hr
    simp only [gamma, id_eq, hr]
  have hQgGerm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      ∀ᶠ r in 𝓝 s, (Qg r : E) = (Q r : E) := by
    filter_upwards [hrhoGerm s hs] with r hr
    change (Q (rho r) : E) = (Q r : E)
    exact congrArg (fun q : ℝ ↦ (Q q : E))
      (by simpa only [id_eq] using hr)
  have hzero : gamma 0 = alpha 0 :=
    (hgammaGerm 0 ⟨le_rfl, hb.le⟩).self_of_nhds
  have hend : gamma b = alpha b :=
    (hgammaGerm b ⟨hb.le, le_rfl⟩).self_of_nhds
  have haction :
      lRegularizedAction S T gamma 0 b = lRegularizedAction S T alpha 0 b := by
    apply lRegularizedAction_congr (I := I) S T
    intro s hs
    have hs' : s ∈ Ioo (0 : ℝ) b := by
      simpa only [uIoo_of_le hb.le] using hs
    exact (hgammaGerm s ⟨hs'.1.le, hs'.2.le⟩).self_of_nhds
  have hgeoRaw := lRegularizedCurve_isLRegularizedCurveOn (I := I) S hS T x Z hb hbdom
  have hgeo : IsLRegularizedCurveOn S T gamma (uIcc (0 : ℝ) b) x Z := by
    refine ⟨hzero.trans hgeoRaw.1, ?_, ?_⟩
    · have hvel : lVelocity (I := I) gamma 0 =
          lVelocity (I := I) alpha 0 := by
        unfold lVelocity
        rw [(hgammaGerm 0 ⟨le_rfl, hb.le⟩).mfderiv_eq
          (I := 𝓘(ℝ, ℝ)) (I' := I)]
        rfl
      exact hvel.trans hgeoRaw.2.1
    · intro s hs
      have hs' : s ∈ Icc (0 : ℝ) b := by
        simpa only [uIcc_of_le hb.le] using hs
      exact lRegularizedData_congr S T s
        (hgammaGerm s hs') (hgeoRaw.2.2 s hs)
  have hminGamma : ∀ delta : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta 0 = gamma 0 → delta b = gamma b →
      lRegularizedAction S T gamma 0 b ≤ lRegularizedAction S T delta 0 b := by
    intro delta hdelta hd0 hdb
    rw [haction]
    exact hmin delta hdelta (hd0.trans hzero) (hdb.trans hend)
  have hminVar : ∀ f : ℝ → ℝ → M,
      IsSmoothVariation (I := I) f →
      (∀ s, f 0 s = gamma s) →
      (∀ u, f u 0 = gamma 0) →
      (∀ u, f u b = gamma b) →
      IsLocalMin (fun u ↦ lRegularizedAction S T (f u) 0 b) 0 := by
    intro f hf hf0 hfa hfb
    change ∀ᶠ u in 𝓝 0,
      lRegularizedAction S T (f 0) 0 b ≤ lRegularizedAction S T (f u) 0 b
    filter_upwards [] with u
    rw [show f 0 = gamma from funext hf0]
    exact hminGamma (f u)
      (((hf : ContMDiff _ _ _ _).comp
        (contMDiff_const.prodMk contMDiff_id)).of_le (by norm_num))
      (hfa u) (hfb u)
  have hQg0 : Qg 0 = 0 := by
    rw [(hQgGerm 0 ⟨le_rfl, hb.le⟩).self_of_nhds]
    exact hQ0
  have hQgb : Qg b = 0 := by
    rw [(hQgGerm b ⟨hb.le, le_rfl⟩).self_of_nhds]
    exact hQb
  have hnonneg := lRegularizedIndex_nonneg (I := I) S hS T gamma 0 b x Z
    hgeo Qg hQg hQg0 hQgb hminVar
  have hindex :
      lRegularizedIndex S T gamma Qg Qg 0 b =
        lRegularizedIndex S T alpha Q Q 0 b := by
    apply lRegularizedIndex_congr_of_eventuallyEq (I := I) S T Qg Qg Q Q
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) b := by
        simpa only [uIoo_of_le hb.le] using hs
      exact hgammaGerm s ⟨hs'.1.le, hs'.2.le⟩
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) b := by
        simpa only [uIoo_of_le hb.le] using hs
      exact hQgGerm s ⟨hs'.1.le, hs'.2.le⟩
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) b := by
        simpa only [uIoo_of_le hb.le] using hs
      exact hQgGerm s ⟨hs'.1.le, hs'.2.le⟩
  rw [hindex] at hnonneg
  exact hnonneg

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem lActBranch_hess_le_of_min
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConjugate S T x Z tau)
    (hmin : ∀ delta : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta 0 = lRegularizedCurve S T x Z 0 →
      delta (Real.sqrt tau) = lRegularizedCurve S T x Z (Real.sqrt tau) →
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) ≤
        lRegularizedAction S T delta 0 (Real.sqrt tau))
    (V : TangentSpace I (lExp S T x Z tau))
    (W : ∀ s, TangentSpace I (lRegularizedCurve S T x Z s))
    {Ω : Set ℝ} (hΩ : IsOpen Ω)
    (hseg : Icc (0 : ℝ) (Real.sqrt tau) ⊆ Ω)
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun s : ℝ ↦
        (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _))
          (lRegularizedCurve S T x Z s) (W s) : TangentBundle I M)) Ω)
    (hW0 : W 0 = 0) (hWb : W (Real.sqrt tau) = V) :
    hessFun (I := I) (S.base.metric (T - tau))
        (lActBranch S hS T x Z tau hdom hconj)
        (lExp S T x Z tau) V V ≤
      2 * lRegularizedIndex S T (lRegularizedCurve S T x Z) W W
        0 (Real.sqrt tau) := by
  have htau : 0 < tau := ((mem_lExpPosDom S T x Z tau).1 hdom).1
  let b : ℝ := Real.sqrt tau
  let alpha : ℝ → M := lRegularizedCurve S T x Z
  let y : M := lExp S T x Z tau
  let g := S.base.metric (T - tau)
  let z : E := Z
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hbdom : b ∈ lRegularizedDomain S T x Z :=
    ((mem_lExpPosDom S T x Z tau).1 hdom).2.2
  let hloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (fun W : E ↦ lExp S T x W tau) z :=
    lExp_localDiffeo S hS T x Z tau hdom hconj
  let U : TangentSpace I x := mfderiv I 𝓘(ℝ, E) hloc.localInverse y V
  let J : ∀ s, TangentSpace I (alpha s) := lRegularizedJacobiField S T x Z U
  let Q : ∀ s, TangentSpace I (alpha s) := fun s ↦ W s - J s
  have hJ0 : J 0 = 0 := lRegularizedJacobi_zero S T x Z U
  have hJb : J b = V := by
    have hright :=
      (hloc.mfderivToContinuousLinearEquiv (by simp)).right_inv V
    change mfderiv 𝓘(ℝ, E) I
      (fun W : E ↦ lExp S T x W tau) z
        (mfderiv I 𝓘(ℝ, E) hloc.localInverse y V) = V at hright
    change lRegularizedJacobiField S T x Z U (Real.sqrt tau) = V
    have hJac := lExpJacobi_eq (I := I) S T x Z U tau
    change mfderiv 𝓘(ℝ, E) I
      (fun W : E ↦ lExp S T x W tau) z U =
        lRegularizedJacobiField S T x Z U (Real.sqrt tau) at hJac
    exact hJac.symm.trans hright
  have hQ0 : Q 0 = 0 := by
    change W 0 - J 0 = 0
    rw [hW0, hJ0, sub_self]
  have hQb : Q b = 0 := by
    change (W b : E) - (J b : E) = (0 : E)
    have hWJ : (W b : E) = (J b : E) := hWb.trans hJb.symm
    exact sub_eq_zero.mpr hWJ
  let O : Set ℝ := Ω ∩ lRegularizedDomain S T x Z
  have hOopen : IsOpen O := hΩ.inter (lRegularizedDomain_isOpen S T x Z)
  have hOseg : Icc (0 : ℝ) b ⊆ O := by
    intro s hs
    exact ⟨hseg hs, lRegularizedDomain_segment S T x Z hbdom hs.1 hs.2⟩
  have hOuseg : uIcc (0 : ℝ) b ⊆ O := by
    simpa only [uIcc_of_le hb.le] using hOseg
  have hJsm : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun s : ℝ ↦
        (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _))
          (alpha s) (J s) : TangentBundle I M)) O := by
    change ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      ((fun p : E × ℝ ↦
        (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _))
          (lRegularizedCurve S T x p.1 p.2)
          (lRegularizedJacobiField S T x p.1 U p.2) : TangentBundle I M)) ∘
        fun s : ℝ ↦ (z, s)) O
    apply (lRegularizedJacobi_smooth (I := I) S hS T x U).comp
      (contMDiff_const.prodMk contMDiff_id).contMDiffOn
    intro s hs
    change s ∈ lRegularizedDomain S T x Z
    exact hs.2
  have hJ8 := hJsm.of_le (by decide :
    (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hW8 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun s : ℝ ↦
        (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _))
          (alpha s) (W s) : TangentBundle I M)) O :=
    hW.mono inter_subset_left
  have hQ8 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun s : ℝ ↦
        (TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _))
          (alpha s) (Q s) : TangentBundle I M)) O := by
    intro s hs
    apply ContMDiffAt.contMDiffWithinAt
    have hWs := (hW8 s hs).contMDiffAt (hOopen.mem_nhds hs)
    have hJs := (hJ8 s hs).contMDiffAt (hOopen.mem_nhds hs)
    rw [Bundle.contMDiffAt_totalSpace] at hWs hJs ⊢
    refine ⟨hWs.1, ?_⟩
    let e := trivializationAt E (TangentSpace I) (alpha s)
    apply (hWs.2.sub hJs.2).congr_of_eventuallyEq
    have he : ∀ᶠ r in 𝓝 s, alpha r ∈ e.baseSet := by
      apply hWs.1.continuousAt
      exact e.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (alpha s))
    filter_upwards [he] with r hr
    change (e ⟨alpha r, W r - J r⟩).2 =
      (e ⟨alpha r, W r⟩).2 - (e ⟨alpha r, J r⟩).2
    exact (e.linear ℝ hr).map_sub (W r) (J r)
  have hQQ : 0 ≤ lRegularizedIndex S T alpha Q Q 0 b :=
    lRayIndex_nonneg_on_of_min S hS T x Z hb hbdom
      hmin Q hOopen hOseg hQ8 hQ0 hQb
  have hJ2 := hJ8.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 8)
  have hQ2 := hQ8.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 8)
  have hgeo := lRegularizedCurve_isLRegularizedCurveOn (I := I) S hS T x Z hb hbdom
  have hreg : ∀ s ∈ uIcc (0 : ℝ) b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have hJJint := intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiffOn (I := I) S hS T 0 b alpha J J
    hOopen hOuseg hJ2 hJ2 hreg
  have hJQint := intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiffOn (I := I) S hS T 0 b alpha J Q
    hOopen hOuseg hJ2 hQ2 hreg
  have hQQint := intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiffOn (I := I) S hS T 0 b alpha Q Q
    hOopen hOuseg hQ2 hQ2 hreg
  have hAlphaDiff : ∀ s ∈ uIcc (0 : ℝ) b,
      ∀ᶠ r in 𝓝 s, MDifferentiableAt 𝓘(ℝ, ℝ) I alpha r := by
    intro s hs
    filter_upwards [hOopen.mem_nhds (hOuseg hs)] with r hr
    have hsec := (hJ2 r hr).contMDiffAt (hOopen.mem_nhds hr)
    have hbase := (Bundle.contMDiffAt_totalSpace.mp hsec).1
    exact hbase.mdifferentiableAt (by norm_num)
  have hA : ∀ s ∈ uIcc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) alpha
          (fun r ↦ lVelocity (I := I) alpha r) s) s := by
    intro s hs
    simpa only [alpha] using (hgeo.2.2 s hs).2.2.1
  have hJac : IsLRegularizedJacobi S T alpha J (uIcc (0 : ℝ) b) := by
    simpa only [alpha, J] using
      lRegularizedCurve_jacobi S hS T x Z U (uIcc (0 : ℝ) b)
        (fun s hs ↦ (hOuseg hs).2)
  have hJdiff : ∀ s ∈ uIcc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) alpha J s) s :=
    fun s hs ↦ (hJac s hs).2.1
  have hQdiff : ∀ s ∈ uIcc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) alpha Q s) s := by
    intro s hs
    exact differentiableAt_chartRepAt_of_contMDiffAt_two (I := I)
      ((hQ2 s (hOuseg hs)).contMDiffAt
        (hOopen.mem_nhds (hOuseg hs)))
  have hJQzero : lRegularizedIndex S T alpha J Q 0 b = 0 := by
    rw [lRegularizedIndex_eq_half_boundary_of_isLRegularizedJacobi (I := I) S hS T alpha J Q 0 b
      hreg hAlphaDiff hA hJac hQdiff hJQint, hQ0, hQb]
    simp
  have hsquare := lRegularizedIndex_add_smul_self (I := I) S T 1 alpha J Q 0 b
    hJdiff hQdiff hJJint hJQint hQQint
  have hfield : (fun s ↦ J s + (1 : ℝ) • Q s) = W := by
    funext s
    dsimp only [Q]
    module
  rw [hfield, hJQzero] at hsquare
  have hJleW : lRegularizedIndex S T alpha J J 0 b ≤
      lRegularizedIndex S T alpha W W 0 b := by
    nlinarith
  have hgreenJJ := lRegularizedIndex_eq_half_boundary_of_isLRegularizedJacobi (I := I) S hS T alpha J J 0 b
    hreg hAlphaDiff hA hJac hJdiff hJJint
  have hJJend : 2 * lRegularizedIndex S T alpha J J 0 b =
      g.inner y (covDerivAlong (I := I) g alpha J b) V := by
    rw [hgreenJJ, hJ0, hJb]
    simp only [map_zero, sub_zero]
    rw [show T - b ^ 2 = T - tau by
      simp only [b, Real.sq_sqrt htau.le],
      show alpha b = y by rfl]
    ring
  have hbranch :
      hessFun (I := I) g
          (lActBranch S hS T x Z tau hdom hconj) y V V =
        g.inner y (covDerivAlong (I := I) g alpha J b) V := by
    simpa only [g, y, alpha, J, U, b, hloc] using
      lActBranch_hess S hS T x Z tau hdom hconj V V
  calc
    hessFun (I := I) (S.base.metric (T - tau))
        (lActBranch S hS T x Z tau hdom hconj)
        (lExp S T x Z tau) V V =
      g.inner y (covDerivAlong (I := I) g alpha J b) V := hbranch
    _ = 2 * lRegularizedIndex S T alpha J J 0 b := hJJend.symm
    _ ≤ 2 * lRegularizedIndex S T alpha W W 0 b :=
      mul_le_mul_of_nonneg_left hJleW (by norm_num)
    _ = 2 * lRegularizedIndex S T (lRegularizedCurve S T x Z) W W
        0 (Real.sqrt tau) := rfl

theorem lActBranch_hess_le_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hbddTau : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt tau) = lExp S T x Z tau ∧
        lRegularizedAction S T alpha 0 (Real.sqrt tau) = r})
    (hbddSigma : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    ∃ hdom : (Z, tau) ∈ lExpPosDom S T x,
      ∃ hconj : ¬ IsLConjugate S T x Z tau,
        ∀ (V : TangentSpace I (lExp S T x Z tau))
          (W : ∀ s, TangentSpace I (lRegularizedCurve S T x Z s))
          {Ω : Set ℝ},
          IsOpen Ω →
          Icc (0 : ℝ) (Real.sqrt tau) ⊆ Ω →
          ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
            (fun s : ℝ ↦
              (TotalSpace.mk' E
                (E := (TangentSpace I : M → Type _))
                (lRegularizedCurve S T x Z s) (W s) : TangentBundle I M)) Ω →
          W 0 = 0 → W (Real.sqrt tau) = V →
          hessFun (I := I) (S.base.metric (T - tau))
              (lActBranch S hS T x Z tau hdom hconj)
              (lExp S T x Z tau) V V ≤
            2 * lRegularizedIndex S T (lRegularizedCurve S T x Z) W W
              0 (Real.sqrt tau) := by
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down_of_bdd S hS T x Z hmin htau hlt.le hbddTau hbddSigma
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hconj : ¬ IsLConjugate S T x Z tau :=
    lMinVec_nconj_lt_of_bdd S hS T x hmin hlt hbddSigma
  refine ⟨hdom, hconj, ?_⟩
  intro V W Ω hΩ hseg hW hW0 hWb
  apply lActBranch_hess_le_of_min S hS T x Z tau hdom hconj
    (fun delta hdelta hd0 hdb ↦
      lMinVec_reg_min_of_bdd S T x hminTau hbddTau
        delta hdelta hd0 hdb)
    V W hΩ hseg hW hW0 hWb

theorem lActBranch_hess_le_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    ∃ hdom : (Z, tau) ∈ lExpPosDom S T x,
      ∃ hconj : ¬ IsLConjugate S T x Z tau,
        ∀ (V : TangentSpace I (lExp S T x Z tau))
          (W : ∀ s, TangentSpace I (lRegularizedCurve S T x Z s))
          {Ω : Set ℝ},
          IsOpen Ω →
          Icc (0 : ℝ) (Real.sqrt tau) ⊆ Ω →
          ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
            (fun s : ℝ ↦
              (TotalSpace.mk' E
                (E := (TangentSpace I : M → Type _))
                (lRegularizedCurve S T x Z s) (W s) : TangentBundle I M)) Ω →
          W 0 = 0 → W (Real.sqrt tau) = V →
          hessFun (I := I) (S.base.metric (T - tau))
              (lActBranch S hS T x Z tau hdom hconj)
              (lExp S T x Z tau) V V ≤
            2 * lRegularizedIndex S T (lRegularizedCurve S T x Z) W W
              0 (Real.sqrt tau) := by
  have hsigma : 0 < sigma := htau.trans hlt
  have hdomSigma : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).1 hmin).1
  have hregSigma : Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ sigma := by
      linarith [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈
        Icc (0 : ℝ) (Real.sqrt sigma) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
    have hclock := lExpPosDom_regularity S T x Z hdomSigma hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hclock
  have hsub : Icc (T - tau) T ⊆ Icc (T - sigma) T := by
    intro t ht
    exact ⟨(sub_le_sub_left hlt.le T).trans ht.1, ht.2⟩
  have hregTau : Icc (T - tau) T ⊆ D.regular :=
    fun _ ht ↦ hregSigma (hsub ht)
  have hRmTau : ∀ t ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K :=
    fun t ht z ↦ hRm t (hsub ht) z
  apply lActBranch_hess_le_of_bdd S hS T x hmin htau hlt
  · exact lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt tau)
      le_rfl (Real.sqrt_nonneg tau)
      (by simpa only [Real.sq_sqrt htau.le] using hregTau)
      (by simpa only [Real.sq_sqrt htau.le] using hRmTau)
      x (lExp S T x Z tau)
  · exact lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt sigma)
      le_rfl (Real.sqrt_nonneg sigma)
      (by simpa only [Real.sq_sqrt hsigma.le] using hregSigma)
      (by simpa only [Real.sq_sqrt hsigma.le] using hRm)
      x (lExp S T x Z sigma)

end DifferentialGeometry.PDE.RicciFlow
