import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.CurveRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.FinitePoleRegularity


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem rm_bound_of_mem_lMinDomain
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : E} {sigma : ℝ} (hmin : (Z, sigma) ∈ lMinDomain S T x) :
    ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K := by
  have hdom := ((mem_lMinDomain S T x Z sigma).mp hmin).1
  have hsigma := lMinDomain_pos S T x Z sigma hmin
  apply hRm sigma hsigma
  intro t ht
  have ht0 : 0 ≤ T - t := sub_nonneg.mpr ht.2
  have htS : T - t ≤ sigma := by linarith only [ht.1]
  have hsqrt : Real.sqrt (T - t) ∈ Icc (0 : ℝ) (Real.sqrt sigma) :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt htS⟩
  have h := lExpPosDom_regularity S T x Z hdom hsqrt
  have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by rw [Real.sq_sqrt ht0]; ring
  simpa only [heq] using h

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem lMinDomain_down_of_slab_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    (Z : E) {sigma rho : ℝ} (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hrho : 0 < rho) (hle : rho ≤ sigma) : (Z, rho) ∈ lMinDomain S T x := by
  obtain ⟨K, hK⟩ := rm_bound_of_mem_lMinDomain S T x hRm hmin
  exact lMinDomain_down_of_rm S hS K T x Z hmin hrho hle hK

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem lMinimizingVector_nconj_lt_of_slab_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : E} {sigma rho : ℝ} (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hle : rho < sigma) : ¬ IsLConjugate S T x Z rho := by
  obtain ⟨K, hK⟩ := rm_bound_of_mem_lMinDomain S T x hRm hmin
  exact lMinVec_nconj_lt_of_rm S hS K T x hmin hle hK


theorem lCost_joint_contMDiffAt_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : E} {tau : ℝ} (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    ContMDiffAt (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : M × ℝ => lCost S T x q.1 q.2) (lExp S T x Z tau, tau) := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down_of_slab_bounds S hS T x hRm Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hnconj : ¬ IsLConjugate S T x Z tau :=
    lMinimizingVector_nconj_lt_of_slab_bounds S hS T x hRm hmin hsigma
  let J := (modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ)
  let K := I.prod (modelWithCornersSelf ℝ ℝ)
  let F : E × ℝ → M × ℝ := fun q => (lExp S T x q.1 q.2, q.2)
  let hloc : IsLocalDiffeomorphAt J K ∞ F (Z, tau) :=
    lExpTime_local S hS T x Z tau hdom hnconj
  let p : M × ℝ → E × ℝ := hloc.localInverse
  let y : M × ℝ := (lExp S T x Z tau, tau)
  let A : E × ℝ → ℝ := fun q =>
    lRegularizedAction S T (lRegularizedCurve S T x q.1) 0 (Real.sqrt q.2)
  have hp0 : p y = (Z, tau) := hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hp : ContMDiffAt K J ∞ p y := hloc.localInverse_contMDiffAt
  have hA : ContMDiffAt J 𝓘(ℝ) ∞ A (Z, tau) := by
    have h := contDiffAt_lRegularizedAction_lRegularizedCurve_sqrt S hS T x hdom
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod] at h
    exact h
  have hAp : ContMDiffAt K 𝓘(ℝ) ∞ (A ∘ p) y := by
    have hA' : ContMDiffAt J 𝓘(ℝ) ∞ A (p y) := by rw [hp0]; exact hA
    exact hA'.comp y hp
  have heq : A ∘ p =ᶠ[𝓝 y] fun q : M × ℝ => lCost S T x q.1 q.2 := by
    let rho : ℝ := (tau + sigma) / 2
    have htRho : tau < rho := by dsimp only [rho]; linarith only [hsigma]
    have hRhoS : rho < sigma := by dsimp only [rho]; linarith only [hsigma]
    have hZrho : Z ∈ lInjDomain S T x rho := ⟨sigma, hRhoS, hmin⟩
    have hsrc : hloc.localInverse.source ∈ 𝓝 y :=
      hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source
    have htime : ∀ᶠ q : M × ℝ in 𝓝 y, q.2 ∈ Ioo (0 : ℝ) rho :=
      continuousAt_snd.eventually (isOpen_Ioo.mem_nhds ⟨htau, htRho⟩)
    have hinj : ∀ᶠ q : M × ℝ in 𝓝 y, (p q).1 ∈ lInjDomain S T x rho := by
      apply hp.continuousAt.fst.eventually
      change lInjDomain S T x rho ∈ 𝓝 (p y).1
      rw [hp0]
      exact (lInj_isOpen_of_rm S hS T hg x hRm rho).mem_nhds hZrho
    filter_upwards [hsrc, htime, hinj] with q hqSource hqTime hqInj
    have hright := hloc.localInverse_right_inv hqSource
    have hp2 : (p q).2 = q.2 := by
      simpa only [F, p] using congrArg Prod.snd hright
    have hend : lExp S T x (p q).1 q.2 = q.1 := by
      have hh : lExp S T x (p q).1 (p q).2 = q.1 := by
        simpa only [F, p] using congrArg Prod.fst hright
      rwa [hp2] at hh
    obtain ⟨theta, hRhoTheta, hWmin⟩ := hqInj
    have hminq : ((p q).1, q.2) ∈ lMinDomain S T x :=
      lMinDomain_down_of_slab_bounds S hS T x hRm (p q).1 hWmin hqTime.1
        (hqTime.2.trans hRhoTheta).le
    have hcost := ((mem_lMinDomain S T x (p q).1 q.2).mp hminq).2
    change lRegularizedAction S T (lRegularizedCurve S T x (p q).1)
      0 (Real.sqrt (p q).2) = lCost S T x q.1 q.2
    rw [hp2]
    calc
      lRegularizedAction S T (lRegularizedCurve S T x (p q).1) 0 (Real.sqrt q.2) =
          lLength S T (fun r => lExp S T x (p q).1 r) 0 q.2 :=
        (lLength_squareRootReparametrization_eq_lRegularizedAction S T
          (lRegularizedCurve S T x (p q).1) q.2 hqTime.1.le).symm
      _ = lCost S T x (lExp S T x (p q).1 q.2) q.2 := hcost
      _ = lCost S T x q.1 q.2 := by rw [hend]
  exact hAp.congr_of_eventuallyEq heq.symm

theorem redLength_joint_contMDiffAt_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : E} {tau : ℝ} (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    ContMDiffAt (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : M × ℝ => redLength S T x q.1 q.2) (lExp S T x Z tau, tau) := by
  have hc := lCost_joint_contMDiffAt_of_rm S hS T hg x hRm htau hZ
  have hsqrt : ContMDiffAt (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : M × ℝ => Real.sqrt q.2) (lExp S T x Z tau, tau) :=
    (Real.contDiffAt_sqrt htau.ne').contMDiffAt.comp _ contMDiffAt_snd
  have hden : (2 : ℝ) * Real.sqrt tau ≠ 0 :=
    mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr htau).ne'
  exact hc.div₀ ((contMDiffAt_const (c := (2 : ℝ))).mul hsqrt) hden

theorem isOpen_lInjDomain_spacetime_image_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K) :
    IsOpen {q : M × ℝ | 0 < q.2 ∧
      ∃ Z ∈ lInjDomain S T x q.2, lExp S T x Z q.2 = q.1} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨y, tau⟩ ⟨htau, Z, hZ, hend⟩
  dsimp only at htau hZ hend
  subst y
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down_of_slab_bounds S hS T x hRm Z hmin htau hsigma.le
  have hdom := ((mem_lMinDomain S T x Z tau).mp hminTau).1
  have hnconj := lMinimizingVector_nconj_lt_of_slab_bounds S hS T x hRm hmin hsigma
  let J := (modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ ℝ)
  let K := I.prod (modelWithCornersSelf ℝ ℝ)
  let F : E × ℝ → M × ℝ := fun q => (lExp S T x q.1 q.2, q.2)
  let hloc : IsLocalDiffeomorphAt J K ∞ F (Z, tau) :=
    lExpTime_local S hS T x Z tau hdom hnconj
  let p : M × ℝ → E × ℝ := hloc.localInverse
  let y : M × ℝ := (lExp S T x Z tau, tau)
  have hp0 : p y = (Z, tau) := hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hp : ContinuousAt p y := hloc.localInverse_contMDiffAt.continuousAt
  let rho : ℝ := (tau + sigma) / 2
  have htRho : tau < rho := by dsimp only [rho]; linarith only [hsigma]
  have hRhoS : rho < sigma := by dsimp only [rho]; linarith only [hsigma]
  have hZrho : Z ∈ lInjDomain S T x rho := ⟨sigma, hRhoS, hmin⟩
  have hsrc : hloc.localInverse.source ∈ 𝓝 y :=
    hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source
  have htime : ∀ᶠ q : M × ℝ in 𝓝 y, q.2 ∈ Ioo (0 : ℝ) rho :=
    continuousAt_snd.eventually (isOpen_Ioo.mem_nhds ⟨htau, htRho⟩)
  have hinj : ∀ᶠ q : M × ℝ in 𝓝 y, (p q).1 ∈ lInjDomain S T x rho := by
    apply hp.fst.eventually
    change lInjDomain S T x rho ∈ 𝓝 (p y).1
    rw [hp0]
    exact (lInj_isOpen_of_rm S hS T hg x hRm rho).mem_nhds hZrho
  filter_upwards [hsrc, htime, hinj] with q hqSource hqTime hqInj
  refine ⟨hqTime.1, (p q).1, ?_, ?_⟩
  · obtain ⟨theta, hRhoTheta, hWmin⟩ := hqInj
    exact ⟨theta, hqTime.2.trans hRhoTheta, hWmin⟩
  · have hright := hloc.localInverse_right_inv hqSource
    have hp2 : (p q).2 = q.2 := by
      simpa only [F, p] using congrArg Prod.snd hright
    have hh : lExp S T x (p q).1 (p q).2 = q.1 := by
      simpa only [F, p] using congrArg Prod.fst hright
    rwa [hp2] at hh

theorem redLength_joint_contMDiffOn_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K) :
    ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : M × ℝ => redLength S T x q.1 q.2)
      {q : M × ℝ | 0 < q.2 ∧
        ∃ Z ∈ lInjDomain S T x q.2, lExp S T x Z q.2 = q.1} := by
  rintro ⟨y, tau⟩ ⟨htau, Z, hZ, hend⟩
  dsimp only at htau hZ hend
  subst y
  exact (redLength_joint_contMDiffAt_of_rm S hS T hg x hRm htau hZ).contMDiffWithinAt

theorem exists_lInjDomain_spacetime_rectangle_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        Tensor0SBundle.normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {Z : E} {tau : ℝ} (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau) :
    ∃ U : TopologicalSpace.Opens M, lExp S T x Z tau ∈ U ∧
      ∃ a b : ℝ, 0 < a ∧ a < tau ∧ tau < b ∧
        ∀ r ∈ Icc a b, ∀ y ∈ U,
          ∃ W ∈ lInjDomain S T x r, lExp S T x W r = y := by
  have hO := isOpen_lInjDomain_spacetime_image_of_rm S hS T hg x hRm
  have hmem : (lExp S T x Z tau, tau) ∈ {q : M × ℝ | 0 < q.2 ∧
      ∃ W ∈ lInjDomain S T x q.2, lExp S T x W q.2 = q.1} :=
    ⟨htau, Z, hZ, rfl⟩
  obtain ⟨U, V, hU, hyU, hV, htV, hUV⟩ :=
    mem_nhds_prod_iff'.mp (hO.mem_nhds hmem)
  have htime : V ∩ Ioi (0 : ℝ) ∈ 𝓝 tau :=
    (hV.inter isOpen_Ioi).mem_nhds ⟨htV, htau⟩
  obtain ⟨l, u, hlt, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp htime
  let a : ℝ := (l + tau) / 2
  let b : ℝ := (tau + u) / 2
  have hla : l < a := by dsimp only [a]; linarith only [hlt.1]
  have hat : a < tau := by dsimp only [a]; linarith only [hlt.1]
  have htb : tau < b := by dsimp only [b]; linarith only [hlt.2]
  have hbu : b < u := by dsimp only [b]; linarith only [hlt.2]
  have ha0 : 0 < a := (hlu ⟨hla, hat.trans hlt.2⟩).2
  refine ⟨⟨U, hU⟩, hyU, a, b, ha0, hat, htb, ?_⟩
  intro r hr y hy
  have hrV : r ∈ V := (hlu ⟨hla.trans_le hr.1, hr.2.trans_lt hbu⟩).1
  exact (hUV (show (y, r) ∈ U ×ˢ V from ⟨hy, hrV⟩)).2

end DifferentialGeometry.PDE.RicciFlow.Perelman
