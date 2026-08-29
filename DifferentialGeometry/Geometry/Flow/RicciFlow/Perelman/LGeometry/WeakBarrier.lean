import DifferentialGeometry.Geometry.Comparison.CGTPaths
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CompleteMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.HamiltonBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RayAdapted

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [PseudoMetricSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem isOpen_germ_eq (f g : Real → M) :
    IsOpen {s : Real | f =ᶠ[nhds s] g} := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  change {r : Real | f r = g r} ∈ nhds s at hs
  obtain ⟨U, hUsub, hUopen, hsU⟩ := mem_nhds_iff.mp hs
  apply mem_of_superset (hUopen.mem_nhds hsU)
  intro r hr
  change {q : Real | f q = g q} ∈ nhds r
  exact mem_of_superset (hUopen.mem_nhds hr) hUsub

private theorem exists_tail_cut
    (n b k eps : Real) (hb : 0 < b) (heps : 0 < eps)
    (tail : Real → Real)
    (htail : Tendsto tail (𝓝[>] (0 : Real)) (nhds k)) :
    ∃ a : Real, 0 < a ∧ a < b ∧
      n / (2 * b * (b - a)) - n / (2 * b ^ 2) +
          k / (2 * b ^ 3) - tail a / (2 * b * (b - a) ^ 2) < eps := by
  let err : Real → Real := fun a ↦
    n / (2 * b * (b - a)) - n / (2 * b ^ 2) +
      k / (2 * b ^ 3) - tail a / (2 * b * (b - a) ^ 2)
  have ha0 : Tendsto (fun a : Real ↦ a) (𝓝[>] (0 : Real)) (nhds 0) :=
    tendsto_inf_left tendsto_id
  have hpair : Tendsto (fun a : Real ↦ (a, tail a)) (𝓝[>] (0 : Real))
      (nhds (0, k)) := ha0.prodMk_nhds htail
  have hden1 : ContinuousAt (fun q : Real × Real ↦ 2 * b * (b - q.1)) (0, k) :=
    continuousAt_const.mul (continuousAt_const.sub continuousAt_fst)
  have hden1_ne : 2 * b * (b - (0, k).1) ≠ 0 := by
    simp only [sub_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hb.ne') hb.ne'
  have hden2 : ContinuousAt
      (fun q : Real × Real ↦ 2 * b * (b - q.1) ^ 2) (0, k) :=
    continuousAt_const.mul ((continuousAt_const.sub continuousAt_fst).pow 2)
  have hden2_ne : 2 * b * (b - (0, k).1) ^ 2 ≠ 0 := by
    simp only [sub_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hb.ne') (pow_ne_zero 2 hb.ne')
  have hcont : ContinuousAt (fun q : Real × Real ↦
      n / (2 * b * (b - q.1)) - n / (2 * b ^ 2) +
        k / (2 * b ^ 3) - q.2 / (2 * b * (b - q.1) ^ 2)) (0, k) := by
    exact (((continuousAt_const.div hden1 hden1_ne).sub continuousAt_const).add
      continuousAt_const).sub (continuousAt_snd.div hden2 hden2_ne)
  have hlim0 : n / (2 * b * (b - (0, k).1)) - n / (2 * b ^ 2) +
      k / (2 * b ^ 3) - (0, k).2 / (2 * b * (b - (0, k).1) ^ 2) = 0 := by
    simp only [sub_zero]
    field_simp [hb.ne']
    ring
  have herr : Tendsto err (𝓝[>] (0 : Real)) (nhds 0) := by
    have hraw := hcont.tendsto.comp hpair
    have heq : ((fun q : Real × Real ↦
        n / (2 * b * (b - q.1)) - n / (2 * b ^ 2) +
          k / (2 * b ^ 3) - q.2 / (2 * b * (b - q.1) ^ 2)) ∘
        fun a : Real ↦ (a, tail a)) = fun a : Real ↦
          n / (2 * b * (b - a)) - n / (2 * b ^ 2) +
            k / (2 * b ^ 3) - tail a / (2 * b * (b - a) ^ 2) := by
      funext a
      rfl
    rw [heq, hlim0] at hraw
    simpa only [err] using hraw
  have hevent : ∀ᶠ a in 𝓝[>] (0 : Real), err a < eps := by
    exact (tendsto_order.1 herr).2 eps heps
  have hall : ∀ᶠ a in 𝓝[>] (0 : Real), err a < eps ∧ a ∈ Ioo 0 b :=
    hevent.and (Ioo_mem_nhdsGT hb)
  obtain ⟨a, haerr, ha⟩ := Filter.Eventually.exists hall
  exact ⟨a, ha.1, ha.2, by simpa only [err] using haerr⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_redWeak_sup [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T sigma tau : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (htau : 0 < tau) (htausigma : tau < sigma)
    (hreg : Icc (T - sigma) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : M) (eps : Real) (heps : 0 < eps) :
    ∃ (U : Set M) (J : Set Real) (Phi : M → Real → Real) (d : Real),
      IsOpen U ∧ y ∈ U ∧ IsOpen J ∧ tau ∈ J ∧
      J ⊆ Ioo (0 : Real) sigma ∧
      (∀ z ∈ U, ∀ rho ∈ J,
        redLength S T x z rho ≤ Phi z rho) ∧
      Phi y tau = redLength S T x y tau ∧
      ContMDiffOn I 𝓘(Real, Real) ∞ (fun z : M ↦ Phi z tau) U ∧
      HasDerivAt (Phi y) d tau ∧
      d + laplacian (I := I) (LeviCivita (I := I)
          (S.base.metric (T - tau))) (S.base.metric (T - tau))
          (fun z : M ↦ Phi z tau) y ≤
        ((Module.finrank Real E : Real) / 2 - redLength S T x y tau) / tau + eps := by
  classical
  let b : Real := Real.sqrt tau
  have hb : 0 < b := by simpa only [b] using Real.sqrt_pos.2 htau
  have hbSq : b ^ 2 = tau := by simpa only [b] using Real.sq_sqrt htau.le
  have hsigma : 0 < sigma := htau.trans htausigma
  have hregTau : Icc (T - tau) T ⊆ D.regular := by
    intro q hq
    apply hreg
    constructor
    · linarith [hq.1, htausigma]
    · exact hq.2
  have hRmTau : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    intro q hq z
    exact hRm q (by
      constructor
      · linarith [hq.1, htausigma]
      · exact hq.2) z
  obtain ⟨alpha0, halpha0, halpha00, halpha0b⟩ :
      ∃ alpha0 : Real → M, ContMDiff 𝓘(Real, Real) I 1 alpha0 ∧
        alpha0 0 = x ∧ alpha0 (Real.sqrt tau) = y := by
    let g := S.base.metric T
    let : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E
        (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    have hxy : Manifold.riemannianEDist I x y < (⊤ : ENNReal) :=
      lt_of_le_of_ne le_top
        (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
          (I := I) x y)
    obtain ⟨path, hpath, _hlen⟩ :=
      DifferentialGeometry.Geometry.Riemannian.CGT.exists_flat_path
        (I := I) hxy
    let alpha0 : Real → M := fun s ↦ path.extend (s / b)
    have halpha0 : ContMDiff 𝓘(Real, Real) I 1 alpha0 := by
      apply hpath.c1.comp
      rw [contMDiff_iff_contDiff]
      fun_prop
    refine ⟨alpha0, halpha0, ?_, ?_⟩
    · simp only [alpha0, zero_div, Path.extend_zero]
    · simp only [alpha0, b, div_self hb.ne', Path.extend_one]
  obtain ⟨Z, hZmin, hZend⟩ :=
    exists_lMinVec_rm (I := I) S hS K T hg tau htau hregTau hRmTau
      x y alpha0 halpha0 halpha00 halpha0b
  have hbdom : b ∈ lRegDomain S T x Z := by
    have hpos : (Z, tau) ∈ lExpPosDom S T x :=
      ((mem_lMinDomain S T x Z tau).1 hZmin).1
    simpa only [b] using
      ((mem_lExpPosDom S T x Z tau).1 hpos).2.2
  let gamma : Real → M := lRegCurve S T x Z
  let kval : Real := lK S T gamma b
  obtain ⟨a, ha0, hab, herr⟩ :=
    exists_tail_cut (Module.finrank Real E : Real) b kval eps hb heps
      (fun a ↦ lKTail S T gamma a b)
      (by simpa only [gamma, kval] using lKTail_tendsto S hS T x Z hb hbdom)
  obtain ⟨V, hVopen, hA0V, Ktime, hKopen, hKconn, h0K, haK, hbK,
      alpha, halpha, hcurves, hinj⟩ :=
    exists_lTail_inj (E := E) (I := I) S hS K T x hZmin hregTau hRmTau
      ha0 (by simpa only [b] using hab)
  let x0 : M := gamma a
  let A0 : TangentSpace I x0 := lVelocity (I := I) gamma a
  have hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a) := by
    intro A hAV
    rw [(hcurves A hAV).1, (hcurves A0 hA0V).1]
  have hregFamily : ∀ q ∈ V ×ˢ Ktime, T - q.2 ^ 2 ∈ D.regular := by
    intro q hq
    exact ((hcurves q.1 hq.1).2.2 q.2 hq.2).1
  have hEulerFamily : ∀ A ∈ V, ∀ s ∈ Ktime,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A, z)) r) s =
        lRegAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A, r)) s) := by
    intro A hAV s hs
    exact ((hcurves A hAV).2.2 s hs).2.2.2
  let Rdom : Set Real := lRegDomain S T x Z
  have hRdomOpen : IsOpen Rdom := by
    simpa only [Rdom] using lRegDomain_isOpen S T x Z
  have hRdomConn : IsPreconnected Rdom := by
    simpa only [Rdom] using lRegDomain_preconn S T x Z
  have h0Rdom : 0 ∈ Rdom := by
    simpa only [Rdom] using lRegDomain_seg S T x Z hbdom le_rfl hb.le
  have haRdom : a ∈ Rdom := by
    simpa only [Rdom] using lRegDomain_seg S T x Z hbdom ha0.le hab.le
  have hbRdom : b ∈ Rdom := by simpa only [Rdom] using hbdom
  have hgamma : ∀ r ∈ Rdom,
      T - r ^ 2 ∈ D.regular ∧
        MDifferentiableAt 𝓘(Real, Real) I gamma r ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun q : Real ↦ lVelocity (I := I) gamma q) r) r ∧
        covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) gamma
            (fun q : Real ↦ lVelocity (I := I) gamma q) r =
          lRegAccel S T r (gamma r) (lVelocity (I := I) gamma r) := by
    intro r hr
    have hrdom : r ∈ lRegDomain S T x Z := by simpa only [Rdom] using hr
    obtain ⟨L, hLopen, hLconn, h0L, hrL, hchosen⟩ :=
      lRegChosen_spec S T x Z hrdom
    have heqOn : Set.EqOn gamma (lRegChosen S T x Z hrdom) L := by
      simpa only [gamma] using
        lRegCurve_eqOn S hS T hLopen hLconn h0L hchosen
    have heq : gamma =ᶠ[nhds r] lRegChosen S T x Z hrdom :=
      heqOn.eventuallyEq_of_mem (hLopen.mem_nhds hrL)
    exact lRegData_congr S T r heq (hchosen.2.2 r hrL)
  have hcenterEq : Set.EqOn (fun r ↦ alpha (A0, r)) gamma
      (Ktime ∩ Rdom) :=
    lRegSol_eqOn S hS T hKopen hKconn haK hRdomOpen hRdomConn haRdom
      (hcurves A0 hA0V).2.2 hgamma
      (by simpa only [x0] using (hcurves A0 hA0V).1)
      (by simpa only [A0] using (hcurves A0 hA0V).2.1)
  have hsegK : Icc (0 : Real) b ⊆ Ktime :=
    hKconn.ordConnected.out h0K hbK
  have hsegR : Icc (0 : Real) b ⊆ Rdom :=
    hRdomConn.ordConnected.out h0Rdom hbRdom
  have hcenter : ∀ s ∈ Icc (0 : Real) b,
      (fun r ↦ alpha (A0, r)) =ᶠ[nhds s] gamma := by
    intro s hs
    exact hcenterEq.eventuallyEq_of_mem
      ((hKopen.inter hRdomOpen).mem_nhds ⟨hsegK hs, hsegR hs⟩)
  have hcenterB : alpha (A0, b) = y := by
    calc
      alpha (A0, b) = gamma b :=
        (hcenter b ⟨hb.le, le_rfl⟩).self_of_nhds
      _ = lExp S T x Z tau := by simp only [gamma, b, lExp]
      _ = y := hZend
  obtain ⟨P0, Omega0, hOmega0, hOmega0seg, hP0sm, hP0ode, hP0ON⟩ :=
    exists_lRayAdapt (I := I) S hS T x hb hbdom
  let beta : Real → M := fun s ↦ alpha (A0, s)
  let P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (beta s) := fun i s ↦ (P0 i s : E)
  let Omega : Set Real :=
    {s : Real | beta =ᶠ[nhds s] gamma} ∩ Omega0
  have hOmega : IsOpen Omega :=
    (isOpen_germ_eq beta gamma).inter hOmega0
  have hOmegaSeg : Icc (0 : Real) b ⊆ Omega := by
    intro s hs
    refine ⟨?_, hOmega0seg hs⟩
    change beta =ᶠ[nhds s] gamma
    simpa only [beta] using hcenter s hs
  have hPsm : ∀ i, ContMDiffOn 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (beta s) (P i s) : TangentBundle I M)) Omega := by
    intro i s hs
    have heq : beta =ᶠ[nhds s] gamma := hs.1
    have hraw := (hP0sm i s hs.2).contMDiffAt (hOmega0.mem_nhds hs.2)
    apply ContMDiffAt.contMDiffWithinAt
    apply hraw.congr_of_eventuallyEq
    filter_upwards [heq] with r hr
    change TotalSpace.mk' E (beta r) (P i r) =
      TotalSpace.mk' E (gamma r) (P0 i r)
    rw [hr]
  have hPode : ∀ i s, s ∈ Icc a b →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) beta (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (beta s) (P i s) := by
    intro i s hs
    have hs0b : s ∈ Icc (0 : Real) b := ⟨ha0.le.trans hs.1, hs.2⟩
    have heq := hcenter s hs0b
    have hfield : ∀ᶠ r in nhds s, (P i r : E) = (P0 i r : E) := by
      filter_upwards
      intro r
      rfl
    have hcov :=
      DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
        (I := I) (S.base.metric (T - s ^ 2)) (P i) (P0 i) heq hfield
    have hbase := heq.self_of_nhds
    change (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
      beta (P i) s : E) =
        ((-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (beta s) (P i s) : E)
    rw [hcov]
    have hbeta : beta s = gamma s := by simpa only [beta] using hbase
    rw [hbeta]
    simpa only [P] using congrArg
      (fun v : TangentSpace I (gamma s) ↦ (v : E))
      (hP0ode i s (hOmega0seg hs0b))
  have hPON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
          (P i b) (P j b) = if i = j then 1 else 0 := by
    intro i j
    rw [show alpha (A0, b) = gamma b from
      (hcenter b ⟨hb.le, le_rfl⟩).self_of_nhds]
    simpa only [P] using hP0ON i j
  let htime := lTailTime_local hVopen hA0V hKopen hbK halpha hinj
  let hfixed := lTail_localDiffeo hVopen hA0V hbK halpha hinj
  let head : Real := lRegAction S T gamma 0 a
  let joint : M × Real → Real := fun q ↦
    lRegAction S T
      (fun s : Real ↦ alpha ((htime.localInverse q).1, s))
      a (htime.localInverse q).2
  let fixed : M → Real := fun z ↦
    lRegAction S T (fun s : Real ↦ alpha (hfixed.localInverse z, s)) a b
  let Phi : M → Real → Real := fun z rho ↦
    (head + joint (z, Real.sqrt rho)) / (2 * Real.sqrt rho)
  have htime0 : htime.localInverse (y, b) = (A0, b) := by
    rw [← hcenterB]
    exact htime.localInverse_left_inv htime.localInverse_mem_target
  have hfixed0 : hfixed.localInverse y = A0 := by
    rw [← hcenterB]
    simpa only [hfixed] using
      hfixed.localInverse_left_inv hfixed.localInverse_mem_target
  have hgoodOpen : IsOpen
      (htime.localInverse.source ∩ htime.localInverse ⁻¹' (V ×ˢ Ktime)) :=
    htime.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
      htime.localInverse_open_source (hVopen.prod hKopen)
  have hgood : (y, b) ∈
      htime.localInverse.source ∩ htime.localInverse ⁻¹' (V ×ˢ Ktime) := by
    have hsource : (alpha (A0, b), b) ∈ htime.localInverse.source := by
      simpa only [htime, A0, b] using htime.localInverse_mem_source
    rw [hcenterB] at hsource
    refine ⟨hsource, ?_⟩
    change htime.localInverse (y, b) ∈ V ×ˢ Ktime
    rw [htime0]
    exact ⟨hA0V, hbK⟩
  let rawMap : M × Real → M × Real := fun q ↦ (q.1, Real.sqrt q.2)
  have hrawCont : Continuous rawMap :=
    continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd)
  let N : Set (M × Real) := rawMap ⁻¹'
      (htime.localInverse.source ∩ htime.localInverse ⁻¹' (V ×ˢ Ktime)) ∩
        (Set.univ ×ˢ Ioo (a ^ 2) sigma)
  have hNopen : IsOpen N := by
    exact (hgoodOpen.preimage hrawCont).inter (isOpen_univ.prod isOpen_Ioo)
  have haSqTau : a ^ 2 < tau := by
    rw [← hbSq]
    nlinarith [ha0, hab]
  have hNmem : (y, tau) ∈ N := by
    refine ⟨?_, Set.mem_prod.2 ⟨Set.mem_univ _, haSqTau, htausigma⟩⟩
    change (y, Real.sqrt tau) ∈
      htime.localInverse.source ∩ htime.localInverse ⁻¹' (V ×ˢ Ktime)
    simpa only [b] using hgood
  obtain ⟨U, J, hUopen, hyU, hJopen, htauJ, hprod⟩ :=
    mem_nhds_prod_iff'.mp (hNopen.mem_nhds hNmem)
  have hJsub : J ⊆ Ioo (0 : Real) sigma := by
    intro rho hrho
    have hN : (y, rho) ∈ N := hprod (Set.mem_prod.2 ⟨hyU, hrho⟩)
    have hrange := hN.2.2
    exact ⟨lt_of_le_of_lt (sq_nonneg a) hrange.1, hrange.2⟩
  have hsupport : ∀ z ∈ U, ∀ rho ∈ J,
      redLength S T x z rho ≤ Phi z rho := by
    intro z hz rho hrho
    have hN : (z, rho) ∈ N := hprod (Set.mem_prod.2 ⟨hz, hrho⟩)
    have hqgood := hN.1
    have hrange := hN.2.2
    have hrho0 : 0 < rho := (hJsub hrho).1
    let c : Real := Real.sqrt rho
    have hc : 0 < c := by simpa only [c] using Real.sqrt_pos.2 hrho0
    have hcSq : c ^ 2 = rho := by simpa only [c] using Real.sq_sqrt hrho0.le
    have hac : a < c := by
      rw [← sq_lt_sq₀ ha0.le hc.le]
      simpa only [hcSq] using hrange.1
    let p : E × Real := htime.localInverse (z, c)
    have hpVK : p ∈ V ×ˢ Ktime := by
      have hpVK' : htime.localInverse (z, Real.sqrt rho) ∈ V ×ˢ Ktime :=
        hqgood.2
      simpa only [c, p] using hpVK'
    have hright : (alpha p, p.2) = (z, c) := by
      simpa only [htime, p] using htime.localInverse_right_inv hqgood.1
    have hp2 : p.2 = c := congrArg Prod.snd hright
    have hend : alpha (p.1, c) = z := by
      have hfirst := congrArg Prod.fst hright
      rw [hp2] at hfirst
      calc
        alpha (p.1, c) = alpha p :=
          congrArg alpha (Prod.ext rfl hp2.symm)
        _ = z := by simpa only [Prod.fst] using hfirst
    have hsegC : Icc (0 : Real) c ⊆ Ktime := by
      have hcK : c ∈ Ktime := by rw [← hp2]; exact hpVK.2
      exact hKconn.ordConnected.out h0K hcK
    have hregC : Icc (T - c ^ 2) T ⊆ D.regular := by
      intro q hq
      apply hreg
      constructor
      · linarith [hq.1, hrange.2, hcSq]
      · exact hq.2
    have hRmC : ∀ q ∈ Icc (T - c ^ 2) T, ∀ w : M,
        normSq0S (I := I) (S.base.metric q) w 4 (S.base.rm04 q w) ≤ K := by
      intro q hq w
      apply hRm q
      constructor
      · linarith [hq.1, hrange.2, hcSq]
      · exact hq.2
    have hbdd := lRegCosts_bdd_rm (I := I) S hS K T 0 c
      (by norm_num) hc.le hregC hRmC x z
    have hregBack : ∀ s ∈ Icc (0 : Real) c,
        T - s ^ 2 ∈ D.regular := by
      intro s hs
      apply hregC
      have hs2 : s ^ 2 ≤ c ^ 2 := (sq_le_sq₀ hs.1 hc.le).2 hs.2
      constructor <;> linarith [sq_nonneg s]
    have hheadC1 : ContMDiffOn 𝓘(Real, Real) I 1 gamma
        (Icc (0 : Real) a) :=
      (lRegCurve_c1On (I := I) S hS T x Z hbdom).mono
        (fun s hs ↦ ⟨hs.1, hs.2.trans hab.le⟩)
    let delta : Real → M := fun s ↦ alpha (p.1, s)
    have htailC1 : ContMDiffOn 𝓘(Real, Real) I 1 delta
        (Icc a c) := by
      have hpair : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
          (fun s : Real ↦ (p.1, s)) := contMDiff_const.prodMk contMDiff_id
      exact (halpha.comp hpair.contMDiffOn (fun s hs ↦
        ⟨hpVK.1, hsegC ⟨ha0.le.trans hs.1, hs.2⟩⟩)).of_le (by norm_num)
    have hnode : gamma a = delta a := by
      change gamma a = alpha (p.1, a)
      rw [hstart p.1 hpVK.1]
      exact ((hcenter a ⟨ha0.le, hab.le⟩).self_of_nhds).symm
    have hle := lCost_le_join_bdd (I := I) S hS T c hc x z ha0 hac
      hbdd hregBack gamma delta hheadC1 htailC1 hnode
      (by simpa only [gamma] using lRegCurve_zero S T x Z) hend
    change lCost S T x z rho / (2 * Real.sqrt rho) ≤
      (head + joint (z, Real.sqrt rho)) / (2 * Real.sqrt rho)
    rw [show rho = c ^ 2 from hcSq.symm, Real.sqrt_sq hc.le]
    apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hc)).2
    simpa only [head, joint, gamma, p, hp2, delta] using hle
  have hfull : lRegAction S T gamma 0 b = lCost S T x y tau := by
    have hvec := (mem_lMinDomain S T x Z tau).1 hZmin
    calc
      lRegAction S T gamma 0 b =
          lLength S T (sqrtReparam gamma) 0 tau := by
        simpa only [gamma, b] using
          (lLength_sqrt (I := I) S T gamma tau htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau := by
        change lLength S T (fun r : Real ↦ gamma (Real.sqrt r)) 0 tau = _
        simpa only [gamma, lExp] using hvec.2
      _ = lCost S T x y tau := by rw [hZend]
  have hheadTail : head + fixed y = lRegAction S T gamma 0 b := by
    have hheadInt := lRayLag_int S hS T x Z hb hbdom
    have hheadInt' : IntervalIntegrable (lRegLag S T gamma) volume 0 a :=
      hheadInt.mono_set (by
        simpa only [uIcc_of_le hb.le, uIcc_of_le ha0.le] using
          (show Icc (0 : Real) a ⊆ Icc (0 : Real) b from
            fun s hs ↦ ⟨hs.1, hs.2.trans hab.le⟩))
    have htailInt : IntervalIntegrable (lRegLag S T gamma) volume a b :=
      hheadInt.mono_set (by
        simpa only [uIcc_of_le hb.le, uIcc_of_le hab.le] using
          (show Icc a b ⊆ Icc (0 : Real) b from
            fun s hs ↦ ⟨ha0.le.trans hs.1, hs.2⟩))
    have hadd := lRegAction_add (I := I) S T gamma 0 a b hheadInt' htailInt
    have htailEq : fixed y = lRegAction S T gamma a b := by
      rw [show fixed y = lRegAction S T
        (fun s ↦ alpha (hfixed.localInverse y, s)) a b by rfl, hfixed0]
      apply lRegAction_congr (I := I) S T
      intro s hs
      have hs' : s ∈ Ioo a b := by simpa only [uIoo_of_le hab.le] using hs
      exact hcenterEq ⟨hsegK ⟨ha0.le.trans hs'.1.le, hs'.2.le⟩,
        hsegR ⟨ha0.le.trans hs'.1.le, hs'.2.le⟩⟩
    rw [htailEq]
    simpa only [head] using hadd
  have hjoint0 : joint (y, b) = fixed y := by
    simp only [joint, fixed, htime0, hfixed0]
  have htouch : Phi y tau = redLength S T x y tau := by
    rw [show Phi y tau = (head + joint (y, b)) / (2 * b) by
      simp only [Phi, b]]
    rw [hjoint0, hheadTail, hfull]
    rfl
  obtain ⟨Ufix, hUfixOpen, hyUfix, Ffix, hFfixSmooth, hFfixEq⟩ :=
    lTailBranch_smooth S hS T a b hab hVopen hA0V hKopen hKconn
      haK hbK halpha hregFamily hinj
  have hyUfixY : y ∈ Ufix := by
    rw [← hcenterB]
    simpa only [A0, b] using hyUfix
  have hfixedSmoothOn : ContMDiffOn I 𝓘(Real, Real) ∞ fixed Ufix :=
    hFfixSmooth.congr (fun z hz ↦ (hFfixEq z hz).symm)
  have hslice : (fun z : M ↦ (htime.localInverse (z, b)).1) =ᶠ[nhds y]
      hfixed.localInverse := by
    have hsliceRaw : (fun z : M ↦ (htime.localInverse (z, b)).1)
        =ᶠ[nhds (alpha (A0, b))] hfixed.localInverse := by
      simpa only [htime, hfixed, A0, b, gamma] using
        lTailInv_slice hVopen hA0V hKopen hbK halpha hinj
    rw [hcenterB] at hsliceRaw
    exact hsliceRaw
  have hPhiFixed : (fun z : M ↦ Phi z tau) =ᶠ[nhds y]
      (fun z : M ↦ (head + fixed z) / (2 * b)) := by
    have hsrc : {z : M | (z, b) ∈ htime.localInverse.source} ∈ nhds y := by
      have hpair : ContinuousAt (fun z : M ↦ (z, b)) y :=
        continuousAt_id.prodMk continuousAt_const
      apply hpair.preimage_mem_nhds
      have hmem : htime.localInverse.source ∈
          nhds (alpha (A0, b), b) := by
        simpa only [htime, A0, b] using
          htime.localInverse_open_source.mem_nhds htime.localInverse_mem_source
      simpa only [hcenterB] using hmem
    filter_upwards [hslice, hsrc] with z hz hzs
    have hright := htime.localInverse_right_inv hzs
    have hsecond : (htime.localInverse (z, b)).2 = b :=
      congrArg Prod.snd hright
    simp only [Phi]
    rw [show Real.sqrt tau = b by rfl]
    simp only [joint, fixed]
    rw [hsecond, hz]
  have hfixedSmoothAt : ContMDiffAt I 𝓘(Real, Real) ∞ fixed y := by
    exact hfixedSmoothOn.contMDiffAt (hUfixOpen.mem_nhds hyUfixY)
  have hPsiSmoothAt : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun z : M ↦ (head + fixed z) / (2 * b)) y := by
    exact (contMDiffAt_const.add hfixedSmoothAt).div_const (2 * b)
  have hPhiSmoothAt : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun z : M ↦ Phi z tau) y :=
    hPsiSmoothAt.congr_of_eventuallyEq hPhiFixed
  let vel : TangentSpace I (alpha (A0, b)) :=
    lVelocity (I := I) (fun s : Real ↦ alpha (A0, s)) b
  let lag : Real := lRegLag S T (fun s : Real ↦ alpha (A0, s)) b
  let action : Real := lRegAction S T gamma 0 b
  let d : Real := (lag - (S.base.metric (T - b ^ 2)).inner
      (alpha (A0, b)) vel vel) / (4 * b ^ 2) - action / (4 * b ^ 3)
  have hjointM := lTailJoint_mfd S hS T a b hab hVopen hA0V hKopen
    hKconn haK hbK hstart halpha hregFamily
    (fun s hs ↦ hEulerFamily A0 hA0V s (hsegK ⟨ha0.le.trans hs.1, hs.2⟩)) hinj
  let ctime : Real := lag - (S.base.metric (T - b ^ 2)).inner
    (alpha (A0, b)) vel vel
  let Lj : E × Real →L[Real] Real :=
    ((S.base.metric (T - b ^ 2)).inner (alpha (A0, b)) vel).comp
        (ContinuousLinearMap.fst Real E Real) +
      ctime • ContinuousLinearMap.snd Real E Real
  let Lid := ContinuousLinearMap.id Real
    (TangentSpace 𝓘(Real, Real) b)
  let Lq : TangentSpace 𝓘(Real, Real) b →L[Real]
      TangentSpace I y × TangentSpace 𝓘(Real, Real) b :=
    (0 : TangentSpace 𝓘(Real, Real) b →L[Real] TangentSpace I y).prod Lid
  let Lstd : Real →L[Real] Real :=
    ctime • ContinuousLinearMap.id Real Real
  have hjointMY : HasMFDerivAt (I.prod 𝓘(Real, Real)) 𝓘(Real, Real)
      joint (y, b) Lj := by
    rw [← hcenterB]
    simpa only [joint, htime, Lj, ctime, lag, vel, A0, gamma] using hjointM
  have hline : HasMFDerivAt 𝓘(Real, Real)
      (I.prod 𝓘(Real, Real)) (fun r : Real ↦ (y, r)) b Lq := by
    change HasMFDerivAt 𝓘(Real, Real) (I.prod 𝓘(Real, Real))
      (fun r : Real ↦ (y, id r)) b _
    exact (hasMFDerivAt_const (c := y) (x := b)).prodMk
      (hasMFDerivAt_id b)
  have hLcomp : Lj.comp Lq = Lstd := by
    ext
    have hfst : (ContinuousLinearMap.fst Real E Real)
        ((0 : TangentSpace I (alpha (A0, b))), (1 : Real)) = 0 := rfl
    have hsnd : (ContinuousLinearMap.snd Real E Real)
        ((0 : TangentSpace I (alpha (A0, b))), (1 : Real)) = 1 := rfl
    simp only [Lj, Lq, Lid]
    calc
      _ = (S.base.metric (T - b ^ 2)).inner (alpha (A0, b)) vel
            (0 : TangentSpace I (alpha (A0, b))) + ctime * 1 :=
        congrArg₂ (· + ·)
          (congrArg (fun v : TangentSpace I (alpha (A0, b)) ↦
            (S.base.metric (T - b ^ 2)).inner (alpha (A0, b)) vel v) hfst)
          (congrArg (fun r : Real ↦ ctime * r) hsnd)
      _ = _ := by
        rw [map_zero, zero_add, mul_one]
        have hLstd : Lstd 1 = ctime := by
          change ctime * 1 = ctime
          ring
        exact hLstd.symm
  have hjointTime : HasDerivAt (fun r : Real ↦ joint (y, r))
      ctime b := by
    have hcomp := hjointMY.comp b hline
    have hcomp' := hcomp.congr_mfderiv hLcomp
    have hrawF := hcomp'.hasFDerivAt
    have hLstd : Lstd 1 = ctime := by
      change ctime * 1 = ctime
      ring
    have hmap : Lstd = ContinuousLinearMap.toSpanSingleton Real ctime := by
      rw [← ContinuousLinearMap.toSpanSingleton_apply_map_one (R₁ := Real) Lstd, hLstd]
    have hrawF' := hrawF.congr_fderiv hmap
    have heq : joint ∘ Prod.mk y = fun r : Real ↦ joint (y, r) := by
      funext r
      rfl
    rw [heq] at hrawF'
    unfold HasDerivAt HasDerivAtFilter
    unfold HasFDerivAt at hrawF'
    exact hrawF'
  have hjointDeriv : HasDerivAt (fun rho : Real ↦ joint (y, Real.sqrt rho))
      ((lag - (S.base.metric (T - b ^ 2)).inner
        (alpha (A0, b)) vel vel) / (2 * b)) tau := by
    have hcomp := hjointTime.comp tau (Real.hasDerivAt_sqrt htau.ne')
    change HasDerivAt (fun rho : Real ↦ joint (y, Real.sqrt rho))
      (ctime / (2 * b)) tau
    have hcoef : ctime * (1 / (2 * Real.sqrt tau)) = ctime / (2 * b) := by
      change ctime * (1 / (2 * b)) = ctime / (2 * b)
      field_simp [hb.ne']
    have hcomp' := hcomp.congr_deriv hcoef
    have heq : (fun r : Real ↦ joint (y, r)) ∘ Real.sqrt =
        fun rho : Real ↦ joint (y, Real.sqrt rho) := by
      funext rho
      rfl
    rw [heq] at hcomp'
    unfold HasDerivAt HasDerivAtFilter at hcomp' ⊢
    exact hcomp'
  have hnum : HasDerivAt
      (fun rho : Real ↦ head + joint (y, Real.sqrt rho))
      ((lag - (S.base.metric (T - b ^ 2)).inner
        (alpha (A0, b)) vel vel) / (2 * b)) tau :=
    hjointDeriv.const_add head
  have hden : HasDerivAt (fun rho : Real ↦ 2 * Real.sqrt rho)
      (1 / b) tau := by
    have hraw := (Real.hasDerivAt_sqrt htau.ne').const_mul 2
    have hcoef : 2 * (1 / (2 * Real.sqrt tau)) = 1 / b := by
      change 2 * (1 / (2 * b)) = 1 / b
      field_simp [hb.ne']
    exact hraw.congr_deriv hcoef
  have hPhiDeriv : HasDerivAt (Phi y) d tau := by
    have hquot := hnum.div hden (mul_ne_zero (by norm_num) hb.ne')
    apply hquot.congr_deriv
    have hnumAt : head + joint (y, Real.sqrt tau) = action := by
      change head + joint (y, b) = lRegAction S T gamma 0 b
      rw [hjoint0]
      exact hheadTail
    simp only [d]
    rw [hnumAt]
    field_simp [hb.ne']
    ring
  have hlapRaw := lTail_lap_K (I := I) S hS T a b ha0 hab x Z hbdom
    (lMinVec_min_rm (I := I) S hS K T x hZmin hregTau hRmTau)
    hVopen hA0V hKopen hKconn h0K hbK hstart halpha hregFamily
    hEulerFamily hcenter hinj P hOmega hOmegaSeg
    (fun i ↦ (hPsm i).of_le (by decide :
      (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))) hPode hPON
  have hKtail : lKTail S T beta a b = lKTail S T gamma a b := by
    unfold lKTail
    apply congrArg (fun q : Real ↦ 2 * q)
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using hs
    have heq := hcenter s ⟨ha0.le.trans hs'.1, hs'.2⟩
    have hvel : lVelocity (I := I) beta s =
        lVelocity (I := I) gamma s := by
      unfold lVelocity
      change ((mfderiv 𝓘(Real, Real) I (fun r : Real ↦ alpha (A0, r)) s) 1) = _
      rw [heq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
      rfl
    have hpt := heq.self_of_nhds
    have hptBeta : beta s = gamma s := by simpa only [beta] using hpt
    unfold lHamSq
    dsimp only
    rw [hptBeta]
    rw [hvel]
  have hlapFixedBeta : laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - b ^ 2))) (S.base.metric (T - b ^ 2))
        fixed y ≤
      (Module.finrank Real E : Real) / (b - a) -
        2 * b * S.scalar (T - b ^ 2) y -
        lKTail S T beta a b / (b - a) ^ 2 := by
    rw [← hcenterB]
    simpa only [fixed, hfixed, beta] using hlapRaw
  have hlapFixed : laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - b ^ 2))) (S.base.metric (T - b ^ 2))
        fixed y ≤
      (Module.finrank Real E : Real) / (b - a) -
        2 * b * S.scalar (T - b ^ 2) y -
        lKTail S T gamma a b / (b - a) ^ 2 := by
    rw [hKtail] at hlapFixedBeta
    exact hlapFixedBeta
  have hPhiLap : laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - tau))) (S.base.metric (T - tau))
        (fun z : M ↦ Phi z tau) y =
      (1 / (2 * b)) * laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - b ^ 2))) (S.base.metric (T - b ^ 2)) fixed y := by
    rw [← hbSq]
    have hPhiSmoothB : ContMDiffAt I 𝓘(Real, Real) ∞
        (fun z : M ↦ Phi z (b ^ 2)) y := by
      simpa only [hbSq] using hPhiSmoothAt
    have hPhiFixedB : (fun z : M ↦ Phi z (b ^ 2)) =ᶠ[nhds y]
        (fun z : M ↦ (head + fixed z) / (2 * b)) := by
      simpa only [hbSq] using hPhiFixed
    have hcongr := laplacian_congr_of_eventuallyEq (I := I)
      (LeviCivita (I := I) (S.base.metric (T - b ^ 2)))
      (S.base.metric (T - b ^ 2))
      (f := fun z : M ↦ Phi z (b ^ 2))
      (h := fun z : M ↦ (head + fixed z) / (2 * b)) (x := y)
      hPhiSmoothB hPsiSmoothAt hPhiFixedB
    rw [hcongr]
    have hnorm : (fun z : M ↦ (head + fixed z) / (2 * b)) =
        (1 / (2 * b)) • (fun z : M ↦ head + fixed z) := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hnorm]
    have hfixedMD : ∀ᶠ z in nhds y,
        MDifferentiableAt I 𝓘(Real, Real) fixed z := by
      filter_upwards [hUfixOpen.mem_nhds hyUfixY] with z hz
      exact (hfixedSmoothOn.contMDiffAt
        (hUfixOpen.mem_nhds hz)).mdifferentiableAt (by simp)
    have hfixedGrad := gradientFun_mdiffOn (E := E) (I := I) (M := M)
      (U := Ufix) (f := fixed) (x := y) (S.base.metric (T - b ^ 2))
      hUfixOpen hfixedSmoothOn hyUfixY
    have haddMD : ∀ᶠ z in nhds y,
        MDifferentiableAt I 𝓘(Real, Real) (fun w : M ↦ head + fixed w) z := by
      filter_upwards [hfixedMD] with z hz
      exact mdifferentiableAt_const.add hz
    have haddSmoothOn : ContMDiffOn I 𝓘(Real, Real) ∞
        (fun z : M ↦ head + fixed z) Ufix :=
      contMDiffOn_const.add hfixedSmoothOn
    have haddGrad := gradientFun_mdiffOn (E := E) (I := I) (M := M)
      (U := Ufix) (f := fun z : M ↦ head + fixed z) (x := y)
      (S.base.metric (T - b ^ 2)) hUfixOpen haddSmoothOn hyUfixY
    rw [laplacian_smul_at (I := I) _ _ _ haddMD haddGrad]
    rw [laplacian_add_const (I := I) _ _ head hfixedMD hfixedGrad]
  have henergy := lK_ray_energy S hS T x Z hb hbdom
  have hlagEq : lag = lRegLag S T gamma b := by
    have heq := hcenter b ⟨hb.le, le_rfl⟩
    have hptBeta : beta b = gamma b := by
      simpa only [beta] using heq.self_of_nhds
    have hvelEq : lVelocity (I := I) beta b =
        lVelocity (I := I) gamma b := by
      unfold lVelocity
      change ((mfderiv 𝓘(Real, Real) I (fun r : Real ↦ alpha (A0, r)) b) 1) = _
      rw [heq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
      rfl
    unfold lag
    change lRegLag S T beta b = lRegLag S T gamma b
    dsimp only [lRegLag]
    rw [hptBeta]
    rw [show lVelocity (I := I) beta b = lVelocity (I := I) gamma b from hvelEq]
  have hvelEq : (S.base.metric (T - b ^ 2)).inner
      (alpha (A0, b)) vel vel =
      (S.base.metric (T - b ^ 2)).inner (gamma b)
        (lVelocity (I := I) gamma b) (lVelocity (I := I) gamma b) := by
    have heq := hcenter b ⟨hb.le, le_rfl⟩
    have hv : lVelocity (I := I) beta b =
        lVelocity (I := I) gamma b := by
      unfold lVelocity
      change ((mfderiv 𝓘(Real, Real) I (fun r : Real ↦ alpha (A0, r)) b) 1) = _
      rw [heq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
      rfl
    rw [show alpha (A0, b) = gamma b from heq.self_of_nhds]
    simpa only [vel, beta] using congrArg
      (fun v : TangentSpace I (gamma b) ↦
        (S.base.metric (T - b ^ 2)).inner (gamma b) v v) hv
  have hpre : d + laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - tau))) (S.base.metric (T - tau))
        (fun z : M ↦ Phi z tau) y ≤
      (Module.finrank Real E : Real) / (2 * b * (b - a)) -
        Phi y tau / b ^ 2 + kval / (2 * b ^ 3) -
        lKTail S T gamma a b / (2 * b * (b - a) ^ 2) := by
    rw [hPhiLap]
    have hPhiAction : Phi y tau = lRegAction S T gamma 0 b / (2 * b) := by
      rw [htouch, redLength, hfull]
    have hbaseEq : alpha (A0, b) = gamma b :=
      (hcenter b ⟨hb.le, le_rfl⟩).self_of_nhds
    let speed : Real := (S.base.metric (T - b ^ 2)).inner (gamma b)
      (lVelocity (I := I) gamma b) (lVelocity (I := I) gamma b)
    have hspeed : (S.base.metric (T - b ^ 2)).inner
        (alpha (A0, b)) vel vel = speed := by
      simpa only [speed] using hvelEq
    have hgammaB : gamma b = y := hbaseEq.symm.trans hcenterB
    have hlagShape : lag = (1 / 2 : Real) * speed +
        2 * b ^ 2 * S.scalar (T - b ^ 2) y := by
      rw [hlagEq]
      dsimp only [lRegLag]
      simp only [speed]
      rw [hgammaB]
    have henergy' : kval = (action - b * lag) / 2 := by
      rw [hlagEq]
      simpa only [kval, action, gamma] using henergy
    have hdNorm : d = S.scalar (T - b ^ 2) y - Phi y tau / b ^ 2 +
        kval / (2 * b ^ 3) := by
      unfold d
      rw [hspeed, hPhiAction, henergy', hlagShape]
      field_simp [hb.ne']
      ring
    have hbma : 0 < b - a := sub_pos.mpr hab
    have hscale' : (1 / (2 * b)) * laplacian (I := I)
          (LeviCivita (I := I) (S.base.metric (T - b ^ 2)))
          (S.base.metric (T - b ^ 2)) fixed y ≤
        (Module.finrank Real E : Real) / (2 * b * (b - a)) -
          S.scalar (T - b ^ 2) y -
          lKTail S T gamma a b / (2 * b * (b - a) ^ 2) := by
      calc
        _ ≤ (1 / (2 * b)) *
            ((Module.finrank Real E : Real) / (b - a) -
              2 * b * S.scalar (T - b ^ 2) y -
              lKTail S T gamma a b / (b - a) ^ 2) :=
          mul_le_mul_of_nonneg_left hlapFixed
            (by positivity : 0 ≤ 1 / (2 * b))
        _ = _ := by
          field_simp [hb.ne', hbma.ne']
    rw [hdNorm]
    linarith [hscale']
  have hfinal : d + laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - tau))) (S.base.metric (T - tau))
        (fun z : M ↦ Phi z tau) y ≤
      ((Module.finrank Real E : Real) / 2 - redLength S T x y tau) / tau + eps := by
    calc
      _ ≤ (Module.finrank Real E : Real) / (2 * b * (b - a)) -
          Phi y tau / b ^ 2 + kval / (2 * b ^ 3) -
          lKTail S T gamma a b / (2 * b * (b - a) ^ 2) := hpre
      _ ≤ (Module.finrank Real E : Real) / (2 * b ^ 2) -
          Phi y tau / b ^ 2 + eps := by linarith [herr]
      _ = ((Module.finrank Real E : Real) / 2 -
          redLength S T x y tau) / tau + eps := by
        rw [htouch, hbSq]
        field_simp [htau.ne']
  have hPhiEqMem : {z : M |
      Phi z tau = (head + fixed z) / (2 * b)} ∈ nhds y := by
    change ∀ᶠ z in nhds y, Phi z tau = (head + fixed z) / (2 * b)
    exact hPhiFixed
  obtain ⟨W, hWsub, hWopen, hyW⟩ := mem_nhds_iff.mp hPhiEqMem
  let U' : Set M := (U ∩ Ufix) ∩ W
  have hU'open : IsOpen U' := (hUopen.inter hUfixOpen).inter hWopen
  have hyU' : y ∈ U' := ⟨⟨hyU, hyUfixY⟩, hyW⟩
  have hPhiSmooth : ContMDiffOn I 𝓘(Real, Real) ∞
      (fun z : M ↦ Phi z tau) U' := by
    intro z hz
    have hPsi : ContMDiffAt I 𝓘(Real, Real) ∞
        (fun w : M ↦ (head + fixed w) / (2 * b)) z := by
      have hfixz : ContMDiffAt I 𝓘(Real, Real) ∞ fixed z := by
        exact hfixedSmoothOn.contMDiffAt (hUfixOpen.mem_nhds hz.1.2)
      exact (contMDiffAt_const.add hfixz).div_const (2 * b)
    have hEq : (fun w : M ↦ Phi w tau) =ᶠ[nhds z]
        (fun w : M ↦ (head + fixed w) / (2 * b)) :=
      Filter.eventuallyEq_of_mem (hWopen.mem_nhds hz.2) hWsub
    exact (hPsi.congr_of_eventuallyEq hEq).contMDiffWithinAt
  refine ⟨U', J, Phi, d, hU'open, hyU', hJopen, htauJ, hJsub, ?_,
    htouch, hPhiSmooth, hPhiDeriv, hfinal⟩
  intro z hz rho hrho
  exact hsupport z hz.1.1 rho hrho

end DifferentialGeometry.PDE.RicciFlow.Perelman
