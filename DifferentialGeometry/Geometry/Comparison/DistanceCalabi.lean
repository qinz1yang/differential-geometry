import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Comparison.Variation.MinimizingNoConj
import DifferentialGeometry.Geometry.Comparison.RadialLaplacian
import DifferentialGeometry.Geometry.Comparison.Volume.BishopIntrinsic
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
import DifferentialGeometry.Geometry.Exponential.ExpInvBranch
import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Metric.DistanceScaling

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Explicit-metric distance bounds for Calabi broken paths

This file exposes the standard distance-bounded-by-length inequality with the
smooth Riemannian metric supplied explicitly.  It also packages the two-arc
broken-path estimate used by point-centered Calabi upper supports.
-/

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry

open Geometry.Riemannian
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.HopfRinow
open Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [Module.Finite Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The deterministic fixed-first data selected from a finite-distance
minimizing geodesic at the Calabi split time `1 / 4`.

The selected branch contains the nonzero terminal launch vector and remains
nonconjugate on an open interval extending beyond time one. -/
structure CalabiTailData
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (O x : M) (r : Real) where
  p : M
  u : TangentSpace I p
  left : Real
  ell : Real
  branch : ExpInvBranch (I := I) g hEnorm p
  b : Real
  left_pos : 0 < left
  left_nonneg : 0 ≤ left
  ell_pos : 0 < ell
  split : left + ell = r
  half_le : r / 2 ≤ ell
  left_edist : riemannianEDist I O p = ENNReal.ofReal left
  u_norm : Real.sqrt (g.inner p u u) = ell
  source_mem : (u : E) ∈ branch.hom.source
  map_eq : branch.hom (u : E) = x
  one_lt : 1 < b
  no_conj :
    ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The selected tail vector exponentiates to the terminal point. -/
theorem CalabiTailData.exp_eq
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {O x : M} {r : Real}
    (tail : CalabiTailData (I := I) g hEnorm O x r) :
    expMapIntrinsic (I := I) g hEnorm tail.p tail.u = x :=
  (tail.branch.hom_eq tail.source_mem).trans tail.map_eq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The terminal point lies in the target of the selected fixed-first branch. -/
theorem CalabiTailData.target_mem
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {O x : M} {r : Real}
    (tail : CalabiTailData (I := I) g hEnorm O x r) :
    x ∈ tail.branch.dom := by
  have hmem : tail.branch.hom (tail.u : E) ∈ tail.branch.hom.target :=
    tail.branch.hom.map_source tail.source_mem
  rw [tail.map_eq] at hmem
  exact hmem

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A finite-distance minimizing geodesic supplies the deterministic
quarter-split Calabi tail, together with a fixed-first inverse branch and a
nonconjugate radial interval extending past its endpoint. -/
theorem exists_calabiTail
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    {O x : M} {r : Real} (v : TangentSpace I O)
    (hexp : expMapIntrinsic (I := I) g hEnorm O v = x)
    (hlen : Real.sqrt (g.inner O v v) = r)
    (hr : 0 < r)
    (hr_def : r = (riemannianEDist I O x).toReal) :
    Nonempty (CalabiTailData (I := I) g hEnorm O x r) := by
  classical
  let s₀ : Real := 1 / 4
  let z : TangentBundle I M :=
    intrinsicVelocityLift (I := I) g hEnorm O v s₀
  let u : TangentSpace I z.proj := (1 - s₀) • z.snd
  let left : Real := s₀ * r
  let ell : Real := (1 - s₀) * r
  have hs₀ : s₀ ∈ Set.Ioo (0 : Real) 1 := by
    dsimp [s₀]
    norm_num
  have hs₀_closed : s₀ ∈ Set.Icc (0 : Real) 1 :=
    ⟨hs₀.1.le, hs₀.2.le⟩
  have hfin : riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hr_def
    linarith
  have hlen_dist :
      Real.sqrt (g.inner O v v) =
        (riemannianEDist I O x).toReal :=
    hlen.trans hr_def
  have hnot :
      ¬ IsConjVec (I := I) g hEnorm z.proj (u : E) := by
    simpa only [z, u] using
      Geometry.Riemannian.Variation.tail_not_conj_of_min
        (I := I) g hEnorm v hexp hlen_dist
          (hr_def ▸ hr) hs₀
  obtain ⟨B, hsource⟩ :=
    branch_of_not_conj (I := I) g hEnorm hnot
  have hexp_tail :
      expMapIntrinsic (I := I) g hEnorm z.proj u = x := by
    have hcontinue :=
      congrFun
        (intrinsicGeodesic_continuation
          (I := I) g hEnorm O v s₀) (1 - s₀)
    have hend :
        intrinsicGeodesic (I := I) g hEnorm O v 1 = x := by
      simpa only [expMapIntrinsic_def] using hexp
    change intrinsicGeodesic (I := I) g hEnorm z.proj u 1 = x
    dsimp only [u]
    rw [intrinsicGeodesic_smul (I := I) g hEnorm]
    rw [show z.proj =
        intrinsicGeodesic (I := I) g hEnorm O v s₀ by
          exact velocityLift_proj (I := I) g hEnorm O v s₀]
    rw [show z.snd =
        (mfderiv 𝓘(Real, Real) I
          (intrinsicGeodesic (I := I) g hEnorm O v) s₀ :
            Real →L[Real] TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm O v s₀)) 1 by rfl]
    calc
      intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm O v s₀)
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm O v) s₀ 1)
          (1 - s₀) =
          intrinsicGeodesic (I := I) g hEnorm O v (1 - s₀ + s₀) :=
        hcontinue.symm
      _ = intrinsicGeodesic (I := I) g hEnorm O v 1 := by
        congr 1
        ring
      _ = x := hend
  have hmap_eq : B.hom (u : E) = x :=
    (B.hom_eq hsource).symm.trans hexp_tail
  have hscale_cont : Continuous (fun t : Real => t • (u : E)) :=
    continuous_id.smul continuous_const
  have hsource_nhds :
      {t : Real | t • (u : E) ∈ B.hom.source} ∈ 𝓝 (1 : Real) := by
    apply hscale_cont.continuousAt.preimage_mem_nhds
    simpa only [one_smul] using B.hom.open_source.mem_nhds hsource
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.mp hsource_nhds
  let b : Real := 1 + ε / 2
  have hb : 1 < b := by
    dsimp [b]
    linarith
  have hsource_tail :
      ∀ t ∈ Set.Icc (1 : Real) b,
        t • (u : E) ∈ B.hom.source := by
    intro t ht
    apply hε_sub
    rw [Metric.mem_ball, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr ht.1)]
    dsimp [b] at ht
    calc
      t - 1 ≤ ε / 2 := by linarith [ht.2]
      _ < ε := by linarith [hε]
  have htail_no :
      ∀ t ∈ Set.Ioc (0 : Real) 1,
        ¬ IsConjVec (I := I) g hEnorm z.proj
          ((t • u : TangentSpace I z.proj) : E) := by
    simpa only [z, u] using
      Geometry.Riemannian.Variation.tail_no_conj
        (I := I) g hEnorm v hexp hlen_dist
          (hr_def ▸ hr) hs₀
  have hno :
      ∀ t ∈ Set.Ioo (0 : Real) b,
        ¬ IsConjVec (I := I) g hEnorm z.proj
          ((t • u : TangentSpace I z.proj) : E) := by
    intro t ht
    rcases le_total t 1 with ht1 | h1t
    · exact htail_no t ⟨ht.1, ht1⟩
    · exact B.not_conj (hsource_tail t ⟨h1t, ht.2.le⟩)
  have hspeed :
      g.inner z.proj z.snd z.snd = g.inner O v v := by
    simpa only [z, intrinsicVelocityLift] using
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm O v s₀
  have hu_norm :
      Real.sqrt (g.inner z.proj u u) = ell := by
    dsimp only [u]
    rw [sqrt_gInner_smul_self (I := I) g z.proj
      (sub_nonneg.mpr hs₀.2.le) z.snd, hspeed, hlen]
  have hleft :
      riemannianEDist I O z.proj = ENNReal.ofReal left := by
    simpa only [z, velocityLift_proj, left] using
      Geometry.Riemannian.Variation.minSeg_edist
        (I := I) g hEnorm v hexp hlen hr_def hfin hs₀_closed
  have hleftPos : 0 < left := by
    dsimp [left, s₀]
    positivity
  refine ⟨{
    p := z.proj
    u := u
    left := left
    ell := ell
    branch := B
    b := b
    left_pos := hleftPos
    left_nonneg := hleftPos.le
    ell_pos := by
      dsimp [ell, s₀]
      linarith
    split := by
      dsimp [left, ell]
      ring
    half_le := by
      dsimp [ell, s₀]
      linarith
    left_edist := hleft
    u_norm := hu_norm
    source_mem := hsource
    map_eq := hmap_eq
    one_lt := hb
    no_conj := hno
  }⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A finite nonbase point has selected Calabi-tail data whose explicit
fixed-first branch radius is a smooth upper support with the standard
Ricci-lower-bound Laplacian estimate. -/
theorem exists_calabiData
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (q : Real) (hq : 0 ≤ q)
    (hRic : Geometry.Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    {O x : M} (hOx : O ≠ x)
    (hfin : riemannianEDist I O x ≠ (⊤ : ENNReal)) :
    let r := (riemannianEDist I O x).toReal
    ∃ tail : CalabiTailData (I := I) g hEnorm O x r,
      let rho : M → Real := fun y =>
        tail.left + branchRadius (I := I) g tail.branch y
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      rho x = r ∧
      (∀ᶠ y in 𝓝 x,
        (riemannianEDist I O y).toReal ≤ rho y) ∧
      (∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) rho y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (T% fun y : M => gradientFun (I := I) g rho y) x ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 ∧
      laplacian (I := I)
          (LeviCivita (I := I) g) g rho x ≤
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  classical
  dsimp only
  let r : Real := (riemannianEDist I O x).toReal
  have hdist_ne : riemannianEDist I O x ≠ 0 := by
    intro hzero
    exact hOx (riemannianEDist_eq_zero_imp_eq (I := I) O x hzero)
  have hr : 0 < r := by
    exact ENNReal.toReal_pos hdist_ne hfin
  obtain ⟨v, hexp, hlen⟩ :=
    minExp_of_ne_top (I := I) g hEnorm O x hfin
  obtain ⟨tail⟩ :=
    exists_calabiTail (I := I) g hEnorm v hexp hlen hr rfl
  have hsqrt_pos :
      0 < Real.sqrt (g.inner tail.p tail.u tail.u) := by
    rw [tail.u_norm]
    exact tail.ell_pos
  have hu_pos : 0 < g.inner tail.p tail.u tail.u :=
    Real.sqrt_pos.mp hsqrt_pos
  obtain ⟨w, hwLI, hwperp, hmean⟩ :=
    Geometry.Riemannian.VolumeComparison.exists_intrMean
      (I := I) g hEnorm tail.p tail.u q tail.b
        hq tail.one_lt hu_pos tail.no_conj hRic
  let rho : M → Real := fun y =>
    tail.left + branchRadius (I := I) g tail.branch y
  have hbr_inf :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (branchRadius (I := I) g tail.branch) x := by
    have h :=
      branchRadius_infAt (I := I) tail.branch tail.source_mem hu_pos
    rw [tail.exp_eq] at h
    exact h
  have hrho_inf : ContMDiffAt I 𝓘(Real, Real) ∞ rho x := by
    exact contMDiffAt_const.add hbr_inf
  have hrad_x :
      branchRadius (I := I) g tail.branch x = tail.ell := by
    calc
      branchRadius (I := I) g tail.branch x =
          branchRadius (I := I) g tail.branch
            (expMapIntrinsic (I := I) g hEnorm tail.p tail.u) :=
        congrArg (branchRadius (I := I) g tail.branch) tail.exp_eq.symm
      _ = Real.sqrt (g.inner tail.p tail.u tail.u) :=
        branchRadius_exp (I := I) tail.branch tail.source_mem
      _ = tail.ell := tail.u_norm
  have hrho_x : rho x = r := by
    dsimp only [rho]
    rw [hrad_x, tail.split]
  have hupper :
      ∀ᶠ y in 𝓝 x,
        (riemannianEDist I O y).toReal ≤ rho y := by
    filter_upwards [
      tail.branch.hom.open_target.mem_nhds tail.target_mem] with y hy
    have hrad_nonneg :
        0 ≤ branchRadius (I := I) g tail.branch y :=
      Real.sqrt_nonneg _
    have hdist :
        riemannianEDist I O y ≤
          ENNReal.ofReal tail.left +
            ENNReal.ofReal
              (branchRadius (I := I) g tail.branch y) := by
      calc
        riemannianEDist I O y ≤
            riemannianEDist I O tail.p +
              riemannianEDist I tail.p y :=
          Manifold.riemannianEDist_triangle
        _ ≤ ENNReal.ofReal tail.left +
              ENNReal.ofReal
                (branchRadius (I := I) g tail.branch y) := by
          exact add_le_add tail.left_edist.le
            (tail.branch.edist_le_radius hy)
    have hreal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hdist
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal tail.left_nonneg,
      ENNReal.toReal_ofReal hrad_nonneg] at hreal
    exact hreal
  have hbr_diff :
      MDifferentiableAt I 𝓘(Real, Real)
        (branchRadius (I := I) g tail.branch) x :=
    hbr_inf.mdifferentiableAt (by simp)
  have hgrad_rho :
      gradientFun (I := I) g rho x =
        gradientFun (I := I) g
          (branchRadius (I := I) g tail.branch) x := by
    calc
      gradientFun (I := I) g rho x =
          gradientFun (I := I) g (fun _ : M => tail.left) x +
            gradientFun (I := I) g
              (branchRadius (I := I) g tail.branch) x := by
        exact gradientFun_add (I := I) g
          mdifferentiableAt_const hbr_diff
      _ = gradientFun (I := I) g
            (branchRadius (I := I) g tail.branch) x := by
        rw [gradientFun_const, zero_add]
  have hgrad_br :
      gradientFun (I := I) g
          (branchRadius (I := I) g tail.branch) x =
        (Real.sqrt (g.inner tail.p tail.u tail.u))⁻¹ •
          (intrinsicVelocityLift
            (I := I) g hEnorm tail.p tail.u 1).snd := by
    have h :=
      grad_branchRadius
        (I := I) tail.branch tail.source_mem hu_pos
    rw [tail.exp_eq] at h
    exact h
  have hspeed :
      g.inner x
          (intrinsicVelocityLift
            (I := I) g hEnorm tail.p tail.u 1).snd
          (intrinsicVelocityLift
            (I := I) g hEnorm tail.p tail.u 1).snd =
        g.inner tail.p tail.u tail.u := by
    have h :=
      intrinsicGeodesic_speedSq_eq
        (I := I) g hEnorm tail.p tail.u 1
    rw [← expMapIntrinsic_def, tail.exp_eq] at h
    simpa only [intrinsicVelocityLift] using h
  have hu_sq :
      g.inner tail.p tail.u tail.u = tail.ell ^ 2 := by
    have hsq :=
      Real.sq_sqrt
        (gInner_self_nonneg (I := I) g tail.p tail.u)
    rw [tail.u_norm] at hsq
    exact hsq.symm
  let Vx : TangentSpace I x :=
    show TangentSpace I x from
      ((intrinsicVelocityLift
        (I := I) g hEnorm tail.p tail.u 1).snd : E)
  have hgrad_br' :
      gradientFun (I := I) g
          (branchRadius (I := I) g tail.branch) x =
        (Real.sqrt (g.inner tail.p tail.u tail.u))⁻¹ • Vx := by
    simpa only [Vx] using hgrad_br
  have hspeed' :
      g.inner x Vx Vx = g.inner tail.p tail.u tail.u := by
    simpa only [Vx] using hspeed
  have hgrad_norm :
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 := by
    rw [hgrad_rho, hgrad_br',
      gInner_smul_self (I := I) g x, hspeed', tail.u_norm,
      hu_sq]
    field_simp [tail.ell_pos.ne']
  obtain ⟨U, hUopen, hxU, hbrU⟩ :=
    branchRadius_open
      (I := I) tail.branch tail.source_mem hu_pos
  rw [tail.exp_eq] at hxU
  have hrhoU :
      ContMDiffOn I 𝓘(Real, Real) ∞ rho U := by
    simpa only [rho] using
      (contMDiffOn_const.add hbrU)
  have hrho_ev :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) rho y := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact
      ((hrhoU y hy).contMDiffAt
        (hUopen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hrho_grad :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) g rho y) x :=
    gradientFun_mdiffOn (I := I) g hUopen hrhoU hxU
  have hbr_ev :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real)
          (branchRadius (I := I) g tail.branch) y := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact
      ((hbrU y hy).contMDiffAt
        (hUopen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hbr_grad :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) g
            (branchRadius (I := I) g tail.branch) y) x :=
    gradientFun_mdiffOn (I := I) g hUopen hbrU hxU
  have hlap_rho :
      laplacian (I := I) (LeviCivita (I := I) g) g rho x =
        laplacian (I := I) (LeviCivita (I := I) g) g
          (branchRadius (I := I) g tail.branch) x := by
    exact laplacian_add_const
      (I := I) (LeviCivita (I := I) g) g tail.left hbr_ev hbr_grad
  have hlap_br :=
    branchLap_eq_mean
      (I := I) g hEnorm tail.branch tail.u w
        tail.source_mem hu_pos hwLI hwperp (by simp)
  dsimp only at hlap_br
  rw [← expMapIntrinsic_def, tail.exp_eq, tail.u_norm] at hlap_br
  dsimp only at hmean
  rw [tail.u_norm] at hmean
  have hlap_bound :
      laplacian (I := I) (LeviCivita (I := I) g) g rho x ≤
        ((Module.finrank Real E - 1 : Nat) : Real) / tail.ell +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
    rw [hlap_rho, hlap_br]
    exact hmean
  have hfrac :
      ((Module.finrank Real E - 1 : Nat) : Real) / tail.ell ≤
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r := by
    apply (div_le_iff₀ tail.ell_pos).2
    rw [show
      2 * ((Module.finrank Real E - 1 : Nat) : Real) / r * tail.ell =
        (2 * ((Module.finrank Real E - 1 : Nat) : Real) * tail.ell) / r by
          ring]
    apply (le_div_iff₀ hr).2
    have hn :
        0 ≤ ((Module.finrank Real E - 1 : Nat) : Real) :=
      Nat.cast_nonneg _
    have hrell : r ≤ 2 * tail.ell := by
      linarith [tail.half_le]
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hrell)]
  refine ⟨tail, hrho_inf, hrho_x, hupper, hrho_ev, hrho_grad,
    hgrad_norm, ?_⟩
  linarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The distance from `O` admits a smooth Calabi upper support at every finite
nonbase point, with the standard Ricci-lower-bound Laplacian estimate. -/
theorem calabiDist_support
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (q : Real) (hq : 0 ≤ q)
    (hRic : Geometry.Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    {O x : M} (hOx : O ≠ x)
    (hfin : riemannianEDist I O x ≠ (⊤ : ENNReal)) :
    let r := (riemannianEDist I O x).toReal
    ∃ rho : M → Real,
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      rho x = r ∧
      (∀ᶠ y in 𝓝 x,
        (riemannianEDist I O y).toReal ≤ rho y) ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) ≤ 1 ∧
      laplacian (I := I)
          (LeviCivita (I := I) g) g rho x ≤
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  dsimp only
  obtain ⟨tail, hrho_inf, hrho_x, hupper, _hrho_ev, _hrho_grad,
      hgrad_norm, hlap⟩ :=
    exists_calabiData (I := I) g hEnorm q hq hRic hOx hfin
  exact
    ⟨fun y => tail.left + branchRadius (I := I) g tail.branch y,
      hrho_inf, hrho_x, hupper, hgrad_norm.le, hlap⟩

private theorem continuousAt_fiber_smul
    {X B F : Type*} [TopologicalSpace X] [TopologicalSpace B]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module Real (V b)]
    [∀ b, TopologicalSpace (V b)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle Real F V]
    {b : X → B} {v : ∀ x, V (b x)} {a : X → Real} {x₀ : X}
    (hv : ContinuousAt (fun x => TotalSpace.mk' F (b x) (v x)) x₀)
    (ha : ContinuousAt a x₀) :
    ContinuousAt (fun x => TotalSpace.mk' F (b x) (a x • v x)) x₀ := by
  rw [FiberBundle.continuousAt_totalSpace] at hv ⊢
  refine ⟨hv.1, ?_⟩
  let e := trivializationAt F V (b x₀)
  have hb : ∀ᶠ x in 𝓝 x₀, b x ∈ e.baseSet :=
    hv.1 (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (b x₀)))
  have heq :
      (fun x => (e (TotalSpace.mk' F (b x) (a x • v x))).2) =ᶠ[𝓝 x₀]
        fun x => a x • (e (TotalSpace.mk' F (b x) (v x))).2 := by
    filter_upwards [hb] with x hx
    exact (e.linear Real hx).map_smul (a x) (v x)
  exact (ha.smul hv.2).congr_of_eventuallyEq heq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The extended distance of an explicitly supplied Riemannian metric is at
most the arc length of any `C¹` curve joining the endpoints. -/
theorem edistOf_le_arcLength
    (g : SmoothRiemannianMetric I M) {γ : Real → M} {a b : Real}
    (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b)) :
    riemannianEDistOf (I := I) g (γ a) (γ b) ≤
      ENNReal.ofReal
        (Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  change riemannianEDist I (γ a) (γ b) ≤ _
  apply Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength
    (I := I) g hab hγ
  intro t ht
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
  congr 2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A broken path made of two `C¹` arcs bounds the explicit Riemannian
extended distance by the sum of their arc lengths. -/
theorem edistOf_le_two_arcs
    (g : SmoothRiemannianMetric I M)
    {γ δ : Real → M} {a b c d : Real}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b))
    (hδ : ContMDiffOn 𝓘(Real, Real) I 1 δ (Set.Icc c d))
    (hjoin : γ b = δ c) :
    riemannianEDistOf (I := I) g (γ a) (δ d) ≤
      ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) +
        ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g δ c d) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  change riemannianEDist I (γ a) (δ d) ≤ _
  calc
    riemannianEDist I (γ a) (δ d) ≤
        riemannianEDist I (γ a) (γ b) +
          riemannianEDist I (γ b) (δ d) :=
      Manifold.riemannianEDist_triangle
    _ = riemannianEDist I (γ a) (γ b) +
          riemannianEDist I (δ c) (δ d) := by rw [hjoin]
    _ ≤ ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) +
        ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g δ c d) :=
      add_le_add
        (edistOf_le_arcLength (I := I) g hab hγ)
        (edistOf_le_arcLength (I := I) g hcd hδ)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A minimizing intrinsic geodesic from `O` to `x` admits a terminal point
strictly before `x` whose remaining velocity lies in a prescribed inverse
branch centered at `x`. -/
theorem calabi_tail_of
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (O x : M) (hOx : riemannianEDist I O x ≠ ⊤)
    (B : DiagInvBranch (I := I) g hEnorm x) :
    ∃ (v : TangentSpace I O) (s₀ : Real),
      expMapIntrinsic (I := I) g hEnorm O v = x ∧
      Real.sqrt (g.inner O v v) = (riemannianEDist I O x).toReal ∧
      0 < s₀ ∧ s₀ < 1 ∧
      let velocity : Real → TangentBundle I M :=
        intrinsicVelocityLift (I := I) g hEnorm O v
      let tail : Real → TangentBundle I M := fun s =>
        ⟨(velocity s).proj, (1 - s) • (velocity s).snd⟩
      tail s₀ ∈ B.hom.source ∧
        ((tail s₀).proj, x) ∈ B.dom ∧
        expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd = x ∧
        B.inv ((tail s₀).proj, x) = tail s₀ := by
  obtain ⟨v, hvx, hvmin⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
      (I := I) g hEnorm O x hOx
  let velocity : Real → TangentBundle I M :=
    intrinsicVelocityLift (I := I) g hEnorm O v
  let tail : Real → TangentBundle I M := fun s =>
    ⟨(velocity s).proj, (1 - s) • (velocity s).snd⟩
  have hvelocity : Continuous velocity :=
    (lift_isIntegral (I := I) g hEnorm O v).continuous
  have htail : ContinuousAt tail 1 := by
    apply continuousAt_fiber_smul hvelocity.continuousAt
    fun_prop
  have hvelocity_one : (velocity 1).proj = x := by
    change intrinsicGeodesic (I := I) g hEnorm O v 1 = x
    simpa only [expMapIntrinsic_def] using hvx
  have htail_one :
      tail 1 = (⟨x, (0 : TangentSpace I x)⟩ : TangentBundle I M) := by
    apply TotalSpace.ext hvelocity_one
    apply heq_of_eq
    simp only [tail, sub_self, zero_smul]
    rfl
  have htail_mem : tail 1 ∈ B.hom.source := by
    rw [htail_one]
    exact B.zero_mem
  have hsource_nhds : {s : Real | tail s ∈ B.hom.source} ∈ 𝓝 (1 : Real) :=
    htail.preimage_mem_nhds (B.hom.open_source.mem_nhds htail_mem)
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.mp hsource_nhds
  let d : Real := min ε 1 / 2
  let s₀ : Real := 1 - d
  have hd_pos : 0 < d := by
    dsimp [d]
    exact half_pos (lt_min hε zero_lt_one)
  have hd_lt_one : d < 1 := by
    dsimp [d]
    nlinarith [min_le_right ε (1 : Real)]
  have hd_lt_ε : d < ε := by
    dsimp [d]
    nlinarith [min_le_left ε (1 : Real), lt_min hε zero_lt_one]
  have hs₀_pos : 0 < s₀ := by
    dsimp [s₀]
    linarith
  have hs₀_lt : s₀ < 1 := by
    dsimp [s₀]
    linarith
  have hs₀_ball : s₀ ∈ Metric.ball (1 : Real) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have : |s₀ - 1| = d := by
      dsimp [s₀]
      rw [abs_of_nonpos]
      · ring
      · linarith
    rw [this]
    exact hd_lt_ε
  have hs₀_source : tail s₀ ∈ B.hom.source := hε_sub hs₀_ball
  have hs₀_exp :
      expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd = x := by
    have hcontinue :=
      congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm O v s₀) (1 - s₀)
    have hend :
        intrinsicGeodesic (I := I) g hEnorm O v 1 = x := by
      simpa only [expMapIntrinsic_def] using hvx
    change intrinsicGeodesic (I := I) g hEnorm (velocity s₀).proj
      ((1 - s₀) • (velocity s₀).snd) 1 = x
    rw [intrinsicGeodesic_smul (I := I) g hEnorm]
    rw [show (velocity s₀).proj =
        intrinsicGeodesic (I := I) g hEnorm O v s₀ by
          exact velocityLift_proj (I := I) g hEnorm O v s₀]
    rw [show (velocity s₀).snd =
        (mfderiv 𝓘(Real, Real) I
          (intrinsicGeodesic (I := I) g hEnorm O v) s₀ :
            Real →L[Real] TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm O v s₀)) 1 by rfl]
    calc
      intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm O v s₀)
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm O v) s₀ 1)
          (1 - s₀) =
          intrinsicGeodesic (I := I) g hEnorm O v (1 - s₀ + s₀) :=
        hcontinue.symm
      _ = intrinsicGeodesic (I := I) g hEnorm O v 1 := by
        congr 1
        ring
      _ = x := hend
  have hs₀_dom : ((tail s₀).proj, x) ∈ B.dom := by
    have hmap : B.hom (tail s₀) ∈ B.hom.target :=
      B.hom.map_source hs₀_source
    have hhom : B.hom (tail s₀) = ((tail s₀).proj, x) := by
      have hdiag :
          diagExp (I := I) g hEnorm (tail s₀) = ((tail s₀).proj, x) := by
        change ((tail s₀).proj,
          expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd) =
            ((tail s₀).proj, x)
        rw [hs₀_exp]
      change (fun u ↦ B.hom u) (tail s₀) = ((tail s₀).proj, x)
      exact (B.hom_eq hs₀_source).trans hdiag
    change ((tail s₀).proj, x) ∈ B.hom.target
    rwa [← hhom]
  refine ⟨v, s₀, hvx, hvmin, hs₀_pos, hs₀_lt, ?_⟩
  dsimp only
  refine ⟨hs₀_source, hs₀_dom, hs₀_exp, ?_⟩
  exact B.inv_eq_of_exp hs₀_source hs₀_exp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The generic diagonal-exponential branch supplies the terminal inverse
segment needed in the Calabi broken-path construction. -/
theorem exists_calabi_tail
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (O x : M) (hOx : riemannianEDist I O x ≠ ⊤) :
    ∃ (v : TangentSpace I O) (s₀ : Real),
      expMapIntrinsic (I := I) g hEnorm O v = x ∧
      Real.sqrt (g.inner O v v) = (riemannianEDist I O x).toReal ∧
      0 < s₀ ∧ s₀ < 1 ∧
      let velocity : Real → TangentBundle I M :=
        intrinsicVelocityLift (I := I) g hEnorm O v
      let tail : Real → TangentBundle I M := fun s =>
        ⟨(velocity s).proj, (1 - s) • (velocity s).snd⟩
      tail s₀ ∈
          (Geometry.Riemannian.Exponential.stdBranch (I := I) g hEnorm x).hom.source ∧
        ((tail s₀).proj, x) ∈
          (Geometry.Riemannian.Exponential.stdBranch (I := I) g hEnorm x).dom ∧
        expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd = x ∧
        (Geometry.Riemannian.Exponential.stdBranch (I := I) g hEnorm x).inv
          ((tail s₀).proj, x) = tail s₀ := by
  exact calabi_tail_of (I := I) g hEnorm O x hOx
    (Geometry.Riemannian.Exponential.stdBranch (I := I) g hEnorm x)

end DifferentialGeometry
