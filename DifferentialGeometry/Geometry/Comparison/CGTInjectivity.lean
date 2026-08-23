import DifferentialGeometry.Geometry.Comparison.IntrinsicInjectivityRadius
import DifferentialGeometry.Geometry.Comparison.Volume.BishopBall
import DifferentialGeometry.Geometry.Comparison.Volume.BallVolume
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentFrameBound
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentMeasure
import DifferentialGeometry.Geometry.Comparison.CGTPropeller

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold MeasureTheory Metric Set
open scoped ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CGT
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

noncomputable def intrPullVol
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (R : Real) : ENNReal :=
  ∫⁻ z in ball (0 : E) R,
    ENNReal.ofReal
      (curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p
          (normalFrame (I := I) g p z))
        (fun i t =>
          intrinsicJacobi (I := I) g hEnorm p
            (normalFrame (I := I) g p z)
            ((normalBasis (I := I) g p) i) t)
        1)
    ∂(volume : Measure E)

omit [CompleteSpace E] [ConnectedSpace M] in
theorem intrPullVol_le_hyp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {q R : Real} (hq : 0 ≤ q) (hR : 0 < R)
    (hno : ∀ z, z ∈ ball (0 : E) R → z ≠ 0 →
      ∀ t, t ∈ Ioo (0 : Real) 1 →
        ¬ IsConjVec (I := I) g hEnorm p
          ((t • normalFrame (I := I) g p z :
            TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    intrPullVol (I := I) g hEnorm p R ≤
      (volume : Measure E).toSphere Set.univ *
        ENNReal.ofReal
          (hypRadVol q (Module.finrank Real E - 1) R) := by
  classical
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let L : E ≃L[Real] E := normalFrame (I := I) (E := E) g p
  let Dn : E → Real := fun z =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm p (L z))
      (fun i t =>
        intrinsicJacobi (I := I) g hEnorm p (L z)
          ((normalBasis (I := I) g p) i) t)
      1
  let Dh : E → ENNReal := fun z =>
    ENNReal.ofReal
      (hypDensity (q * ‖z‖) (Module.finrank Real E - 1) 1)
  have hpoint :
      ∀ᵐ z ∂(volume : Measure E), z ∈ ball (0 : E) R →
        ENNReal.ofReal (Dn z) ≤ Dh z := by
    filter_upwards [Measure.ae_ne (volume : Measure E) (0 : E)] with z hz0 hz
    have hu0 : L z ≠ 0 := by
      intro hLz
      apply hz0
      exact L.injective (by simpa only [map_zero] using hLz)
    have hdens :=
      expDens_le_hyp (I := I) g hEnorm p (L z)
        (normalBasis (I := I) g p)
        (normalBasis_inner (I := I) g p)
        q hq hu0 (hno z hz hz0) hRic
    have hsqrt :
        Real.sqrt (g.inner p (L z) (L z)) = ‖z‖ := by
      simpa only [L] using normalFrame_sqrt (I := I) g p z
    apply ENNReal.ofReal_le_ofReal
    simpa only [Dn, Dh, hsqrt] using hdens
  have hmono :
      (∫⁻ z in ball (0 : E) R,
          ENNReal.ofReal (Dn z) ∂(volume : Measure E)) ≤
        ∫⁻ z in ball (0 : E) R, Dh z ∂(volume : Measure E) :=
    setLIntegral_mono_ae' measurableSet_ball hpoint
  calc
    intrPullVol (I := I) g hEnorm p R =
        ∫⁻ z in ball (0 : E) R,
          ENNReal.ofReal (Dn z) ∂(volume : Measure E) := rfl
    _ ≤ ∫⁻ z in ball (0 : E) R, Dh z ∂(volume : Measure E) := hmono
    _ = (volume : Measure E).toSphere Set.univ *
        ENNReal.ofReal
          (hypRadVol q (Module.finrank Real E - 1) R) := by
      simpa only [Dh] using hypBall_lintegral (E := E) q hq hR

private theorem ratio_le_half
    {r L : Real} {V P : ENNReal}
    (hL : 0 < L)
    (harea :
      ((⌊r / L⌋₊ : Nat) : ENNReal) * V ≤ P) :
    ENNReal.ofReal (r / 2) * V / (V + P) ≤
      ENNReal.ofReal (L / 2) := by
  let N : Nat := ⌊r / L⌋₊
  have hupper : r / L < (N : Real) + 1 := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (r / L)
  have hrN : r < ((N : Real) + 1) * L :=
    (div_lt_iff₀ hL).mp hupper
  have hrhalf : r / 2 ≤ ((N : Real) + 1) * (L / 2) := by
    nlinarith
  have hscale :
      ENNReal.ofReal (r / 2) ≤
        ((N : ENNReal) + 1) * ENNReal.ofReal (L / 2) := by
    have hscale' := ENNReal.ofReal_le_ofReal hrhalf
    simpa only [
      ENNReal.ofReal_mul (by positivity : 0 ≤ (N : Real) + 1),
      ENNReal.ofReal_add (Nat.cast_nonneg N) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one] using hscale'
  have hareaN : (N : ENNReal) * V ≤ P := by
    simpa only [N] using harea
  apply ENNReal.div_le_of_le_mul'
  calc
    ENNReal.ofReal (r / 2) * V ≤
        (((N : ENNReal) + 1) * ENNReal.ofReal (L / 2)) * V :=
      by gcongr
    _ = ENNReal.ofReal (L / 2) * ((N : ENNReal) * V + V) := by
      ring
    _ ≤ ENNReal.ofReal (L / 2) * (P + V) := by
      gcongr
    _ = (V + P) * ENNReal.ofReal (L / 2) := by
      rw [add_comm P V, mul_comm]

omit [T2Space (TangentBundle I M)] in
theorem flatLoop_ge_cgt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {K R r₀ s ell : Real}
    (hK : 0 < K) (hR : 0 < R)
    (hRpi : R ≤ Real.pi / Real.sqrt K)
    (hRm : Rm04GlobalBound (I := I) (M := M) g K)
    (hloc :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (intrinsicFramedExp (I := I) g hEnorm p)
        (ball (0 : E) R))
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hfit : r₀ + 2 * s < R) (hquarter : r₀ < R / 4)
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hell : 0 < ell)
    (hcLen : pathLen (I := I) c = ENNReal.ofReal (2 * ell))
    (A : IntrFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0) :
    ENNReal.ofReal (r₀ / 2) *
          riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} /
        (riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} +
          intrPullVol (I := I) g hEnorm p (r₀ + s))
      ≤ ENNReal.ofReal ell := by
  classical
  let V : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | riemannianEDist I p y < ENNReal.ofReal s}
  let P : ENNReal := intrPullVol (I := I) g hEnorm p (r₀ + s)
  let A₀ : ENNReal := ENNReal.ofReal (r₀ / 2) * V / (V + P)
  change A₀ ≤ ENNReal.ofReal ell
  have h4rR : 4 * r₀ < R := by
    linarith
  have h2rR : 2 * r₀ < R := by
    linarith
  have has : r₀ + s < R := by
    linarith
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hRroot : R * Real.sqrt K ≤ Real.pi :=
    (le_div_iff₀ hsqrtK).mp hRpi
  have h4root :
      4 * r₀ * Real.sqrt K < R * Real.sqrt K :=
    mul_lt_mul_of_pos_right h4rR hsqrtK
  have h2root : 2 * r₀ * Real.sqrt K < Real.pi / 2 := by
    nlinarith
  have hsmall : K * (2 * r₀) ^ 2 < (Real.pi / 2) ^ 2 := by
    have hsq :
        (2 * r₀ * Real.sqrt K) ^ 2 < (Real.pi / 2) ^ 2 :=
      (sq_lt_sq₀ (by positivity) (by positivity)).2 h2root
    calc
      K * (2 * r₀) ^ 2 =
          (Real.sqrt K) ^ 2 * (2 * r₀) ^ 2 := by
        rw [Real.sq_sqrt hK.le]
      _ = (2 * r₀ * Real.sqrt K) ^ 2 := by
        ring
      _ < (Real.pi / 2) ^ 2 := hsq
  have hRmLocal :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K := by
    intro z _
    exact hRm _
  have harea_of_L :
      ∀ L : Real, 2 * ell < L → L < r₀ →
        ((⌊r₀ / L⌋₊ : Nat) : ENNReal) * V ≤ P := by
    intro L h2ellL hLr
    have hL : 0 < L := by
      linarith
    let N : Nat := ⌊r₀ / L⌋₊
    have hratio : 0 ≤ r₀ / L := div_nonneg hr₀.le hL.le
    have hNoneRatio : 1 ≤ r₀ / L := by
      apply (le_div_iff₀ hL).2
      simpa only [one_mul] using hLr.le
    have hNpos : 0 < N := by
      simpa only [N] using (Nat.floor_pos.mpr hNoneRatio)
    have hNge : 1 ≤ N := hNpos
    have hNfloor : (N : Real) ≤ r₀ / L := by
      simpa only [N] using Nat.floor_le hratio
    have hNmul : (N : Real) * L ≤ r₀ :=
      (le_div_iff₀ hL).mp hNfloor
    have hpredCast : ((N - 1 : Nat) : Real) < (N : Real) := by
      exact_mod_cast Nat.sub_one_lt (Nat.ne_of_gt hNpos)
    have hpredMul : ((N - 1 : Nat) : Real) * L < r₀ := by
      exact (mul_lt_mul_of_pos_right hpredCast hL).trans_le hNmul
    have hfitL : L + r₀ < R := by
      linarith
    have hcLenL : pathLen (I := I) c < ENNReal.ofReal L := by
      rw [hcLen]
      exact
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 h2ellL
    let U : Set E := ball (0 : E) (r₀ + s)
    let S : Set M :=
      {y : M | riemannianEDist I p y < ENNReal.ofReal s}
    have hU : MeasurableSet U := measurableSet_ball
    have hS : MeasurableSet S := by
      have hcont :
          Continuous (fun y : M => riemannianEDist I p y) := by
        simpa only [riemannianEDist_comm] using
          (continuous_riemannianEDist_to (I := I) p)
      simpa only [S] using
        (isOpen_lt hcont
          (continuous_const :
            Continuous (fun _ : M => ENNReal.ofReal s))).measurableSet
    have hlocU :
        IsLocalHomeomorphOn
          (intrinsicFramedExp (I := I) g hEnorm p) U :=
      hloc.isLocalHomeomorphOn.mono
        (Metric.ball_subset_ball has.le)
    have hcount :
        ∀ y ∈ S, (N : ENat) ≤
          {w : E | w ∈ U ∧
            intrinsicFramedExp (I := I) g hEnorm p w = y}.encard := by
      intro y hy
      have hcount' :=
        CGT.intrFiber_count_core (I := I) g hEnorm p
          hR h4rR hL.le hr₀.le hfitL hloc hK.le hsmall hRmLocal
          c hc hcLenL A hA (N - 1) hpredMul hs has
          (q := y) (by simpa only [S, Set.mem_setOf_eq] using hy)
      have hENat :
          ((N - 1 : Nat) : ENat) + 1 = (N : ENat) := by
        exact_mod_cast Nat.sub_add_cancel hNge
      simpa only [U, CGT.intrFiber, Set.mem_setOf_eq,
        hENat] using hcount'
    have harea :=
      framed_mul_le_area (I := I) g hEnorm p hU hS
        (m := (N : ENat)) hlocU hcount
    simpa only [N, V, P, U, S, ENat.toENNReal_coe, intrPullVol] using harea
  have hratio_bound :
      ∀ L : Real, 2 * ell < L → L < r₀ →
        A₀ ≤ ENNReal.ofReal (L / 2) := by
    intro L h2ellL hLr
    have hL : 0 < L := by
      linarith
    simpa only [A₀] using
      ratio_le_half hL (harea_of_L L h2ellL hLr)
  have hA₀r : A₀ ≤ ENNReal.ofReal (r₀ / 2) := by
    have hVD : V ≤ V + P := le_add_right le_rfl
    have hVratio : V / (V + P) ≤ 1 := by
      exact ENNReal.div_le_of_le_mul' (by simpa only [mul_one] using hVD)
    calc
      A₀ = ENNReal.ofReal (r₀ / 2) * (V / (V + P)) := by
        dsimp only [A₀]
        rw [mul_div_assoc]
      _ ≤ ENNReal.ofReal (r₀ / 2) * 1 :=
        by gcongr
      _ = ENNReal.ofReal (r₀ / 2) := mul_one _
  have hA₀top : A₀ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA₀r
  by_contra hbound
  have hellA₀ : ENNReal.ofReal ell < A₀ :=
    lt_of_not_ge hbound
  have hellReal : ell < A₀.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hell.le hA₀top).mp hellA₀
  have hA₀real : A₀.toReal ≤ r₀ / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hA₀r
  let L : Real := ell + A₀.toReal
  have h2ellL : 2 * ell < L := by
    dsimp only [L]
    linarith
  have hLr : L < r₀ := by
    dsimp only [L]
    linarith
  have hAL : A₀ ≤ ENNReal.ofReal (L / 2) :=
    hratio_bound L h2ellL hLr
  have hArealL : A₀.toReal ≤ L / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hAL
  dsimp only [L] at hArealL
  linarith

omit [T2Space (TangentBundle I M)] in
theorem collision_ge_cgt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {K R r₀ s ell : Real}
    (hK : 0 < K) (hR : 0 < R)
    (hRpi : R ≤ Real.pi / Real.sqrt K)
    (hRm : Rm04GlobalBound (I := I) (M := M) g K)
    (hloc :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (intrinsicFramedExp (I := I) g hEnorm p)
        (ball (0 : E) R))
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hfit : r₀ + 2 * s < R) (hquarter : r₀ < R / 4)
    {u v : E} (huv : u ≠ v)
    (hcollision :
      intrinsicFramedExp (I := I) g hEnorm p u =
        intrinsicFramedExp (I := I) g hEnorm p v)
    (hell : 0 < ell) (hlen : ‖u‖ + ‖v‖ = 2 * ell)
    (hshort : ‖u‖ + ‖v‖ < R) :
    ENNReal.ofReal (r₀ / 2) *
          riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} /
        (riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} +
          intrPullVol (I := I) g hEnorm p (r₀ + s))
      ≤ ENNReal.ofReal ell := by
  let pu :
      Path p (intrinsicFramedExp (I := I) g hEnorm p u) :=
    radialFlat (I := I) g hEnorm p u
  let pv :
      Path p (intrinsicFramedExp (I := I) g hEnorm p u) :=
    (radialFlat (I := I) g hEnorm p v).cast rfl hcollision
  let c : Path p p := pu.trans pv.symm
  have hpu : IsFlatC1Path (I := I) pu := by
    simpa only [pu] using radialFlat_flat (I := I) g hEnorm p u
  have hpv : IsFlatC1Path (I := I) pv := by
    have hflat := radialFlat_flat (I := I) g hEnorm p v
    refine {
      c1 := ?_
      flat_zero := ?_
      flat_one := ?_ }
    · simpa only [pv, Path.extend_cast] using hflat.c1
    · simpa only [pv, Path.extend_cast] using hflat.flat_zero
    · simpa only [pv, Path.extend_cast, hcollision] using hflat.flat_one
  have hc : IsFlatC1Path (I := I) c := by
    exact hpu.trans hpv.symm
  have hpuLen :
      pathLen (I := I) pu = ENNReal.ofReal ‖u‖ := by
    simpa only [pu] using radialFlat_len (I := I) g hEnorm p u
  have hpvLen :
      pathLen (I := I) pv = ENNReal.ofReal ‖v‖ := by
    simpa only [pathLen, pv, Path.extend_cast] using
      radialFlat_len (I := I) g hEnorm p v
  have hcLen :
      pathLen (I := I) c = ENNReal.ofReal (2 * ell) := by
    change pathLen (I := I) (pu.trans pv.symm) = _
    rw [pathLen_trans hpu hpv.symm, pathLen_symm hpv,
      hpuLen, hpvLen, ← ENNReal.ofReal_add (norm_nonneg u) (norm_nonneg v),
      hlen]
  have hcR :
      pathLen (I := I) c < ENNReal.ofReal R := by
    rw [hcLen]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2 (by linarith)
  have hex :
      Nonempty (IntrFrameLift (I := I) g hEnorm p c.extend 0 1) :=
    exists_intr_lift (I := I) g hEnorm p zero_le_one
      hc.c1.contMDiffOn (by simp only [c, Path.extend_zero])
      hR hcR hloc
  let A : IntrFrameLift (I := I) g hEnorm p c.extend 0 1 :=
    Classical.choice hex
  have hpuR :
      pathLen (I := I) pu < ENNReal.ofReal R := by
    rw [hpuLen]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2
      (lt_of_le_of_lt (by linarith [norm_nonneg v]) hshort)
  have hpvR :
      pathLen (I := I)
          (radialFlat (I := I) g hEnorm p v) <
        ENNReal.ofReal R := by
    rw [radialFlat_len]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2
      (lt_of_le_of_lt (by linarith [norm_nonneg u]) hshort)
  have hmid :
      A.toFun (1 / 2) = u := by
    let Au :
        IntrFrameLift (I := I) g hEnorm p pu.extend 0 1 :=
      radialFlatLift (I := I) g hEnorm p u
    have hAu :
        Au.toFun 1 = u := by
      simpa only [Au] using radialLift_one (I := I) g hEnorm p u
    have happ :
        A.toFun (1 / 2) = Au.toFun 1 := by
      exact Au.append_mid_eq A hR hpuR hcR hloc
    exact happ.trans hAu
  have hA : A.toFun 1 ≠ 0 := by
    intro hA0
    let B :
        IntrFrameLift (I := I) g hEnorm p
          (radialFlat (I := I) g hEnorm p v).extend 0 1 := {
      toFun := fun t => A.toFun (1 - t / 2)
      contDiff := by
        apply A.contDiff.comp
        · fun_prop
        · intro t ht
          constructor <;> linarith [ht.1, ht.2]
      start := by
        simpa only [zero_div, sub_zero] using hA0
      lifts := by
        intro t ht
        have harg : 1 - t / 2 ∈ Set.Icc (0 : Real) 1 := by
          constructor <;> linarith [ht.1, ht.2]
        have hhalf : 1 / 2 ≤ 1 - t / 2 := by
          linarith [ht.2]
        calc
          intrinsicFramedExp (I := I) g hEnorm p
                (A.toFun (1 - t / 2)) =
              c.extend (1 - t / 2) := by
            simpa only [Function.comp_apply] using A.lifts harg
          _ = pv.symm.extend (2 * (1 - t / 2) - 1) := by
            exact Path.extend_trans_of_half_le pu pv.symm hhalf
          _ = pv.extend (1 - (2 * (1 - t / 2) - 1)) := by
            rw [Path.extend_symm]
          _ = pv.extend t := by congr 1; ring
          _ = (radialFlat (I := I) g hEnorm p v).extend t := by
            simp only [pv, Path.extend_cast] }
    have hB :=
      B.eqOn (radialFlatLift (I := I) g hEnorm p v)
        zero_le_one hR hpvR hloc
        (show (1 : Real) ∈ Set.Icc 0 1 by exact ⟨zero_le_one, le_rfl⟩)
    have hBv : B.toFun 1 = v := by
      exact hB.trans (radialLift_one (I := I) g hEnorm p v)
    apply huv
    calc
      u = A.toFun (1 / 2) := hmid.symm
      _ = B.toFun 1 := by
        change A.toFun (1 / 2) = A.toFun (1 - 1 / 2)
        norm_num
      _ = v := hBv
  exact
    flatLoop_ge_cgt (I := I) g hEnorm p hK hR hRpi hRm hloc
      hr₀ hs hfit hquarter c hc hell hcLen A hA

omit [T2Space (TangentBundle I M)] in
theorem intrLoop_ge_cgt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {K R r₀ s ell : Real}
    (hK : 0 < K) (hR : 0 < R)
    (hRpi : R ≤ Real.pi / Real.sqrt K)
    (hRm : Rm04GlobalBound (I := I) (M := M) g K)
    (hloc :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (intrinsicFramedExp (I := I) g hEnorm p)
        (ball (0 : E) R))
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hfit : r₀ + 2 * s < R) (hquarter : r₀ < R / 4)
    {u : E} (hell : 0 < ell) (hlen : ‖u‖ = 2 * ell)
    (hloop : intrinsicFramedExp (I := I) g hEnorm p u = p) :
    ENNReal.ofReal (r₀ / 2) *
          riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} /
        (riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} +
          intrPullVol (I := I) g hEnorm p (r₀ + s))
      ≤ ENNReal.ofReal ell := by
  let c : Path p p :=
    (radialFlat (I := I) g hEnorm p u).cast rfl hloop.symm
  have hc : IsFlatC1Path (I := I) c := by
    have hflat := radialFlat_flat (I := I) g hEnorm p u
    refine {
      c1 := ?_
      flat_zero := ?_
      flat_one := ?_ }
    · simpa only [c, Path.extend_cast] using hflat.c1
    · simpa only [c, Path.extend_cast] using hflat.flat_zero
    · simpa only [c, Path.extend_cast, hloop] using hflat.flat_one
  have hcLen :
      pathLen (I := I) c = ENNReal.ofReal (2 * ell) := by
    simpa only [pathLen, c, Path.extend_cast, hlen] using
      radialFlat_len (I := I) g hEnorm p u
  let A : IntrFrameLift (I := I) g hEnorm p c.extend 0 1 := {
    toFun := (radialFlatLift (I := I) g hEnorm p u).toFun
    contDiff := (radialFlatLift (I := I) g hEnorm p u).contDiff
    start := (radialFlatLift (I := I) g hEnorm p u).start
    lifts := by
      simpa only [c, Path.extend_cast] using
        (radialFlatLift (I := I) g hEnorm p u).lifts }
  have hu0 : u ≠ 0 := by
    intro hu
    rw [hu, norm_zero] at hlen
    nlinarith
  have hA : A.toFun 1 ≠ 0 := by
    have hAone : A.toFun 1 = u := by
      simpa only [A] using radialLift_one (I := I) g hEnorm p u
    exact hAone.symm ▸ hu0
  exact
    flatLoop_ge_cgt (I := I) g hEnorm p hK hR hRpi hRm hloc
      hr₀ hs hfit hquarter c hc hell hcLen A hA

omit [T2Space (TangentBundle I M)] in
theorem intrInj_ge_cgt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {K R r₀ s : Real}
    (hK : 0 < K) (hR : 0 < R)
    (hRpi : R ≤ Real.pi / Real.sqrt K)
    (hRm : Rm04GlobalBound (I := I) (M := M) g K)
    (hloc :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (intrinsicFramedExp (I := I) g hEnorm p)
        (ball (0 : E) R))
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hfit : r₀ + 2 * s < R) (hquarter : r₀ < R / 4) :
    ENNReal.ofReal (r₀ / 2) *
          riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} /
        (riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} +
          intrPullVol (I := I) g hEnorm p (r₀ + s))
      ≤ intrInjRadius (I := I) g hEnorm p := by
  classical
  let V : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | riemannianEDist I p y < ENNReal.ofReal s}
  let P : ENNReal := intrPullVol (I := I) g hEnorm p (r₀ + s)
  let A₀ : ENNReal := ENNReal.ofReal (r₀ / 2) * V / (V + P)
  change A₀ ≤ intrInjRadius (I := I) g hEnorm p
  apply le_intrInjRadius (I := I) g hEnorm p
  change InjOn (intrinsicFramedExp (I := I) g hEnorm p)
    (Metric.eball (0 : E) A₀)
  have hA₀r : A₀ ≤ ENNReal.ofReal (r₀ / 2) := by
    have hVD : V ≤ V + P := le_add_right le_rfl
    have hVratio : V / (V + P) ≤ 1 := by
      exact ENNReal.div_le_of_le_mul' (by simpa only [mul_one] using hVD)
    calc
      A₀ = ENNReal.ofReal (r₀ / 2) * (V / (V + P)) := by
        dsimp only [A₀]
        rw [mul_div_assoc]
      _ ≤ ENNReal.ofReal (r₀ / 2) * 1 := by gcongr
      _ = ENNReal.ofReal (r₀ / 2) := mul_one _
  have hA₀top : A₀ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA₀r
  have hA₀real : A₀.toReal ≤ r₀ / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hA₀r
  intro u hu v hv hcollision
  by_contra huv
  have huE : ENNReal.ofReal ‖u‖ < A₀ := by
    simpa only [Metric.mem_eball, edist_dist, dist_zero_right] using hu
  have hvE : ENNReal.ofReal ‖v‖ < A₀ := by
    simpa only [Metric.mem_eball, edist_dist, dist_zero_right] using hv
  have huReal : ‖u‖ < A₀.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg u) hA₀top).mp huE
  have hvReal : ‖v‖ < A₀.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg v) hA₀top).mp hvE
  have hsumPos : 0 < ‖u‖ + ‖v‖ := by
    have hone : u ≠ 0 ∨ v ≠ 0 := by
      by_cases hu0 : u = 0
      · right
        intro hv0
        exact huv (hu0.trans hv0.symm)
      · exact Or.inl hu0
    rcases hone with hu0 | hv0
    · exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hu0) (norm_nonneg v)
    · exact add_pos_of_nonneg_of_pos (norm_nonneg u) (norm_pos_iff.mpr hv0)
  let ell : Real := (‖u‖ + ‖v‖) / 2
  have hell : 0 < ell := by
    dsimp only [ell]
    linarith
  have hlen : ‖u‖ + ‖v‖ = 2 * ell := by
    dsimp only [ell]
    ring
  have h4rR : 4 * r₀ < R := by
    linarith
  have hshort : ‖u‖ + ‖v‖ < R := by
    linarith
  have hcg :
      A₀ ≤ ENNReal.ofReal ell := by
    simpa only [A₀, V, P] using
      collision_ge_cgt (I := I) g hEnorm p hK hR hRpi hRm hloc
        hr₀ hs hfit hquarter huv hcollision hell hlen hshort
  have hellReal : ell < A₀.toReal := by
    dsimp only [ell]
    linarith
  have hellA₀ : ENNReal.ofReal ell < A₀ :=
    (ENNReal.ofReal_lt_iff_lt_toReal hell.le hA₀top).2 hellReal
  exact (not_le_of_gt hellA₀) hcg

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
