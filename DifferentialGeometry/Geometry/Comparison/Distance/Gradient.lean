import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Interior
import DifferentialGeometry.Geometry.Comparison.Variation.NoConjugatePoints.MinimizingSegment
import DifferentialGeometry.Geometry.Exponential.Inverse.Radius
import DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Operator
open Exponential Variation VolumeComparison

private theorem hasFDerivAt_of_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]
    {l f u : X → Real} {x : X} {D : X →L[Real] Real}
    (hl : HasFDerivAt l D x) (hu : HasFDerivAt u D x)
    (hlx : l x = f x) (hux : f x = u x)
    (hord : ∀ᶠ y in 𝓝 x, l y ≤ f y ∧ f y ≤ u y) :
    HasFDerivAt f D x := by
  rw [hasFDerivAt_iff_tendsto] at hl hu ⊢
  have hmax := hl.max hu
  simp only [max_self] at hmax
  refine squeeze_zero'
    (g := fun y =>
      max
        (‖y - x‖⁻¹ * ‖l y - l x - D (y - x)‖)
        (‖y - x‖⁻¹ * ‖u y - u x - D (y - x)‖)) ?_ ?_ hmax
  · exact Eventually.of_forall fun y =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · filter_upwards [hord] with y hy
    have hres :
        l y - l x - D (y - x) ≤ f y - f x - D (y - x) ∧
          f y - f x - D (y - x) ≤ u y - u x - D (y - x) := by
      constructor <;> linarith
    have habs := abs_le_max_abs_abs hres.1 hres.2
    rw [← Real.norm_eq_abs] at habs
    calc
      ‖y - x‖⁻¹ * ‖f y - f x - D (y - x)‖ ≤
          ‖y - x‖⁻¹ *
            max ‖l y - l x - D (y - x)‖
              ‖u y - u x - D (y - x)‖ :=
        mul_le_mul_of_nonneg_left habs
          (inv_nonneg.mpr (norm_nonneg (y - x)))
      _ = max
          (‖y - x‖⁻¹ * ‖l y - l x - D (y - x)‖)
          (‖y - x‖⁻¹ * ‖u y - u x - D (y - x)‖) := by
        rw [mul_max_of_nonneg _ _
          (inv_nonneg.mpr (norm_nonneg (y - x)))]

private theorem hasMFDerivAt_of_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {l f u : M → Real} {x : M}
    {D : TangentSpace I x →L[Real] Real}
    (hl : HasMFDerivAt I 𝓘(Real, Real) l x D)
    (hu : HasMFDerivAt I 𝓘(Real, Real) u x D)
    (hlx : l x = f x) (hux : f x = u x)
    (hord : ∀ᶠ y in 𝓝 x, l y ≤ f y ∧ f y ≤ u y) :
    HasMFDerivAt I 𝓘(Real, Real) f x D := by
  have hfcont : ContinuousAt f x := by
    have hlt : Tendsto l (𝓝 x) (𝓝 (f x)) := by
      rw [← hlx]
      exact hl.continuousAt
    have hut : Tendsto u (𝓝 x) (𝓝 (f x)) := by
      rw [hux]
      exact hu.continuousAt
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlt hut
      (hord.mono fun _ hy => hy.1) (hord.mono fun _ hy => hy.2)
  refine ⟨hfcont, ?_⟩
  have hlF : HasFDerivAt
      (writtenInExtChartAt I 𝓘(Real, Real) x l) D
      ((extChartAt I x) x) := by
    have hlf := hl.2
    rw [ModelWithCorners.Boundaryless.range_eq_univ] at hlf
    have hlf' := hasFDerivWithinAt_univ.mp hlf
    exact hlf'
  have huF : HasFDerivAt
      (writtenInExtChartAt I 𝓘(Real, Real) x u) D
      ((extChartAt I x) x) := by
    have huf := hu.2
    rw [ModelWithCorners.Boundaryless.range_eq_univ] at huf
    have huf' := hasFDerivWithinAt_univ.mp huf
    exact huf'
  have hfF : HasFDerivAt
      (writtenInExtChartAt I 𝓘(Real, Real) x f) D
      ((extChartAt I x) x) := by
    apply hasFDerivAt_of_le hlF huF
    · simp only [writtenInExtChartAt, Function.comp_apply,
        PartialEquiv.left_inv _
          (mem_extChartAt_source (I := I) x), hlx]
    · simp only [writtenInExtChartAt, Function.comp_apply,
        PartialEquiv.left_inv _
          (mem_extChartAt_source (I := I) x), hux]
    · have hsymm :
        (extChartAt I x).symm ((extChartAt I x) x) = x :=
      PartialEquiv.left_inv _ (mem_extChartAt_source (I := I) x)
      have hcont : Tendsto (extChartAt I x).symm
          (𝓝 ((extChartAt I x) x)) (𝓝 x) := by
        have hc := continuousAt_extChartAt_symm (I := I) x
        have heq : 𝓝 ((extChartAt I x).symm ((extChartAt I x) x)) =
            𝓝 x := congrArg 𝓝 hsymm
        rw [← heq]
        exact hc
      have hchart := hcont.eventually hord
      filter_upwards [hchart] with y hy
      simpa only [writtenInExtChartAt, Function.comp_apply,
        extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using hy
  rw [ModelWithCorners.Boundaryless.range_eq_univ]
  exact hfF.hasFDerivWithinAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M]
variable [RiemannianBundle (fun y : M ↦ TangentSpace I y)]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edist_toReal_tri
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (x y z : M) :
    (riemannianEDist I x z).toReal ≤
      (riemannianEDist I x y).toReal +
        (riemannianEDist I y z).toReal := by
  have hxy : riemannianEDist I x y ≠ (⊤ : ENNReal) :=
    riemannianEDist_ne_top (I := I) x y
  have hyz : riemannianEDist I y z ≠ (⊤ : ENNReal) :=
    riemannianEDist_ne_top (I := I) y z
  have htri : riemannianEDist I x z ≤
      riemannianEDist I x y + riemannianEDist I y z :=
    riemannianEDist_triangle
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩) htri
  rwa [ENNReal.toReal_add hxy hyz] at hreal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem dist_grad_radial
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p : M} {v : TangentSpace I p}
    (hv : v ∈ SegmentInt (I := I) g (show ∀ (y : M) (w : TangentSpace I y), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) p)
    (hv0 : v ≠ 0) :
    let q := expMapIntrinsic (I := I) g hEnorm p v
    MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M ↦ (riemannianEDist I p y).toReal) q ∧
      gradientFun (I := I) g
          (fun y : M ↦ (riemannianEDist I p y).toReal) q =
        (Real.sqrt (g.inner p v v))⁻¹ •
          (intrinsicVelocityLift (I := I) g hEnorm p v 1).snd := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let q : M := expMapIntrinsic (I := I) g hEnorm p v
  let ρ : M → Real := fun y => (riemannianEDist I p y).toReal
  change MDifferentiableAt I 𝓘(Real, Real) ρ q ∧
    gradientFun (I := I) g ρ q =
      (Real.sqrt (g.inner p v v))⁻¹ •
        (intrinsicVelocityLift (I := I) g hEnorm p v 1).snd
  have hv_pos : 0 < g.inner p v v := g.pos p v hv0
  have hv_dom : v ∈ SegmentDom (I := I) g hEnorm p :=
    segmentInt_subset (I := I) g
      (show ∀ (y : M) (w : TangentSpace I y),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) p hv
  have hρq : Real.sqrt (g.inner p v v) = ρ q := by
    simpa only [ρ, q, mem_segmentDom] using hv_dom
  have hno_p : ¬ IsConjVec (I := I) g hEnorm p (v : E) :=
    segmentInt_no_conj (I := I) g
      (show ∀ (y : M) (w : TangentSpace I y),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) from hEnorm) hv
  obtain ⟨Bp, hvBp⟩ := branch_of_not_conj (I := I) g hEnorm hno_p
  let U : M → Real := branchRadius (I := I) g Bp
  have hqBp : q ∈ Bp.dom := by
    rw [show q = Bp.hom (v : E) from
      Bp.hom_eq hvBp]
    exact Bp.hom.map_source hvBp
  have hUdiff : MDifferentiableAt I 𝓘(Real, Real) U q := by
    simpa only [U, q] using
      branchRadius_diff (I := I) Bp hvBp hv_pos
  have hUq : U q = ρ q := by
    calc
      U q = Real.sqrt (g.inner p v v) := by
        simpa only [U, q] using branchRadius_exp (I := I) Bp hvBp
      _ = ρ q := hρq
  obtain ⟨c, hc, hcv⟩ := hv
  have hc0 : 0 < c := one_pos.trans hc
  let a : TangentSpace I p := c • v
  let s₀ : Real := c⁻¹
  let x : M := expMapIntrinsic (I := I) g hEnorm p a
  have ha0 : a ≠ 0 := by
    exact smul_ne_zero hc0.ne' hv0
  have ha_pos : 0 < g.inner p a a := g.pos p a ha0
  have hlenx : Real.sqrt (g.inner p a a) =
      (riemannianEDist I p x).toReal := by
    simpa only [a, x, mem_segmentDom] using hcv
  have hs₀ : s₀ ∈ Ioo (0 : Real) 1 := by
    exact ⟨inv_pos.mpr hc0, (inv_lt_one₀ hc0).2 hc⟩
  let z := intrinsicVelocityLift (I := I) g hEnorm p a s₀
  let uTail : TangentSpace I z.proj := (1 - s₀) • z.snd
  let z₁ := intrinsicVelocityLift (I := I) g hEnorm z.proj uTail 1
  let w : TangentSpace I z₁.proj := -z₁.snd
  have hzq : z.proj = q := by
    change intrinsicGeodesic (I := I) g hEnorm p a s₀ = q
    calc
      intrinsicGeodesic (I := I) g hEnorm p a s₀ =
          expMapIntrinsic (I := I) g hEnorm p (s₀ • a) := by
        rw [expMapIntrinsic_def,
          intrinsicGeodesic_smul (I := I) g hEnorm]
      _ = q := by
        congr 1
        dsimp only [s₀, a]
        rw [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
  have hz₁x : z₁.proj = x := by
    have htail := congrFun (Variation.tailCurve_eq (I := I) g hEnorm p a s₀) 1
    change intrinsicGeodesic (I := I) g hEnorm z.proj uTail 1 = x
    calc
      intrinsicGeodesic (I := I) g hEnorm z.proj uTail 1 =
          intrinsicGeodesic (I := I) g hEnorm p a
            ((1 - s₀) * 1 + s₀) := by
        simpa only [z, uTail] using htail
      _ = intrinsicGeodesic (I := I) g hEnorm p a 1 := by
        congr 1
        ring
      _ = x := by rfl
  have htail_no :
      ¬ IsConjVec (I := I) g hEnorm z.proj (uTail : E) := by
    have hrx : 0 < (riemannianEDist I p x).toReal := by
      rw [← hlenx]
      exact Real.sqrt_pos.2 ha_pos
    simpa only [z, uTail] using
      tail_not_conj_of_min (I := I) g hEnorm a (x := x) rfl hlenx hrx hs₀
  have hw_no : ¬ IsConjVec (I := I) g hEnorm z₁.proj (w : E) := by
    simpa only [z₁, w] using
      (not_congr (conjVec_reverse (I := I) g hEnorm z.proj uTail)).mp htail_no
  have hspeed_z : g.inner z.proj z.snd z.snd = g.inner p a a := by
    convert intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p a s₀ using 1 ;
      rfl
  have hzvel0 : z.snd ≠ 0 := by
    intro hz0
    have : 0 < g.inner z.proj z.snd z.snd := hspeed_z.symm ▸ ha_pos
    rw [hz0] at this
    simp at this
  have huTail0 : uTail ≠ 0 := by
    exact smul_ne_zero (sub_pos.mpr hs₀.2).ne' hzvel0
  have hspeed_tail :
      g.inner z₁.proj z₁.snd z₁.snd =
        g.inner z.proj uTail uTail := by
    convert intrinsicGeodesic_speedSq_eq (I := I) g hEnorm z.proj uTail 1 using 1 ;
      rfl
  have hz₁vel0 : z₁.snd ≠ 0 := by
    intro hz0
    have hpos : 0 < g.inner z.proj uTail uTail :=
      g.pos z.proj uTail huTail0
    rw [← hspeed_tail, hz0] at hpos
    simp at hpos
  have hw0 : w ≠ 0 := neg_ne_zero.mpr hz₁vel0
  have hw_pos : 0 < g.inner z₁.proj w w := g.pos z₁.proj w hw0
  have hexpw : expMapIntrinsic (I := I) g hEnorm z₁.proj w = q := by
    have hrev := congrFun
      (intrinsicGeo_reverse
        (I := I) g hEnorm z.proj uTail) 1
    change intrinsicGeodesic (I := I) g hEnorm z₁.proj w 1 = q
    simpa only [z₁, w, sub_self,
      intrinsicGeodesic_zero, hzq] using hrev
  obtain ⟨Bm, hwBm⟩ := branch_of_not_conj (I := I) g hEnorm hw_no
  let V : M → Real := branchRadius (I := I) g Bm
  have hqBm : q ∈ Bm.dom := by
    rw [← hexpw, show expMapIntrinsic (I := I) g hEnorm z₁.proj w =
        Bm.hom (w : E) from Bm.hom_eq hwBm]
    exact Bm.hom.map_source hwBm
  have hVdiff : MDifferentiableAt I 𝓘(Real, Real) V q := by
    have h := branchRadius_diff (I := I) Bm hwBm hw_pos
    change MDiffAt (branchRadius (I := I) g Bm)
      (expMapIntrinsic (I := I) g hEnorm z₁.proj w) at h
    rw [hexpw] at h
    simpa only [V] using h
  let r : Real := Real.sqrt (g.inner p a a)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hs₀0 : 0 ≤ s₀ := hs₀.1.le
  have hs₀1 : s₀ ≤ 1 := hs₀.2.le
  have hwlen : Real.sqrt (g.inner z₁.proj w w) = (1 - s₀) * r := by
    have hzsqrt : Real.sqrt (g.inner z.proj z.snd z.snd) = r := by
      rw [hspeed_z]
    calc
      Real.sqrt (g.inner z₁.proj w w) =
          Real.sqrt (g.inner z₁.proj z₁.snd z₁.snd) := by
        dsimp only [w]
        rw [(g.inner z₁.proj).map_neg, neg_apply,
          map_neg, neg_neg]
      _ = Real.sqrt (g.inner z.proj uTail uTail) := by rw [hspeed_tail]
      _ = (1 - s₀) * Real.sqrt (g.inner z.proj z.snd z.snd) := by
        exact sqrt_gInner_smul_self (I := I) g z.proj
          (sub_nonneg.mpr hs₀1) z.snd
      _ = (1 - s₀) * r := by rw [hzsqrt]
  have hVq : V q = (1 - s₀) * r := by
    calc
      V q = V (expMapIntrinsic (I := I) g hEnorm z₁.proj w) := by rw [hexpw]
      _ = Real.sqrt (g.inner z₁.proj w w) := by
        exact branchRadius_exp (I := I) Bm hwBm
      _ = (1 - s₀) * r := hwlen
  have hρq_scale : ρ q = s₀ * r := by
    have hfin : riemannianEDist I p x ≠ (⊤ : ENNReal) :=
      riemannianEDist_ne_top (I := I) p x
    have hseg := Variation.minSegment_edist (I := I) g hEnorm a (x := x) (r := r)
      rfl rfl hlenx hfin ⟨hs₀0, hs₀1⟩
    change riemannianEDist I p z.proj = ENNReal.ofReal (s₀ * r) at hseg
    rw [hzq] at hseg
    have hreal := congrArg ENNReal.toReal hseg
    simpa only [ρ, ENNReal.toReal_ofReal (mul_nonneg hs₀0 hr0)] using hreal
  have hρz₁ : ρ z₁.proj = r := by
    rw [hz₁x]
    exact hlenx.symm
  have hsum_q : U q + V q = ρ z₁.proj := by
    rw [hUq, hρq_scale, hVq, hρz₁]
    ring
  have hupper : ∀ᶠ y in 𝓝 q, ρ y ≤ U y := by
    filter_upwards [Bp.hom.open_target.mem_nhds hqBp] with y hy
    have hrad : 0 ≤ U y := Real.sqrt_nonneg _
    have h := Bp.edist_le_radius hy
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [ρ, U, ENNReal.toReal_ofReal hrad] using hreal
  have hlower : ∀ᶠ y in 𝓝 q, ρ z₁.proj - V y ≤ ρ y := by
    filter_upwards [Bm.hom.open_target.mem_nhds hqBm] with y hy
    have hrad : 0 ≤ V y := Real.sqrt_nonneg _
    have hm := Bm.edist_le_radius hy
    have hmreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    have hyV : (riemannianEDist I y z₁.proj).toReal ≤ V y := by
      rw [riemannianEDist_comm]
      simpa only [V, ENNReal.toReal_ofReal hrad] using hmreal
    have htri := edist_toReal_tri (I := I) p y z₁.proj
    dsimp only [ρ]
    linarith
  have hmin : IsLocalMin (fun y : M => U y + V y) q := by
    change ∀ᶠ y in 𝓝 q, U q + V q ≤ U y + V y
    filter_upwards [hlower, hupper] with y hly huy
    rw [hsum_q]
    linarith
  have hsum_diff : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => U y + V y) q := hUdiff.add hVdiff
  have hsum_zero : mfderiv I 𝓘(Real, Real)
      (fun y : M => U y + V y) q = 0 :=
    mfderiv_eq_zero_at_spatial_min (I := I) hmin hsum_diff
  let L : M → Real := fun y => ρ z₁.proj - V y
  let DU : TangentSpace I q →L[Real] Real := by
    exact mfderiv I 𝓘(Real, Real) U q
  let DV : TangentSpace I q →L[Real] Real := by
    exact mfderiv I 𝓘(Real, Real) V q
  have hUhas : HasMFDerivAt I 𝓘(Real, Real) U q DU := by
    dsimp only [DU]
    exact hUdiff.hasMFDerivAt
  have hVhas : HasMFDerivAt I 𝓘(Real, Real) V q DV := by
    dsimp only [DV]
    exact hVdiff.hasMFDerivAt
  have hsum_has : HasMFDerivAt I 𝓘(Real, Real) (U + V) q
      (DU + DV) := hUhas.add hVhas
  have hsum_zero' : DU + DV = 0 := by
    rw [← hsum_has.mfderiv]
    exact hsum_zero
  have hDU : DU = -DV := eq_neg_of_add_eq_zero_left hsum_zero'
  have hLhas0 : HasMFDerivAt I 𝓘(Real, Real) L q
      ((0 : TangentSpace I q →L[Real] Real) - DV) := by
    have hconst : HasMFDerivAt I 𝓘(Real, Real)
        (fun _ : M => ρ z₁.proj) q
        (0 : TangentSpace I q →L[Real] Real) := by
      exact hasMFDerivAt_const (I := I) (I' := 𝓘(Real, Real))
        (c := ρ z₁.proj) (x := q)
    have hsub := hconst.sub hVhas
    change HasMFDerivAt I 𝓘(Real, Real)
      ((fun _ : M => ρ z₁.proj) - V) q
      ((0 : TangentSpace I q →L[Real] Real) - DV)
    exact hsub
  have hLhas : HasMFDerivAt I 𝓘(Real, Real) L q DU := by
    rw [hDU]
    simpa only [zero_sub] using hLhas0
  have hρhas : HasMFDerivAt I 𝓘(Real, Real) ρ q DU := by
    apply hasMFDerivAt_of_le hLhas hUhas
    · dsimp only [L]
      rw [← hsum_q, hUq]
      ring
    · exact hUq.symm
    · filter_upwards [hlower, hupper] with y hly huy
      exact ⟨hly, huy⟩
  refine ⟨hρhas.mdifferentiableAt, ?_⟩
  have hgrad_eq : gradientFun (I := I) g ρ q =
      gradientFun (I := I) g U q := by
    apply (metricFlatEquiv (I := I) g q).injective
    ext w
    rw [metricFlatEquiv_apply, metricFlatEquiv_apply]
    rw [inner_gradientFun, inner_gradientFun]
    rw [mvfderiv_real_eq_mfderiv, mvfderiv_real_eq_mfderiv]
    rw [hρhas.mfderiv, hUhas.mfderiv]
    rfl
  rw [hgrad_eq]
  simpa only [U, q] using grad_branchRadius (I := I) Bp hvBp hv_pos

end Riemannian
end Geometry
end DifferentialGeometry

end
