import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ClassWidth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import DifferentialGeometry.Geometry.Geodesic.Chart.Regularity
import DifferentialGeometry.Geometry.Metric.ShortGeodesic
import DifferentialGeometry.Geometry.Metric.Comparison.CurveLength
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Comparison.Distance.EndpointRate
import DifferentialGeometry.Topology.Compactness.DiagonalNeighborhood
import DifferentialGeometry.Topology.Manifold.ZeroDimensional
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

structure FlatteningProfile where
  psi : ℝ → ℝ
  smooth : ContDiff ℝ ∞ psi
  nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ psi x
  positive : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < psi x
  integral_one : (∫ x in (0 : ℝ)..1, psi x) = 1
  flat_zero : ∀ m : ℕ, iteratedDeriv m psi 0 = 0
  flat_one : ∀ m : ℕ, iteratedDeriv m psi 1 = 0
  symmetric : ∀ x ∈ Icc (0 : ℝ) 1, psi (1 - x) = psi x
  monotone_first_half : MonotoneOn psi (Icc (0 : ℝ) (1 / 2))


def FlatteningProfile.beta (P : FlatteningProfile) (x : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..x, P.psi w

private theorem zero_jets_left {f : ℝ → ℝ} {x : ℝ} (hf : ContDiff ℝ ∞ f)
    (hz : EqOn f (fun _ => 0) (Iio x)) (m : ℕ) : iteratedDeriv m f x = 0 := by
  have heq : EqOn (iteratedDeriv m f) (fun _ => 0) (Iio x) := by
    intro y hy
    simpa only [iteratedDeriv_fun_const_zero] using (hz.iteratedDeriv_of_isOpen isOpen_Iio m) hy
  exact heq.closure (ContDiff.continuous_iteratedDeriv' m (contDiff_infty.mp hf m)) continuous_const
    (by simp only [closure_Iio, mem_Iic, le_refl])

private theorem zero_jets_right {f : ℝ → ℝ} {x : ℝ} (hf : ContDiff ℝ ∞ f)
    (hz : EqOn f (fun _ => 0) (Ioi x)) (m : ℕ) : iteratedDeriv m f x = 0 := by
  have heq : EqOn (iteratedDeriv m f) (fun _ => 0) (Ioi x) := by
    intro y hy
    simpa only [iteratedDeriv_fun_const_zero] using (hz.iteratedDeriv_of_isOpen isOpen_Ioi m) hy
  exact heq.closure (ContDiff.continuous_iteratedDeriv' m (contDiff_infty.mp hf m)) continuous_const
    (by simp only [closure_Ioi, mem_Ici, le_refl])


theorem flatteningProfile_exists : Nonempty FlatteningProfile := by
  let raw : ℝ → ℝ := fun x => expNegInvGlue (x * (1 - x))
  have hraw : ContDiff ℝ ∞ raw :=
    expNegInvGlue.contDiff.comp (contDiff_id.mul (contDiff_const.sub contDiff_id))
  have hrawpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < raw x :=
    expNegInvGlue.pos_of_pos (mul_pos hx.1 (sub_pos.mpr hx.2))
  let Z : ℝ := ∫ x in (0 : ℝ)..1, raw x
  have hZ : 0 < Z := intervalIntegral.integral_pos (by norm_num)
    hraw.continuous.continuousOn (fun x _ => expNegInvGlue.nonneg _)
    ⟨1 / 2, by norm_num, hrawpos _ (by norm_num)⟩
  let psi : ℝ → ℝ := fun x => raw x / Z
  have hpsi : ContDiff ℝ ∞ psi := hraw.div_const Z
  refine ⟨{
    psi := psi
    smooth := hpsi
    nonneg := ?_
    positive := ?_
    integral_one := ?_
    flat_zero := ?_
    flat_one := ?_
    symmetric := ?_
    monotone_first_half := ?_ }⟩
  · intro x _hx
    exact div_nonneg (expNegInvGlue.nonneg _) hZ.le
  · intro x hx
    exact div_pos (hrawpos x hx) hZ
  · change (∫ x in (0 : ℝ)..1, raw x / Z) = 1
    rw [intervalIntegral.integral_div]
    exact div_self hZ.ne'
  · intro m
    apply zero_jets_left hpsi ?_ m
    intro x hx
    change x < 0 at hx
    have hz : raw x = 0 := expNegInvGlue.zero_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (show x ≤ 0 from le_of_lt hx) (by linarith))
    simp only [psi, hz, zero_div]
  · intro m
    apply zero_jets_right hpsi ?_ m
    intro x hx
    change 1 < x at hx
    have hz : raw x = 0 := expNegInvGlue.zero_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x by linarith [hx]) (by linarith [hx]))
    simp only [psi, hz, zero_div]
  · intro x _hx
    change expNegInvGlue ((1 - x) * (1 - (1 - x))) / Z =
      expNegInvGlue (x * (1 - x)) / Z
    congr 2
    ring
  · intro x hx y hy hxy
    apply div_le_div_of_nonneg_right _ hZ.le
    apply expNegInvGlue.monotone
    have hprod := mul_nonneg (sub_nonneg.mpr hxy)
      (show 0 ≤ 1 - x - y by linarith [hy.2])
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

def IsShortSegment (g : SmoothRiemannianMetric I Q) (p q : Q) (c : ℝ → Q) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c (Ioo (-1 : ℝ) 2) ∧
    IsGeodesicOn (I := I) g c (Ioo (-1 : ℝ) 2) ∧
    c 0 = p ∧ c 1 = q ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      riemannianEDistOf g (c s) (c t) =
        ENNReal.ofReal |s - t| * riemannianEDistOf g p q

def shortSegment (g : SmoothRiemannianMetric I Q) (p q : Q) : ℝ → Q := by
  classical
  exact if h : ∃ c : ℝ → Q, IsShortSegment g p q c then Classical.choose h else fun _ => p


def polygonVertex (γ : Surgery.Topology.Circle → Q) (N : ℕ) (i : ℤ) : Q :=
  γ (((i : ℝ) / N : ℝ) : Surgery.Topology.Circle)

def flatPolygon (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    (N : ℕ) (γ : Surgery.Topology.Circle → Q) : Surgery.Topology.Circle → Q :=
  AddCircle.liftIco (1 : ℝ) 0 (fun x : ℝ =>
    let i : ℤ := ⌊(N : ℝ) * x⌋
    shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
      (P.beta ((N : ℝ) * x - i)))

def initialRamp (γ : Surgery.Topology.Circle → Q) : ProductCurve Q where
  map x _ := (γ x, x)
  y x _ := x
  degree := 1
  lift_eq _ _ := rfl
  increment _ _ := by simp

variable [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
include hT2 hCompact hConnected hBoundary

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem shortSegment_neighborhood (g : SmoothRiemannianMetric I Q) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ p q, riemannianEDistOf g p q < ENNReal.ofReal radius →
        IsShortSegment g p q (shortSegment g p q) ∧
        ∀ c : ℝ → Q, IsShortSegment g p q c →
          EqOn c (shortSegment g p q) (Ioo (-1 : ℝ) 2)) ∧
      ContMDiffOn ((I.prod I).prod 𝓘(ℝ, ℝ)) I ∞
        (fun z : (Q × Q) × ℝ => shortSegment g z.1.1 z.1.2 z.2)
        ({pq : Q × Q | riemannianEDistOf g pq.1 pq.2 < ENNReal.ofReal radius} ×ˢ
          Ioo (-1 : ℝ) 2) ∧
      ∀ p t, t ∈ Icc (0 : ℝ) 1 → shortSegment g p p t = p := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton Q :=
      DifferentialGeometry.subsingleton_of_preconnected_of_finrank_eq_zero I hdim
    have hsub : ∀ a b : Q, a = b := fun a b => Subsingleton.elim a b
    refine ⟨1, one_pos, ?_, ?_, ?_⟩
    · intro p q _h
      obtain rfl : p = q := hsub p q
      have hex : ∃ c : ℝ → Q, IsShortSegment g p p c :=
        ⟨fun _ => p, contMDiffOn_const, (isGeodesic_const g p).isGeodesicOn _,
          rfl, rfl, fun s _ t _ => by simp only [riemannianEDistOf_self, mul_zero]⟩
      have hshort : shortSegment g p p = Classical.choose hex := by
        rw [shortSegment, dif_pos hex]
      refine ⟨?_, ?_⟩
      · rw [hshort]; exact Classical.choose_spec hex
      · intro c _hc t _ht; exact hsub _ _
    · have hconst : (fun z : (Q × Q) × ℝ => shortSegment g z.1.1 z.1.2 z.2) =
          fun _ => Classical.choice (inferInstance : Nonempty Q) := by
        funext z; exact hsub _ _
      rw [hconst]
      exact contMDiffOn_const
    · intro p t _ht; exact hsub _ _
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    let : RiemannianBundle (TangentSpace I : Q → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace I : Q → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let : PseudoEMetricSpace Q := .ofRiemannianMetric I Q
    have hEnorm : IsMetricNorm (I := I) (M := Q) g :=
      fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
    have hdist : ∀ p q : Q, riemannianEDistOf g p q = edist p q := fun p q => rfl
    obtain ⟨ε, hε, hinj⟩ :=
      DifferentialGeometry.Geometry.exists_uniform_diagExp_injective (I := I) g hEnorm
    obtain ⟨W, hW, hdiagW, hsmoothW⟩ :=
      exists_smooth_shortGeodesic_neighborhood (I := I) g hEnorm
    obtain ⟨A, U, _hA, hU, htime, hdiagU, hAUW⟩ :=
      generalized_tube_lemma (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2))
        (isCompact_range (continuous_id.prodMk continuous_id)) hW
        (by
          rintro ⟨t, z⟩ ⟨_ht, p, hp⟩
          change (p, p) = z at hp
          subst z
          exact hdiagW t p)
    obtain ⟨ρs, hρs, hρsU⟩ :=
      DifferentialGeometry.Analysis.exists_uniform_diagonal_radius hU
        (fun x => hdiagU (mem_range_self x))
    have h0mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 := by norm_num
    have h1mem : (1 : ℝ) ∈ Ioo (-1 : ℝ) 2 := by norm_num
    have hchar : ∀ (p q : Q) (c : ℝ → Q), IsShortSegment g p q c →
        ∀ t ∈ Ioo (-1 : ℝ) 2, c t = expMapIntrinsic (I := I) g hEnorm p
          (t • ((mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) : E) : TangentSpace I p)) := by
      intro p q c hc t ht
      let v : TangentSpace I p := ((mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) : E))
      have heq : EqOn c (intrinsicGeodesic (I := I) g hEnorm p v) (Ioo (-1 : ℝ) 2) := by
        refine geo_eqOn_of_initial (I := I) g isOpen_Ioo isPreconnected_Ioo h0mem hc.2.1
          ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v).isGeodesicOn _)
          hc.1.continuousOn (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousOn
          (by rw [intrinsicGeodesic_zero]; exact hc.2.2.1) ?_
        exact (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v).symm
      calc c t = intrinsicGeodesic (I := I) g hEnorm p v t := heq ht
        _ = intrinsicGeodesic (I := I) g hEnorm p (t • v) 1 :=
              (intrinsicGeodesic_smul (I := I) g hEnorm p v t).symm
        _ = expMapIntrinsic (I := I) g hEnorm p (t • v) := rfl
    have hkey : ∀ (p q : Q) (c₁ c₂ : ℝ → Q), riemannianEDistOf g p q ≠ ⊤ →
        (riemannianEDistOf g p q).toReal < ε →
        IsShortSegment g p q c₁ → IsShortSegment g p q c₂ →
        EqOn c₁ c₂ (Ioo (-1 : ℝ) 2) := by
      intro p q c₁ c₂ hDne hDlt hc₁ hc₂
      have hnorm : ∀ (c : ℝ → Q), IsShortSegment g p q c →
          Real.sqrt (g.inner p
            (((mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) : E)) : TangentSpace I p)
            (((mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) : E)) : TangentSpace I p)) =
          (riemannianEDistOf g p q).toReal := by
        intro c hc
        have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I c 0 :=
          (hc.1.contMDiffAt (isOpen_Ioo.mem_nhds h0mem)).mdifferentiableAt (by norm_num)
        have hlim := riemannianEDistOf_div_tendsto_speed (I := I) g c 0 hmd
        have hIoo : Ioo (0 : ℝ) 1 ∈ 𝓝[Ioi (0 : ℝ)] (0 : ℝ) := by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          refine ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo.mem_nhds (by norm_num), ?_⟩
          rintro h ⟨hh, hpos⟩
          exact ⟨hpos, hh.2⟩
        have hev : (fun h : ℝ => (riemannianEDistOf g (c (0 + h)) (c 0)).toReal / h)
            =ᶠ[𝓝[Ioi (0 : ℝ)] (0 : ℝ)] fun _ => (riemannianEDistOf g p q).toReal := by
          filter_upwards [hIoo] with h hh
          have hpos : 0 < h := hh.1
          have hmem : h ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hpos, le_of_lt hh.2⟩
          have hdf := hc.2.2.2.2 h hmem 0 ⟨le_rfl, zero_le_one⟩
          have habs : |h - 0| = h := by rw [sub_zero, abs_of_pos hpos]
          rw [habs] at hdf
          have hprod : (ENNReal.ofReal h * riemannianEDistOf g p q).toReal =
              h * (riemannianEDistOf g p q).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hpos)]
          rw [zero_add, hdf, hprod]
          exact mul_div_cancel_left₀ _ (ne_of_gt hpos)
        have hlim2 : Tendsto (fun h : ℝ =>
            (riemannianEDistOf g (c (0 + h)) (c 0)).toReal / h) (𝓝[Ioi (0 : ℝ)] (0 : ℝ))
            (𝓝 (riemannianEDistOf g p q).toReal) :=
          tendsto_const_nhds.congr' hev.symm
        have h := tendsto_nhds_unique hlim hlim2
        rwa [hc.2.2.1] at h
      have hvt : ∀ (c : ℝ → Q), IsShortSegment g p q c →
          expMapIntrinsic (I := I) g hEnorm p
            (((mfderiv 𝓘(ℝ, ℝ) I c 0 (1 : ℝ) : E)) : TangentSpace I p) = q := by
        intro c hc
        have h := hchar p q c hc 1 h1mem
        rw [one_smul, hc.2.2.2.1] at h
        exact h.symm
      have hveq : ((mfderiv 𝓘(ℝ, ℝ) I c₁ 0 (1 : ℝ) : E) : TangentSpace I p) =
          ((mfderiv 𝓘(ℝ, ℝ) I c₂ 0 (1 : ℝ) : E) : TangentSpace I p) := by
        have hu1 : Real.sqrt (g.inner p
            (((mfderiv 𝓘(ℝ, ℝ) I c₁ 0 (1 : ℝ) : E)) : TangentSpace I p)
            (((mfderiv 𝓘(ℝ, ℝ) I c₁ 0 (1 : ℝ) : E)) : TangentSpace I p)) ≤ ε :=
          (hnorm c₁ hc₁).trans_le hDlt.le
        have hu2 : Real.sqrt (g.inner p
            (((mfderiv 𝓘(ℝ, ℝ) I c₂ 0 (1 : ℝ) : E)) : TangentSpace I p)
            (((mfderiv 𝓘(ℝ, ℝ) I c₂ 0 (1 : ℝ) : E)) : TangentSpace I p)) ≤ ε :=
          (hnorm c₂ hc₂).trans_le hDlt.le
        have hdiag : diagExp (I := I) g hEnorm
              (TotalSpace.mk' E p (((mfderiv 𝓘(ℝ, ℝ) I c₁ 0 (1 : ℝ) : E)) : TangentSpace I p)) =
            diagExp (I := I) g hEnorm
              (TotalSpace.mk' E p (((mfderiv 𝓘(ℝ, ℝ) I c₂ 0 (1 : ℝ) : E)) : TangentSpace I p)) := by
          rw [diagExp_apply, diagExp_apply, hvt c₁ hc₁, hvt c₂ hc₂]
        have := hinj hu1 hu2 hdiag
        exact congrArg Bundle.TotalSpace.snd this
      intro t ht
      calc c₁ t = expMapIntrinsic (I := I) g hEnorm p
            (t • ((mfderiv 𝓘(ℝ, ℝ) I c₁ 0 (1 : ℝ) : E) : TangentSpace I p)) :=
            hchar p q c₁ hc₁ t ht
        _ = expMapIntrinsic (I := I) g hEnorm p
            (t • ((mfderiv 𝓘(ℝ, ℝ) I c₂ 0 (1 : ℝ) : E) : TangentSpace I p)) :=
            congrArg (fun w : TangentSpace I p =>
              expMapIntrinsic (I := I) g hEnorm p (t • w)) hveq
        _ = c₂ t := (hchar p q c₂ hc₂ t ht).symm
    have hseg : ∀ (p q : Q), riemannianEDistOf g p q ≠ ⊤ →
        IsShortSegment g p q (shortGeodesic g hEnorm p q) := by
      intro p q hDne
      set D : ℝ := (riemannianEDistOf g p q).toReal with hDdef
      have hDnn : 0 ≤ D := ENNReal.toReal_nonneg
      have hspeed : ∀ u : ℝ, Real.sqrt (g.inner (shortGeodesic g hEnorm p q u)
          (mfderiv 𝓘(ℝ, ℝ) I (shortGeodesic g hEnorm p q) u (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (shortGeodesic g hEnorm p q) u (1 : ℝ))) = D := by
        intro u
        have hred : riemannianEDistOf (I := I) g p q = Manifold.riemannianEDist I p q := rfl
        have h := shortGeodesic_speed (I := I) g hEnorm hDne u
        rw [hDdef, hred]
        exact h
      have hsmoothInf : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (shortGeodesic g hEnorm p q) univ :=
        intrinsicGeodesic_contMDiffOn_infty (I := I) g hEnorm p (minimizingLog g hEnorm p q)
      have hbound : ∀ {a b : ℝ}, a ≤ b → b ≤ 1 →
          riemannianEDistOf g (shortGeodesic g hEnorm p q a) (shortGeodesic g hEnorm p q b) ≤
            ENNReal.ofReal ((b - a) * D) := by
        intro a b hab hb
        have h1 := DifferentialGeometry.riemannianEDistOf_le_arcLength (I := I) g hab
          ((hsmoothInf.of_le (ENat.LEInfty.out (m := (1 : ℕ∞ω)))).mono (subset_univ _))
        have h2 : Variation.arcLength (I := I) g (shortGeodesic g hEnorm p q) a b = (b - a) * D := by
          rw [Variation.arcLength]
          have hconst : (∫ u in a..b, D) = (b - a) * D := by
            rw [intervalIntegral.integral_const]; ring
          rw [← hconst]
          exact intervalIntegral.integral_congr (fun u _ => hspeed u)
        rwa [h2] at h1
      have hmain : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → s ≤ t →
          riemannianEDistOf g (shortGeodesic g hEnorm p q s) (shortGeodesic g hEnorm p q t) =
            ENNReal.ofReal ((t - s) * D) := by
        intro s t hs ht hst
        have hle : riemannianEDistOf g (shortGeodesic g hEnorm p q s)
            (shortGeodesic g hEnorm p q t) ≤ ENNReal.ofReal ((t - s) * D) :=
          hbound hst ht.2
        have hge : ENNReal.ofReal ((t - s) * D) ≤ riemannianEDistOf g
            (shortGeodesic g hEnorm p q s) (shortGeodesic g hEnorm p q t) := by
          set X : ENNReal := riemannianEDistOf g (shortGeodesic g hEnorm p q s)
            (shortGeodesic g hEnorm p q t) with hXdef
          have htri1 := riemannianEDistOf_triangle g p (shortGeodesic g hEnorm p q s) q
          have htri2 := riemannianEDistOf_triangle g (shortGeodesic g hEnorm p q s)
            (shortGeodesic g hEnorm p q t) q
          have hA : riemannianEDistOf g p (shortGeodesic g hEnorm p q s) ≤
              ENNReal.ofReal (s * D) := by
            simpa only [shortGeodesic_zero, sub_zero] using hbound hs.1 hs.2
          have hB : riemannianEDistOf g (shortGeodesic g hEnorm p q t) q ≤
              ENNReal.ofReal ((1 - t) * D) := by
            simpa only [shortGeodesic_one (I := I) g hEnorm hDne]
              using hbound ht.2 (le_refl 1)
          have hcomb : riemannianEDistOf g p q ≤
              ENNReal.ofReal (s * D) + X + ENNReal.ofReal ((1 - t) * D) := by
            calc riemannianEDistOf g p q ≤
                  riemannianEDistOf g p (shortGeodesic g hEnorm p q s) +
                    riemannianEDistOf g (shortGeodesic g hEnorm p q s) q := htri1
              _ ≤ ENNReal.ofReal (s * D) + (X + ENNReal.ofReal ((1 - t) * D)) :=
                  add_le_add hA (htri2.trans (add_le_add le_rfl hB))
              _ = ENNReal.ofReal (s * D) + X + ENNReal.ofReal ((1 - t) * D) := by
                  rw [add_assoc]
          have hDfin : riemannianEDistOf g p q = ENNReal.ofReal D := by
            rw [hDdef]; exact (ENNReal.ofReal_toReal hDne).symm
          have hY : ENNReal.ofReal ((1 - (t - s)) * D) ≠ ⊤ := ENNReal.ofReal_ne_top
          have h1nn : 0 ≤ (t - s) * D := mul_nonneg (sub_nonneg.mpr hst) hDnn
          have h2nn : 0 ≤ (1 - (t - s)) * D :=
            mul_nonneg (by linarith [ht.2, hs.1]) hDnn
          have h3nn : 0 ≤ s * D := mul_nonneg hs.1 hDnn
          have h4nn : 0 ≤ (1 - t) * D := mul_nonneg (by linarith [ht.2]) hDnn
          have hleft : ENNReal.ofReal D = ENNReal.ofReal ((t - s) * D) +
              ENNReal.ofReal ((1 - (t - s)) * D) := by
            rw [← ENNReal.ofReal_add h1nn h2nn]
            congr 1; ring
          have hright : ENNReal.ofReal (s * D) + ENNReal.ofReal ((1 - t) * D) =
              ENNReal.ofReal ((1 - (t - s)) * D) := by
            rw [← ENNReal.ofReal_add h3nn h4nn]
            congr 1; ring
          have hrhs : ENNReal.ofReal (s * D) + X + ENNReal.ofReal ((1 - t) * D) =
              X + ENNReal.ofReal ((1 - (t - s)) * D) := by
            rw [add_comm (ENNReal.ofReal (s * D)) X, add_assoc, hright]
          rw [hDfin, hleft, hrhs] at hcomb
          exact (ENNReal.add_le_add_iff_right hY).mp hcomb
        exact le_antisymm hle hge
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact hsmoothInf.mono (subset_univ _)
      · exact (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
          (minimizingLog g hEnorm p q)).isGeodesicOn _
      · exact shortGeodesic_zero (I := I) g hEnorm p q
      · exact shortGeodesic_one (I := I) g hEnorm hDne
      · intro s hs t ht
        rcases le_total s t with hst | hts
        · have h1 := hmain s t hs ht hst
          have h2 : ENNReal.ofReal ((t - s) * D) =
              ENNReal.ofReal |s - t| * riemannianEDistOf g p q := by
            rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub,
              ENNReal.ofReal_mul (sub_nonneg.mpr hst), hDdef, ENNReal.ofReal_toReal hDne]
          rw [h1, h2]
        · have h1 := hmain t s ht hs hts
          have h2 : ENNReal.ofReal ((s - t) * D) =
              ENNReal.ofReal |s - t| * riemannianEDistOf g p q := by
            rw [abs_of_nonneg (sub_nonneg.mpr hts), ENNReal.ofReal_mul (sub_nonneg.mpr hts),
              hDdef, ENNReal.ofReal_toReal hDne]
          conv_lhs => rw [riemannianEDistOf_comm g (shortGeodesic g hEnorm p q s)
            (shortGeodesic g hEnorm p q t)]
          rw [h1, h2]
    refine ⟨min (ρs : ℝ) ε, lt_min (by exact_mod_cast hρs) hε, ?_, ?_, ?_⟩
    · intro p q hpq
      have hne : riemannianEDistOf g p q ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hpq le_top)
      have hDlt : (riemannianEDistOf g p q).toReal < ε :=
        ENNReal.toReal_ofReal hε.le ▸
          ((ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).mpr
            (lt_of_lt_of_le hpq (ENNReal.ofReal_le_ofReal (min_le_right _ _))))
      have hex : ∃ c : ℝ → Q, IsShortSegment g p q c := ⟨_, hseg p q hne⟩
      have hshort : shortSegment g p q = Classical.choose hex := by
        rw [shortSegment, dif_pos hex]
      have hspec : IsShortSegment g p q (shortSegment g p q) := by
        rw [hshort]; exact Classical.choose_spec hex
      exact ⟨hspec, fun c hc => hkey p q c (shortSegment g p q) hne hDlt hc hspec⟩
    · have hsmoothA : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod I)) I ∞
          (fun p : ℝ × (Q × Q) => shortGeodesic g hEnorm p.2.1 p.2.2 p.1) (A ×ˢ U) :=
        hsmoothW.mono hAUW
      have hswap : ContMDiff ((I.prod I).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (I.prod I)) ∞
          (fun z : (Q × Q) × ℝ => (z.2, z.1)) :=
        contMDiff_snd.prodMk contMDiff_fst
      have hcomp : ContMDiffOn ((I.prod I).prod 𝓘(ℝ, ℝ)) I ∞
          (fun z : (Q × Q) × ℝ => shortGeodesic g hEnorm z.1.1 z.1.2 z.2)
          {z : (Q × Q) × ℝ | z.2 ∈ A ∧ z.1 ∈ U} :=
        hsmoothA.comp hswap.contMDiffOn (fun z hz => hz)
      have hsubS : ({pq : Q × Q | riemannianEDistOf g pq.1 pq.2 <
            ENNReal.ofReal (min (ρs : ℝ) ε)} ×ˢ Ioo (-1 : ℝ) 2) ⊆
          {z : (Q × Q) × ℝ | z.2 ∈ A ∧ z.1 ∈ U} := by
        rintro ⟨pq, t⟩ ⟨hpq, ht⟩
        refine ⟨htime ⟨le_of_lt ht.1, le_of_lt ht.2⟩, ?_⟩
        refine hρsU pq.1 pq.2 ?_
        rw [← hdist]
        simpa only [ENNReal.ofReal_coe_nnreal] using le_of_lt (lt_of_lt_of_le hpq
          (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
      refine (hcomp.mono hsubS).congr fun z hz => ?_
      obtain ⟨hzball, hzIoo⟩ := hz
      have hne : riemannianEDistOf g z.1.1 z.1.2 ≠ ⊤ :=
        ne_top_of_lt (lt_of_lt_of_le hzball le_top)
      have hDlt : (riemannianEDistOf g z.1.1 z.1.2).toReal < ε :=
        ENNReal.toReal_ofReal hε.le ▸
          ((ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).mpr
            (lt_of_lt_of_le hzball (ENNReal.ofReal_le_ofReal (min_le_right _ _))))
      have hex : ∃ c : ℝ → Q, IsShortSegment g z.1.1 z.1.2 c := ⟨_, hseg z.1.1 z.1.2 hne⟩
      have hshort : shortSegment g z.1.1 z.1.2 = Classical.choose hex := by
        rw [shortSegment, dif_pos hex]
      have hspec : IsShortSegment g z.1.1 z.1.2 (shortSegment g z.1.1 z.1.2) := by
        rw [hshort]; exact Classical.choose_spec hex
      exact (hkey z.1.1 z.1.2 (shortGeodesic g hEnorm z.1.1 z.1.2)
        (shortSegment g z.1.1 z.1.2) hne hDlt (hseg z.1.1 z.1.2 hne) hspec hzIoo).symm
    · intro p t ht
      have hp : riemannianEDistOf g p p < ENNReal.ofReal (min (ρs : ℝ) ε) := by
        rw [riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.mpr (lt_min (by exact_mod_cast hρs) hε)
      have hne : riemannianEDistOf g p p ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hp le_top)
      have hDlt : (riemannianEDistOf g p p).toReal < ε :=
        ENNReal.toReal_ofReal hε.le ▸
          ((ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).mpr
            (lt_of_lt_of_le hp (ENNReal.ofReal_le_ofReal (min_le_right _ _))))
      have hconstseg : IsShortSegment g p p (fun _ : ℝ => p) :=
        ⟨contMDiffOn_const, (isGeodesic_const g p).isGeodesicOn _,
          rfl, rfl, fun s _ t _ => by simp only [riemannianEDistOf_self, mul_zero]⟩
      have hex : ∃ c : ℝ → Q, IsShortSegment g p p c := ⟨_, hconstseg⟩
      have hshort : shortSegment g p p = Classical.choose hex := by
        rw [shortSegment, dif_pos hex]
      have hspec : IsShortSegment g p p (shortSegment g p p) := by
        rw [hshort]; exact Classical.choose_spec hex
      exact (hkey p p (fun _ => p) (shortSegment g p p) hne hDlt hconstseg hspec
        ⟨by linarith [ht.1], by linarith [ht.2]⟩).symm

theorem rfs_flat_polygon_bounds (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ (N : ℕ), 2 ≤ N → ∀ γ : RegularLoop I Q,
        (∀ i : Fin N, riemannianEDistOf g (polygonVertex γ N i.val)
          (polygonVertex γ N (i.val + 1)) < ENNReal.ofReal radius) →
        ∃ c : RegularLoop I Q,
          (∀ z, c z = flatPolygon g P N γ z) ∧
          ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift c.toContinuousLoop) ∧
          (∀ (i : ℤ) (m : ℕ), 0 < m →
            iteratedDeriv m (e.map ∘ loopLift c.toContinuousLoop) ((i : ℝ) / N) = 0) ∧
          loopLength g c.toContinuousLoop =
            ∑ i : Fin N, (riemannianEDistOf g (polygonVertex γ N i.val)
              (polygonVertex γ N (i.val + 1))).toReal ∧
          loopLength g c.toContinuousLoop ≤ loopLength g γ.toContinuousLoop ∧
          ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
            (initialRamp c).SmoothOn (I := I) univ ∧
            (initialRamp c).IsRampOn (fun _ => g) lambda univ ∧
            (initialRamp c).length (fun _ => g) lambda 0 ≤ loopLength g γ.toContinuousLoop + 1 ∧
            (initialRamp c).totalCurvature (fun _ => g) lambda 0 ≤ (N : ℝ) * Real.pi) ∧
      (∀ (K : Type*) [TopologicalSpace K] (N : ℕ), 2 ≤ N →
        ∀ v : K → Surgery.Topology.Circle → Q,
          (∀ i : Fin N, Continuous (fun k => polygonVertex (v k) N i.val)) →
          (∀ k (i : Fin N), riemannianEDistOf g (polygonVertex (v k) N i.val)
            (polygonVertex (v k) N (i.val + 1)) < ENNReal.ofReal radius) →
          ∀ m : ℕ, Continuous (fun p : K × ℝ =>
            iteratedDeriv m (fun x : ℝ =>
              e.map (flatPolygon g P N (v p.1) (x : Surgery.Topology.Circle))) p.2)) := by
  sorry

theorem rfs_prepared_family (g : SmoothRiemannianMetric I Q) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (eta : ℝ) (heta : 0 < eta) :
    ∃ P : FlatteningProfile, ∃ N : ℕ, 2 ≤ N ∧
      ∃ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        (∀ p z, (prepared p).1 z = flatPolygon g P N (Γ p).1 z) ∧
        HasContinuousSmoothLoopJets e prepared ∧
        ContinuousMap.Homotopic prepared Γ ∧
        (∀ p, |regularLeastArea g (prepared p) - regularLeastArea g (Γ p)| < eta) ∧
        let L₀ := 1 + sSup (Set.range (fun p => loopLength g (Γ p).1.toContinuousLoop))
        let Theta₀ := (N : ℝ) * Real.pi
        let Ainit := familyMaximum g Γ + eta
        0 ≤ L₀ ∧ 0 ≤ Theta₀ ∧ 0 ≤ Ainit ∧
          ∀ p (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
            (initialRamp (prepared p).1).SmoothOn (I := I) univ ∧
            (initialRamp (prepared p).1).IsRampOn (fun _ => g) lambda univ ∧
            (initialRamp (prepared p).1).length (fun _ => g) lambda 0 ≤ L₀ ∧
            (initialRamp (prepared p).1).totalCurvature (fun _ => g) lambda 0 ≤ Theta₀ ∧
            regularLeastArea g (prepared p) ≤ Ainit := by
  sorry

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.beta_zero (P : FlatteningProfile) : P.beta 0 = 0 :=
  intervalIntegral.integral_same

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.beta_one (P : FlatteningProfile) : P.beta 1 = 1 :=
  P.integral_one

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.beta_monotoneOn (P : FlatteningProfile) :
    MonotoneOn P.beta (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx' : IntervalIntegrable P.psi volume (0 : ℝ) x :=
    P.smooth.continuous.intervalIntegrable _ _
  have hy' : IntervalIntegrable P.psi volume x y :=
    P.smooth.continuous.intervalIntegrable _ _
  have hsplit : (∫ w in (0 : ℝ)..x, P.psi w) + (∫ w in x..y, P.psi w) =
      ∫ w in (0 : ℝ)..y, P.psi w :=
    intervalIntegral.integral_add_adjacent_intervals hx' hy'
  have hnonneg : 0 ≤ ∫ w in x..y, P.psi w :=
    intervalIntegral.integral_nonneg hxy
      (fun w hw => P.nonneg w ⟨le_trans hx.1 hw.1, le_trans hw.2 hy.2⟩)
  change P.beta x ≤ P.beta y
  rw [FlatteningProfile.beta, FlatteningProfile.beta, ← hsplit]
  linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.beta_mem_Icc (P : FlatteningProfile) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : P.beta x ∈ Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have h := P.beta_monotoneOn h0 hx hx.1
    rwa [P.beta_zero] at h
  · have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have h := P.beta_monotoneOn hx h1 hx.2
    rwa [P.beta_one] at h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.beta_strictMonoOn (P : FlatteningProfile) :
    StrictMonoOn P.beta (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx' : IntervalIntegrable P.psi volume (0 : ℝ) x :=
    P.smooth.continuous.intervalIntegrable _ _
  have hy' : IntervalIntegrable P.psi volume x y :=
    P.smooth.continuous.intervalIntegrable _ _
  have hsplit : (∫ w in (0 : ℝ)..x, P.psi w) + (∫ w in x..y, P.psi w) =
      ∫ w in (0 : ℝ)..y, P.psi w :=
    intervalIntegral.integral_add_adjacent_intervals hx' hy'
  have hmem : ∀ w ∈ Icc x y, w ∈ Icc (0 : ℝ) 1 :=
    fun w hw => ⟨le_trans hx.1 hw.1, le_trans hw.2 hy.2⟩
  have hpos : 0 < ∫ w in x..y, P.psi w := by
    refine intervalIntegral.integral_pos hxy (P.smooth.continuous.continuousOn.mono hmem)
      (fun w hw => P.nonneg w (hmem w ⟨hw.1.le, hw.2⟩)) ?_
    refine ⟨(x + y) / 2, ⟨by linarith, by linarith⟩, P.positive _ ⟨?_, ?_⟩⟩
    · exact lt_of_le_of_lt hx.1 (by linarith)
    · exact lt_of_lt_of_le (by linarith) hy.2
  change P.beta x < P.beta y
  rw [FlatteningProfile.beta, FlatteningProfile.beta, ← hsplit]
  linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.hasDerivAt_beta (P : FlatteningProfile) (x : ℝ) :
    HasDerivAt P.beta (P.psi x) x :=
  intervalIntegral.integral_hasDerivAt_right (P.smooth.continuous.intervalIntegrable _ _)
    (Continuous.stronglyMeasurableAtFilter P.smooth.continuous volume (𝓝 x))
    P.smooth.continuous.continuousAt

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.deriv_beta (P : FlatteningProfile) (x : ℝ) :
    deriv P.beta x = P.psi x :=
  (P.hasDerivAt_beta x).deriv

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.differentiable_beta (P : FlatteningProfile) :
    Differentiable ℝ P.beta :=
  fun x => (P.hasDerivAt_beta x).differentiableAt

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.contDiff_beta (P : FlatteningProfile) :
    ContDiff ℝ ∞ P.beta := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨P.differentiable_beta, ?_⟩
  have h : deriv P.beta = P.psi := funext fun x => P.deriv_beta x
  rw [h]
  exact P.smooth

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.iteratedDeriv_beta (P : FlatteningProfile) {m : ℕ} (hm : 0 < m)
    (x : ℝ) : iteratedDeriv m P.beta x = iteratedDeriv (m - 1) P.psi x := by
  induction m with
  | zero => exact absurd hm (Nat.lt_irrefl 0)
  | succ k _ =>
      rw [iteratedDeriv_succ', Nat.add_sub_cancel]
      congr 1
      exact funext fun y => P.deriv_beta y

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.iteratedDeriv_beta_zero (P : FlatteningProfile) {m : ℕ} (hm : 0 < m) :
    iteratedDeriv m P.beta 0 = 0 := by
  rw [P.iteratedDeriv_beta hm, P.flat_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem FlatteningProfile.iteratedDeriv_beta_one (P : FlatteningProfile) {m : ℕ} (hm : 0 < m) :
    iteratedDeriv m P.beta 1 = 0 := by
  rw [P.iteratedDeriv_beta hm, P.flat_one]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem iteratedDeriv_comp_eq_zero_of_flat {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℝ → F} {ψ : ℝ → ℝ} {x₀ : ℝ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hflat : ∀ m, 0 < m → iteratedDeriv m ψ x₀ = 0) {m : ℕ} (hm : 0 < m) :
    iteratedDeriv m (φ ∘ ψ) x₀ = 0 := by
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hφ.contDiffAt hψ.contDiffAt
    (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)]
  refine Finset.sum_eq_zero fun c _ => ?_
  obtain ⟨j, -⟩ := c.cover (⟨0, hm⟩ : Fin m)
  have hzero : (fun j : Fin c.length => iteratedDeriv (c.partSize j) ψ x₀) = 0 := by
    funext j
    exact hflat (c.partSize j) (c.partSize_pos j)
  rw [hzero]
  exact ContinuousMultilinearMap.map_coord_zero _ j (by simp)

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
theorem flatPolygon_coe_apply (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) (N : ℕ)
    (γ : Surgery.Topology.Circle → Q) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    flatPolygon g P N γ (x : Surgery.Topology.Circle) =
      shortSegment g (polygonVertex γ N ⌊(N : ℝ) * x⌋)
        (polygonVertex γ N (⌊(N : ℝ) * x⌋ + 1))
        (P.beta ((N : ℝ) * x - ⌊(N : ℝ) * x⌋)) := by
  rw [flatPolygon, AddCircle.liftIco_coe_apply (p := (1 : ℝ)) (a := (0 : ℝ))
    (by simpa using hx)]

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
theorem flatPolygon_apply_of_mem_Ico (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    (N : ℕ) (γ : Surgery.Topology.Circle → Q) {i : ℤ} {x : ℝ} (hN : 0 < N)
    (hi : 0 ≤ i) (hiN : i < N)
    (hx : x ∈ Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N)) :
    flatPolygon g P N γ (x : Surgery.Topology.Circle) =
      shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
        (P.beta ((N : ℝ) * x - i)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hxi : (i : ℝ) ≤ (N : ℝ) * x := by
    have h := (div_le_iff₀ hNR).mp hx.1
    linarith [h]
  have hxi' : (N : ℝ) * x < i + 1 := by
    have h := (lt_div_iff₀ hNR).mp hx.2
    linarith [h]
  have hfloor : ⌊(N : ℝ) * x⌋ = i := Int.floor_eq_iff.mpr ⟨hxi, hxi'⟩
  have hx0 : (0 : ℝ) ≤ x := by
    have h : (0 : ℝ) ≤ (i : ℝ) / N := div_nonneg (by exact_mod_cast hi) hNR.le
    linarith [h, hx.1]
  have hx1 : x < 1 := by
    have hle : ((i : ℝ) + 1) / N ≤ 1 := by
      rw [div_le_one hNR]
      have : (i + 1 : ℤ) ≤ N := by omega
      exact_mod_cast this
    linarith [hx.2, hle]
  have hxI : x ∈ Ico (0 : ℝ) 1 := ⟨hx0, hx1⟩
  rw [flatPolygon_coe_apply g P N γ hxI, hfloor]

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
