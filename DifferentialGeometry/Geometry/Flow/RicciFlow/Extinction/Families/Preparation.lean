import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ClassWidth
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.JetGluing.Seam
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem iteratedDeriv_comp_eq_zero_of_flat_of_contDiffAt {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℝ → F} {ψ : ℝ → ℝ} {x₀ : ℝ} (hφ : ContDiffAt ℝ ∞ φ (ψ x₀))
    (hψ : ContDiffAt ℝ ∞ ψ x₀) (hflat : ∀ m, 0 < m → iteratedDeriv m ψ x₀ = 0)
    {m : ℕ} (hm : 0 < m) : iteratedDeriv m (φ ∘ ψ) x₀ = 0 := by
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hφ hψ
    (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ (∞ : ℕ∞ω))]
  refine Finset.sum_eq_zero fun c _ => ?_
  obtain ⟨j, -⟩ := c.cover (⟨0, hm⟩ : Fin m)
  have hzero : (fun j : Fin c.length => iteratedDeriv (c.partSize j) ψ x₀) = 0 := by
    funext j
    exact hflat (c.partSize j) (c.partSize_pos j)
  rw [hzero]
  exact ContinuousMultilinearMap.map_coord_zero _ j (by simp)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem iteratedDeriv_comp_const_mul_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {m : ℕ} (hf : ContDiff ℝ m f) (N i x : ℝ) :
    iteratedDeriv m (fun y : ℝ => f (N * y - i)) x = N ^ m • iteratedDeriv m f (N * x - i) := by
  set c : ℝ := N * x - i with hc
  have hfun : (fun y : ℝ => f (N * y - i)) =
      fun y : ℝ => (fun z : ℝ => f (N * z + c)) (y - x) := by
    funext y
    congr 1
    rw [hc]; ring
  rw [hfun, iteratedDeriv_comp_sub_const m (fun z : ℝ => f (N * z + c)) x]
  simp only
  have hcomp := iteratedDeriv_comp_const_smul
    (f := fun w : ℝ => f (w + c)) (hf.comp (contDiff_id.add contDiff_const)) N
  rw [hcomp]
  simp only
  have h2 : iteratedDeriv m (fun w : ℝ => f (w + c)) 0 = iteratedDeriv m f c := by
    rw [iteratedDeriv_comp_add_const m f c]
    simp only [zero_add]
  have hNz : N * (x - x) = (0 : ℝ) := by rw [sub_self, mul_zero]
  rw [hNz, h2, hc]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem iteratedDeriv_comp_beta_mul_sub_eq_zero (P : FlatteningProfile) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : ℝ → F} {c : ℝ}
    (hφ : ContDiffAt ℝ ∞ φ (P.beta c)) {N : ℝ} (hN : N ≠ 0) (i : ℝ)
    (hbeta : ∀ k, 0 < k → iteratedDeriv k P.beta c = 0) {m : ℕ} (hm : 0 < m) :
    iteratedDeriv m (φ ∘ fun y : ℝ => P.beta (N * y - i)) ((i + c) / N) = 0 := by
  have harg : N * ((i + c) / N) - i = c := by
    field_simp
    ring
  have hinner : ContDiffAt ℝ ∞ (fun y : ℝ => N * y - i) ((i + c) / N) :=
    ((contDiff_const.mul contDiff_id).sub contDiff_const).contDiffAt
  have hφ' : ContDiffAt ℝ ∞ φ (P.beta (N * ((i + c) / N) - i)) := by
    rw [harg]; exact hφ
  have hψ' : ContDiffAt ℝ ∞ (fun y : ℝ => P.beta (N * y - i)) ((i + c) / N) :=
    ContDiffAt.comp (f := fun y : ℝ => N * y - i) (g := P.beta) ((i + c) / N)
      (by rw [harg]; exact P.contDiff_beta.contDiffAt) hinner
  refine iteratedDeriv_comp_eq_zero_of_flat_of_contDiffAt (ψ := fun y : ℝ => P.beta (N * y - i))
    (x₀ := (i + c) / N) hφ' hψ' ?_ hm
  intro k hk
  rw [iteratedDeriv_comp_const_mul_sub (f := P.beta) (m := k)
      (P.contDiff_beta.of_le (by exact_mod_cast le_top : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω))) N i ((i + c) / N),
    harg]
  rw [hbeta k hk, smul_zero]

omit [CompleteSpace E] hCompact hConnected in
omit hT2 hBoundary in
theorem flatPolygon_add_one (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) (N : ℕ)
    (γ : Surgery.Topology.Circle → Q) (x : ℝ) :
    flatPolygon g P N γ ((x + 1 : ℝ) : Surgery.Topology.Circle) =
      flatPolygon g P N γ (x : Surgery.Topology.Circle) := by
  rw [AddCircle.coe_add_period (p := (1 : ℝ)) x]

omit [CompleteSpace E] hCompact hConnected in
omit hT2 hBoundary in
theorem flatPolygon_add_int (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) (N : ℕ)
    (γ : Surgery.Topology.Circle → Q) (k : ℤ) (x : ℝ) :
    flatPolygon g P N γ ((x + k : ℝ) : Surgery.Topology.Circle) =
      flatPolygon g P N γ (x : Surgery.Topology.Circle) := by
  have hx : (x + (k : ℝ) : ℝ) = x + k • (1 : ℝ) := by simp
  rw [hx, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero, add_zero]


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

omit [CompleteSpace E] hCompact hConnected in
omit hT2 hBoundary in
theorem flatPolygon_eventuallyEq_right (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {N : ℕ} (hN : 0 < N) (γ : Surgery.Topology.Circle → Q) {i : ℤ} (hi : 0 ≤ i) (hiN : i < N) :
    (fun x : ℝ => flatPolygon g P N γ (x : Surgery.Topology.Circle))
      =ᶠ[𝓝[Set.Ici ((i : ℝ) / N)] ((i : ℝ) / N)]
      (fun x : ℝ => shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
        (P.beta ((N : ℝ) * x - i))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hx0 : (i : ℝ) / N ∈ Ico (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by exact_mod_cast hi) hNR.le, ?_⟩
    rw [div_lt_one hNR]
    exact_mod_cast hiN
  have hlt : (i : ℝ) / N < ((i : ℝ) + 1) / N := by
    rw [div_lt_div_iff_of_pos_right hNR]
    linarith
  have hnbhd : (Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) ∩ Iio (((i : ℝ) + 1) / N))
      ∈ 𝓝[Set.Ici ((i : ℝ) / N)] ((i : ℝ) / N) :=
    inter_mem (Icc_mem_nhdsGE hlt) (nhdsWithin_le_nhds (Iio_mem_nhds hlt))
  filter_upwards [hnbhd] with x hx
  rcases eq_or_lt_of_le hx.1.1 with hxe | hxlt
  · subst hxe
    rw [flatPolygon_coe_apply g P N γ hx0]
    have hfloor : ⌊(N : ℝ) * ((i : ℝ) / N)⌋ = i := by
      rw [mul_div_cancel₀ _ (ne_of_gt hNR), Int.floor_intCast]
    rw [hfloor]
  · have hmem : x ∈ Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N) := ⟨hxlt.le, hx.2⟩
    exact flatPolygon_apply_of_mem_Ico g P N γ hN hi hiN hmem

omit [CompleteSpace E] hCompact hConnected in
omit hT2 hBoundary in
theorem flatPolygon_eventuallyEq_left (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {N : ℕ} (hN : 0 < N) (γ : Surgery.Topology.Circle → Q) {i : ℤ} (hi : 0 < i) (hiN : i < N)
    (hsegL : IsShortSegment g (polygonVertex γ N (i - 1)) (polygonVertex γ N i)
      (shortSegment g (polygonVertex γ N (i - 1)) (polygonVertex γ N i)))
    (hsegR : IsShortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)))) :
    (fun x : ℝ => flatPolygon g P N γ (x : Surgery.Topology.Circle))
      =ᶠ[𝓝[Set.Iic ((i : ℝ) / N)] ((i : ℝ) / N)]
      (fun x : ℝ => shortSegment g (polygonVertex γ N (i - 1)) (polygonVertex γ N i)
        (P.beta ((N : ℝ) * x - ((i : ℝ) - 1)))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hi1 : (0 : ℤ) ≤ i - 1 := by omega
  have hi1N : i - 1 < (N : ℤ) := by omega
  have hx0 : (i : ℝ) / N ∈ Ico (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ i)) hNR.le, ?_⟩
    rw [div_lt_one hNR]
    exact_mod_cast hiN
  have hlt : (((i : ℝ) - 1) / N) < (i : ℝ) / N := by
    rw [div_lt_div_iff_of_pos_right hNR]
    linarith
  have hnbhd : (Icc (((i : ℝ) - 1) / N) ((i : ℝ) / N) ∩ Ioi (((i : ℝ) - 1) / N))
      ∈ 𝓝[Set.Iic ((i : ℝ) / N)] ((i : ℝ) / N) :=
    inter_mem (Icc_mem_nhdsLE hlt) (nhdsWithin_le_nhds (Ioi_mem_nhds hlt))
  filter_upwards [hnbhd] with x hx
  rcases eq_or_lt_of_le hx.1.2 with hxe | hxlt
  · subst hxe
    rw [flatPolygon_coe_apply g P N γ hx0]
    have hfloor : ⌊(N : ℝ) * ((i : ℝ) / N)⌋ = i := by
      rw [mul_div_cancel₀ _ (ne_of_gt hNR), Int.floor_intCast]
    rw [hfloor]
    have h0 : (N : ℝ) * ((i : ℝ) / N) - i = 0 := by
      rw [mul_div_cancel₀ _ (ne_of_gt hNR), sub_self]
    have h1 : (N : ℝ) * ((i : ℝ) / N) - ((i : ℝ) - 1) = 1 := by
      rw [mul_div_cancel₀ _ (ne_of_gt hNR)]
      ring
    rw [h0, h1, P.beta_zero, P.beta_one, hsegR.2.2.1, hsegL.2.2.2.1]
  · have hcast : (((i - 1 : ℤ)) : ℝ) = (i : ℝ) - 1 := by push_cast; ring
    have hcast1 : (((i - 1 : ℤ)) : ℝ) + 1 = (i : ℝ) := by push_cast; ring
    have hmem : x ∈ Ico ((((i - 1 : ℤ)) : ℝ) / N) (((((i - 1 : ℤ)) : ℝ) + 1) / N) := by
      refine ⟨?_, ?_⟩
      · rw [hcast]; exact hx.2.le
      · rw [hcast1]; exact hxlt
    have hthis := flatPolygon_apply_of_mem_Ico g P N γ hN hi1 hi1N hmem
    have hz : i - 1 + 1 = i := by omega
    rw [hcast, hz] at hthis
    exact hthis

omit [CompleteSpace E] hCompact hConnected in
theorem IsShortSegment.speed_eq (g : SmoothRiemannianMetric I Q) {p q : Q} {c : ℝ → Q}
    (hc : IsShortSegment g p q c) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    Real.sqrt (g.inner (c s) (mfderiv 𝓘(ℝ, ℝ) I c s (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I c s (1 : ℝ))) = (riemannianEDistOf g p q).toReal := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · have hq : c (1 / 4 : ℝ) = c (1 / 2 : ℝ) :=
      @IsPreconnected.constant ℝ _ Q _ (discrete_topology_of_finrank_eq_zero I hdim)
        (Ioo (-1 : ℝ) 2) isPreconnected_Ioo c hc.1.continuousOn (1 / 4) (1 / 2)
        (by norm_num) (by norm_num)
    have hdf := hc.2.2.2.2 (1 / 4) (by norm_num : (1 / 4 : ℝ) ∈ Icc (0 : ℝ) 1)
      (1 / 2) (by norm_num : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1)
    rw [hq, riemannianEDistOf_self] at hdf
    have hfac : ENNReal.ofReal |(1 / 4 : ℝ) - 1 / 2| ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      norm_num
    have hD : riemannianEDistOf g p q = 0 := by
      rcases mul_eq_zero.mp hdf.symm with h | h
      · exact absurd h hfac
      · exact h
    have hsubE : Subsingleton E := Module.finrank_zero_iff.mp hdim
    have hv : mfderiv 𝓘(ℝ, ℝ) I c s (1 : ℝ) = 0 :=
      @Subsingleton.elim (TangentSpace I (c s)) hsubE _ _
    rw [hD, hv]
    simp
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    have hms : s ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I c s :=
      (hc.1.contMDiffAt (isOpen_Ioo.mem_nhds hms)).mdifferentiableAt (by norm_num)
    have hlim := riemannianEDistOf_div_tendsto_speed (I := I) g c s hmd
    have hIoo : Ioo (0 : ℝ) (1 - s) ∈ 𝓝[Ioi (0 : ℝ)] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by linarith [hs.2])
    have hev : (fun h : ℝ => (riemannianEDistOf g (c (s + h)) (c s)).toReal / h)
        =ᶠ[𝓝[Ioi (0 : ℝ)] (0 : ℝ)] fun _ => (riemannianEDistOf g p q).toReal := by
      filter_upwards [hIoo] with h hh
      have hpos : 0 < h := hh.1
      have hlt : h < 1 - s := hh.2
      have hmem : s + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1, hpos], by linarith⟩
      have hdf := hc.2.2.2.2 (s + h) hmem s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      have habs : |s + h - s| = h := by rw [add_sub_cancel_left, abs_of_pos hpos]
      rw [habs] at hdf
      have hprod : (ENNReal.ofReal h * riemannianEDistOf g p q).toReal =
          h * (riemannianEDistOf g p q).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hpos)]
      rw [hdf, hprod]
      exact mul_div_cancel_left₀ _ (ne_of_gt hpos)
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
private lemma deriv_beta_affine (P : FlatteningProfile) (N : ℕ) (i : ℤ) (x : ℝ) :
    deriv (fun y : ℝ => P.beta ((N : ℝ) * y - (i : ℝ))) x = (N : ℝ) * P.psi ((N : ℝ) * x - (i : ℝ)) := by
  have hinner : HasDerivAt (fun y : ℝ => (N : ℝ) * y - (i : ℝ)) (N : ℝ) x := by
    simpa using ((hasDerivAt_id x).const_mul (N : ℝ)).sub_const (i : ℝ)
  have h2 : HasDerivAt (fun y : ℝ => P.beta ((N : ℝ) * y - (i : ℝ)))
      (P.psi ((N : ℝ) * x - (i : ℝ)) * (N : ℝ)) x :=
    (P.hasDerivAt_beta _).comp x hinner
  rw [h2.deriv, mul_comm]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
private lemma curveVelocity_comp (f : ℝ → Q) (φ : ℝ → ℝ) (t : ℝ)
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f (φ t)) (hφ : DifferentiableAt ℝ φ t) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f (φ s)) t (1 : ℝ) =
      deriv φ t • mfderiv 𝓘(ℝ, ℝ) I f (φ t) (1 : ℝ) := by
  have ha : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t := hφ.mdifferentiableAt
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f (φ s)) t (1 : ℝ) =
      (mfderiv 𝓘(ℝ, ℝ) I f (φ t)) ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t) (1 : ℝ)) :=
    mfderiv_comp_apply (f := φ) (g := f) (x := t) hf ha (1 : ℝ)
  have ha_one : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t) (1 : ℝ) = deriv φ t := by
    have hclm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t =
        ContinuousLinearMap.toSpanSingleton ℝ (deriv φ t) := by
      rw [mfderiv_eq_fderiv, ← toSpanSingleton_deriv]
    have h := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hclm
    rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
    exact h
  rw [hcomp, ha_one]
  let A := mfderiv 𝓘(ℝ, ℝ) I f (φ t)
  have hA : A ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ)) (φ t)).symm (deriv φ t)) =
      deriv φ t • A ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ)) (φ t)).symm 1) := by
    rw [← A.map_smul]
    congr 1
    apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ)) (φ t)).injective
    simp
  with_unfolding_all exact hA

omit [CompleteSpace E] hCompact hConnected in
theorem shortSegment_comp_beta_speed (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {p q : Q} (hseg : IsShortSegment g p q (shortSegment g p q)) {N : ℕ} {i : ℤ} {x : ℝ}
    (ha : (N : ℝ) * x - (i : ℝ) ∈ Ioo (0 : ℝ) 1) :
    Real.sqrt (g.inner (shortSegment g p q (P.beta ((N : ℝ) * x - (i : ℝ))))
      (mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => shortSegment g p q (P.beta ((N : ℝ) * y - (i : ℝ)))) x (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => shortSegment g p q (P.beta ((N : ℝ) * y - (i : ℝ)))) x (1 : ℝ)))
      = (N : ℝ) * P.psi ((N : ℝ) * x - (i : ℝ)) * (riemannianEDistOf g p q).toReal := by
  have haI : (N : ℝ) * x - (i : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hb : P.beta ((N : ℝ) * x - (i : ℝ)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by simpa only [P.beta_zero] using P.beta_strictMonoOn h0 haI ha.1,
      by simpa only [P.beta_one] using P.beta_strictMonoOn haI h1 ha.2⟩
  have hSmd : MDifferentiableAt 𝓘(ℝ, ℝ) I (shortSegment g p q) (P.beta ((N : ℝ) * x - (i : ℝ))) :=
    (hseg.1.contMDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith [hb.1], by linarith [hb.2]⟩)).mdifferentiableAt
      (by norm_num)
  have hφd : DifferentiableAt ℝ (fun y : ℝ => P.beta ((N : ℝ) * y - (i : ℝ))) x := by
    have hinner : Differentiable ℝ (fun y : ℝ => (N : ℝ) * y - (i : ℝ)) := by
      simpa using ((differentiable_id.const_mul (N : ℝ)).sub_const (i : ℝ))
    simpa only [Function.comp_def] using (P.differentiable_beta.comp hinner).differentiableAt
  have hchain := curveVelocity_comp (shortSegment g p q)
    (fun y : ℝ => P.beta ((N : ℝ) * y - (i : ℝ))) x hSmd hφd
  have hderiv := deriv_beta_affine P N i x
  have hnn : 0 ≤ (N : ℝ) * P.psi ((N : ℝ) * x - (i : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg N) (P.nonneg _ haI)
  have hv := IsShortSegment.speed_eq g hseg hb
  rw [hchain, hderiv, gInner_smul_self, ← hv, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]

omit [CompleteSpace E] hCompact hConnected in
private lemma flatPolygon_pointwise_speed (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {N : ℕ} (hN : 0 < N) (γ : Surgery.Topology.Circle → Q) {i : ℤ} (hi : 0 ≤ i) (hiN : i < N)
    (hseg : IsShortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    {x : ℝ} (hxab : x ∈ Ioo ((i : ℝ) / N) (((i : ℝ) + 1) / N)) :
    Real.sqrt (g.inner (flatPolygon g P N γ (x : Surgery.Topology.Circle))
      (mfderiv 𝓘(ℝ, ℝ) I
        (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I
        (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ)))
    = (N : ℝ) * P.psi ((N : ℝ) * x - (i : ℝ)) *
      (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hxilt : (i : ℝ) < (N : ℝ) * x := by
    have h := (div_lt_iff₀ hNR).mp hxab.1
    linarith [h]
  have hxi' : (N : ℝ) * x < (i : ℝ) + 1 := by
    have h := (lt_div_iff₀ hNR).mp hxab.2
    linarith [h]
  have haI : (N : ℝ) * x - (i : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hval := flatPolygon_apply_of_mem_Ico g P N γ hN hi hiN ⟨hxab.1.le, hxab.2⟩
  have hev : (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) =ᶠ[𝓝 x]
      (fun y : ℝ => shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
        (P.beta ((N : ℝ) * y - (i : ℝ)))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxab] with y hy
    exact flatPolygon_apply_of_mem_Ico g P N γ hN hi hiN ⟨hy.1.le, hy.2⟩
  have hmf : mfderiv 𝓘(ℝ, ℝ) I
        (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x =
      mfderiv 𝓘(ℝ, ℝ) I
        (fun y : ℝ => shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
          (P.beta ((N : ℝ) * y - (i : ℝ)))) x :=
    Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I) hev
  rw [hval, hmf]
  exact shortSegment_comp_beta_speed g P hseg haI

omit [CompleteSpace E] hCompact hConnected in
private lemma flatPolygon_piece_integral (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {N : ℕ} (hN : 0 < N) (γ : Surgery.Topology.Circle → Q) {i : ℤ} (hi : 0 ≤ i) (hiN : i < N)
    (hseg : IsShortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)))) :
    (∫ x in ((i : ℝ) / N)..(((i : ℝ) + 1) / N),
        Real.sqrt (g.inner (flatPolygon g P N γ (x : Surgery.Topology.Circle))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))))
      = (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hab : (i : ℝ) / N < ((i : ℝ) + 1) / N := by
    rw [div_lt_div_iff_of_pos_right hNR]
    linarith
  have hpoint : EqOn (fun x : ℝ => Real.sqrt
        (g.inner (flatPolygon g P N γ (x : Surgery.Topology.Circle))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))))
      (fun x : ℝ => (N : ℝ) * P.psi ((N : ℝ) * x - (i : ℝ)) *
        (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal)
      (uIoo ((i : ℝ) / N) (((i : ℝ) + 1) / N)) := by
    intro x hx
    have h1 : (i : ℝ) / N < x := by
      simpa only [min_eq_left hab.le] using hx.1
    have h2 : x < ((i : ℝ) + 1) / N := by
      simpa only [max_eq_right hab.le] using hx.2
    exact flatPolygon_pointwise_speed g P hN γ hi hiN hseg ⟨h1, h2⟩
  rw [intervalIntegral.integral_congr_uIoo hpoint]
  rw [intervalIntegral.integral_mul_const]
  have hsub : (∫ x in ((i : ℝ) / N)..(((i : ℝ) + 1) / N),
      (N : ℝ) * P.psi ((N : ℝ) * x - (i : ℝ))) = ∫ u in (0 : ℝ)..1, P.psi u := by
    have hcomp := intervalIntegral.integral_comp_mul_add (f := fun u : ℝ => (N : ℝ) * P.psi u)
      (a := (i : ℝ) / N) (b := ((i : ℝ) + 1) / N) (c := (N : ℝ)) (d := -(i : ℝ)) hNne
    have hla : (N : ℝ) * ((i : ℝ) / N) + -(i : ℝ) = 0 := by
      field_simp
      ring
    have hlb : (N : ℝ) * (((i : ℝ) + 1) / N) + -(i : ℝ) = 1 := by
      field_simp
      ring
    rw [hla, hlb] at hcomp
    simp only [sub_eq_add_neg]
    rw [hcomp, smul_eq_mul, intervalIntegral.integral_const_mul, ← mul_assoc,
      inv_mul_cancel₀ hNne, one_mul]
  rw [hsub, P.integral_one, one_mul]

omit [CompleteSpace E] hCompact hConnected in
private lemma flatPolygon_piece_intervalIntegrable (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {N : ℕ} (hN : 0 < N) (γ : Surgery.Topology.Circle → Q) {i : ℤ}
    (hi : 0 ≤ i) (hiN : i < N)
    (hseg : IsShortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)))) :
    IntervalIntegrable (fun x : ℝ => Real.sqrt
      (g.inner (flatPolygon g P N γ (x : Surgery.Topology.Circle))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))))
      volume ((i : ℝ) / N) (((i : ℝ) + 1) / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : (i : ℝ) / N < ((i : ℝ) + 1) / N := by
    rw [div_lt_div_iff_of_pos_right hNR]
    linarith
  have hcont : Continuous (fun x : ℝ => (N : ℝ) * P.psi ((N : ℝ) * x - (i : ℝ)) *
      (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal) :=
    (continuous_const.mul (P.smooth.continuous.comp ((continuous_const.mul continuous_id).sub continuous_const))).mul
      continuous_const
  refine (hcont.intervalIntegrable _ _).congr_uIoo ?_
  intro x hx
  have h1 : (i : ℝ) / N < x := by
    simpa only [min_eq_left hab.le] using hx.1
  have h2 : x < ((i : ℝ) + 1) / N := by
    simpa only [max_eq_right hab.le] using hx.2
  exact (flatPolygon_pointwise_speed g P hN γ hi hiN hseg ⟨h1, h2⟩).symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
private lemma integral_zero_one_eq_sum (F : ℝ → ℝ) (N : ℕ) (hN : 0 < N)
    (hint : ∀ k < N, IntervalIntegrable F volume ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N)) :
    (∫ x in (0 : ℝ)..1, F x) =
      ∑ k ∈ Finset.range N, ∫ x in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), F x := by
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := F)
    (a := fun k : ℕ => (k : ℝ) / N) (μ := volume) (n := N) hint
  simpa only [Nat.cast_zero, zero_div, div_self hNne] using h.symm

omit [CompleteSpace E] hCompact hConnected in
theorem flatPolygon_loopLength_eq_sum (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    {N : ℕ} (hN : 0 < N) (γ : Surgery.Topology.Circle → Q) (c : RegularLoop I Q)
    (hc : ∀ z, c z = flatPolygon g P N γ z)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)))) :
    loopLength g c.toContinuousLoop =
      ∑ i : Fin N, (riemannianEDistOf g (polygonVertex γ N (i : ℤ))
        (polygonVertex γ N ((i : ℤ) + 1))).toReal := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hlift : loopLift c.toContinuousLoop =
      fun x : ℝ => flatPolygon g P N γ (x : Surgery.Topology.Circle) := by
    funext x
    rw [loopLift]
    exact hc _
  have hloop : loopLength g c.toContinuousLoop = ∫ x in Icc (0 : ℝ) 1, Real.sqrt
      (g.inner (flatPolygon g P N γ (x : Surgery.Topology.Circle))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))) := by
    rw [loopLength]
    simp only [loopVelocity]
    rw [hlift]
  rw [hloop, ← MeasureTheory.restrict_Ioc_eq_restrict_Icc,
    ← intervalIntegral.integral_of_le zero_le_one]
  have hpieceInt : ∀ k < N, IntervalIntegrable (fun x : ℝ => Real.sqrt
      (g.inner (flatPolygon g P N γ (x : Surgery.Topology.Circle))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))))
      volume ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) := by
    intro k hk
    simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_one] using
      flatPolygon_piece_intervalIntegrable (I := I) g P hN γ (Int.natCast_nonneg k)
        (by exact_mod_cast hk) (hseg (k : ℤ) (Int.natCast_nonneg k) (by exact_mod_cast hk))
  rw [integral_zero_one_eq_sum (fun x : ℝ => Real.sqrt
      (g.inner (flatPolygon g P N γ (x : Surgery.Topology.Circle))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) x (1 : ℝ))))
      N hN hpieceInt]
  rw [Finset.sum_congr rfl (fun k hk => by
    simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_one] using
      flatPolygon_piece_integral (I := I) g P hN γ (Int.natCast_nonneg k)
        (by exact_mod_cast Finset.mem_range.mp hk)
        (hseg (k : ℤ) (Int.natCast_nonneg k) (by exact_mod_cast Finset.mem_range.mp hk)))]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (riemannianEDistOf g (polygonVertex γ N (k : ℤ))
      (polygonVertex γ N ((k : ℤ) + 1))).toReal)]

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
private theorem contDiffAt_map_shortSegment (g : SmoothRiemannianMetric I Q) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) {p q : Q}
    (h : IsShortSegment g p q (shortSegment g p q)) {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 2) :
    ContDiffAt ℝ ∞ (fun y : ℝ => e.map (shortSegment g p q y)) s :=
  ((e.smooth.contMDiffAt).comp s (h.1.contMDiffAt (isOpen_Ioo.mem_nhds hs))).contDiffAt

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
theorem contMDiffOn_shortSegment_beta (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {p q : Q} (h : IsShortSegment g p q (shortSegment g p q))
    {c e : ℝ} {s : Set ℝ} (hmap : ∀ x ∈ s, c * x + e ∈ Icc (0 : ℝ) 1) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun x : ℝ => shortSegment g p q (P.beta (c * x + e))) s := by
  have hinner : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ => P.beta (c * x + e)) s :=
    (P.contDiff_beta.contMDiff.comp
      (((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff)).contMDiffOn
  refine h.1.comp hinner fun x hx => ?_
  have hx' := hmap x hx
  exact ⟨by linarith [(P.beta_mem_Icc hx').1], by linarith [(P.beta_mem_Icc hx').2]⟩

omit [TopologicalSpace Q] in
omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
private theorem polygonVertex_add_int (γ : Surgery.Topology.Circle → Q) (N : ℕ) (i k : ℤ) :
    polygonVertex γ N (i + k * N) = polygonVertex γ N i := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hcast : (((i + k * N : ℤ)) : ℝ) = (i : ℝ) + (k : ℝ) * N := by push_cast; ring
    have hdiv : ((i : ℝ) + (k : ℝ) * N) / N = (i : ℝ) / N + (k : ℝ) := by
      rw [add_div, mul_div_cancel_right₀ _ hNne]
    simp only [polygonVertex, hcast, hdiv]
    have hsmul : (i : ℝ) / N + (k : ℝ) = (i : ℝ) / N + k • (1 : ℝ) := by rw [zsmul_one]
    rw [hsmul, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero,
      add_zero]

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
private theorem contDiffAt_chart_shortSegment (g : SmoothRiemannianMetric I Q) {p q pt : Q}
    (h : IsShortSegment g p q (shortSegment g p q)) {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 2)
    (hv : shortSegment g p q s = pt) :
    ContDiffAt ℝ ∞ (fun y : ℝ => (extChartAt I pt) (shortSegment g p q y)) s := by
  have h1 : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (shortSegment g p q) s := h.1.contMDiffAt (isOpen_Ioo.mem_nhds hs)
  have h2 : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I pt) (shortSegment g p q s) := by
    rw [hv]; exact contMDiffAt_extChartAt
  exact (h2.comp s h1).contDiffAt

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
private theorem flatPolygon_eventuallyEq_left_zero (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {N : ℕ} (hN : 0 < N) (γ : Surgery.Topology.Circle → Q)
    (hsegR : IsShortSegment g (polygonVertex γ N 0) (polygonVertex γ N 1)
      (shortSegment g (polygonVertex γ N 0) (polygonVertex γ N 1)))
    (hsegL : IsShortSegment g (polygonVertex γ N (-1)) (polygonVertex γ N 0)
      (shortSegment g (polygonVertex γ N (-1)) (polygonVertex γ N 0))) :
    (fun x : ℝ => flatPolygon g P N γ (x : Surgery.Topology.Circle))
      =ᶠ[𝓝[Set.Iic 0] 0]
      (fun x : ℝ => shortSegment g (polygonVertex γ N (-1)) (polygonVertex γ N 0)
        (P.beta ((N : ℝ) * x - (-1)))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : -(1 / (N : ℝ)) < 0 := by
    have hp : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  have hmem0 : (0 : ℤ) ≤ ((N : ℤ) - 1) := by omega
  have hmem1 : ((N : ℤ) - 1) < N := by omega
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨Icc (-(1 / (N : ℝ))) 0, Icc_mem_nhdsLE hlt, ?_⟩
  intro x hx
  rcases eq_or_lt_of_le hx.2 with hx0 | hx0
  · subst hx0
    dsimp only
    have hxI : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
    rw [flatPolygon_coe_apply g P N γ hxI]
    have hfloor : ⌊(N : ℝ) * 0⌋ = (0 : ℤ) := by simp
    rw [hfloor]
    norm_num
    rw [P.beta_zero, P.beta_one, hsegR.2.2.1, hsegL.2.2.2.1]
  · have hx1 : x + 1 ∈ Ico ((((N : ℤ) - 1 : ℤ) : ℝ) / (N : ℝ))
        (((((N : ℤ) - 1 : ℤ) : ℝ) + 1) / (N : ℝ)) := by
      constructor
      · have hcastN : ((((N : ℤ) - 1 : ℤ) : ℝ)) = (N : ℝ) - 1 := by push_cast; ring
        rw [div_le_iff₀ hNR, hcastN]
        have hx' : -(1 / (N : ℝ)) ≤ x := hx.1
        have hmul : -(1 / (N : ℝ)) * N ≤ x * N := mul_le_mul_of_nonneg_right hx' hNR.le
        rw [neg_mul, one_div, inv_mul_cancel₀ hNR.ne'] at hmul
        linarith
      · have hN1 : (((((N : ℤ) - 1 : ℤ) : ℝ)) + 1) = (N : ℝ) := by push_cast; ring
        have hdiv : (((((N : ℤ) - 1 : ℤ) : ℝ)) + 1) / (N : ℝ) = 1 := by
          rw [hN1, div_self hNR.ne']
        rw [hdiv]
        linarith
    dsimp only
    have hF : flatPolygon g P N γ ((x : ℝ) : Surgery.Topology.Circle)
        = flatPolygon g P N γ ((x + 1 : ℝ) : Surgery.Topology.Circle) :=
      (flatPolygon_add_one g P N γ x).symm
    rw [hF, flatPolygon_apply_of_mem_Ico g P N γ hN hmem0 hmem1 hx1]
    have hpvL : polygonVertex γ N ((N : ℤ) - 1) = polygonVertex γ N (-1) := by
      have h := polygonVertex_add_int γ N (-1) 1
      have harg : (-1 : ℤ) + 1 * (N : ℤ) = (N : ℤ) - 1 := by ring
      rwa [harg] at h
    have hpvR : polygonVertex γ N (((N : ℤ) - 1) + 1) = polygonVertex γ N (0 : ℤ) := by
      have h := polygonVertex_add_int γ N (0 : ℤ) 1
      have harg : (0 : ℤ) + 1 * (N : ℤ) = ((N : ℤ) - 1) + 1 := by ring
      rwa [harg] at h
    have harg : (N : ℝ) * (x + 1) - ((((N : ℤ) - 1 : ℤ)) : ℝ) = (N : ℝ) * x - (-1) := by
      push_cast; ring
    rw [hpvL, hpvR, harg]


omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
theorem contDiffAt_map_flatPolygon_and_iteratedDeriv_eq_zero (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d) {N : ℕ}
    (hN : 0 < N) (γ : Surgery.Topology.Circle → Q)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    {i : ℤ} (hi : 0 ≤ i) (hiN : i < N) :
    ContDiffAt ℝ ∞ (fun x : ℝ => e.map (flatPolygon g P N γ (x : Surgery.Topology.Circle)))
      ((i : ℝ) / N) ∧
    ∀ m : ℕ, 0 < m →
      iteratedDeriv m (fun x : ℝ => e.map (flatPolygon g P N γ (x : Surgery.Topology.Circle)))
        ((i : ℝ) / N) = 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsegR : IsShortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))) := hseg i hi hiN
  have hsegL : IsShortSegment g (polygonVertex γ N (i - 1)) (polygonVertex γ N i)
      (shortSegment g (polygonVertex γ N (i - 1)) (polygonVertex γ N i)) := by
    rcases eq_or_lt_of_le hi with h0 | h0
    · rw [← h0]
      have hA : polygonVertex γ N ((0 : ℤ) - 1) = polygonVertex γ N ((N : ℤ) - 1) := by
        have h := polygonVertex_add_int γ N (-1) 1
        have harg : (-1 : ℤ) + 1 * (N : ℤ) = (N : ℤ) - 1 := by ring
        rw [harg] at h
        simpa only [zero_sub] using h.symm
      have hB : polygonVertex γ N (0 : ℤ) = polygonVertex γ N (N : ℤ) := by
        have h := polygonVertex_add_int γ N (0 : ℤ) 1
        have harg : (0 : ℤ) + 1 * (N : ℤ) = (N : ℤ) := by ring
        rw [harg] at h
        exact h.symm
      rw [hA, hB]
      simpa only [sub_add_cancel] using hseg ((N : ℤ) - 1) (by omega) (by omega)
    · simpa only [sub_add_cancel] using hseg (i - 1) (by omega) (by omega)
  set L : ℝ → Q := fun x => shortSegment g (polygonVertex γ N (i - 1)) (polygonVertex γ N i)
    (P.beta ((N : ℝ) * x - ((i : ℝ) - 1))) with hL_def
  set R : ℝ → Q := fun x => shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
    (P.beta ((N : ℝ) * x - (i : ℝ))) with hR_def
  have hφL : ContDiffAt ℝ ∞ (fun y : ℝ => e.map
      (shortSegment g (polygonVertex γ N (i - 1)) (polygonVertex γ N i) y)) (P.beta 1) :=
    contDiffAt_map_shortSegment g e hsegL (by rw [P.beta_one]; norm_num)
  have hφR : ContDiffAt ℝ ∞ (fun y : ℝ => e.map
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)) y)) (P.beta 0) :=
    contDiffAt_map_shortSegment g e hsegR (by rw [P.beta_zero]; norm_num)
  have hLcd : ContDiffAt ℝ ∞ (fun x : ℝ => e.map (L x)) ((i : ℝ) / N) := by
    rw [hL_def]
    have hinner : ContDiffAt ℝ ∞ (fun x : ℝ => P.beta ((N : ℝ) * x - ((i : ℝ) - 1)))
        ((i : ℝ) / N) :=
      ContDiffAt.comp (f := fun x : ℝ => (N : ℝ) * x - ((i : ℝ) - 1)) (g := P.beta) _
        (P.contDiff_beta.contDiffAt)
        (((contDiff_const.mul contDiff_id).sub contDiff_const).contDiffAt)
    exact ContDiffAt.comp (f := fun x : ℝ => P.beta ((N : ℝ) * x - ((i : ℝ) - 1)))
      (g := fun y : ℝ => e.map (shortSegment g (polygonVertex γ N (i - 1)) (polygonVertex γ N i) y))
      _ (by rw [mul_div_cancel₀ _ (ne_of_gt hNR), sub_sub_cancel]; exact hφL) hinner
  have hRcd : ContDiffAt ℝ ∞ (fun x : ℝ => e.map (R x)) ((i : ℝ) / N) := by
    rw [hR_def]
    have hinner : ContDiffAt ℝ ∞ (fun x : ℝ => P.beta ((N : ℝ) * x - (i : ℝ))) ((i : ℝ) / N) :=
      ContDiffAt.comp (f := fun x : ℝ => (N : ℝ) * x - (i : ℝ)) (g := P.beta) _
        (P.contDiff_beta.contDiffAt)
        (((contDiff_const.mul contDiff_id).sub contDiff_const).contDiffAt)
    exact ContDiffAt.comp (f := fun x : ℝ => P.beta ((N : ℝ) * x - (i : ℝ)))
      (g := fun y : ℝ => e.map (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)) y))
      _ (by rw [mul_div_cancel₀ _ (ne_of_gt hNR), sub_self]; exact hφR) hinner
  have hLx : L ((i : ℝ) / N) = polygonVertex γ N i := by
    rw [hL_def]
    dsimp only
    rw [mul_div_cancel₀ _ (ne_of_gt hNR), sub_sub_cancel, P.beta_one, hsegL.2.2.2.1]
  have hRx : R ((i : ℝ) / N) = polygonVertex γ N i := by
    rw [hR_def]
    dsimp only
    rw [mul_div_cancel₀ _ (ne_of_gt hNR), sub_self, P.beta_zero, hsegR.2.2.1]
  have heL : (fun x : ℝ => flatPolygon g P N γ (x : Surgery.Topology.Circle))
      =ᶠ[𝓝[Iic ((i : ℝ) / N)] ((i : ℝ) / N)] L := by
    rcases eq_or_lt_of_le hi with h0 | h0
    · have hsegR' : IsShortSegment g (polygonVertex γ N 0) (polygonVertex γ N 1)
          (shortSegment g (polygonVertex γ N 0) (polygonVertex γ N 1)) := by
        have h1 : (0 : ℤ) = i := h0
        have h2 : (1 : ℤ) = i + 1 := by rw [← h0]; norm_num
        rw [h1, h2]
        exact hsegR
      have hsegL' : IsShortSegment g (polygonVertex γ N (-1)) (polygonVertex γ N 0)
          (shortSegment g (polygonVertex γ N (-1)) (polygonVertex γ N 0)) := by
        have h1 : (-1 : ℤ) = i - 1 := by rw [← h0]; norm_num
        have h2 : (0 : ℤ) = i := h0
        rw [h1, h2]
        exact hsegL
      rw [hL_def, ← h0]
      simp only [Int.cast_zero, zero_div, zero_sub]
      exact flatPolygon_eventuallyEq_left_zero g P hN γ hsegR' hsegL'
    · rw [hL_def]
      exact flatPolygon_eventuallyEq_left g P hN γ h0 hiN hsegL hsegR
  have heR : (fun x : ℝ => flatPolygon g P N γ (x : Surgery.Topology.Circle))
      =ᶠ[𝓝[Ici ((i : ℝ) / N)] ((i : ℝ) / N)] R := by
    rw [hR_def]
    exact flatPolygon_eventuallyEq_right g P hN γ hi hiN
  obtain ⟨sL, hsL, heqL⟩ := Filter.eventuallyEq_iff_exists_mem.mp heL
  obtain ⟨a₁, ha₁, hsub₁⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp hsL
  obtain ⟨sR, hsR, heqR⟩ := Filter.eventuallyEq_iff_exists_mem.mp heR
  obtain ⟨b₁, hb₁, hsub₁'⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hsR
  have ha : max a₁ (((i : ℝ) - 1) / N) < (i : ℝ) / N := by
    refine max_lt ha₁ ?_
    rw [div_lt_div_iff_of_pos_right hNR]
    linarith
  have hb : (i : ℝ) / N < min b₁ (((i : ℝ) + 1) / N) := by
    refine lt_min hb₁ ?_
    rw [div_lt_div_iff_of_pos_right hNR]
    linarith
  have hF₁ : ∀ x ∈ Icc a₁ ((i : ℝ) / N),
      flatPolygon g P N γ (x : Surgery.Topology.Circle) = L x :=
    fun x hx => heqL (hsub₁ hx)
  have hF₁' : ∀ x ∈ Icc ((i : ℝ) / N) b₁,
      flatPolygon g P N γ (x : Surgery.Topology.Circle) = R x :=
    fun x hx => heqR (hsub₁' hx)
  have hML : ContDiffOn ℝ ∞ (fun x : ℝ => e.map (L x))
      (Icc (max a₁ (((i : ℝ) - 1) / N)) ((i : ℝ) / N)) := by
    rw [hL_def]
    refine ((e.smooth.comp_contMDiffOn ?_).contDiffOn)
    refine contMDiffOn_shortSegment_beta g P hsegL ?_
    intro x hx
    have h1 : ((i : ℝ) - 1) / N ≤ x := le_trans (le_max_right a₁ _) hx.1
    have h1' : (i : ℝ) - 1 ≤ x * N := (div_le_iff₀ hNR).mp h1
    have h2 : x * N ≤ (i : ℝ) := (le_div_iff₀ hNR).mp hx.2
    constructor
    · linarith
    · linarith
  have hMR : ContDiffOn ℝ ∞ (fun x : ℝ => e.map (R x))
      (Icc ((i : ℝ) / N) (min b₁ (((i : ℝ) + 1) / N))) := by
    rw [hR_def]
    refine ((e.smooth.comp_contMDiffOn ?_).contDiffOn)
    refine contMDiffOn_shortSegment_beta g P hsegR ?_
    intro x hx
    have h1 : (i : ℝ) ≤ x * N := (div_le_iff₀ hNR).mp hx.1
    have h2 : x ≤ ((i : ℝ) + 1) / N := le_trans hx.2 (min_le_right b₁ _)
    have h2' : x * N ≤ (i : ℝ) + 1 := (le_div_iff₀ hNR).mp h2
    constructor
    · linarith
    · linarith
  have hjet : ∀ n : ℕ,
      iteratedDerivWithin n (fun x : ℝ => e.map (L x))
        (Icc (max a₁ (((i : ℝ) - 1) / N)) ((i : ℝ) / N)) ((i : ℝ) / N)
      = iteratedDerivWithin n (fun x : ℝ => e.map (R x))
        (Icc ((i : ℝ) / N) (min b₁ (((i : ℝ) + 1) / N))) ((i : ℝ) / N) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      simp only [iteratedDerivWithin_zero]
      rw [hLx, hRx]
    · have h1 : iteratedDeriv n (fun x : ℝ => e.map (L x)) ((i : ℝ) / N) = 0 := by
        rw [hL_def]
        have h := iteratedDeriv_comp_beta_mul_sub_eq_zero (P := P)
          (φ := fun y : ℝ => e.map
            (shortSegment g (polygonVertex γ N (i - 1)) (polygonVertex γ N i) y))
          (c := 1) hφL (ne_of_gt hNR) ((i : ℝ) - 1)
          (fun k hk => P.iteratedDeriv_beta_one hk) hn0
        have hpt : ((i : ℝ) - 1 + 1) / (N : ℝ) = (i : ℝ) / N := by rw [sub_add_cancel]
        rwa [hpt] at h
      have h2 : iteratedDeriv n (fun x : ℝ => e.map (R x)) ((i : ℝ) / N) = 0 := by
        rw [hR_def]
        have h := iteratedDeriv_comp_beta_mul_sub_eq_zero (P := P)
          (φ := fun y : ℝ => e.map
            (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)) y))
          (c := 0) hφR (ne_of_gt hNR) (i : ℝ)
          (fun k hk => P.iteratedDeriv_beta_zero hk) hn0
        have hpt : ((i : ℝ) + 0) / (N : ℝ) = (i : ℝ) / N := by rw [add_zero]
        rwa [hpt] at h
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ha)
          (hLcd.of_le (WithTop.coe_le_coe.mpr le_top : (n : ℕ∞ω) ≤ ∞))
          ⟨ha.le, le_rfl⟩,
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb)
          (hRcd.of_le (WithTop.coe_le_coe.mpr le_top : (n : ℕ∞ω) ≤ ∞))
          ⟨le_rfl, hb.le⟩, h1, h2]
  have hG : ContDiffAt ℝ ∞ (fun x : ℝ => if x ≤ (i : ℝ) / N then e.map (L x) else e.map (R x))
      ((i : ℝ) / N) :=
    DifferentialGeometry.Analysis.SmoothExtension.contDiffAt_ite_of_jet_match ha hb hML hMR hjet
  have hEqOn : Set.EqOn (fun x : ℝ => if x ≤ (i : ℝ) / N then e.map (L x) else e.map (R x))
      (fun x : ℝ => e.map (R x)) (Ici ((i : ℝ) / N)) := by
    intro x hx
    rcases eq_or_lt_of_le (mem_Ici.mp hx) with h | h
    · subst h
      simp only [if_pos le_rfl, hLx, hRx]
    · simp only [if_neg (not_le.mpr h)]
  have hFG : (fun x : ℝ => e.map (flatPolygon g P N γ (x : Surgery.Topology.Circle)))
      =ᶠ[𝓝 ((i : ℝ) / N)]
      (fun x : ℝ => if x ≤ (i : ℝ) / N then e.map (L x) else e.map (R x)) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Icc (max a₁ (((i : ℝ) - 1) / N)) (min b₁ (((i : ℝ) + 1) / N)),
        Icc_mem_nhds ha hb, fun x hx => ?_⟩
    dsimp only
    by_cases h : x ≤ (i : ℝ) / N
    · have hxL : x ∈ Icc a₁ ((i : ℝ) / N) := ⟨le_trans (le_max_left a₁ _) hx.1, h⟩
      rw [hF₁ x hxL, if_pos h]
    · have hxR : x ∈ Icc ((i : ℝ) / N) b₁ :=
        ⟨le_of_lt (not_le.mp h), le_trans hx.2 (min_le_left b₁ _)⟩
      rw [hF₁' x hxR, if_neg h]
  refine ⟨hG.congr_of_eventuallyEq hFG, ?_⟩
  intro m hm
  rw [Filter.EventuallyEq.iteratedDeriv_eq m hFG]
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici ((i : ℝ) / N))
    (hG.of_le (WithTop.coe_le_coe.mpr le_top : (m : ℕ∞ω) ≤ ∞)) (mem_Ici.mpr le_rfl)]
  rw [(iteratedDerivWithin_congr hEqOn) (mem_Ici.mpr le_rfl)]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici ((i : ℝ) / N))
    (hRcd.of_le (WithTop.coe_le_coe.mpr le_top : (m : ℕ∞ω) ≤ ∞)) (mem_Ici.mpr le_rfl)]
  rw [hR_def]
  dsimp only
  have h := iteratedDeriv_comp_beta_mul_sub_eq_zero (P := P)
    (φ := fun y : ℝ => e.map
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)) y))
    (c := 0) hφR (ne_of_gt hNR) (i : ℝ)
    (fun k hk => P.iteratedDeriv_beta_zero hk) hm
  have hpt : ((i : ℝ) + 0) / (N : ℝ) = (i : ℝ) / N := by rw [add_zero]
  rwa [hpt] at h

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
theorem iteratedDeriv_map_flatPolygon_eq_zero (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d) {N : ℕ}
    (hN : 0 < N) (γ : Surgery.Topology.Circle → Q)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    {i : ℤ} (hi : 0 ≤ i) (hiN : i < N) {m : ℕ} (hm : 0 < m) :
    iteratedDeriv m (fun x : ℝ => e.map (flatPolygon g P N γ (x : Surgery.Topology.Circle)))
      ((i : ℝ) / N) = 0 :=
  (contDiffAt_map_flatPolygon_and_iteratedDeriv_eq_zero g P e hN γ hseg hi hiN).2 m hm

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
