import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.Estimates
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.Tail
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.DirectLimit.Completeness
import DifferentialGeometry.Topology.FirstExit
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphComposition

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open Set Topology TopologicalSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]

section ApproxData

open Bundle

variable [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]
variable [NeZero (Module.finrank ℝ E)]

omit [I.Boundaryless]
  [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [NeZero (Module.finrank ℝ E)] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem half_ambient_le_tail
    (b : ∀ j, M j) (j₀ : ℕ)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
        (1 / 2 : ℝ) * (g (j₀ + n)).inner (x : M (j₀ + n)) v v ≤
          (tailMetric (I := I) b j₀ gInf n).inner x v v := by
  let U : ∀ n, Opens (M (j₀ + n)) :=
    fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  let d : ℝ := Module.finrank ℝ E
  let ε₀ : ℝ := 1 / (d + 1)
  have hd₀ : 0 ≤ d := by
    dsimp only [d]
    positivity
  have hden : 0 < d + 1 := by linarith
  have hε₀ : 0 < ε₀ := by
    dsimp only [ε₀]
    positivity
  have hdε : d * ε₀ ≤ 1 := by
    calc
      d * ε₀ = d / (d + 1) := by
        dsimp only [ε₀]
        ring
      _ ≤ 1 := (div_le_one hden).2 (by linarith)
  obtain ⟨n₀, hn₀⟩ := hclose ε₀ hε₀ 0
  refine ⟨n₀, fun n hn x v => ?_⟩
  let inc : tailBallOpen b j₀ n → U n := Opens.inclusion (tail_ball_le_large b j₀ n)
  have hnorm₀ := hn₀ n hn 0 0 (by omega) (inc x)
  rw [chain_pullback_zero (I := I) Ψ g (U n) (hU n)] at hnorm₀
  have hquad := metricQuadFormDiff_le_metricDerivNorm (I := I)
    ((g (j₀ + n)).restrictOpen (I := I) (U n)) (gInf n) (gInf n) (inc x) v
  have hcoef :
      (Module.finrank ℝ (TangentSpace I (inc x)) : ℝ) *
          metricDerivNorm (I := I) 0
            ((g (j₀ + n)).restrictOpen (I := I) (U n)) (gInf n) (gInf n) (inc x) ≤ 1 := by
    change d * metricDerivNorm (I := I) 0
      ((g (j₀ + n)).restrictOpen (I := I) (U n)) (gInf n) (gInf n) (inc x) ≤ 1
    exact (mul_le_mul_of_nonneg_left hnorm₀ hd₀).trans hdε
  have hinner₀ : 0 ≤ (gInf n).inner (inc x) v v :=
    metric_inner_self_nonneg (I := I) (gInf n) (inc x) v
  have hscaled :
      (Module.finrank ℝ (TangentSpace I (inc x)) : ℝ) *
          metricDerivNorm (I := I) 0
            ((g (j₀ + n)).restrictOpen (I := I) (U n)) (gInf n) (gInf n) (inc x) *
            (gInf n).inner (inc x) v v ≤ (gInf n).inner (inc x) v v := by
    calc
      _ ≤ 1 * (gInf n).inner (inc x) v v :=
        mul_le_mul_of_nonneg_right hcoef hinner₀
      _ = (gInf n).inner (inc x) v v := one_mul _
  have hbound := hquad.trans hscaled
  have hbound' :
      |(g (j₀ + n)).inner (x : M (j₀ + n)) v v -
          (tailMetric (I := I) b j₀ gInf n).inner x v v| ≤
        (tailMetric (I := I) b j₀ gInf n).inner x v v := by
    with_unfolding_all
      exact hbound
  rw [abs_le] at hbound'
  nlinarith [hbound'.2]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
  [I.Boundaryless] [∀ j, IsRiemannianManifold I (M j)] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem enorm_val_le_two
    (b : ∀ j, M j) (j₀ n : ℕ)
    (gAmb : SmoothRiemannianMetric I (M (j₀ + n)))
    (gTail : SmoothRiemannianMetric I (tailBallOpen b j₀ n))
    (hAmbNorm : ∀ (y : M (j₀ + n)) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gAmb.inner y w w)))
    (x : tailBallOpen b j₀ n) (v : TangentSpace I x)
    (hlow : (1 / 2 : ℝ) * gAmb.inner (x : M (j₀ + n)) v v ≤
      gTail.inner x v v) :
    letI : RiemannianBundle (fun y : tailBallOpen b j₀ n => TangentSpace I y) :=
      ⟨gTail.toRiemannianMetric⟩
    ‖mfderiv I I (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) x v‖ₑ ≤
      2 * ‖v‖ₑ := by
  let _ : RiemannianBundle (fun y : tailBallOpen b j₀ n => TangentSpace I y) :=
    ⟨gTail.toRiemannianMetric⟩
  have hquad : gAmb.inner (x : M (j₀ + n)) v v ≤ 2 * gTail.inner x v v := by
    nlinarith
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  calc
    ‖mfderiv I I (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) x v‖ₑ =
        ENNReal.ofReal (Real.sqrt (gAmb.inner (x : M (j₀ + n))
          (mfderiv I I (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) x v)
          (mfderiv I I (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) x v))) :=
      hAmbNorm _ _
    _ = ENNReal.ofReal (Real.sqrt (gAmb.inner (x : M (j₀ + n)) v v)) := by
      rw [mfderiv_subtype_val_apply]
    _ ≤ ENNReal.ofReal (Real.sqrt (2 * gTail.inner x v v)) :=
      ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hquad)
    _ = ENNReal.ofReal (Real.sqrt 2) *
        ENNReal.ofReal (Real.sqrt (gTail.inner x v v)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    _ = ENNReal.ofReal (Real.sqrt 2) * ‖v‖ₑ := by
      exact congrArg (ENNReal.ofReal (Real.sqrt 2) * ·)
        (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          gTail x v).symm
    _ ≤ ENNReal.ofReal 2 * ‖v‖ₑ := mul_le_mul_left
      (ENNReal.ofReal_le_ofReal hsqrt2) _
    _ = 2 * ‖v‖ₑ := by norm_num

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
  [I.Boundaryless] [∀ j, IsRiemannianManifold I (M j)] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem path_elength_val_le
    (b : ∀ j, M j) (j₀ n : ℕ)
    (gAmb : SmoothRiemannianMetric I (M (j₀ + n)))
    (gTail : SmoothRiemannianMetric I (tailBallOpen b j₀ n))
    (hAmbNorm : ∀ (y : M (j₀ + n)) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gAmb.inner y w w)))
    (hlow : ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
      (1 / 2 : ℝ) * gAmb.inner (x : M (j₀ + n)) v v ≤ gTail.inner x v v)
    {γ : ℝ → tailBallOpen b j₀ n} {t₀ t₁ : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc t₀ t₁)) :
    letI : RiemannianBundle (fun y : tailBallOpen b j₀ n => TangentSpace I y) :=
      ⟨gTail.toRiemannianMetric⟩
    Manifold.pathELength I ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ γ) t₀ t₁ ≤
      2 * Manifold.pathELength I γ t₀ t₁ := by
  let _ : RiemannianBundle (fun y : tailBallOpen b j₀ n => TangentSpace I y) :=
    ⟨gTail.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    ← MeasureTheory.lintegral_const_mul' (2 : ENNReal) _ (by norm_num)]
  refine MeasureTheory.lintegral_mono_ae
    (Filter.eventually_of_mem
      (MeasureTheory.self_mem_ae_restrict measurableSet_Ioo) ?_)
  intro t ht
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  have hval : MDifferentiableAt I I
      (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) (γ t) :=
    (contMDiff_subtype_val (I := I) (U := tailBallOpen b j₀ n)
      (n := (∞ : WithTop ℕ∞))).mdifferentiableAt (by simp)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I
      ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ γ) t =
      (mfderiv I I (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) (γ t)).comp
        (mfderiv 𝓘(ℝ, ℝ) I γ t) := mfderiv_comp t hval hγt
  rw [hcomp]
  exact enorm_val_le_two b j₀ n gAmb gTail hAmbNorm (γ t)
    (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (hlow _ _)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [∀ j, SigmaCompactSpace (M j)] [I.Boundaryless] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem path_escape_core
    (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))]
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    (gTail : ∀ m, SmoothRiemannianMetric I (tailBallOpen b j₀ m))
    (hgTail : S.MetricCocycle gTail)
    (gAmb : SmoothRiemannianMetric I (M (j₀ + n)))
    (hAmbNorm : ∀ (y : M (j₀ + n)) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gAmb.inner y w w)))
    (hlow : ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
      (1 / 2 : ℝ) * gAmb.inner (x : M (j₀ + n)) v v ≤ (gTail n).inner x v v)
    {γ : ℝ → S.toSeqSystem.Lim}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 1))
    (hγ0 : γ 0 = S.toSeqSystem.incl n (tailCenter b j₀ n))
    (hγ1 : γ 1 ∉ limitCore b j₀ S n) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
    ENNReal.ofReal ((2 : ℝ) ^ n / 4) ≤ Manifold.pathELength I γ 0 1 := by
  let _ : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
  let _ : RiemannianBundle
      (fun x : tailBallOpen b j₀ n => TangentSpace I x) :=
    ⟨(gTail n).toRiemannianMetric⟩
  have hstart : γ 0 ∈ interior (limitCore b j₀ S n) := by
    rw [hγ0]
    exact center_mem_core_interior b j₀ n S
  obtain ⟨t, ht, hstay, hfront⟩ := exists_first_exit_frontier
    (limit_core_closed b j₀ n S) zero_lt_one hγ.continuousOn hstart hγ1
  obtain ⟨x, hxinc, hxrad⟩ := frontier_core_radius b j₀ n S hfront
  have hγpre : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 t) :=
    hγ.mono (Set.Icc_subset_Icc le_rfl ht.2)
  have hrange : ∀ s ∈ Set.Icc (0 : ℝ) t,
      γ s ∈ Set.range (S.toSeqSystem.incl n) := by
    intro s hs
    have hsK := hstay s hs
    obtain ⟨y, _, hyeq⟩ := hsK
    exact ⟨y, hyeq⟩
  let δ : ℝ → tailBallOpen b j₀ n :=
    Function.invFun (S.toSeqSystem.incl n) ∘ γ
  have hδ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 δ (Set.Icc 0 t) := by
    intro s hs
    exact ContMDiffAt.comp_contMDiffWithinAt s
      ((S.contMDiffAt_invIncl n (hrange s hs)).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ∞))
      (hγpre s hs)
  have hvalδ : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) (Set.Icc 0 t) :=
    ((contMDiff_subtype_val (I := I) (U := tailBallOpen b j₀ n)
      (n := (∞ : WithTop ℕ∞))).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)).comp_contMDiffOn hδ
  have hδ0 : δ 0 = tailCenter b j₀ n := by
    change Function.invFun (S.toSeqSystem.incl n) (γ 0) = tailCenter b j₀ n
    rw [hγ0]
    exact Function.leftInverse_invFun (S.toSeqSystem.incl_injective n) _
  have hδt : δ t = x := by
    change Function.invFun (S.toSeqSystem.incl n) (γ t) = x
    rw [← hxinc]
    exact Function.leftInverse_invFun (S.toSeqSystem.incl_injective n) _
  have hval0 :
      ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) 0 = b (j₀ + n) := by
    change (δ 0 : M (j₀ + n)) = b (j₀ + n)
    rw [hδ0]
    rfl
  have hvalt :
      ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) t =
        (x : M (j₀ + n)) := by
    change (δ t : M (j₀ + n)) = (x : M (j₀ + n))
    rw [hδt]
  have hamb : Manifold.riemannianEDist I (b (j₀ + n)) (x : M (j₀ + n)) ≤
      Manifold.pathELength I
        ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) 0 t :=
    Manifold.riemannianEDist_le_pathELength hvalδ hval0 hvalt ht.1.le
  have hradius : ENNReal.ofReal (coreRadius n) ≤
      Manifold.pathELength I
        ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) 0 t := by
    calc
      ENNReal.ofReal (coreRadius n) = edist (b (j₀ + n)) (x : M (j₀ + n)) := by
        rw [edist_dist, hxrad]
      _ = Manifold.riemannianEDist I (b (j₀ + n)) (x : M (j₀ + n)) :=
        IsRiemannianManifold.out (I := I) _ _
      _ ≤ _ := hamb
  have hvalLe := path_elength_val_le b j₀ n gAmb (gTail n) hAmbNorm hlow hδ
  have hpull : Manifold.pathELength I δ 0 t = Manifold.pathELength I γ 0 t := by
    simpa only [δ] using S.pathELength_invIncl gTail hgTail n hγpre hrange
  have hprefix : Manifold.pathELength I γ 0 t ≤ Manifold.pathELength I γ 0 1 :=
    Manifold.pathELength_mono le_rfl ht.2
  have hRle : ENNReal.ofReal (coreRadius n) ≤
      2 * Manifold.pathELength I γ 0 1 := by
    calc
      ENNReal.ofReal (coreRadius n) ≤
          Manifold.pathELength I
            ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) 0 t := hradius
      _ ≤ 2 * Manifold.pathELength I δ 0 t := hvalLe
      _ = 2 * Manifold.pathELength I γ 0 t := by rw [hpull]
      _ ≤ 2 * Manifold.pathELength I γ 0 1 := by
        simpa only [mul_comm] using mul_le_mul_left hprefix (2 : ENNReal)
  have hsplit : (2 : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ n / 4) =
      ENNReal.ofReal (coreRadius n) := by
    calc
      (2 : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ n / 4) =
          ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ n / 4) := by norm_num
      _ = ENNReal.ofReal ((2 : ℝ) * ((2 : ℝ) ^ n / 4)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ENNReal.ofReal (coreRadius n) := by
        congr 1
        simp only [coreRadius]
        ring
  apply (ENNReal.mul_le_mul_iff_right (a := (2 : ENNReal))
    (by norm_num) ENNReal.ofNat_ne_top).mp
  rw [hsplit]
  exact hRle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [∀ j, SigmaCompactSpace (M j)] [I.Boundaryless] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem mem_core_of_edist
    (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))]
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    [∀ m, SigmaCompactSpace (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    (gTail : ∀ m, SmoothRiemannianMetric I (tailBallOpen b j₀ m))
    (hgTail : S.MetricCocycle gTail)
    (gAmb : SmoothRiemannianMetric I (M (j₀ + n)))
    (hAmbNorm : ∀ (y : M (j₀ + n)) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gAmb.inner y w w)))
    (hlow : ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
      (1 / 2 : ℝ) * gAmb.inner (x : M (j₀ + n)) v v ≤ (gTail n).inner x v v)
    {q : S.toSeqSystem.Lim}
    (hq :
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
      Manifold.riemannianEDist I
        (S.toSeqSystem.incl n (tailCenter b j₀ n)) q <
          ENNReal.ofReal ((2 : ℝ) ^ n / 4)) :
    q ∈ limitCore b j₀ S n := by
  let _ := (inferInstance : (∀ (m : ℕ), SigmaCompactSpace ↥(DifferentialGeometry.HCGCompactness.tailBallOpen b j₀ m)))
  let _ : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
  by_contra hqK
  obtain ⟨γ, hγ0, hγ1, hγC, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hq
  have hγout : γ 1 ∉ limitCore b j₀ S n := by
    rw [hγ1]
    exact hqK
  have hesc := path_escape_core b j₀ n S gTail hgTail gAmb hAmbNorm hlow
    hγC hγ0 hγout
  exact (not_lt_of_ge hesc) hγlen

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [∀ j, SigmaCompactSpace (M j)] [I.Boundaryless] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem base_range_exhausts
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j) (j₀ : ℕ)
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    [∀ m, SigmaCompactSpace (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    (gTail : ∀ m, SmoothRiemannianMetric I (tailBallOpen b j₀ m))
    (hgTail : S.MetricCocycle gTail)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (y : M j) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner y w w)))
    (O : S.toSeqSystem.Lim)
    (hcenter : ∀ n, S.toSeqSystem.incl n (tailCenter b j₀ n) = O)
    (hlow : ∃ n₀, ∀ n, n₀ ≤ n →
      ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
        (1 / 2 : ℝ) * (g (j₀ + n)).inner (x : M (j₀ + n)) v v ≤
          (gTail n).inner x v v)
    (r : ENNReal) (hr : r ≠ ⊤) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
    ∃ n, ∀ q : S.toSeqSystem.Lim,
      Manifold.riemannianEDist I O q ≤ r → q ∈ Set.range (S.toSeqSystem.incl n) := by
  let _ : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
  obtain ⟨n₀, hn₀⟩ := hlow
  have hevPow : ∀ᶠ n : ℕ in Filter.atTop,
      4 * r.toReal < (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num)).eventually
      (Filter.eventually_gt_atTop (4 * r.toReal))
  obtain ⟨n, hn, hpow⟩ :=
    ((Filter.eventually_ge_atTop n₀).and hevPow).exists
  have hreal : r.toReal < (2 : ℝ) ^ n / 4 := by
    nlinarith
  have hcost : r < ENNReal.ofReal ((2 : ℝ) ^ n / 4) := by
    rw [← ENNReal.ofReal_toReal hr]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hreal
  refine ⟨n, fun q hq => ?_⟩
  have hqcost : Manifold.riemannianEDist I
      (S.toSeqSystem.incl n (tailCenter b j₀ n)) q <
        ENNReal.ofReal ((2 : ℝ) ^ n / 4) := by
    rw [hcenter n]
    exact hq.trans_lt hcost
  have hcore := mem_core_of_edist b j₀ n S gTail hgTail (g (j₀ + n))
    (hnorm (j₀ + n)) (hn₀ n hn) hqcost
  obtain ⟨x, _, hx⟩ := hcore
  exact ⟨x, hx⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [∀ j, SigmaCompactSpace (M j)] [I.Boundaryless] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem finite_range_exhausts
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j) (j₀ : ℕ)
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    [∀ m, SigmaCompactSpace (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    (gTail : ∀ m, SmoothRiemannianMetric I (tailBallOpen b j₀ m))
    (hgTail : S.MetricCocycle gTail)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (y : M j) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner y w w)))
    (O : S.toSeqSystem.Lim)
    (hcenter : ∀ n, S.toSeqSystem.incl n (tailCenter b j₀ n) = O)
    (hlow : ∃ n₀, ∀ n, n₀ ≤ n →
      ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
        (1 / 2 : ℝ) * (g (j₀ + n)).inner (x : M (j₀ + n)) v v ≤
          (gTail n).inner x v v)
    (hfinite :
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
      ∀ z : S.toSeqSystem.Lim, Manifold.riemannianEDist I O z ≠ ⊤)
    (z : S.toSeqSystem.Lim) (r : ENNReal) (hr : r ≠ ⊤) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
    ∃ n, ∀ q : S.toSeqSystem.Lim,
      Manifold.riemannianEDist I z q ≤ r → q ∈ Set.range (S.toSeqSystem.incl n) := by
  let _ : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
  have hR : Manifold.riemannianEDist I O z + r ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfinite z, hr⟩
  obtain ⟨n, hn⟩ := base_range_exhausts b j₀ S gTail hgTail g hnorm O hcenter hlow
    (Manifold.riemannianEDist I O z + r) hR
  refine ⟨n, fun q hq => hn q ?_⟩
  exact (Manifold.riemannianEDist_triangle (I := I) (x := O) (y := z) (z := q)).trans
    (add_le_add le_rfl hq)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tail_range_exhausts
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :
          Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hstep : ∀ n,
      let F : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) →
          ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :=
        PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n)
      ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n))
        (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
    letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
    let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
    let gTail := tailMetric (I := I) b j₀ gInf
    let hgTail : S.MetricCocycle gTail :=
      tail_ball_system_metric_cocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
    ∀ (z : S.toSeqSystem.Lim) (r : ENNReal), r ≠ ⊤ →
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
      ∃ n, ∀ q : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z q ≤ r →
          q ∈ Set.range (S.toSeqSystem.incl n) := by
  let _ : ∀ n, PreconnectedSpace (tailBallOpen b j₀ n) := fun n =>
    tail_ball_preconnected (I := I) b j₀ n
  let _ : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
  let _ : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  let gTail := tailMetric (I := I) b j₀ gInf
  let hgTail : S.MetricCocycle gTail :=
    tail_ball_system_metric_cocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
  let O : S.toSeqSystem.Lim := S.toSeqSystem.incl 0 (tailCenter b j₀ 0)
  let _ : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
  let _ : ConnectedSpace S.toSeqSystem.Lim := inferInstance
  let _ : IsContinuousRiemannianBundle E
      (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨⟨(S.limitMetric gTail hgTail).inner,
      (S.limitMetric gTail hgTail).contMDiff.continuous,
      by intro x v w; rfl⟩⟩
  have hcenter : ∀ n, S.toSeqSystem.incl n (tailCenter b j₀ n) = O := by
    intro n
    exact tail_ball_system_incl_center (I := I) b Ψ hbase g hnorm j₀ D₀ n
  have hlow : ∃ n₀, ∀ n, n₀ ≤ n →
      ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
        (1 / 2 : ℝ) * (g (j₀ + n)).inner (x : M (j₀ + n)) v v ≤
          (gTail n).inner x v v := by
    simpa only [gTail] using
      half_ambient_le_tail (I := I) b j₀ Ψ g hU gInf hclose
  have hfinite : ∀ z : S.toSeqSystem.Lim,
      Manifold.riemannianEDist I O z ≠ ⊤ := by
    intro z
    exact Geometry.Riemannian.Exponential.riemannianEDist_ne_top (I := I) O z
  dsimp only
  intro z r hr
  exact finite_range_exhausts (I := I) (b := b) (j₀ := j₀) (S := S)
    (gTail := gTail) (hgTail := hgTail) (g := g) (hnorm := hnorm) (O := O)
    (hcenter := hcenter) (hlow := hlow) (hfinite := hfinite) (z := z) (r := r) hr

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tail_limit_complete
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ) (hj₀ : 1 ≤ j₀)
    (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :
          Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hstep : ∀ n,
      let F : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) →
          ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :=
        PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n)
      ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n))
        (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
    letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
    let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
    let gTail := tailMetric (I := I) b j₀ gInf
    let hgTail : S.MetricCocycle gTail :=
      tail_ball_system_metric_cocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
    MetricComplete (I := I)
      (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail) := by
  let _ : ∀ n, PreconnectedSpace (tailBallOpen b j₀ n) := fun n =>
    tail_ball_preconnected (I := I) b j₀ n
  let _ : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tail_ball_nonempty b j₀ n
  let _ : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  let gTail := tailMetric (I := I) b j₀ gInf
  let hgTail : S.MetricCocycle gTail :=
    tail_ball_system_metric_cocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
  dsimp only
  have hexh : ∀ (z : S.toSeqSystem.Lim) (r : ENNReal), r ≠ ⊤ →
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
      ∃ n, ∀ q : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z q ≤ r →
          q ∈ Set.range (S.toSeqSystem.incl n) := by
    simpa only [S, gTail, hgTail] using
      tail_range_exhausts (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep hclose
  have hcompact : ∀ n, ∃ K : Set (tailBallOpen b j₀ (n + 1)), IsCompact K ∧
      Set.range (S.toSeqSystem.F (Nat.le_succ n)) ⊆ K := by
    simpa only [S] using
      tail_ball_system_step_range_compact (I := I) b Ψ hbase g hnorm j₀ hj₀ D₀
  have hcover : S.hasCompactBallCover gTail hgTail :=
    S.hasCompactBallCover_of_step gTail hgTail hexh hcompact
  exact limit_complete_of_compact_ball_cover S (tailCenter b j₀ 0) gTail hgTail hcover

end ApproxData

end HCGCompactness
end DifferentialGeometry
