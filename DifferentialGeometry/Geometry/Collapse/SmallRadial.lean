import DifferentialGeometry.Geometry.Collapse.SmallFields
import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBall
/-!
The complete selected radial specification returns to the original source along its small model.
The same function and selected metric control the gradient and cutoff clauses.
-/
set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Manifold Set Bundle
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Collapse
universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓡 3
theorem smallModel_radial_spec_back
    {M : Type u} [mM : MetricSpace M] [i1 : ChartedSpace E3 M] [i2 : IsManifold I3 ∞ M]
    (S : SmallManifoldModel (I := I3) M) (g : SmoothRiemannianMetric I3 M)
    (radius : ℝ) (hradius : 0 < radius) (center : S.Carrier) (radial : S.Carrier → ℝ)
    (ε e lo hi : ℝ) (hlo : lo ≤ 1 / 10) (hhi : 10 ≤ hi)
    (hSpec :
      letI _smallMetric := S.metricSpace.rescale radius⁻¹ (inv_pos.mpr hradius)
      let gsR := scaleMetric (radius⁻¹ ^ 2) (pow_pos (inv_pos.mpr hradius) 2) (S.metric g)
    LipschitzWith (Real.toNNReal (1 + ε)) radial ∧
      (∃ O : Set S.Carrier, IsOpen O ∧
        {x : S.Carrier | lo ≤ dist x center ∧ dist x center ≤ hi} ⊆ O ∧
       
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ radial O) ∧
      (∀ x, |radial x - Metric.infDist x {center}| < e) ∧
      (∀ x, x ∉ {x : S.Carrier | 1 / 20 < dist x center ∧ dist x center < 20} →
        radial x = Metric.infDist x {center}) ∧
      (∀ x y, |(radial x - Metric.infDist x {center}) -
          (radial y - Metric.infDist y {center})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ radial x) ∧ radial center = 0 ∧
      (∀ q ∈ {x : S.Carrier | 1 / 10 ≤ dist x center ∧ dist x center ≤ 10},
        1 - ε ≤ Real.sqrt (gsR.inner q (gradFun gsR radial q) (gradFun gsR radial q)) ∧
          Real.sqrt (gsR.inner q (gradFun gsR radial q) (gradFun gsR radial q)) ≤ 1 + ε) ∧
      (∀ x, radial x ∈ Icc (1 / 5 : ℝ) 2 →
        1 / 5 - e < dist x center ∧ dist x center < 2 + e) ∧
      radial ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : S.Carrier | 1 / 10 ≤ dist x center ∧ dist x center ≤ 10} ∧
      (∃ O' : Set S.Carrier, IsOpen O' ∧ radial ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ radial O' ∧ ∀ q ∈ O', gradFun gsR radial q ≠ 0) ∧
      ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
        ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (radial x)) ∧
        (∀ x, annularCutoff cutoffProfile (radial x) ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, radial x ∈ Icc (3 / 10 : ℝ) (4 / 5) →
          annularCutoff cutoffProfile (radial x) = 1) ∧
        tsupport (fun x => annularCutoff cutoffProfile (radial x)) ⊆
          {x : S.Carrier | 1 / 5 - e < dist x center ∧ dist x center < 9 / 10 + e} ∧
        ∀ q, Real.sqrt (gsR.inner q
          (gradFun gsR (fun x => annularCutoff cutoffProfile (radial x)) q)
          (gradFun gsR (fun x => annularCutoff cutoffProfile (radial x)) q)) ≤ L * (1 + ε)) :
    let p := S.diffeo center
    let f := smallModel_backFunction S radial
    letI _sourceRescaled := mM.rescale radius⁻¹ (inv_pos.mpr hradius)
    let gR := scaleMetric (radius⁻¹ ^ 2) (pow_pos (inv_pos.mpr hradius) 2) g
    LipschitzWith (Real.toNNReal (1 + ε)) f ∧
      (∃ O : Set M, IsOpen O ∧ {x : M | lo ≤ dist x p ∧ dist x p ≤ hi} ⊆ O ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ f O) ∧
      (∀ x, |f x - Metric.infDist x {p}| < e) ∧
      (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} →
        f x = Metric.infDist x {p}) ∧
      (∀ x y, |(f x - Metric.infDist x {p}) -
          (f y - Metric.infDist y {p})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ f x) ∧ f p = 0 ∧
      (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
        1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR f q) (gradFun gR f q)) ∧
          Real.sqrt (gR.inner q (gradFun gR f q) (gradFun gR f q)) ≤ 1 + ε) ∧
      (∀ x, f x ∈ Icc (1 / 5 : ℝ) 2 →
        1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
      f ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
      (∃ O' : Set M, IsOpen O' ∧ f ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ f O' ∧ ∀ q ∈ O', gradFun gR f q ≠ 0) ∧
      ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
        ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (f x)) ∧
        (∀ x, annularCutoff cutoffProfile (f x) ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, f x ∈ Icc (3 / 10 : ℝ) (4 / 5) →
          annularCutoff cutoffProfile (f x) = 1) ∧
        tsupport (fun x => annularCutoff cutoffProfile (f x)) ⊆
          {x : M | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
        ∀ q, Real.sqrt (gR.inner q
          (gradFun gR (fun x => annularCutoff cutoffProfile (f x)) q)
          (gradFun gR (fun x => annularCutoff cutoffProfile (f x)) q)) ≤ L * (1 + ε) := by
  let smallMetric := S.metricSpace
  let eR := (S.isometryEquiv).rescale radius⁻¹ (inv_pos.mpr hradius)
  let gR := scaleMetric (radius⁻¹ ^ 2) (pow_pos (inv_pos.mpr hradius) 2) g
  let gsR := scaleMetric (radius⁻¹ ^ 2) (pow_pos (inv_pos.mpr hradius) 2) (S.metric g)
  have hm : S.metric gR = gsR :=
    Diffeomorph.pullbackMetricCross_scaleMetric g S.diffeo _ _
  have hspec := hSpec
  let smallRescaled := smallMetric.rescale radius⁻¹ (inv_pos.mpr hradius)
  let sourceRescaled := mM.rescale radius⁻¹ (inv_pos.mpr hradius)
  let f := smallModel_backFunction (mM := mM) S radial
  let p := S.diffeo center
  have hf (x : M) : f x = radial (S.diffeo.symm x) := rfl
  have hd (x : M) : dist (S.diffeo.symm x) center = dist x p := by
    rw [← S.diffeo.symm_apply_apply center]
    exact eR.symm.dist_eq x (S.diffeo center)
  have hdd (x y : M) : dist (S.diffeo.symm x) (S.diffeo.symm y) = dist x y :=
    eR.symm.dist_eq x y
  have hg (x : M) (hx : MDifferentiableAt I3 𝓘(ℝ, ℝ) radial (S.diffeo.symm x)) :
      gR.inner x (gradFun gR f x) (gradFun gR f x) =
        gsR.inner (S.diffeo.symm x) (gradFun gsR radial (S.diffeo.symm x))
          (gradFun gsR radial (S.diffeo.symm x)) := by
    rw [← hm]
    exact smallModel_backFunction_gradientNorm (mM := mM) S gR radial x hx
  change
    LipschitzWith (Real.toNNReal (1 + ε)) radial ∧
      (∃ O : Set S.Carrier, IsOpen O ∧
        {x : S.Carrier | lo ≤ dist x center ∧ dist x center ≤ hi} ⊆ O ∧
       
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ radial O) ∧
      (∀ x, |radial x - Metric.infDist x {center}| < e) ∧
      (∀ x, x ∉ {x : S.Carrier | 1 / 20 < dist x center ∧ dist x center < 20} →
        radial x = Metric.infDist x {center}) ∧
      (∀ x y, |(radial x - Metric.infDist x {center}) -
          (radial y - Metric.infDist y {center})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ radial x) ∧ radial center = 0 ∧
      (∀ q ∈ {x : S.Carrier | 1 / 10 ≤ dist x center ∧ dist x center ≤ 10},
        1 - ε ≤ Real.sqrt (gsR.inner q (gradFun gsR radial q) (gradFun gsR radial q)) ∧
          Real.sqrt (gsR.inner q (gradFun gsR radial q) (gradFun gsR radial q)) ≤ 1 + ε) ∧
      (∀ x, radial x ∈ Icc (1 / 5 : ℝ) 2 →
        1 / 5 - e < dist x center ∧ dist x center < 2 + e) ∧
      radial ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : S.Carrier | 1 / 10 ≤ dist x center ∧ dist x center ≤ 10} ∧
      (∃ O' : Set S.Carrier, IsOpen O' ∧ radial ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ radial O' ∧ ∀ q ∈ O', gradFun gsR radial q ≠ 0) ∧
      ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
        ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (radial x)) ∧
        (∀ x, annularCutoff cutoffProfile (radial x) ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, radial x ∈ Icc (3 / 10 : ℝ) (4 / 5) →
          annularCutoff cutoffProfile (radial x) = 1) ∧
        tsupport (fun x => annularCutoff cutoffProfile (radial x)) ⊆
          {x : S.Carrier | 1 / 5 - e < dist x center ∧ dist x center < 9 / 10 + e} ∧
        ∀ q, Real.sqrt (gsR.inner q
          (gradFun gsR (fun x => annularCutoff cutoffProfile (radial x)) q)
          (gradFun gsR (fun x => annularCutoff cutoffProfile (radial x)) q)) ≤ L * (1 + ε) at hspec
  change
    LipschitzWith (Real.toNNReal (1 + ε)) f ∧
      (∃ O : Set M, IsOpen O ∧ {x : M | lo ≤ dist x p ∧ dist x p ≤ hi} ⊆ O ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ f O) ∧
      (∀ x, |f x - Metric.infDist x {p}| < e) ∧
      (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} →
        f x = Metric.infDist x {p}) ∧
      (∀ x y, |(f x - Metric.infDist x {p}) -
          (f y - Metric.infDist y {p})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ f x) ∧ f p = 0 ∧
      (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
        1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR f q) (gradFun gR f q)) ∧
          Real.sqrt (gR.inner q (gradFun gR f q) (gradFun gR f q)) ≤ 1 + ε) ∧
      (∀ x, f x ∈ Icc (1 / 5 : ℝ) 2 →
        1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
      f ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
      (∃ O' : Set M, IsOpen O' ∧ f ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ f O' ∧ ∀ q ∈ O', gradFun gR f q ≠ 0) ∧
      ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
        ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (f x)) ∧
        (∀ x, annularCutoff cutoffProfile (f x) ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, f x ∈ Icc (3 / 10 : ℝ) (4 / 5) →
          annularCutoff cutoffProfile (f x) = 1) ∧
        tsupport (fun x => annularCutoff cutoffProfile (f x)) ⊆
          {x : M | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
        ∀ q, Real.sqrt (gR.inner q
          (gradFun gR (fun x => annularCutoff cutoffProfile (f x)) q)
          (gradFun gR (fun x => annularCutoff cutoffProfile (f x)) q)) ≤ L * (1 + ε)
  rcases hspec with ⟨hLip, ⟨O, hO, hbuf, hsm⟩, herr, hout, hdiff, hpos, hzero,
    hgrad, hlevel, hsub, ⟨O', hO', hsub', hsm', hnonzero⟩, L, hL, hLcut,
    hcutsm, hcutrange, hcutone, hcutsupport, hcutgrad⟩
  have hxin (x : M) (hx : 1 / 10 ≤ dist x p ∧ dist x p ≤ 10) :
      S.diffeo.symm x ∈ O :=
    hbuf ⟨(by rw [hd]; linarith [hx.1, hlo]), (by rw [hd]; linarith [hx.2, hhi])⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := hLip.comp eR.symm.isometry.lipschitzWith
    change LipschitzWith (_ * 1) f at hh
    simpa only [mul_one] using hh
  · refine ⟨S.diffeo '' O, S.diffeo.toHomeomorph.isOpenMap _ hO, ?_,
      smallModel_backFunction_smoothOn (mM := mM) S radial O hsm⟩
    intro x hx
    refine ⟨S.diffeo.symm x, ?_, S.diffeo.apply_symm_apply x⟩
    apply hbuf
    change lo ≤ dist (S.diffeo.symm x) center ∧
      dist (S.diffeo.symm x) center ≤ hi
    simpa only [mem_ofPred_eq, hd] using hx
  · intro x
    simpa only [hf, Metric.infDist_singleton, hd] using herr (S.diffeo.symm x)
  · intro x hx
    have hh := hout (S.diffeo.symm x) (by
      simpa only [mem_ofPred_eq, hd] using hx)
    simpa only [hf, Metric.infDist_singleton, hd] using hh
  · intro x y
    simpa only [hf, Metric.infDist_singleton, hd, hdd] using
      hdiff (S.diffeo.symm x) (S.diffeo.symm y)
  · exact fun x => hpos (S.diffeo.symm x)
  · change radial (S.diffeo.symm (S.diffeo center)) = 0
    simpa only [Diffeomorph.symm_apply_apply] using hzero
  · intro x hx
    have hxsm := (hsm _ (hxin x hx)).contMDiffAt (hO.mem_nhds (hxin x hx))
    rw [hg x (hxsm.mdifferentiableAt (by simp))]
    apply hgrad
    simpa only [mem_ofPred_eq, hd] using hx
  · intro x hx
    simpa only [hd] using hlevel (S.diffeo.symm x) hx
  · intro x hx
    have h := hsub hx
    simpa only [mem_ofPred_eq, hd] using h
  · refine ⟨S.diffeo '' O', S.diffeo.toHomeomorph.isOpenMap _ hO', ?_,
      smallModel_backFunction_smoothOn (mM := mM) S radial O' hsm', ?_⟩
    · intro x hx
      exact ⟨S.diffeo.symm x, hsub' hx, S.diffeo.apply_symm_apply x⟩
    · rintro x ⟨y, hy, hxy⟩
      have hxO : S.diffeo.symm x ∈ O' := by
        rw [← hxy, S.diffeo.symm_apply_apply]
        exact hy
      apply smallModel_backFunction_gradientNonzero (mM := mM) S gR radial x
      · exact ((hsm' _ hxO).contMDiffAt (hO'.mem_nhds hxO)).mdifferentiableAt (by simp)
      · rw [hm]
        exact hnonzero _ hxO
  · refine ⟨L, hL, hLcut,
      smallModel_backFunction_smooth (mM := mM) S
        (fun x => annularCutoff cutoffProfile (radial x)) hcutsm,
      fun x => hcutrange (S.diffeo.symm x), fun x hx => hcutone (S.diffeo.symm x) hx,
      ?_, ?_⟩
    · intro x hx
      have hs := tsupport_comp_eq_preimage
        (fun y => annularCutoff cutoffProfile (radial y)) S.diffeo.symm.toHomeomorph
      have ht : S.diffeo.symm x ∈ tsupport (fun y => annularCutoff cutoffProfile (radial y)) :=
        hs.le hx
      simpa only [mem_ofPred_eq, hd] using hcutsupport ht
    · intro x
      have ht := smallModel_backFunction_gradientNorm (mM := mM) S gR
        (fun y => annularCutoff cutoffProfile (radial y)) x
        (hcutsm.mdifferentiableAt (by simp))
      rw [hm] at ht
      rw [show gR.inner x
          (gradFun gR (fun y => annularCutoff cutoffProfile (f y)) x)
          (gradFun gR (fun y => annularCutoff cutoffProfile (f y)) x) = _ from ht]
      exact hcutgrad (S.diffeo.symm x)
theorem smallModel_zeroRadial_back
    {M : Type u} [mM : MetricSpace M] [i3 : ChartedSpace E3 M] [i4 : IsManifold I3 ∞ M]
    (S : SmallManifoldModel (I := I3) M) (g : SmoothRiemannianMetric I3 M)
    {ι : Type} (N C : ι → Type) [mN : ∀ b, MetricSpace (N b)]
    [cN : ∀ b, ChartedSpace E3 (N b)] [mC : ∀ b, MetricSpace (C b)]
    (o : ∀ b, C b) (δ ε e : ℝ)
    (Z : letI _smallMetric := S.metricSpace
      ZeroModelBall I3 S.Carrier (S.metric g) N C o δ ε e) :
    letI _smallMetric := S.metricSpace
    let p := S.diffeo Z.center
    let f := smallModel_backFunction S Z.radial
    letI _sourceRescaled := mM.rescale Z.radius⁻¹ (inv_pos.mpr Z.radius_pos)
    let gR := scaleMetric (Z.radius⁻¹ ^ 2) (pow_pos (inv_pos.mpr Z.radius_pos) 2) g
    LipschitzWith (Real.toNNReal (1 + ε)) f ∧
      (∃ O : Set M, IsOpen O ∧ {x : M | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ f O) ∧
      (∀ x, |f x - Metric.infDist x {p}| < e) ∧
      (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} →
        f x = Metric.infDist x {p}) ∧
      (∀ x y, |(f x - Metric.infDist x {p}) -
          (f y - Metric.infDist y {p})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ f x) ∧ f p = 0 ∧
      (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
        1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR f q) (gradFun gR f q)) ∧
          Real.sqrt (gR.inner q (gradFun gR f q) (gradFun gR f q)) ≤ 1 + ε) ∧
      (∀ x, f x ∈ Icc (1 / 5 : ℝ) 2 →
        1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
      f ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
      (∃ O' : Set M, IsOpen O' ∧ f ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ f O' ∧ ∀ q ∈ O', gradFun gR f q ≠ 0) ∧
      ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
        ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (f x)) ∧
        (∀ x, annularCutoff cutoffProfile (f x) ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, f x ∈ Icc (3 / 10 : ℝ) (4 / 5) →
          annularCutoff cutoffProfile (f x) = 1) ∧
        tsupport (fun x => annularCutoff cutoffProfile (f x)) ⊆
          {x : M | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
        ∀ q, Real.sqrt (gR.inner q
          (gradFun gR (fun x => annularCutoff cutoffProfile (f x)) q)
          (gradFun gR (fun x => annularCutoff cutoffProfile (f x)) q)) ≤ L * (1 + ε)
 := by
  let smallMetric := S.metricSpace
  exact smallModel_radial_spec_back S g Z.radius Z.radius_pos Z.center Z.radial ε e
    (3 / 40) 11 (by norm_num) (by norm_num) Z.radial_spec
end DifferentialGeometry.Geometry.Collapse
