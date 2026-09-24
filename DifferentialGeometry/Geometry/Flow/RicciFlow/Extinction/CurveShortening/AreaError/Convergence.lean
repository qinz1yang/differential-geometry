import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaError.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaError.Naturality
import DifferentialGeometry.Geometry.Curve.NormalVelocityErrorDensity
import DifferentialGeometry.Analysis.Calculus.TimeJet.Convergence
import DifferentialGeometry.Analysis.Integration.Integral.UniformConvergence
import DifferentialGeometry.Geometry.Metric.Family.Retraction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Basic

noncomputable section
open Filter MeasureTheory Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tendstoUniformlyOn_areaError_of_integrand
    {A : Type*} {l : Filter A} {J : Set ℝ}
    (g : ℝ → SmoothRiemannianMetric I M) (c : A → CurveMap M) (cInf : CurveMap M)
    (hc : ∀ᶠ i in l, ∀ t ∈ J, IntervalIntegrable
      (fun x => Real.sqrt ((c i).normSq g ((c i).normalVelocityError g J) x t) *
        (c i).speed g x t) volume 0 1)
    (hInf : ∀ t ∈ J, IntervalIntegrable
      (fun x => Real.sqrt (cInf.normSq g (cInf.normalVelocityError g J) x t) *
        cInf.speed g x t) volume 0 1)
    (hconv : TendstoUniformlyOn
      (fun i (p : ℝ × ℝ) =>
        Real.sqrt ((c i).normSq g ((c i).normalVelocityError g J) p.1 p.2) *
          (c i).speed g p.1 p.2)
      (fun p : ℝ × ℝ =>
        Real.sqrt (cInf.normSq g (cInf.normalVelocityError g J) p.1 p.2) *
          cInf.speed g p.1 p.2) l (Icc (0 : ℝ) 1 ×ˢ J)) :
    TendstoUniformlyOn (fun i => (c i).areaError g J) (cInf.areaError g J) l J := by
  rw [← uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hconv
  exact hconv.intervalIntegral hc hInf

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curve
open DifferentialGeometry.Analysis

private theorem uniform_prod_same {α β γ ι : Type*} [UniformSpace β] [UniformSpace γ]
    {l : Filter ι} {K : Set α} {f : ι → α → β} {g : α → β}
    {f' : ι → α → γ} {g' : α → γ}
    (hf : TendstoUniformlyOn f g l K) (hg : TendstoUniformlyOn f' g' l K) :
    TendstoUniformlyOn (fun i q => (f i q, f' i q)) (fun q => (g q, g' q)) l K := by
  intro V hV
  exact (tendsto_id.prodMk tendsto_id).eventually ((hf.prodMk hg) V hV)

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {U : TopologicalSpace.Opens F}

private def opensSpacetimeJet (c : CurveMap U) (J : Set ℝ) (p : ℝ × ℝ) :
    ℝ × U × F × F × F :=
  (p.2, c.lift p.1 p.2,
    deriv (fun x => (c.lift x p.2 : F)) p.1,
    deriv (deriv (fun x => (c.lift x p.2 : F))) p.1,
    derivWithin (fun t => (c.lift p.1 t : F)) J p.2)

omit [FiniteDimensional ℝ F] in
private theorem opensSpacetimeJet_continuousOn
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) {c : CurveMap U}
    (hc : c.SmoothOn (I := 𝓘(ℝ, F)) J) :
    ContinuousOn (opensSpacetimeJet c J) (univ ×ˢ J) := by
  have hcF : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (c.lift p.1 p.2 : F)) (univ ×ˢ J) :=
    (contMDiffOn_iff_contDiffOn.mp (contMDiff_subtype_val.comp_contMDiffOn hc)).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)
  have hj := continuousOn_spacetime_derivatives hJ hcF
  exact continuousOn_snd.prodMk (hc.continuousOn.prodMk
    (hj.snd.fst.prodMk (hj.snd.snd.fst.prodMk hj.snd.snd.snd)))

omit [FiniteDimensional ℝ F] in
private theorem opensSpacetimeJet_X_ne_zero {J : Set ℝ} {c : CurveMap U}
    (hi : c.ImmersedOn (I := 𝓘(ℝ, F)) J)
    {p : ℝ × ℝ} (hp : p ∈ univ ×ˢ J) : (opensSpacetimeJet c J p).2.2.1 ≠ 0 := by
  rw [opensSpacetimeJet, ← X_opens_eq_deriv c p.1 p.2]
  exact hi p.1 p.2 hp.2

private theorem density_opensSpacetimeJet_eq {J : Set ℝ} {c : CurveMap U}
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U)
    (hJ : UniqueDiffOn ℝ J) (hc : c.SmoothOn (I := 𝓘(ℝ, F)) J)
    {p : ℝ × ℝ} (hp : p ∈ univ ×ˢ J) :
    normalVelocityErrorDensity (covariantCurveJet g (opensSpacetimeJet c J p)) =
      Real.sqrt (c.normSq g (c.normalVelocityError g J) p.1 p.2) * c.speed g p.1 p.2 := by
  symm
  exact areaError_integrand_opens_eq_normalVelocityErrorDensity c g J p.1 p.2
    (((contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc p.2 hp.2)) p.1).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out))
    ((c.time_slice_contMDiffWithinAt J hc p.1 p.2 hp.2).mdifferentiableWithinAt (by simp))
    (hJ p.2 hp.2)

theorem tendstoUniformlyOn_areaError_opens_of_iteratedFDerivWithin
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U}
    (hG : MetricFamilySmoothOn D g) {a b : ℝ} (hab : a < b)
    (hreg : Icc a b ⊆ D.regular) (c : ℕ → CurveMap U) (cInf : CurveMap U)
    (hc : ∀ i, (c i).SmoothOn (I := 𝓘(ℝ, F)) (Icc a b))
    (hi : ∀ i, (c i).ImmersedOn (I := 𝓘(ℝ, F)) (Icc a b))
    (hcInf : cInf.SmoothOn (I := 𝓘(ℝ, F)) (Icc a b))
    (hiInf : cInf.ImmersedOn (I := 𝓘(ℝ, F)) (Icc a b))
    (hjet : ∀ m ≤ 2, TendstoUniformlyOn
      (fun i p => iteratedFDerivWithin ℝ m
        (fun q : ℝ × ℝ => ((c i).lift q.1 q.2 : F)) (univ ×ˢ Icc a b) p)
      (fun p => iteratedFDerivWithin ℝ m
        (fun q : ℝ × ℝ => (cInf.lift q.1 q.2 : F)) (univ ×ˢ Icc a b) p)
      atTop (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    TendstoUniformlyOn (fun i => (c i).areaError g (Icc a b))
      (cInf.areaError g (Icc a b)) atTop (Icc a b) := by
  let J := Icc a b
  let K := Icc (0 : ℝ) 1 ×ˢ J
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_Icc hab
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hsub : K ⊆ univ ×ˢ J := fun _ h => ⟨mem_univ _, h.2⟩
  have hcf : ∀ i, ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ((c i).lift p.1 p.2 : F))
      (univ ×ˢ J) := fun i =>
    (contMDiffOn_iff_contDiffOn.mp (contMDiff_subtype_val.comp_contMDiffOn (hc i))).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)
  have hcif : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (cInf.lift p.1 p.2 : F))
      (univ ×ˢ J) :=
    (contMDiffOn_iff_contDiffOn.mp (contMDiff_subtype_val.comp_contMDiffOn hcInf)).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)
  obtain ⟨hv, hx, ht, hxx⟩ := tendstoUniformlyOn_spacetime_derivatives_of_iteratedFDerivWithin
    hJ hsub (Eventually.of_forall hcf) hcif hjet
  have hvU : TendstoUniformlyOn (fun i (p : ℝ × ℝ) => (c i).lift p.1 p.2)
      (fun p => cInf.lift p.1 p.2) atTop K := by
    simpa only [Metric.tendstoUniformlyOn_iff, Subtype.dist_eq] using hv
  have htime : TendstoUniformlyOn (fun _ : ℕ => fun p : ℝ × ℝ => p.2)
      (fun p : ℝ × ℝ => p.2) atTop K := by
    intro V hV
    exact Eventually.of_forall fun _ _ _ => refl_mem_uniformity hV
  have hj : TendstoUniformlyOn (fun i => opensSpacetimeJet (c i) J)
      (opensSpacetimeJet cInf J) atTop K :=
    uniform_prod_same htime (uniform_prod_same hvU (uniform_prod_same hx (uniform_prod_same hxx ht)))
  have hdensity := normalVelocityErrorDensity_covariantCurveJet_tendstoUniformlyOn hG hK
    ((opensSpacetimeJet_continuousOn hJ hcInf).mono hsub)
    (fun p hp => hreg hp.2)
    (fun p hp => opensSpacetimeJet_X_ne_zero hiInf (hsub hp)) hj
  have hactual := (hdensity.congr (Eventually.of_forall fun i p hp =>
    density_opensSpacetimeJet_eq g hJ (hc i) (hsub hp))).congr_right
      (fun p hp => density_opensSpacetimeJet_eq g hJ hcInf (hsub hp))
  have hint : ∀ d : CurveMap U, d.SmoothOn (I := 𝓘(ℝ, F)) J →
      d.ImmersedOn (I := 𝓘(ℝ, F)) J → ∀ t ∈ J,
      IntervalIntegrable (fun x => Real.sqrt (d.normSq g (d.normalVelocityError g J) x t) *
        d.speed g x t) volume 0 1 := by
    intro d hd hid t htJ
    have hjd := opensSpacetimeJet_continuousOn hJ hd
    have hden : ContinuousOn (fun p => normalVelocityErrorDensity
        (covariantCurveJet g (opensSpacetimeJet d J p))) (univ ×ˢ J) := by
      intro p hp
      exact (normalVelocityErrorDensity_covariantCurveJet_continuousAt hG
        (hreg hp.2) (opensSpacetimeJet_X_ne_zero hid hp)).comp_continuousWithinAt
          (hjd p hp)
    have ha : ContinuousOn (fun p : ℝ × ℝ => Real.sqrt
        (d.normSq g (d.normalVelocityError g J) p.1 p.2) * d.speed g p.1 p.2)
        (univ ×ˢ J) := hden.congr fun p hp => (density_opensSpacetimeJet_eq g hJ hd hp).symm
    exact (ha.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x _ => ⟨mem_univ _, htJ⟩)).intervalIntegrable
  exact tendstoUniformlyOn_areaError_of_integrand g c cInf
    (Eventually.of_forall fun i => hint (c i) (hc i) (hi i)) (hint cInf hcInf hiInf) hactual

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

theorem tendstoUniformlyOn_areaError_of_embedding_iteratedFDerivWithin
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn D g) {a b : ℝ} (hab : a < b)
    (hreg : Icc a b ⊆ D.regular) {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hemb : Topology.IsEmbedding e)
    (heImm : ∀ p, Function.Injective (mfderiv I 𝓘(ℝ, F) e p))
    (c : ℕ → CurveMap M) (cInf : CurveMap M)
    (hc : ∀ i, (c i).SmoothOn (I := I) (Icc a b))
    (hi : ∀ i, (c i).ImmersedOn (I := I) (Icc a b))
    (hcInf : cInf.SmoothOn (I := I) (Icc a b))
    (hiInf : cInf.ImmersedOn (I := I) (Icc a b))
    (hjet : ∀ m ≤ 2, TendstoUniformlyOn
      (fun i p => iteratedFDerivWithin ℝ m
        (fun q : ℝ × ℝ => e ((c i).lift q.1 q.2)) (univ ×ˢ Icc a b) p)
      (fun p => iteratedFDerivWithin ℝ m
        (fun q : ℝ × ℝ => e (cInf.lift q.1 q.2)) (univ ×ˢ Icc a b) p)
      atTop (Icc (0 : ℝ) 1 ×ˢ Icc a b)) :
    TendstoUniformlyOn (fun i => (c i).areaError g (Icc a b))
      (cInf.areaError g (Icc a b)) atTop (Icc a b) := by
  let _ : Nonempty M := ⟨cInf 0 0⟩
  obtain ⟨U, hEU, G, hGs, hinner, hII⟩ :=
    exists_metricFamilySmoothOn_totally_geodesic_extension g hG he hemb heImm
  let j : M → U := fun p => ⟨e p, hEU (mem_range_self p)⟩
  have hj : ContMDiff I 𝓘(ℝ, F) ∞ j := (ContMDiff.subtypeVal_comp_iff U j).mp he
  have hmetric : ∀ t p v w, (G t).inner (j p)
      (mfderiv I 𝓘(ℝ, F) j p v) (mfderiv I 𝓘(ℝ, F) j p w) = (g t).inner p v w := by
    intro t p v w
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp j p]
    exact hinner t p v w
  have hsm : ∀ d : CurveMap M, d.SmoothOn (I := I) (Icc a b) →
      CurveMap.SmoothOn (I := 𝓘(ℝ, F)) (fun z t => j (d z t)) (Icc a b) :=
    fun d hd => hj.comp_contMDiffOn hd
  have himm : ∀ d : CurveMap M, d.SmoothOn (I := I) (Icc a b) →
      d.ImmersedOn (I := I) (Icc a b) →
      CurveMap.ImmersedOn (I := 𝓘(ℝ, F)) (fun z t => j (d z t)) (Icc a b) := by
    intro d hd hid x t ht hzero
    have hs := (contMDiffOn_univ.mp (d.space_slice_contMDiffOn (Icc a b) hd t ht)).mdifferentiableAt
      (x := x) (by simp)
    have hX : CurveMap.X (I := 𝓘(ℝ, F)) (fun z t => j (d z t)) x t =
        mfderiv I 𝓘(ℝ, F) j (d.lift x t) (d.X (I := I) x t) :=
      mfderiv_comp_apply x (hj.mdifferentiableAt (by simp)) hs 1
    have hinj : Function.Injective (mfderiv I 𝓘(ℝ, F) j (d.lift x t)) := by
      rw [← DifferentialGeometry.mfderiv_subtypeVal_comp j (d.lift x t)]
      exact heImm (d.lift x t)
    have hXF : (CurveMap.X (I := 𝓘(ℝ, F)) (fun z t => j (d z t)) x t : F) =
        (mfderiv I 𝓘(ℝ, F) j (d.lift x t) (d.X x t) : F) := hX
    have hzF : (CurveMap.X (I := 𝓘(ℝ, F)) (fun z t => j (d z t)) x t : F) = 0 := hzero
    have hlinzero : (mfderiv I 𝓘(ℝ, F) j (d.lift x t) 0 : F) = 0 := map_zero _
    exact hid x t ht (hinj (hXF.symm.trans (hzF.trans hlinzero.symm)))
  have hconv := tendstoUniformlyOn_areaError_opens_of_iteratedFDerivWithin hGs hab hreg
    (fun i z t => j (c i z t)) (fun z t => j (cInf z t))
    (fun i => hsm (c i) (hc i)) (fun i => himm (c i) (hc i) (hi i))
    (hsm cInf hcInf) (himm cInf hcInf hiInf) hjet
  have heq : ∀ d : CurveMap M, d.SmoothOn (I := I) (Icc a b) → ∀ t ∈ Icc a b,
      CurveMap.areaError (I := 𝓘(ℝ, F)) (fun z τ => j (d z τ)) G (Icc a b) t =
        d.areaError g (Icc a b) t := by
    intro d hd t ht
    exact areaError_comp_of_vanishingSecondFundamentalForm hj hmetric hII hd ht
      ((uniqueDiffOn_Icc hab) t ht)
  exact (hconv.congr (Eventually.of_forall fun i t ht => heq (c i) (hc i) t ht)).congr_right
    (fun t ht => heq cInf hcInf t ht)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end
