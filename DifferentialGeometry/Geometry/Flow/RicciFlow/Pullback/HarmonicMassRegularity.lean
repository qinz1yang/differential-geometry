import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicStateMass
import DifferentialGeometry.Analysis.Integration.Measure.FamilyContinuity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Regularity of the finite state-dependent HMF mass

The coefficient derivative of the exponential local addition takes values in
a moving tangent fibre.  `HarmonicDensityJoint` proves that derivative as a
jointly regular bundled section for every fixed finite coefficient direction.
This file takes the finite minimum of those radii, pairs the resulting
sections with the target metric, and reconstructs the whole finite bilinear
mass map from its matrix entries.

There are three outputs used by the nonlinear harmonic-map heat-flow lane:

* the pointwise state mass is jointly `C¹` on one coefficient ball;
* its fixed-volume integral is Lipschitz on one smaller closed ball;
* against a real-time metric family, every fixed state coefficient of the
  faithful mass is continuous in time on a compact interval.

The radius in all three statements is chosen before the spatial point and,
in the time-continuity theorem, before the metric family.  No time-dependent
shrinking is used.
-/

noncomputable section

open Bundle Filter Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M]

/-! ## Finite bilinear reconstruction -/

/-- The canonical Euclidean basis, viewed as an algebraic basis so that its
coordinate maps can be promoted to continuous linear maps. -/
private noncomputable def hmfCBasis (ι : Type*) [Fintype ι] :
    Module.Basis ι ℝ (EuclideanSpace ℝ ι) :=
  (EuclideanSpace.basisFun ι ℝ).toBasis

/-- The `i`-th coefficient functional on a finite Euclidean trial space. -/
private noncomputable def hmfCoord (ι : Type*) [Fintype ι] (i : ι) :
    EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  ((hmfCBasis ι).coord i).toContinuousLinearMap

@[simp] private theorem hmfCoord_apply
    (ι : Type*) [Fintype ι] (i : ι) (v : EuclideanSpace ℝ ι) :
    hmfCoord ι i v = (hmfCBasis ι).coord i v := rfl

/-- A constant matrix-unit bilinear form on a finite coefficient space. -/
private noncomputable def hmfMUnit
    (ι : Type*) [Fintype ι] (i j : ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  (hmfCoord ι i).smulRight (hmfCoord ι j)

@[simp] private theorem hmfMUnit_apply
    (ι : Type*) [Fintype ι] (i j : ι) (v w : EuclideanSpace ℝ ι) :
    hmfMUnit ι i j v w =
      (hmfCBasis ι).coord i v * (hmfCBasis ι).coord j w := by
  simp [hmfMUnit, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- Expansion of a finite-dimensional bilinear form in the canonical
Euclidean basis. -/
private theorem hmfBilinExpand
    (ι : Type*) [Fintype ι]
    (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (v w : EuclideanSpace ℝ ι) :
    B v w = ∑ i, ∑ j,
      (hmfCBasis ι).coord i v * (hmfCBasis ι).coord j w *
        B (hmfCBasis ι i) (hmfCBasis ι j) := by
  let b := hmfCBasis ι
  have hcoord : ∀ (u : EuclideanSpace ℝ ι) (i : ι),
      b.coord i u = b.repr u i :=
    fun u i ↦ Module.Basis.coord_apply b i u
  have hv : B v = ∑ i, b.repr v i • B (b i) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [map_smul]
  have hw : ∀ i, B (b i) w = ∑ j, b.repr w j • B (b i) (b j) := by
    intro i
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [map_smul]
  calc
    B v w = (∑ i, b.repr v i • B (b i)) w := by rw [hv]
    _ = ∑ i, b.repr v i • B (b i) w := by
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [ContinuousLinearMap.smul_apply]
    _ = ∑ i, b.repr v i • ∑ j, b.repr w j • B (b i) (b j) := by
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [hw i]
    _ = ∑ i, ∑ j,
        b.coord i v * b.coord j w * B (b i) (b j) := by
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [smul_eq_mul, smul_eq_mul, hcoord, hcoord]
      ring

/-- A finite bilinear form is the sum of its basis coefficients times the
constant matrix units. -/
private theorem hmfBilin_eq_sum
    (ι : Type*) [Fintype ι]
    (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    B = ∑ i, ∑ j, B (hmfCBasis ι i) (hmfCBasis ι j) • hmfMUnit ι i j := by
  ext v w
  rw [hmfBilinExpand ι B v w]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    hmfMUnit_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ ↦
    Finset.sum_congr rfl (fun j _ ↦ ?_))
  ring

/-! ## Joint pointwise regularity -/

/-- On one coefficient ball, the complete pointwise faithful mass operator is
jointly `C¹` in the coefficient and spatial variables.  The common radius is
the finite minimum of the radii for the zero direction and all canonical
basis directions supplied by `hmfSpecCoeff_cd`.

The zero direction is included so that the common bundled coefficient
producer also supplies the base map needed to pull back `q.inner`. -/
theorem hmfSpecMassPt_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I)
        𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S} →L[ℝ]
          EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ)
        (1 : ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          hmfSpecMassPt (I := I) (M := M) q S p.1 p.2)
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  classical
  let ι := {i // i ∈ S}
  let V := EuclideanSpace ℝ ι
  let IV : ModelWithCorners ℝ V V := 𝓘(ℝ, V)
  let P : ModelWithCorners ℝ (V × E) (V × H) := IV.prod I
  let b : ι → V := fun i ↦ hmfCBasis ι i
  let dir : Option ι → V
    | none => 0
    | some i => b i
  have hdir : ∀ a : Option ι, ∃ R : ℝ, 0 < R ∧
      ContMDiffOn P (I.prod 𝓘(ℝ, E)) (2 : ℕ∞)
        (fun p : V × M ↦
          (TotalSpace.mk' E
            (hmfAdd (I := I) (M := M) q
              (hmfSpecIncl (I := I) (M := M) q S p.1) p.2)
            (mfderiv IV I
              (fun u : V ↦ hmfAdd (I := I) (M := M) q
                (hmfSpecIncl (I := I) (M := M) q S u) p.2)
              p.1 (dir a)) : TangentBundle I M))
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
    intro a
    simpa only [V, IV, P] using
      hmfSpecCoeff_cd (I := I) (M := M) q S (dir a)
  choose rad hrad hsec using hdir
  let R : ℝ := (Finset.univ : Finset (Option ι)).inf'
    Finset.univ_nonempty rad
  have hR : 0 < R := by
    dsimp only [R]
    rw [Finset.lt_inf'_iff]
    intro a _
    exact hrad a
  have hRle : ∀ a : Option ι, R ≤ rad a := by
    intro a
    dsimp only [R]
    exact Finset.inf'_le (s := Finset.univ) (f := rad) (by simp)
  let D : Set (V × M) := Metric.ball 0 R ×ˢ (Set.univ : Set M)
  have hsecR : ∀ a : Option ι,
      ContMDiffOn P (I.prod 𝓘(ℝ, E)) (2 : ℕ∞)
        (fun p : V × M ↦
          (TotalSpace.mk' E
            (hmfAdd (I := I) (M := M) q
              (hmfSpecIncl (I := I) (M := M) q S p.1) p.2)
            (mfderiv IV I
              (fun u : V ↦ hmfAdd (I := I) (M := M) q
                (hmfSpecIncl (I := I) (M := M) q S u) p.2)
              p.1 (dir a)) : TangentBundle I M)) D := by
    intro a
    exact (hsec a).mono (Set.prod_mono
      (Metric.ball_subset_ball (hRle a)) (Set.Subset.rfl))
  let F : V × M → M := fun p ↦
    hmfAdd (I := I) (M := M) q
      (hmfSpecIncl (I := I) (M := M) q S p.1) p.2
  have hmap : ContMDiffOn P I (2 : ℕ∞) F D := by
    intro p hp
    have hat := hsecR none p hp
    rw [Bundle.contMDiffWithinAt_totalSpace] at hat
    exact hat.1
  have hmetric : ContMDiffOn P
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (1 : ℕ∞)
      (fun p : V × M ↦
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (F p) (q.inner (F p))) D := by
    simpa only [Function.comp_apply] using
      (q.contMDiff.of_le (by simp)).comp_contMDiffOn
        (hmap.of_le (by norm_num))
  have hcoeff : ∀ i j : ι, ContMDiffOn P 𝓘(ℝ) (1 : ℕ∞)
      (fun p : V × M ↦
        hmfSpecMassPt (I := I) (M := M) q S p.1 p.2 (b i) (b j)) D := by
    intro i j
    have happ := ContMDiffOn.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := F) hmetric
      ((hsecR (some i)).of_le (by norm_num))
      ((hsecR (some j)).of_le (by norm_num))
    intro p hp
    have hat := happ p hp
    rw [Bundle.contMDiffWithinAt_totalSpace] at hat
    simpa only [hmfSpecMassPt_apply, hmfSpecVar, F, dir] using hat.2
  have hsum : ContMDiffOn P
      𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ) (1 : ℕ∞)
      (fun p : V × M ↦ ∑ i, ∑ j,
        hmfSpecMassPt (I := I) (M := M) q S p.1 p.2 (b i) (b j) •
          hmfMUnit ι i j) D := by
    refine contMDiffOn_finset_sum (fun i _ ↦ ?_)
    refine contMDiffOn_finset_sum (fun j _ ↦ ?_)
    exact (hcoeff i j).smul contMDiffOn_const
  refine ⟨R, hR, ?_⟩
  simpa only [ι, V, IV, P, D] using hsum.congr (by
    intro p hp
    rw [hmfBilin_eq_sum ι
      (hmfSpecMassPt (I := I) (M := M) q S p.1 p.2)])

/-! ## Uniform coefficient Lipschitz bounds -/

/-- Joint `C¹` regularity on an open coefficient ball makes the coefficient
Fréchet derivative jointly continuous on every strictly smaller closed ball.
Only the coefficient factor is differentiated; the manifold point remains a
parameter. -/
private theorem partialFderiv_cont
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : V → M → W) {R r : ℝ} (hrr : r < R)
    (hF : ContMDiffOn (𝓘(ℝ, V).prod I) 𝓘(ℝ, W) (1 : ℕ∞)
      (fun p : V × M ↦ F p.1 p.2)
      (Metric.ball 0 R ×ˢ (Set.univ : Set M))) :
    ContinuousOn
      (fun p : V × M ↦ fderiv ℝ (fun u : V ↦ F u p.2) p.1)
      (Metric.closedBall 0 r ×ˢ (Set.univ : Set M)) := by
  intro p hp
  let IV : ModelWithCorners ℝ V V := 𝓘(ℝ, V)
  let IW : ModelWithCorners ℝ W W := 𝓘(ℝ, W)
  let P := IV.prod I
  have hpD : p ∈ Metric.ball (0 : V) R ×ˢ (Set.univ : Set M) := by
    refine ⟨?_, Set.mem_univ _⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact (Metric.mem_closedBall.mp hp.1).trans_lt hrr
  have hopen : IsOpen
      (Metric.ball (0 : V) R ×ˢ (Set.univ : Set M)) :=
    Metric.isOpen_ball.prod isOpen_univ
  have hFAt : ContMDiffAt P IW (1 : ℕ∞)
      (fun z : V × M ↦ F z.1 z.2) p :=
    (hF p hpD).contMDiffAt (hopen.mem_nhds hpD)
  let f : (V × M) → V → W := fun z u ↦ F u z.2
  have hf : ContMDiffAt (P.prod IV) IW (1 : ℕ∞)
      (Function.uncurry f) (p, p.1) := by
    have hpre : ContMDiffAt (P.prod IV) P (1 : ℕ∞)
        (fun z : (V × M) × V ↦ (z.2, z.1.2)) (p, p.1) :=
      contMDiffAt_snd.prodMk (contMDiffAt_fst.snd)
    simpa only [Function.uncurry_apply_pair, f] using
      hFAt.comp (p, p.1) hpre
  have hD := ContMDiffAt.mfderiv
    (I := IV) (I' := IW) (n := (1 : ℕ∞)) (m := (0 : ℕ∞))
    (f := f) (g := fun z : V × M ↦ z.1) hf contMDiffAt_fst
    (by norm_num)
  have hD' : ContMDiffAt P 𝓘(ℝ, V →L[ℝ] W) (0 : ℕ∞)
      (fun z : V × M ↦ fderiv ℝ (fun u : V ↦ F u z.2) z.1) p := by
    simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv, f]
      using hD
  exact hD'.continuousAt.continuousWithinAt

/-- A jointly `C¹` Banach-valued family on a coefficient ball is uniformly
Lipschitz in the coefficient on a smaller closed ball, uniformly in the
compact manifold parameter. -/
private theorem point_lip_cball
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : V → M → W) {R : ℝ} (hR : 0 < R)
    (hF : ContMDiffOn (𝓘(ℝ, V).prod I) 𝓘(ℝ, W) (1 : ℕ∞)
      (fun p : V × M ↦ F p.1 p.2)
      (Metric.ball 0 R ×ˢ (Set.univ : Set M))) :
    ∃ r : ℝ, 0 < r ∧ ∃ L : ℝ≥0,
      (∀ x : M, LipschitzOnWith L (fun u : V ↦ F u x)
        (Metric.closedBall 0 r)) ∧
      ContinuousOn (fun p : V × M ↦ F p.1 p.2)
        (Metric.closedBall 0 r ×ˢ (Set.univ : Set M)) := by
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := by dsimp only [r]; linarith
  let K : Set (V × M) :=
    Metric.closedBall 0 r ×ˢ (Set.univ : Set M)
  have hDK : ContinuousOn
      (fun p : V × M ↦ fderiv ℝ (fun u : V ↦ F u p.2) p.1) K :=
    partialFderiv_cont (I := I) (M := M) F hrR hF
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : V) r).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hDK.norm
  let L : ℝ≥0 := ⟨max C 0, le_max_right C 0⟩
  have hsub : Metric.closedBall (0 : V) r ⊆ Metric.ball 0 R := by
    intro u hu
    rw [Metric.mem_ball, dist_zero_right]
    exact (Metric.mem_closedBall.mp hu).trans_lt hrR
  have hdiff : ∀ x : M, ∀ u ∈ Metric.closedBall (0 : V) r,
      DifferentiableAt ℝ (fun z : V ↦ F z x) u := by
    intro x u hu
    have hp : (u, x) ∈ Metric.ball (0 : V) R ×ˢ (Set.univ : Set M) :=
      ⟨hsub hu, Set.mem_univ _⟩
    have hopen : IsOpen
        (Metric.ball (0 : V) R ×ˢ (Set.univ : Set M)) :=
      Metric.isOpen_ball.prod isOpen_univ
    have hjoint := (hF (u, x) hp).contMDiffAt (hopen.mem_nhds hp)
    have hincl : ContMDiffAt 𝓘(ℝ, V) (𝓘(ℝ, V).prod I) (1 : ℕ∞)
        (fun z : V ↦ (z, x)) u := contMDiffAt_id.prodMk contMDiffAt_const
    have hslice : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, W) (1 : ℕ∞)
        (fun z : V ↦ F z x) u := hjoint.comp u hincl
    exact (contMDiffAt_iff_contDiffAt.mp hslice).differentiableAt
      (by norm_num)
  have hlip : ∀ x : M, LipschitzOnWith L (fun u : V ↦ F u x)
      (Metric.closedBall 0 r) := by
    intro x
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun u hu ↦ hdiff x u hu)
    · intro u hu
      rw [← NNReal.coe_le_coe]
      exact (hC (u, x) ⟨hu, Set.mem_univ _⟩).trans
        (le_max_left C 0)
    · exact convex_closedBall (0 : V) r
  refine ⟨r, hr, L, hlip, ?_⟩
  exact hF.continuousOn.mono (Set.prod_mono hsub Set.Subset.rfl)

/-- The pointwise faithful mass is uniformly Lipschitz in the state on one
closed coefficient ball, with one Lipschitz constant valid at every spatial
point. -/
theorem hmfSpecMassPt_lip
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧ ∃ L : ℝ≥0, ∀ x : M,
      LipschitzOnWith L
        (fun u : EuclideanSpace ℝ {i // i ∈ S} ↦
          hmfSpecMassPt (I := I) (M := M) q S u x)
        (Metric.closedBall 0 R) := by
  obtain ⟨R, hR, hmass⟩ := hmfSpecMassPt_cd (I := I) (M := M) q S
  obtain ⟨r, hr, L, hlip, _⟩ :=
    point_lip_cball (I := I) (M := M)
      (fun u x ↦ hmfSpecMassPt (I := I) (M := M) q S u x) hR hmass
  exact ⟨r, hr, L, hlip⟩

/-- For every fixed domain metric, the integrated faithful mass is Lipschitz
in the state on one coefficient closed ball.  The radius depends only on the
pointwise local-addition regularity; the Lipschitz constant additionally
contains the finite volume of the chosen domain metric. -/
theorem hmfSpecMass_lip
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧ ∃ L : ℝ≥0,
      LipschitzOnWith L
        (hmfSpecMassOp (I := I) (M := M) q h S)
        (Metric.closedBall 0 R) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) h
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) h
  obtain ⟨R, hR, hmass⟩ := hmfSpecMassPt_cd (I := I) (M := M) q S
  obtain ⟨r, hr, Lp, hpLip, hpCont⟩ :=
    point_lip_cball (I := I) (M := M)
      (fun u x ↦ hmfSpecMassPt (I := I) (M := M) q S u x) hR hmass
  let vol : ℝ≥0 := ⟨μ.real Set.univ, measureReal_nonneg⟩
  let L : ℝ≥0 := Lp * vol
  refine ⟨r, hr, L, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro u hu v hv
  have hcont_u : Continuous
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S u x) := by
    rw [← continuousOn_univ]
    exact hpCont.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ ↦ ⟨hu, Set.mem_univ x⟩)
  have hcont_v : Continuous
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S v x) := by
    rw [← continuousOn_univ]
    exact hpCont.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ ↦ ⟨hv, Set.mem_univ x⟩)
  have hint_u : Integrable
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S u x) μ :=
    integrableOn_univ.mp
      (hcont_u.continuousOn.integrableOn_compact isCompact_univ)
  have hint_v : Integrable
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S v x) μ :=
    integrableOn_univ.mp
      (hcont_v.continuousOn.integrableOn_compact isCompact_univ)
  rw [dist_eq_norm]
  change ‖(∫ x, hmfSpecMassPt (I := I) (M := M) q S u x ∂μ) -
      ∫ x, hmfSpecMassPt (I := I) (M := M) q S v x ∂μ‖ ≤
    (L : ℝ) * ‖u - v‖
  rw [← integral_sub hint_u hint_v]
  have hbound : ∀ᵐ x ∂μ,
      ‖hmfSpecMassPt (I := I) (M := M) q S u x -
          hmfSpecMassPt (I := I) (M := M) q S v x‖ ≤
        (Lp : ℝ) * ‖u - v‖ := by
    filter_upwards with x
    simpa only [dist_eq_norm] using
      (hpLip x).dist_le_mul u hu v hv
  calc
    ‖∫ x, hmfSpecMassPt (I := I) (M := M) q S u x -
        hmfSpecMassPt (I := I) (M := M) q S v x ∂μ‖
        ≤ ((Lp : ℝ) * ‖u - v‖) * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const hbound
    _ = (L : ℝ) * ‖u - v‖ := by
      simp only [L, vol, NNReal.coe_mul, NNReal.coe_mk]
      ring

/-- A uniform upper bound for the total volumes of a metric family turns the
pointwise state estimate into one common state-Lipschitz estimate for all
times in `K`.  The coefficient radius and the pointwise derivative constant
are chosen before `g`, `K`, and the volume bound are used. -/
theorem hmfMassFam_lip
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ} (B : ℝ≥0)
    (hvol : ∀ t ∈ K,
      (riemannianVolumeMeasure (I := I) (M := M) (g t)).real Set.univ ≤ B) :
    ∃ R : ℝ, 0 < R ∧ ∃ L : ℝ≥0, ∀ t ∈ K,
      LipschitzOnWith L
        (hmfSpecMassOp (I := I) (M := M) q (g t) S)
        (Metric.closedBall 0 R) := by
  obtain ⟨R, hR, hmass⟩ := hmfSpecMassPt_cd (I := I) (M := M) q S
  obtain ⟨r, hr, Lp, hpLip, hpCont⟩ :=
    point_lip_cball (I := I) (M := M)
      (fun u x ↦ hmfSpecMassPt (I := I) (M := M) q S u x) hR hmass
  let L : ℝ≥0 := Lp * B
  refine ⟨r, hr, L, ?_⟩
  intro t ht
  let μ := riemannianVolumeMeasure (I := I) (M := M) (g t)
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) (g t)
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  have hcont_u : Continuous
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S u x) := by
    rw [← continuousOn_univ]
    exact hpCont.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ ↦ ⟨hu, Set.mem_univ x⟩)
  have hcont_v : Continuous
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S v x) := by
    rw [← continuousOn_univ]
    exact hpCont.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ ↦ ⟨hv, Set.mem_univ x⟩)
  have hint_u : Integrable
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S u x) μ :=
    integrableOn_univ.mp
      (hcont_u.continuousOn.integrableOn_compact isCompact_univ)
  have hint_v : Integrable
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S v x) μ :=
    integrableOn_univ.mp
      (hcont_v.continuousOn.integrableOn_compact isCompact_univ)
  rw [dist_eq_norm]
  change ‖(∫ x, hmfSpecMassPt (I := I) (M := M) q S u x ∂μ) -
      ∫ x, hmfSpecMassPt (I := I) (M := M) q S v x ∂μ‖ ≤
    (L : ℝ) * ‖u - v‖
  rw [← integral_sub hint_u hint_v]
  have hbound : ∀ᵐ x ∂μ,
      ‖hmfSpecMassPt (I := I) (M := M) q S u x -
          hmfSpecMassPt (I := I) (M := M) q S v x‖ ≤
        (Lp : ℝ) * ‖u - v‖ := by
    filter_upwards with x
    simpa only [dist_eq_norm] using
      (hpLip x).dist_le_mul u hu v hv
  calc
    ‖∫ x, hmfSpecMassPt (I := I) (M := M) q S u x -
        hmfSpecMassPt (I := I) (M := M) q S v x ∂μ‖
        ≤ ((Lp : ℝ) * ‖u - v‖) * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const hbound
    _ ≤ ((Lp : ℝ) * ‖u - v‖) * (B : ℝ) := by
      exact mul_le_mul_of_nonneg_left (hvol t ht)
        (mul_nonneg Lp.coe_nonneg (norm_nonneg _))
    _ = (L : ℝ) * ‖u - v‖ := by
      simp only [L, NNReal.coe_mul]
      ring

/-- The fixed-background specialization requested by the finite HMF solver.
It has exactly the same state radius as the arbitrary-fixed-volume theorem. -/
theorem hmfSpecMassQ_lip
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧ ∃ L : ℝ≥0,
      LipschitzOnWith L
        (hmfSpecMassOp (I := I) (M := M) q q S)
        (Metric.closedBall 0 R) :=
  hmfSpecMass_lip (I := I) (M := M) q q S

/-! ## Zero-state identification and coercivity -/

/-- At state zero, the faithful finite mass operator is exactly the older
finite HMF mass restricted along the canonical spectral inclusion. -/
theorem hmfSpecMass_zero
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    hmfSpecMassOp (I := I) (M := M) q h S 0 =
      hmfFinMass (I := I) (M := M) q h
        (hmfSpecIncl (I := I) (M := M) q S) := by
  obtain ⟨Rm, hRm, hmass⟩ := hmfSpecMassPt_cd (I := I) (M := M) q S
  obtain ⟨Ra, hRa, hmap⟩ :=
    hmfSpecMap_cd (I := I) (M := M) q S 1 (by norm_num)
  have hzero_m : (0 : EuclideanSpace ℝ {i // i ∈ S}) ∈ Metric.ball 0 Rm := by
    simpa only [Metric.mem_ball, dist_self] using hRm
  have hzero_a : (0 : EuclideanSpace ℝ {i // i ∈ S}) ∈ Metric.ball 0 Ra := by
    simpa only [Metric.mem_ball, dist_self] using hRa
  have hcont : Continuous
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S 0 x) := by
    rw [← continuousOn_univ]
    exact hmass.continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun x _ ↦ ⟨hzero_m, Set.mem_univ x⟩)
  have hint : Integrable
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S 0 x)
      (riemannianVolumeMeasure (I := I) (M := M) h) :=
    integrableOn_univ.mp
      (hcont.continuousOn.integrableOn_compact isCompact_univ)
  have hmd : ∀ x : M,
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
        (fun z : EuclideanSpace ℝ {i // i ∈ S} ↦
          hmfAdd (I := I) (M := M) q
            (hmfSpecIncl (I := I) (M := M) q S z) x) 0 := by
    intro x
    have hp : ((0 : EuclideanSpace ℝ {i // i ∈ S}), x) ∈
        Metric.ball 0 Ra ×ˢ (Set.univ : Set M) :=
      ⟨hzero_a, Set.mem_univ _⟩
    have hopen : IsOpen
        (Metric.ball (0 : EuclideanSpace ℝ {i // i ∈ S}) Ra ×ˢ
          (Set.univ : Set M)) := Metric.isOpen_ball.prod isOpen_univ
    have hjoint := (hmap (0, x) hp).contMDiffAt (hopen.mem_nhds hp)
    have hincl : ContMDiffAt
        𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S})
        (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (1 : ℕ∞)
        (fun z : EuclideanSpace ℝ {i // i ∈ S} ↦ (z, x)) 0 :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact (hjoint.comp 0 hincl).mdifferentiableAt (by norm_num)
  ext v w
  calc
    hmfSpecMassOp (I := I) (M := M) q h S 0 v w =
        hmfStateMass (I := I) (M := M) q h
          (hmfSpecIncl (I := I) (M := M) q S 0)
          (hmfSpecIncl (I := I) (M := M) q S v)
          (hmfSpecIncl (I := I) (M := M) q S w) :=
      hmfSpecMass_state (I := I) (M := M) q h S 0 v w hmd hint
    _ = hmfMass (I := I) (M := M) q h
          (hmfSpecIncl (I := I) (M := M) q S v)
          (hmfSpecIncl (I := I) (M := M) q S w) := by
      rw [map_zero, hmfStateMass_zero_eq]
    _ = hmfFinMass (I := I) (M := M) q h
          (hmfSpecIncl (I := I) (M := M) q S) v w := by
      rw [hmfFinMass_apply]

/-- Reverse volume domination gives the exact common zero-state lower bound
needed by `coerOn_of_lip`.  In particular, a time-uniform comparison constant
immediately gives a time-uniform zero-state coercivity constant. -/
theorem hmfSpecMass_lower
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I) (M := M) h)
    (v : EuclideanSpace ℝ {i // i ∈ S}) :
    C.toReal⁻¹ * ‖v‖ * ‖v‖ ≤
      hmfSpecMassOp (I := I) (M := M) q h S 0 v v := by
  rw [hmfSpecMass_zero (I := I) (M := M) q h S]
  exact hmfFinMass_lower (I := I) (M := M) q h C hC0 hCtop hvol
    (hmfSpecIncl (I := I) (M := M) q S)
    (hmfSpecIncl_orth (I := I) (M := M) q S) v

/-! ## Real-time moving-volume continuity -/

/-- On one state ball chosen independently of the metric family, every fixed
faithful state-mass coefficient is continuous in real time.  Only the volume
measure moves, so `integral_family_cont` applies directly; no parameterized
measure-continuity wrapper is used. -/
theorem hmfStateTime_cont
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧
      ∀ (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ}, IsCompact K →
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
        (fun p : ℝ × M ↦ chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      ∀ u : EuclideanSpace ℝ {i // i ∈ S}, u ∈ Metric.ball 0 R →
      ∀ v w : EuclideanSpace ℝ {i // i ∈ S},
        ContinuousOn
          (fun t ↦ hmfStateMass (I := I) (M := M) q (g t)
            (hmfSpecIncl (I := I) (M := M) q S u)
            (hmfSpecIncl (I := I) (M := M) q S v)
            (hmfSpecIncl (I := I) (M := M) q S w)) K := by
  obtain ⟨Rm, hRm, hmass⟩ := hmfSpecMassPt_cd (I := I) (M := M) q S
  obtain ⟨Ra, hRa, hmap⟩ :=
    hmfSpecMap_cd (I := I) (M := M) q S 1 (by norm_num)
  let R := min Rm Ra
  have hR : 0 < R := lt_min hRm hRa
  refine ⟨R, hR, ?_⟩
  intro g K hK hgram u hu v w
  have hu_m : u ∈ Metric.ball
      (0 : EuclideanSpace ℝ {i // i ∈ S}) Rm :=
    Metric.ball_subset_ball (min_le_left Rm Ra) hu
  have hu_a : u ∈ Metric.ball
      (0 : EuclideanSpace ℝ {i // i ∈ S}) Ra :=
    Metric.ball_subset_ball (min_le_right Rm Ra) hu
  have hpt : Continuous
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S u x) := by
    rw [← continuousOn_univ]
    exact hmass.continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun x _ ↦ ⟨hu_m, Set.mem_univ x⟩)
  have hscalar : Continuous
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S u x v w) :=
    (hpt.clm_apply continuous_const).clm_apply continuous_const
  have hmd : ∀ x : M,
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
        (fun z : EuclideanSpace ℝ {i // i ∈ S} ↦
          hmfAdd (I := I) (M := M) q
            (hmfSpecIncl (I := I) (M := M) q S z) x) u := by
    intro x
    have hp : (u, x) ∈
        Metric.ball (0 : EuclideanSpace ℝ {i // i ∈ S}) Ra ×ˢ
          (Set.univ : Set M) := ⟨hu_a, Set.mem_univ _⟩
    have hopen : IsOpen
        (Metric.ball (0 : EuclideanSpace ℝ {i // i ∈ S}) Ra ×ˢ
          (Set.univ : Set M)) := Metric.isOpen_ball.prod isOpen_univ
    have hjoint := (hmap (u, x) hp).contMDiffAt (hopen.mem_nhds hp)
    have hincl : ContMDiffAt
        𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S})
        (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (1 : ℕ∞)
        (fun z : EuclideanSpace ℝ {i // i ∈ S} ↦ (z, x)) u :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact (hjoint.comp u hincl).mdifferentiableAt (by norm_num)
  have heq : (fun x : M ↦
      q.inner
        (hmfAdd (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S u) x)
        (hmfStateVar (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S u)
          (hmfSpecIncl (I := I) (M := M) q S v) x)
        (hmfStateVar (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S u)
          (hmfSpecIncl (I := I) (M := M) q S w) x)) =
      (fun x : M ↦ hmfSpecMassPt (I := I) (M := M) q S u x v w) := by
    funext x
    rw [hmfSpecVar_state (I := I) (M := M) q S u v x (hmd x),
      hmfSpecVar_state (I := I) (M := M) q S u w x (hmd x),
      hmfSpecMassPt_apply]
  unfold hmfStateMass
  apply integral_family_cont (I := I) (M := M) hK hgram
  have hspace : Continuous (fun x : M ↦
      q.inner
        (hmfAdd (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S u) x)
        (hmfStateVar (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S u)
          (hmfSpecIncl (I := I) (M := M) q S v) x)
        (hmfStateVar (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S u)
          (hmfSpecIncl (I := I) (M := M) q S w) x)) := by
    rw [heq]
    exact hscalar
  exact (hspace.comp continuous_snd).continuousOn

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
