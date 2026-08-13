import DifferentialGeometry.Analysis.Parabolic.Euclidean.VariableCoefficient
import DifferentialGeometry.Analysis.Schauder.Interpolation

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicGradientComponent
    (u : Real → Euc n → F) (i : n) : ParabolicPoint (Euc n) → F :=
  fun p ↦ continuousMultilinearCurryFin1 Real (Euc n) F
    (parabolicSpatialJet 1 u p) (EuclideanSpace.basisFun n Real i)

def parabolicDriftTerm
    (b : n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  fun p ↦ ∑ i, b i p • parabolicGradientComponent u i p

def parabolicPotentialTerm
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  fun p ↦ c p • u p.time p.space

def parabolicLowerOrderTerm
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  parabolicDriftTerm b u + parabolicPotentialTerm c u

def parabolicNondivergenceOperator
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  parabolicVariableMatrixOperator a u - parabolicLowerOrderTerm b c u

def parabolicDriftCoefficientRescale
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (b : n → ParabolicPoint (Euc n) → Real) :
    n → ParabolicPoint (Euc n) → Real :=
  fun i p ↦ (r : Real) * b i (parabolicDilationAt r p0 p)

def parabolicPotentialCoefficientRescale
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (c : ParabolicPoint (Euc n) → Real) :
    ParabolicPoint (Euc n) → Real :=
  fun p ↦ (r : Real) ^ 2 * c (parabolicDilationAt r p0 p)

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicDriftCoefficientRescale_apply
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (b : n → ParabolicPoint (Euc n) → Real)
    (i : n) (p : ParabolicPoint (Euc n)) :
    parabolicDriftCoefficientRescale r p0 b i p =
      (r : Real) * b i (parabolicDilationAt r p0 p) := rfl

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicPotentialCoefficientRescale_apply
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (c : ParabolicPoint (Euc n) → Real) (p : ParabolicPoint (Euc n)) :
    parabolicPotentialCoefficientRescale r p0 c p =
      (r : Real) ^ 2 * c (parabolicDilationAt r p0 p) := rfl

omit [DecidableEq n] [Nonempty n] in
theorem parabolicDriftCoefficientRescale_holderWith_unitBall
    {alpha : NNReal} (r : NNReal) (hr : 0 < r)
    (p0 : ParabolicPoint (Euc n))
    (b : n → ParabolicPoint (Euc n) → Real) (Kb : n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((Metric.ball p0 r).restrict (b i))) :
    ∀ i, HolderWith (Kb i * r ^ (alpha : Real) * r) alpha
      ((Metric.ball (parabolicPoint 0 0) 1).restrict
        (parabolicDriftCoefficientRescale r p0 b i)) := by
  intro i
  have hadapt := parabolicHolder_dilationAt_unitBall r hr p0 (hb i)
  have hscaled := hadapt.smul (r : Real)
  have hrnorm : ‖(r : Real)‖₊ = r := by
    ext
    simp only [coe_nnnorm, Real.norm_of_nonneg r.coe_nonneg]
  rw [hrnorm] at hscaled
  simpa only [parabolicDriftCoefficientRescale, Function.comp_apply,
    Set.restrict_apply, Pi.smul_apply, smul_eq_mul] using hscaled

omit [DecidableEq n] [Nonempty n] in
theorem parabolicPotentialCoefficientRescale_holderWith_unitBall
    {alpha Kc : NNReal} (r : NNReal) (hr : 0 < r)
    (p0 : ParabolicPoint (Euc n))
    (c : ParabolicPoint (Euc n) → Real)
    (hc : HolderWith Kc alpha ((Metric.ball p0 r).restrict c)) :
    HolderWith (Kc * r ^ (alpha : Real) * r ^ 2) alpha
      ((Metric.ball (parabolicPoint 0 0) 1).restrict
        (parabolicPotentialCoefficientRescale r p0 c)) := by
  have hadapt := parabolicHolder_dilationAt_unitBall r hr p0 hc
  have hscaled := hadapt.smul ((r : Real) ^ 2)
  have hrnorm : ‖(r : Real) ^ 2‖₊ = r ^ 2 := by
    ext
    simp only [coe_nnnorm, Real.norm_of_nonneg (sq_nonneg (r : Real)),
      NNReal.coe_pow]
  rw [hrnorm] at hscaled
  simpa only [parabolicPotentialCoefficientRescale, Function.comp_apply,
    Set.restrict_apply, Pi.smul_apply, smul_eq_mul] using hscaled

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicDriftCoefficientRescale_le_of_mem_unitBall
    (r : NNReal) (hr : 0 < r) (p0 : ParabolicPoint (Euc n))
    (b : n → ParabolicPoint (Euc n) → Real) (Bb : n → NNReal)
    (hb : ∀ i p, p ∈ Metric.ball p0 r → ‖b i p‖ ≤ Bb i)
    (i : n) (p : ParabolicPoint (Euc n))
    (hp : p ∈ Metric.ball (parabolicPoint 0 0) 1) :
    ‖parabolicDriftCoefficientRescale r p0 b i p‖ ≤ r * Bb i := by
  have hmap := parabolicDilationAt_mapsTo_unitBall r hr p0 hp
  rw [parabolicDriftCoefficientRescale_apply, norm_mul,
    Real.norm_of_nonneg r.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (hb i _ hmap) r.coe_nonneg

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicPotentialCoefficientRescale_le_of_mem_unitBall
    (r : NNReal) (hr : 0 < r) (p0 : ParabolicPoint (Euc n))
    (c : ParabolicPoint (Euc n) → Real) (Bc : NNReal)
    (hc : ∀ p, p ∈ Metric.ball p0 r → ‖c p‖ ≤ Bc)
    (p : ParabolicPoint (Euc n))
    (hp : p ∈ Metric.ball (parabolicPoint 0 0) 1) :
    ‖parabolicPotentialCoefficientRescale r p0 c p‖ ≤ r ^ 2 * Bc := by
  have hmap := parabolicDilationAt_mapsTo_unitBall r hr p0 hp
  rw [parabolicPotentialCoefficientRescale_apply, norm_mul,
    Real.norm_of_nonneg (sq_nonneg (r : Real))]
  exact mul_le_mul_of_nonneg_left (hc _ hmap) (sq_nonneg (r : Real))

omit [Nonempty n] [NormedSpace Real F] in
theorem exists_parabolicNondivergenceCoefficientRescale_schauder_bounds_of_holderWith_on_parabolicCylinder
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    {a t₀ t₁ b r R : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R)
    {center : Euc n} {p0 : ParabolicPoint (Euc n)}
    (hp0 : p0 ∈ parabolicCylinder (Set.Icc t₀ t₁)
      (Metric.closedBall center r))
    (hA : (Matrix.of fun i j ↦ principal i j p0).PosDef)
    (alpha : NNReal) (halpha : 0 < alpha)
    (Ka : n → n → NNReal) (Kb Bb : n → NNReal) (Kc Bc : NNReal)
    (T : Real)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (principal i j)))
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (drift i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        potential))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖drift i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖potential p‖ ≤ Bc) :
    ∃ rho : NNReal, 0 < rho ∧ rho ≤ 1 ∧
      (rho : Real) ≤ parabolicInteriorRadius a t₀ t₁ b r R ∧
      (∀ i j, HolderWith (Ka i j * rho ^ (alpha : Real)) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicMatrixCoefficientRescale rho p0 principal i j))) ∧
      (∀ i j p, p ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖principal i j p0 -
            parabolicMatrixCoefficientRescale rho p0 principal i j p‖ ≤
          Ka i j * rho ^ (alpha : Real)) ∧
      (∀ i, HolderWith (Kb i * rho ^ (alpha : Real) * rho) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicDriftCoefficientRescale rho p0 drift i))) ∧
      (∀ i p, p ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖parabolicDriftCoefficientRescale rho p0 drift i p‖ ≤
          rho * Bb i) ∧
      HolderWith (Kc * rho ^ (alpha : Real) * rho ^ 2) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicPotentialCoefficientRescale rho p0 potential)) ∧
      (∀ p, p ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖parabolicPotentialCoefficientRescale rho p0 potential p‖ ≤
          rho ^ 2 * Bc) ∧
      spdParabolicSchauderDefectConst
        (Matrix.of fun i j ↦ principal i j p0) hA alpha
        (fun i j ↦ Ka i j * rho ^ (alpha : Real))
        (fun i j ↦ Ka i j * rho ^ (alpha : Real)) T < 1 := by
  obtain ⟨rho, hrho, hrhoOne, hrhoInterior, haRescaled,
      hoscillation, hsmall⟩ :=
    exists_parabolicMatrixCoefficientRescale_schauder_bounds_of_holderWith_on_parabolicCylinder
      principal hat₀ ht₁b hrR hp0 hA alpha halpha Ka T ha
  have hball : Metric.ball p0 (rho : Real) ⊆
      parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) :=
    (Metric.ball_subset_ball hrhoInterior).trans
      (ball_parabolicInteriorRadius_subset_parabolicCylinder
        hat₀ ht₁b hrR hp0)
  have hbLocal : ∀ i, HolderWith (Kb i) alpha
      ((Metric.ball p0 rho).restrict (drift i)) := by
    intro i
    exact ((HolderWith.restrict_iff.mp (hb i)).mono hball).holderWith
  have hcLocal : HolderWith Kc alpha
      ((Metric.ball p0 rho).restrict potential) :=
    ((HolderWith.restrict_iff.mp hc).mono hball).holderWith
  have hbNormLocal : ∀ i p, p ∈ Metric.ball p0 rho →
      ‖drift i p‖ ≤ Bb i := fun i p hp ↦ hbNorm i p (hball hp)
  have hcNormLocal : ∀ p, p ∈ Metric.ball p0 rho →
      ‖potential p‖ ≤ Bc := fun p hp ↦ hcNorm p (hball hp)
  refine ⟨rho, hrho, hrhoOne, hrhoInterior, haRescaled, hoscillation,
    parabolicDriftCoefficientRescale_holderWith_unitBall
      rho hrho p0 drift Kb hbLocal,
    ?_, parabolicPotentialCoefficientRescale_holderWith_unitBall
      rho hrho p0 potential hcLocal, ?_, hsmall⟩
  · intro i p hp
    exact norm_parabolicDriftCoefficientRescale_le_of_mem_unitBall
      rho hrho p0 drift Bb hbNormLocal i p hp
  · intro p hp
    exact norm_parabolicPotentialCoefficientRescale_le_of_mem_unitBall
      rho hrho p0 potential Bc hcNormLocal p hp

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicGradientComponent_apply
    (u : Real → Euc n → F) (i : n) (p : ParabolicPoint (Euc n)) :
    parabolicGradientComponent u i p =
      continuousMultilinearCurryFin1 Real (Euc n) F
        (parabolicSpatialJet 1 u p)
          (EuclideanSpace.basisFun n Real i) := rfl

omit [Fintype n] [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicPotentialTerm_apply
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n)) :
    parabolicPotentialTerm c u p = c p • u p.time p.space := rfl

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicLowerOrderTerm_apply
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n)) :
    parabolicLowerOrderTerm b c u p =
      (∑ i, b i p • parabolicGradientComponent u i p) +
        c p • u p.time p.space := by
  rfl

omit [DecidableEq n] [Nonempty n] in
theorem parabolicGradientComponent_rescaleAt
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (u : Real → Euc n → F) (i : n) (p : ParabolicPoint (Euc n))
    (hspace : ContDiff Real 1
      (u (p0.time + (r : Real) ^ 2 * p.time))) :
    parabolicGradientComponent (parabolicRescaleAt r p0 u) i p =
      (r : Real) •
        parabolicGradientComponent u i (parabolicDilationAt r p0 p) := by
  unfold parabolicGradientComponent
  rw [parabolicSpatialJet_rescaleAt r p0 u 1 p hspace]
  simp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicDriftTerm_rescaleAt
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (b : n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n))
    (hspace : ContDiff Real 1
      (u (p0.time + (r : Real) ^ 2 * p.time))) :
    parabolicDriftTerm (parabolicDriftCoefficientRescale r p0 b)
        (parabolicRescaleAt r p0 u) p =
      (r : Real) ^ 2 •
        parabolicDriftTerm b u (parabolicDilationAt r p0 p) := by
  simp only [parabolicDriftTerm, parabolicDriftCoefficientRescale,
    parabolicGradientComponent_rescaleAt r p0 u _ p hspace,
    smul_smul, Finset.smul_sum]
  congr 1
  funext i
  congr 1
  ring

omit [DecidableEq n] [Nonempty n] in
theorem parabolicPotentialTerm_rescaleAt
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n)) :
    parabolicPotentialTerm (parabolicPotentialCoefficientRescale r p0 c)
        (parabolicRescaleAt r p0 u) p =
      (r : Real) ^ 2 •
        parabolicPotentialTerm c u (parabolicDilationAt r p0 p) := by
  unfold parabolicPotentialTerm parabolicPotentialCoefficientRescale
    parabolicRescaleAt
  simp only [parabolicDilationAt_time, parabolicDilationAt_space]
  rw [SemigroupAction.mul_smul]

omit [DecidableEq n] [Nonempty n] in
theorem parabolicLowerOrderTerm_rescaleAt
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n))
    (hspace : ContDiff Real 1
      (u (p0.time + (r : Real) ^ 2 * p.time))) :
    parabolicLowerOrderTerm
        (parabolicDriftCoefficientRescale r p0 b)
        (parabolicPotentialCoefficientRescale r p0 c)
        (parabolicRescaleAt r p0 u) p =
      (r : Real) ^ 2 •
        parabolicLowerOrderTerm b c u (parabolicDilationAt r p0 p) := by
  unfold parabolicLowerOrderTerm
  rw [Pi.add_apply, parabolicDriftTerm_rescaleAt r p0 b u p hspace,
    parabolicPotentialTerm_rescaleAt]
  rw [Pi.add_apply, ← smul_add]

omit [DecidableEq n] [Nonempty n] in
theorem parabolicNondivergenceOperator_rescaleAt
    (r : NNReal) (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (p : ParabolicPoint (Euc n))
    (hspace : ContDiff Real 2
      (u (p0.time + (r : Real) ^ 2 * p.time))) :
    parabolicNondivergenceOperator
        (parabolicMatrixCoefficientRescale r p0 a)
        (parabolicDriftCoefficientRescale r p0 b)
        (parabolicPotentialCoefficientRescale r p0 c)
        (parabolicRescaleAt r p0 u) p =
      parabolicSourceRescaleAt r p0
        (parabolicNondivergenceOperator a b c u) p := by
  unfold parabolicNondivergenceOperator parabolicSourceRescaleAt
  rw [Pi.sub_apply,
    parabolicVariableMatrixOperator_rescaleAt r p0 a u p hspace,
    parabolicLowerOrderTerm_rescaleAt r p0 b c u p
      (hspace.of_le (by norm_num)),
    parabolicSourceRescaleAt_apply, ← smul_sub]
  rw [Pi.sub_apply]

omit [DecidableEq n] [Nonempty n] in
theorem parabolicNondivergenceOperator_rescaleAt_holderWith_unitBall
    {alpha K : NNReal} (r : NNReal) (hr : 0 < r)
    (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (hspace : ∀ t, ContDiff Real 2 (u t))
    (hoperator : HolderWith K alpha
      ((Metric.ball p0 r).restrict
        (parabolicNondivergenceOperator a b c u))) :
    HolderWith (K * r ^ (alpha : Real) * r ^ 2) alpha
      ((Metric.ball (parabolicPoint 0 0) 1).restrict
        (parabolicNondivergenceOperator
          (parabolicMatrixCoefficientRescale r p0 a)
          (parabolicDriftCoefficientRescale r p0 b)
          (parabolicPotentialCoefficientRescale r p0 c)
          (parabolicRescaleAt r p0 u))) := by
  have heq :
      (Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicNondivergenceOperator
            (parabolicMatrixCoefficientRescale r p0 a)
            (parabolicDriftCoefficientRescale r p0 b)
            (parabolicPotentialCoefficientRescale r p0 c)
            (parabolicRescaleAt r p0 u)) =
        (Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicSourceRescaleAt r p0
            (parabolicNondivergenceOperator a b c u)) := by
    funext p
    exact parabolicNondivergenceOperator_rescaleAt
      r p0 a b c u p.1 (hspace _)
  rw [heq]
  exact parabolicSourceRescaleAt_holderWith_unitBall r hr p0 _ hoperator

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicNondivergenceOperator_rescaleAt_le_of_mem_unitBall
    (r : NNReal) (hr : 0 < r) (p0 : ParabolicPoint (Euc n))
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (hspace : ∀ t, ContDiff Real 2 (u t))
    (B : NNReal)
    (hoperator : ∀ p, p ∈ Metric.ball p0 r →
      ‖parabolicNondivergenceOperator a b c u p‖ ≤ B)
    (p : ParabolicPoint (Euc n))
    (hp : p ∈ Metric.ball (parabolicPoint 0 0) 1) :
    ‖parabolicNondivergenceOperator
        (parabolicMatrixCoefficientRescale r p0 a)
        (parabolicDriftCoefficientRescale r p0 b)
        (parabolicPotentialCoefficientRescale r p0 c)
        (parabolicRescaleAt r p0 u) p‖ ≤ r ^ 2 * B := by
  rw [parabolicNondivergenceOperator_rescaleAt
    r p0 a b c u p (hspace _)]
  exact norm_parabolicSourceRescaleAt_le_of_mem_unitBall
    r hr p0 _ B hoperator p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) :
    parabolicVariableMatrixOperator a u =
      parabolicNondivergenceOperator a b c u +
        parabolicLowerOrderTerm b c u := by
  unfold parabolicNondivergenceOperator
  abel

omit [DecidableEq n] [Nonempty n] in
theorem parabolicNondivergenceOperator_congr_of_eqOn_open
    {U : Set (ParabolicPoint (Euc n))} (hU : IsOpen U)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u v : Real → Euc n → F) {p : ParabolicPoint (Euc n)} (hp : p ∈ U)
    (huv : Set.EqOn (fun q ↦ u q.time q.space)
      (fun q ↦ v q.time q.space) U) :
    parabolicNondivergenceOperator a b c u p =
      parabolicNondivergenceOperator a b c v p := by
  classical
  have hspaceMap : ContinuousAt
      (fun x ↦ parabolicPoint p.time x) p.space := by
    unfold parabolicPoint
    exact (continuous_const.prodMk continuous_id).continuousAt
  have hspace : u p.time =ᶠ[nhds p.space] v p.time := by
    filter_upwards [hspaceMap (hU.mem_nhds hp)] with x hx
    exact huv hx
  have htimeMap : ContinuousAt
      (fun t ↦ parabolicPoint t p.space) p.time := by
    unfold parabolicPoint
    exact (Metric.Snowflaking.continuous_toSnowflaking.prodMk
      continuous_const).continuousAt
  have htime : (fun t ↦ u t p.space) =ᶠ[nhds p.time]
      fun t ↦ v t p.space := by
    filter_upwards [htimeMap (hU.mem_nhds hp)] with t ht
    exact huv ht
  have hjetOne : parabolicSpatialJet 1 u p =
      parabolicSpatialJet 1 v p := by
    unfold parabolicSpatialJet
    exact (Filter.EventuallyEq.iteratedFDeriv Real hspace 1).eq_of_nhds
  have hjetTwo : parabolicSpatialJet 2 u p =
      parabolicSpatialJet 2 v p := by
    unfold parabolicSpatialJet
    exact (Filter.EventuallyEq.iteratedFDeriv Real hspace 2).eq_of_nhds
  have htimeDeriv : parabolicTimeDerivative u p =
      parabolicTimeDerivative v p := by
    unfold parabolicTimeDerivative
    exact congrArg (fun L : Real →L[Real] F ↦ L 1) htime.fderiv_eq
  have hvalue : u p.time p.space = v p.time p.space := huv hp
  unfold parabolicNondivergenceOperator parabolicVariableMatrixOperator
    parabolicVariableMatrixLap parabolicLowerOrderTerm parabolicDriftTerm
    parabolicGradientComponent parabolicPotentialTerm
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [htimeDeriv, hjetTwo]
  simp_rw [hjetOne, hvalue]

omit [DecidableEq n] [Nonempty n] in
theorem parabolicGradientComponent_norm_le
    (u : Real → Euc n → F) (i : n) (p : ParabolicPoint (Euc n)) :
    ‖parabolicGradientComponent u i p‖ ≤ ‖parabolicSpatialJet 1 u p‖ := by
  rw [parabolicGradientComponent_apply]
  calc
    ‖continuousMultilinearCurryFin1 Real (Euc n) F
        (parabolicSpatialJet 1 u p) (EuclideanSpace.basisFun n Real i)‖ ≤
        ‖continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 u p)‖ := by
      exact (continuousMultilinearCurryFin1 Real (Euc n) F
        (parabolicSpatialJet 1 u p)).le_opNorm _ |>.trans (by
          rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
            mul_one])
    _ = ‖parabolicSpatialJet 1 u p‖ :=
      (continuousMultilinearCurryFin1 Real (Euc n) F).norm_map _

omit [DecidableEq n] [Nonempty n] in
theorem parabolicGradientComponent_holderWith_restrict
    {alpha Kdu : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    {u : Real → Euc n → F}
    (hdu : HolderWith Kdu alpha
      (Q.restrict (parabolicSpatialJet 1 u))) (i : n) :
    HolderWith Kdu alpha
      (Q.restrict (parabolicGradientComponent u i)) := by
  intro p q
  rw [edist_dist, edist_dist]
  have hreal : dist (parabolicGradientComponent u i p.1)
      (parabolicGradientComponent u i q.1) ≤
        (Kdu : Real) * dist p q ^ (alpha : Real) := by
    rw [dist_eq_norm]
    change ‖continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 u p.1)
            (EuclideanSpace.basisFun n Real i) -
        continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 u q.1)
            (EuclideanSpace.basisFun n Real i)‖ ≤ _
    rw [← ContinuousLinearMap.sub_apply, ← map_sub]
    calc
      ‖continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 u p.1 - parabolicSpatialJet 1 u q.1)
            (EuclideanSpace.basisFun n Real i)‖ ≤
          ‖continuousMultilinearCurryFin1 Real (Euc n) F
            (parabolicSpatialJet 1 u p.1 -
              parabolicSpatialJet 1 u q.1)‖ := by
        exact (continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 u p.1 -
            parabolicSpatialJet 1 u q.1)).le_opNorm _ |>.trans (by
              rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
                mul_one])
      _ = ‖parabolicSpatialJet 1 u p.1 -
          parabolicSpatialJet 1 u q.1‖ :=
        (continuousMultilinearCurryFin1 Real (Euc n) F).norm_map _
      _ = dist (parabolicSpatialJet 1 u p.1)
          (parabolicSpatialJet 1 u q.1) := (dist_eq_norm _ _).symm
      _ ≤ (Kdu : Real) * dist p q ^ (alpha : Real) := hdu.dist_le p q
  exact ENNReal.ofReal_le_ofReal hreal |>.trans_eq (by
    rw [ENNReal.ofReal_mul Kdu.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg alpha.coe_nonneg])

def parabolicLowerOrderSupConst
    (Bb : n → NNReal) (Bc Mdu Mu : NNReal) : NNReal :=
  (∑ i, Bb i * Mdu) + Bc * Mu

def parabolicLowerOrderHolderConst
    (Kb Bb : n → NNReal) (Kc Kdu Ku Mdu Bc Mu : NNReal) : NNReal :=
  (∑ i, (Bb i * Kdu + Mdu * Kb i)) + (Bc * Ku + Mu * Kc)

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicLowerOrderSupConst_add
    (Bb : n → NNReal) (Bc Mdu₁ Mdu₂ Mu₁ Mu₂ : NNReal) :
    parabolicLowerOrderSupConst Bb Bc (Mdu₁ + Mdu₂) (Mu₁ + Mu₂) =
      parabolicLowerOrderSupConst Bb Bc Mdu₁ Mu₁ +
        parabolicLowerOrderSupConst Bb Bc Mdu₂ Mu₂ := by
  unfold parabolicLowerOrderSupConst
  simp only [mul_add, Finset.sum_add_distrib]
  ring

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicLowerOrderSupConst_nnreal_mul
    (d : NNReal) (Bb : n → NNReal) (Bc Mdu Mu : NNReal) :
    parabolicLowerOrderSupConst Bb Bc (d * Mdu) (d * Mu) =
      d * parabolicLowerOrderSupConst Bb Bc Mdu Mu := by
  unfold parabolicLowerOrderSupConst
  rw [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    ring
  · ring

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicLowerOrderHolderConst_add
    (Kb Bb : n → NNReal) (Kc Bc : NNReal)
    (Kdu₁ Kdu₂ Ku₁ Ku₂ Mdu₁ Mdu₂ Mu₁ Mu₂ : NNReal) :
    parabolicLowerOrderHolderConst Kb Bb Kc
        (Kdu₁ + Kdu₂) (Ku₁ + Ku₂) (Mdu₁ + Mdu₂) Bc (Mu₁ + Mu₂) =
      parabolicLowerOrderHolderConst Kb Bb Kc Kdu₁ Ku₁ Mdu₁ Bc Mu₁ +
        parabolicLowerOrderHolderConst Kb Bb Kc Kdu₂ Ku₂ Mdu₂ Bc Mu₂ := by
  unfold parabolicLowerOrderHolderConst
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  ring

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem parabolicLowerOrderHolderConst_nnreal_mul
    (d : NNReal) (Kb Bb : n → NNReal)
    (Kc Bc Kdu Ku Mdu Mu : NNReal) :
    parabolicLowerOrderHolderConst Kb Bb Kc
        (d * Kdu) (d * Ku) (d * Mdu) Bc (d * Mu) =
      d * parabolicLowerOrderHolderConst Kb Bb Kc Kdu Ku Mdu Bc Mu := by
  unfold parabolicLowerOrderHolderConst
  rw [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    ring
  · ring

def parabolicLowerOrderInterpolationSupConst
    (Bb : n → NNReal) (Bc epsilon C M : NNReal) : NNReal :=
  parabolicLowerOrderSupConst Bb Bc (2 * M / epsilon + C * epsilon) M

def parabolicLowerOrderInterpolationHolderConst
    (Kb Bb : n → NNReal)
    (Kc Bc epsilon alpha C M : NNReal) : NNReal :=
  parabolicLowerOrderHolderConst Kb Bb Kc
    (parabolicSpatialGradientInterpolationConst epsilon alpha C M)
    (parabolicValueInterpolationConst epsilon alpha C M)
    (2 * M / epsilon + C * epsilon) Bc M

def bufferedParabolicLowerOrderInterpolationSupConst
    (Bb : n → NNReal) (Bc epsilon C M : NNReal) : NNReal :=
  parabolicLowerOrderSupConst Bb Bc (2 * M / epsilon + C * epsilon) M

def bufferedParabolicLowerOrderInterpolationHolderConst
    (Kb Bb : n → NNReal)
    (Kc Bc epsilon delta alpha C M : NNReal) : NNReal :=
  parabolicLowerOrderHolderConst Kb Bb Kc
    (bufferedParabolicSpatialGradientInterpolationConst
      epsilon delta alpha C M)
    (parabolicValueInterpolationConst epsilon alpha C M)
    (2 * M / epsilon + C * epsilon) Bc M

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem bufferedParabolicLowerOrderInterpolationSupConst_add
    (Bb : n → NNReal) (Bc epsilon C₁ C₂ M₁ M₂ : NNReal) :
    bufferedParabolicLowerOrderInterpolationSupConst Bb Bc epsilon
        (C₁ + C₂) (M₁ + M₂) =
      bufferedParabolicLowerOrderInterpolationSupConst Bb Bc epsilon C₁ M₁ +
        bufferedParabolicLowerOrderInterpolationSupConst Bb Bc epsilon C₂ M₂ := by
  unfold bufferedParabolicLowerOrderInterpolationSupConst
  rw [show 2 * (M₁ + M₂) / epsilon + (C₁ + C₂) * epsilon =
      (2 * M₁ / epsilon + C₁ * epsilon) +
        (2 * M₂ / epsilon + C₂ * epsilon) by ring]
  exact parabolicLowerOrderSupConst_add Bb Bc _ _ _ _

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem bufferedParabolicLowerOrderInterpolationSupConst_nnreal_mul
    (d : NNReal) (Bb : n → NNReal) (Bc epsilon C M : NNReal) :
    bufferedParabolicLowerOrderInterpolationSupConst Bb Bc epsilon
        (d * C) (d * M) =
      d * bufferedParabolicLowerOrderInterpolationSupConst Bb Bc epsilon C M := by
  unfold bufferedParabolicLowerOrderInterpolationSupConst
  rw [show 2 * (d * M) / epsilon + d * C * epsilon =
      d * (2 * M / epsilon + C * epsilon) by ring]
  exact parabolicLowerOrderSupConst_nnreal_mul d Bb Bc _ _

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem bufferedParabolicLowerOrderInterpolationHolderConst_add
    (Kb Bb : n → NNReal)
    (Kc Bc epsilon delta alpha C₁ C₂ M₁ M₂ : NNReal) :
    bufferedParabolicLowerOrderInterpolationHolderConst Kb Bb Kc Bc
        epsilon delta alpha (C₁ + C₂) (M₁ + M₂) =
      bufferedParabolicLowerOrderInterpolationHolderConst Kb Bb Kc Bc
          epsilon delta alpha C₁ M₁ +
        bufferedParabolicLowerOrderInterpolationHolderConst Kb Bb Kc Bc
          epsilon delta alpha C₂ M₂ := by
  unfold bufferedParabolicLowerOrderInterpolationHolderConst
  rw [bufferedParabolicSpatialGradientInterpolationConst_add]
  rw [parabolicValueInterpolationConst_add]
  rw [show 2 * (M₁ + M₂) / epsilon + (C₁ + C₂) * epsilon =
      (2 * M₁ / epsilon + C₁ * epsilon) +
        (2 * M₂ / epsilon + C₂ * epsilon) by ring]
  exact parabolicLowerOrderHolderConst_add Kb Bb Kc Bc _ _ _ _ _ _ _ _

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] in
theorem bufferedParabolicLowerOrderInterpolationHolderConst_nnreal_mul
    (d : NNReal) (Kb Bb : n → NNReal)
    (Kc Bc epsilon delta alpha C M : NNReal) :
    bufferedParabolicLowerOrderInterpolationHolderConst Kb Bb Kc Bc
        epsilon delta alpha (d * C) (d * M) =
      d * bufferedParabolicLowerOrderInterpolationHolderConst Kb Bb Kc Bc
        epsilon delta alpha C M := by
  unfold bufferedParabolicLowerOrderInterpolationHolderConst
  rw [bufferedParabolicSpatialGradientInterpolationConst_nnreal_mul]
  rw [parabolicValueInterpolationConst_nnreal_mul]
  rw [show 2 * (d * M) / epsilon + d * C * epsilon =
      d * (2 * M / epsilon + C * epsilon) by ring]
  exact parabolicLowerOrderHolderConst_nnreal_mul d Kb Bb Kc Bc _ _ _ _

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicDriftTerm_le
    {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Bb : n → NNReal) (Mdu : NNReal)
    (hb : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hdu : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ Mdu)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicDriftTerm b u p‖ ≤ ∑ i, Bb i * Mdu := by
  unfold parabolicDriftTerm
  calc
    ‖∑ i, b i p • parabolicGradientComponent u i p‖ ≤
        ∑ i, ‖b i p • parabolicGradientComponent u i p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, (Bb i : Real) * Mdu := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hb i p hp)
        ((parabolicGradientComponent_norm_le u i p).trans (hdu p hp))
        (norm_nonneg _) (by positivity)
    _ = (∑ i, Bb i * Mdu : NNReal) := by push_cast; rfl

omit [DecidableEq n] [Nonempty n] in
theorem parabolicDriftTerm_holderWith_restrict
    {alpha Kdu : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Kb Bb : n → NNReal) (Mdu : NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (Q.restrict (b i)))
    (hbNorm : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hdu : HolderWith Kdu alpha
      (Q.restrict (parabolicSpatialJet 1 u)))
    (hduNorm : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ Mdu) :
    HolderWith (∑ i, (Bb i * Kdu + Mdu * Kb i)) alpha
      (Q.restrict (parabolicDriftTerm b u)) := by
  have hcomponent : ∀ i,
      HolderWith (Bb i * Kdu + Mdu * Kb i) alpha
        (fun p : Q ↦ b i p.1 • parabolicGradientComponent u i p.1) := by
    intro i
    apply holderWith_smul_of_norm_le (hb i)
      (parabolicGradientComponent_holderWith_restrict hdu i)
    · exact fun p ↦ hbNorm i p.1 p.2
    · intro p
      exact (parabolicGradientComponent_norm_le u i p.1).trans
        (hduNorm p.1 p.2)
  have hsum := holderWith_finset_sum (Finset.univ : Finset n)
    (K := fun i ↦ Bb i * Kdu + Mdu * Kb i)
    (f := fun i (p : Q) ↦ b i p.1 • parabolicGradientComponent u i p.1)
    (fun i _hi ↦ hcomponent i)
  simpa only [parabolicDriftTerm, Set.restrict_apply] using hsum

omit [Fintype n] [DecidableEq n] [Nonempty n] in
theorem norm_parabolicPotentialTerm_le
    {Q : Set (ParabolicPoint (Euc n))}
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Bc Mu : NNReal)
    (hc : ∀ p, p ∈ Q → ‖c p‖ ≤ Bc)
    (hu : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicPotentialTerm c u p‖ ≤ Bc * Mu := by
  rw [parabolicPotentialTerm_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hc p hp)
    (hu p hp) (norm_nonneg _) (by positivity)

omit [DecidableEq n] [Nonempty n] in
theorem parabolicPotentialTerm_holderWith_restrict
    {alpha Kc Ku Bc Mu : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (hc : HolderWith Kc alpha (Q.restrict c))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (hcNorm : ∀ p, p ∈ Q → ‖c p‖ ≤ Bc)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith (Bc * Ku + Mu * Kc) alpha
      (Q.restrict (parabolicPotentialTerm c u)) := by
  simpa only [Set.restrict_apply, parabolicPotentialTerm_apply] using
    holderWith_smul_of_norm_le hc hu
      (fun p ↦ hcNorm p.1 p.2) (fun p ↦ huNorm p.1 p.2)

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicLowerOrderTerm_le
    {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Bb : n → NNReal) (Bc Mdu Mu : NNReal)
    (hb : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hc : ∀ p, p ∈ Q → ‖c p‖ ≤ Bc)
    (hdu : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ Mdu)
    (hu : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n)) (hp : p ∈ Q) :
    ‖parabolicLowerOrderTerm b c u p‖ ≤
      parabolicLowerOrderSupConst Bb Bc Mdu Mu := by
  rw [parabolicLowerOrderTerm_apply, parabolicLowerOrderSupConst,
    NNReal.coe_add]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_parabolicDriftTerm_le b u Bb Mdu hb hdu p hp)
    (norm_parabolicPotentialTerm_le c u Bc Mu hc hu p hp))

omit [DecidableEq n] [Nonempty n] in
theorem eSupNormOn_parabolicLowerOrderTerm_le
    {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Bb : n → NNReal) (Bc Mdu Mu : NNReal)
    (hb : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hc : ∀ p, p ∈ Q → ‖c p‖ ≤ Bc)
    (hdu : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ Mdu)
    (hu : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    eSupNormOn Q (parabolicLowerOrderTerm b c u) ≤
      parabolicLowerOrderSupConst Bb Bc Mdu Mu := by
  rw [eSupNormOn_le]
  intro p hp
  rw [ENNReal.ofReal_le_coe]
  exact norm_parabolicLowerOrderTerm_le b c u Bb Bc Mdu Mu
    hb hc hdu hu p hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicLowerOrderTerm_holderWith_restrict
    {alpha Kc Kdu Ku : NNReal} {Q : Set (ParabolicPoint (Euc n))}
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Kb Bb : n → NNReal) (Mdu Bc Mu : NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (Q.restrict (b i)))
    (hc : HolderWith Kc alpha (Q.restrict c))
    (hdu : HolderWith Kdu alpha
      (Q.restrict (parabolicSpatialJet 1 u)))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (hbNorm : ∀ i p, p ∈ Q → ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p, p ∈ Q → ‖c p‖ ≤ Bc)
    (hduNorm : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ Mdu)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith (parabolicLowerOrderHolderConst
      Kb Bb Kc Kdu Ku Mdu Bc Mu) alpha
      (Q.restrict (parabolicLowerOrderTerm b c u)) := by
  exact (parabolicDriftTerm_holderWith_restrict
    b u Kb Bb Mdu hb hbNorm hdu hduNorm).add
    (parabolicPotentialTerm_holderWith_restrict
      c u hc hu hcNorm huNorm)

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicLowerOrderTerm_le_of_interpolation
    {J : Set Real} (epsilon : NNReal) (hepsilon : 0 < epsilon)
    {alpha C M : NNReal}
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Bb : n → NNReal) (Bc : NNReal)
    (hu : IsParabolicC2On
      (parabolicCylinder J Set.univ) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) u ≤ C)
    (huNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖u p.time p.space‖ ≤ M)
    (hbNorm : ∀ i p, p ∈ parabolicCylinder J Set.univ →
      ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖c p‖ ≤ Bc)
    (p : ParabolicPoint (Euc n))
    (hp : p ∈ parabolicCylinder J Set.univ) :
    ‖parabolicLowerOrderTerm b c u p‖ ≤
      parabolicLowerOrderInterpolationSupConst Bb Bc epsilon C M := by
  apply norm_parabolicLowerOrderTerm_le b c u Bb Bc
    (2 * M / epsilon + C * epsilon) M hbNorm hcNorm
  · intro q hq
    exact norm_parabolicSpatialJet_one_le_of_interpolation
      epsilon hepsilon hu hgauge huNorm q hq
  · exact huNorm
  · exact hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicLowerOrderTerm_holderWith_restrict_of_interpolation
    {J : Set Real} (hJ : Convex Real J)
    (epsilon : NNReal) (hepsilon : 0 < epsilon)
    {alpha C M : NNReal} (halpha : alpha ≤ 1)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Kb Bb : n → NNReal) (Kc Bc : NNReal)
    (hu : IsParabolicC2On
      (parabolicCylinder J Set.univ) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) u ≤ C)
    (huNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖u p.time p.space‖ ≤ M)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder J Set.univ).restrict (b i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder J Set.univ).restrict c))
    (hbNorm : ∀ i p, p ∈ parabolicCylinder J Set.univ →
      ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖c p‖ ≤ Bc) :
    HolderWith
      (parabolicLowerOrderInterpolationHolderConst
        Kb Bb Kc Bc epsilon alpha C M) alpha
      ((parabolicCylinder J Set.univ).restrict
        (parabolicLowerOrderTerm b c u)) := by
  apply parabolicLowerOrderTerm_holderWith_restrict
    b c u Kb Bb (2 * M / epsilon + C * epsilon) Bc M hb hc
  · exact parabolicSpatialJet_one_holderWith_restrict_of_interpolation
      hJ epsilon hepsilon halpha hu hgauge huNorm
  · exact parabolicValue_holderWith_restrict_of_interpolation
      hJ convex_univ epsilon hepsilon halpha hu hgauge huNorm
  · exact hbNorm
  · exact hcNorm
  · intro p hp
    exact norm_parabolicSpatialJet_one_le_of_interpolation
      epsilon hepsilon hu hgauge huNorm p hp
  · exact huNorm

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicLowerOrderTerm_le_of_buffered_ball_interpolation
    {J : Set Real} (center : Euc n) {r R : Real} (epsilon : NNReal)
    (hepsilon : 0 < epsilon) (hbuffer : r + epsilon < R)
    {alpha C M : NNReal}
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Bb : n → NNReal) (Bc : NNReal)
    (hu : IsParabolicC2On
      (parabolicCylinder J (Metric.ball center R)) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J (Metric.ball center R)) u ≤ C)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder J (Metric.ball center R) →
        ‖u p.time p.space‖ ≤ M)
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder J (Metric.closedBall center r) →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder J (Metric.closedBall center r) →
        ‖c p‖ ≤ Bc)
    (p : ParabolicPoint (Euc n))
    (hp : p ∈ parabolicCylinder J (Metric.closedBall center r)) :
    ‖parabolicLowerOrderTerm b c u p‖ ≤
      bufferedParabolicLowerOrderInterpolationSupConst
        Bb Bc epsilon C M := by
  have hsubset :
      parabolicCylinder J (Metric.closedBall center r) ⊆
        parabolicCylinder J (Metric.ball center R) := by
    intro q hq
    exact ⟨hq.1, (Metric.mem_closedBall.mp hq.2).trans_lt
      ((lt_add_of_pos_right r (by exact_mod_cast hepsilon)).trans hbuffer)⟩
  apply norm_parabolicLowerOrderTerm_le b c u Bb Bc
    (2 * M / epsilon + C * epsilon) M hbNorm hcNorm
  · intro q hq
    exact norm_parabolicSpatialJet_one_le_of_buffered_ball
      center epsilon hepsilon hbuffer hu hgauge huNorm q hq
  · exact fun q hq ↦ huNorm q (hsubset hq)
  · exact hp

omit [DecidableEq n] [Nonempty n] in
theorem parabolicLowerOrderTerm_holderWith_restrict_of_buffered_ball_interpolation
    {J : Set Real} (hJ : Convex Real J)
    (center : Euc n) {r R : Real} (epsilon delta : NNReal)
    (hepsilon : 0 < epsilon) (hepsilonDelta : epsilon < delta)
    (hbuffer : r + delta ≤ R)
    {alpha C M : NNReal} (halpha : alpha ≤ 1)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (Kb Bb : n → NNReal) (Kc Bc : NNReal)
    (hu : IsParabolicC2On
      (parabolicCylinder J (Metric.ball center R)) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J (Metric.ball center R)) u ≤ C)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder J (Metric.ball center R) →
        ‖u p.time p.space‖ ≤ M)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder J (Metric.closedBall center r)).restrict (b i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder J (Metric.closedBall center r)).restrict c))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder J (Metric.closedBall center r) →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder J (Metric.closedBall center r) →
        ‖c p‖ ≤ Bc) :
    HolderWith
      (bufferedParabolicLowerOrderInterpolationHolderConst
        Kb Bb Kc Bc epsilon delta alpha C M) alpha
      ((parabolicCylinder J (Metric.closedBall center r)).restrict
        (parabolicLowerOrderTerm b c u)) := by
  have hdelta : 0 < delta := hepsilon.trans hepsilonDelta
  have hrR : r < R := by
    calc
      r < r + (delta : Real) :=
        lt_add_of_pos_right r (by exact_mod_cast hdelta)
      _ ≤ R := hbuffer
  have hsubset :
      parabolicCylinder J (Metric.closedBall center r) ⊆
        parabolicCylinder J (Metric.ball center R) := by
    intro p hp
    exact ⟨hp.1, (Metric.mem_closedBall.mp hp.2).trans_lt hrR⟩
  have huInner : IsParabolicC2On
      (parabolicCylinder J (Metric.closedBall center r)) u :=
    ⟨fun p hp ↦ hu.1 p (hsubset hp), fun p hp ↦ hu.2 p (hsubset hp)⟩
  have hgaugeInner : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J (Metric.closedBall center r)) u ≤ C :=
    (eParabolicC2HolderGaugeOn_mono hsubset alpha u).trans hgauge
  have huNormInner : ∀ p,
      p ∈ parabolicCylinder J (Metric.closedBall center r) →
        ‖u p.time p.space‖ ≤ M :=
    fun p hp ↦ huNorm p (hsubset hp)
  apply parabolicLowerOrderTerm_holderWith_restrict
    b c u Kb Bb (2 * M / epsilon + C * epsilon) Bc M hb hc
  · exact
      parabolicSpatialJet_one_holderWith_restrict_of_buffered_ball_interpolation
      hJ center epsilon delta hepsilon hepsilonDelta hbuffer
        halpha hu hgauge huNorm
  · exact parabolicValue_holderWith_restrict_of_interpolation
      hJ (convex_closedBall center r) epsilon hepsilon halpha
        huInner hgaugeInner huNormInner
  · exact hbNorm
  · exact hcNorm
  · intro p hp
    exact norm_parabolicSpatialJet_one_le_of_buffered_ball
      center epsilon hepsilon (by
        calc
          r + (epsilon : Real) < r + (delta : Real) := by gcongr
          _ ≤ R := hbuffer)
      hu hgauge huNorm p hp
  · exact huNormInner

section Schauder

variable [CompleteSpace F]

theorem parabolic_variable_coefficient_schauder_estimate_of_lower_order_source
    {alpha KL BL Klo Blo X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (g : Real → BoundedContinuousFunction (Euc n) F)
    (hrep : u = fun t x ↦
      spdHeatDuh (fun i j ↦ a i j p0) hA t g x)
    (hgfrozen : Set.EqOn (fun p ↦ g p.time p.space)
      (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u)
      (parabolicCylinder (Icc (0 : Real) S) Set.univ))
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicNondivergenceOperator a b c u) ≤ BL)
    (hsourceHolder : HolderWith KL alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicNondivergenceOperator a b c u)))
    (hloBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicLowerOrderTerm b c u) ≤ Blo)
    (hloHolder : HolderWith Klo alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicLowerOrderTerm b c u)))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ) u ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        ((KL + Klo) + X * parabolicMatrixFreezeHolderConst Ka omega)
        ((BL + Blo) + X * parabolicMatrixFreezeSupConst omega) T := by
  let Q : Set (ParabolicPoint (Euc n)) :=
    parabolicCylinder (Icc (0 : Real) S) Set.univ
  have hprincipalBound : eSupNormOn Q
      (parabolicVariableMatrixOperator a u) ≤ BL + Blo := by
    rw [parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm]
    exact (eSupNormOn_add_le Q
      (parabolicNondivergenceOperator a b c u)
      (parabolicLowerOrderTerm b c u)).trans
        (add_le_add hsourceBound hloBound)
  have hprincipalHolder : HolderWith (KL + Klo) alpha
      (Q.restrict (parabolicVariableMatrixOperator a u)) := by
    rw [parabolicVariableMatrixOperator_eq_nondivergenceOperator_add_lowerOrderTerm]
    exact hsourceHolder.add hloHolder
  exact parabolic_variable_coefficient_schauder_estimate_of_frozen_representation
    halpha0 halpha1 hT hTS a p0 hA u g hrep hgfrozen
    hprincipalBound hprincipalHolder Ka omega ha homega hu

theorem parabolic_nondivergence_schauder_estimate_of_frozen_representation
    {alpha KL BL Kc Kdu Ku Bc X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (g : Real → BoundedContinuousFunction (Euc n) F)
    (hrep : u = fun t x ↦
      spdHeatDuh (fun i j ↦ a i j p0) hA t g x)
    (hgfrozen : Set.EqOn (fun p ↦ g p.time p.space)
      (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u)
      (parabolicCylinder (Icc (0 : Real) S) Set.univ))
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicNondivergenceOperator a b c u) ≤ BL)
    (hsourceHolder : HolderWith KL alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicNondivergenceOperator a b c u)))
    (Kb Bb : n → NNReal) (Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (b i)))
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict c))
    (hdu : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicSpatialJet 1 u)))
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ → ‖c p‖ ≤ Bc)
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ) u ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        ((KL + parabolicLowerOrderHolderConst
          Kb Bb Kc Kdu Ku X Bc X) +
            X * parabolicMatrixFreezeHolderConst Ka omega)
        ((BL + parabolicLowerOrderSupConst Bb Bc X X) +
          X * parabolicMatrixFreezeSupConst omega) T := by
  let Q : Set (ParabolicPoint (Euc n)) :=
    parabolicCylinder (Icc (0 : Real) S) Set.univ
  have hduNorm : ∀ p, p ∈ Q → ‖parabolicSpatialJet 1 u p‖ ≤ X :=
    fun p hp ↦ parabolicSpatialJet_norm_le hu (by omega) hp
  have huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ X := by
    intro p hp
    have hzero := parabolicSpatialJet_norm_le hu (j := 0) (by omega) hp
    simpa only [parabolicSpatialJet, norm_iteratedFDeriv_zero] using hzero
  exact parabolic_variable_coefficient_schauder_estimate_of_lower_order_source
    (Klo := parabolicLowerOrderHolderConst Kb Bb Kc Kdu Ku X Bc X)
    (Blo := parabolicLowerOrderSupConst Bb Bc X X)
    halpha0 halpha1 hT hTS a p0 hA b c u g hrep hgfrozen
    hsourceBound hsourceHolder
    (eSupNormOn_parabolicLowerOrderTerm_le b c u Bb Bc X X
      hbNorm hcNorm hduNorm huNorm)
    (parabolicLowerOrderTerm_holderWith_restrict
      b c u Kb Bb X Bc X hb hc hdu huHolder
      hbNorm hcNorm hduNorm huNorm)
    Ka omega ha homega hu

theorem parabolic_nondivergence_schauder_estimate_of_small_freeze_defect
    {alpha KL BL Kc Kdu Ku Bc X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (g : Real → BoundedContinuousFunction (Euc n) F)
    (hrep : u = fun t x ↦
      spdHeatDuh (fun i j ↦ a i j p0) hA t g x)
    (hgfrozen : Set.EqOn (fun p ↦ g p.time p.space)
      (parabolicFrozenMatrixOperator (fun i j ↦ a i j p0) u)
      (parabolicCylinder (Icc (0 : Real) S) Set.univ))
    (hsourceBound : eSupNormOn
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (parabolicNondivergenceOperator a b c u) ≤ BL)
    (hsourceHolder : HolderWith KL alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicNondivergenceOperator a b c u)))
    (Kb Bb : n → NNReal) (Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (b i)))
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict c))
    (hdu : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicSpatialJet 1 u)))
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖b i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ → ‖c p‖ ≤ Bc)
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hu : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ) u ≤ X)
    (hX : (X : ENNReal) ≤ eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      (spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        (KL + parabolicLowerOrderHolderConst
          Kb Bb Kc Kdu Ku X Bc X)
        (BL + parabolicLowerOrderSupConst Bb Bc X X) T /
        (1 - spdParabolicSchauderDefectConst
          (fun i j ↦ a i j p0) hA alpha Ka omega T) : NNReal) := by
  have hraw := parabolic_nondivergence_schauder_estimate_of_frozen_representation
    halpha0 halpha1 hT hTS a p0 hA b c u g hrep hgfrozen
    hsourceBound hsourceHolder Kb Bb Ka omega hb ha hc hdu huHolder
    hbNorm hcNorm homega hu
  exact parabolic_schauder_estimate_of_small_freeze_defect
    halpha1 hT (fun i j ↦ a i j p0) hA Ka omega u hraw hX hsmall

end Schauder

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
