import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakLimit
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakFTC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

def IsWeakEvolutionSolution
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (Bx Bv : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q))
    (u : timeL2 (H1ComplDirichlet q) T) : Prop :=
  ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞,
    ∃ hCg : 1 ≤ Cg,
    ∃ hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v,
    ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
    ∃ hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q,
    ∀ v : H1ComplDirichlet q,
      ∃ w : timeH1 ℝ T,
        w.init = dirichletMassLp (G.metric 0) Cv hCvtop
          (hvol 0 ⟨le_rfl, hT⟩) f₀ (H1ComplDirichletToLp q v) ∧
        (fun t ↦ dirichletMassComplOnIcc G.metric hCg hequiv
            Cv hCv0 hCvtop hvol t (u t) v) =ᵐ[timeMeasure T] w.toFun ∧
        w.deriv =ᵐ[timeMeasure T]
          fun t ↦ dirichletMassVariationComplOnIco hG hreg Bv htrace
              hCg hequiv Cv hCv0 hCvtop hvol t (u t) v +
            dirichletWeakFormComplOnIco G.metric X a Bx hX
              hCg hequiv Cv hCv0 hCvtop hvol t (u t) v

private theorem bilinear_apply_memLp
    {Y Z : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} (u : timeL2 Y T)
    (B : ℝ → Y →L[ℝ] Z →L[ℝ] ℝ)
    (hB : ∀ y z, AEStronglyMeasurable (fun t ↦ B t y z) (timeMeasure T))
    {C : ℝ} (hC : ∀ᵐ t ∂(timeMeasure T), ‖B t‖ ≤ C)
    (z : Z) :
    MemLp (fun t ↦ B t (u t) z) 2 (timeMeasure T) := by
  let F : ℝ → Y →L[ℝ] ℝ := fun t ↦ (B t).flip z
  have hF : ∀ y, AEStronglyMeasurable (fun t ↦ F t y) (timeMeasure T) := by
    intro y
    simpa only [F, ContinuousLinearMap.flip_apply] using hB y z
  let R : ℝ → Y := fun t ↦ (InnerProductSpace.toDual ℝ Y).symm (F t)
  have hR : AEStronglyMeasurable R (timeMeasure T) :=
    dualRepresentative_aestronglyMeasurable_of_apply_aestronglyMeasurable F hF
  have hmeas : AEStronglyMeasurable (fun t ↦ B t (u t) z)
      (timeMeasure T) := by
    refine ((Lp.aestronglyMeasurable u).inner hR).congr
      (Eventually.of_forall fun t ↦ ?_)
    change inner ℝ (u t) (R t) = B t (u t) z
    rw [real_inner_comm]
    change inner ℝ ((InnerProductSpace.toDual ℝ Y).symm (F t)) (u t) =
      F t (u t)
    exact InnerProductSpace.toDual_symm_apply
  let K : ℝ := max 0 C * ‖z‖
  have hmajor : MemLp (fun t ↦ K * ‖u t‖) 2 (timeMeasure T) :=
    (Lp.memLp u).norm.const_mul K
  apply MemLp.mono hmajor hmeas
  filter_upwards [hC] with t hBt
  have hK : 0 ≤ K := mul_nonneg (le_max_left 0 C) (norm_nonneg z)
  change |B t (u t) z| ≤ |K * ‖u t‖|
  rw [abs_of_nonneg (mul_nonneg hK (norm_nonneg _))]
  calc
    |B t (u t) z| = ‖B t (u t) z‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖B t‖ * (‖u t‖ * ‖z‖) := by
      calc
        ‖B t (u t) z‖ ≤ ‖B t (u t)‖ * ‖z‖ := (B t (u t)).le_opNorm z
        _ ≤ (‖B t‖ * ‖u t‖) * ‖z‖ := by
          gcongr
          exact (B t).le_opNorm (u t)
        _ = ‖B t‖ * (‖u t‖ * ‖z‖) := by ring
    _ ≤ K * ‖u t‖ := by
      dsimp only [K]
      calc
        ‖B t‖ * (‖u t‖ * ‖z‖) = (‖B t‖ * ‖z‖) * ‖u t‖ := by ring
        _ ≤ (max 0 C * ‖z‖) * ‖u t‖ := by
          gcongr
          exact hBt.trans (le_max_right 0 C)

theorem IsWeakEvolutionSolution.exists_mass_timeH1
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u) :
    ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞,
      ∃ hCg : 1 ≤ Cg,
      ∃ hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        ∀ v : TangentSpace (I_half n) x,
          Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
            (G.metric t).inner x v v ≤ Cg * q.inner x v v,
      ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
      ∃ hvol : ∀ t ∈ Icc (0 : ℝ) T,
        riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
          Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q,
      ∃ w : timeH1 (H1ComplDirichlet q) T,
        w.init = (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
          ((dirichletMassLp (G.metric 0) Cv hCvtop
            (hvol 0 ⟨le_rfl, hT⟩) f₀).comp (H1ComplDirichletToLp q)) ∧
        (fun t ↦ (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
          (dirichletMassComplOnIcc G.metric hCg hequiv
            Cv hCv0 hCvtop hvol t (u t))) =ᵐ[timeMeasure T] w.toFun ∧
        w.deriv =ᵐ[timeMeasure T] fun t ↦
          (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
            (dirichletMassVariationComplOnIco hG hreg Bv htrace
                hCg hequiv Cv hCv0 hCvtop hvol t (u t) +
              dirichletWeakFormComplOnIco G.metric X a Bx hX
                hCg hequiv Cv hCv0 hCvtop hvol t (u t)) := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, hscalar⟩ := hu
  let massForm := dirichletMassComplOnIcc G.metric hCg hequiv
    Cv hCv0 hCvtop hvol
  let variationForm := dirichletMassVariationComplOnIco hG hreg Bv htrace
    hCg hequiv Cv hCv0 hCvtop hvol
  let weakForm := dirichletWeakFormComplOnIco G.metric X a Bx hX
    hCg hequiv Cv hCv0 hCvtop hvol
  let sourceForm : ℝ → H1ComplDirichlet q →L[ℝ]
      H1ComplDirichlet q →L[ℝ] ℝ := fun t ↦ variationForm t + weakForm t
  let initialForm : H1ComplDirichlet q →L[ℝ] ℝ :=
    (dirichletMassLp (G.metric 0) Cv hCvtop
      (hvol 0 ⟨le_rfl, hT⟩) f₀).comp (H1ComplDirichletToLp q)
  let initial : H1ComplDirichlet q :=
    (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm initialForm
  let mass : ℝ → H1ComplDirichlet q := fun t ↦
    (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm (massForm t (u t))
  let source : ℝ → H1ComplDirichlet q := fun t ↦
    (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm (sourceForm t (u t))
  have hvariationMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ variationForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletMassVariationComplOnIco_aestronglyMeasurable hG hreg
      Bv htrace hCg hequiv Cv hCv0 hCvtop hvol y z
  have hweakMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ weakForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletWeakFormComplOnIco_aestronglyMeasurable hG hreg X
      hXcont a hacont Bx hX hCg hequiv Cv hCv0 hCvtop hvol y z
  obtain ⟨A, hAbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hacont
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hA : 0 ≤ A := (norm_nonneg (a 0)).trans (hAbound 0 hzero)
  have haBound : ∀ t ∈ Ico (0 : ℝ) T, |a t| ≤ A := by
    intro t ht
    rw [← Real.norm_eq_abs]
    exact hAbound t ⟨ht.1, ht.2.le⟩
  have hvariationBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletMassVariationComplOnIco_le
        hG hreg Bv htrace hCg hequiv Cv hCv0 hCvtop hvol t
  have hweakBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletWeakFormComplOnIco_le
        G.metric X a A Bx hA haBound hX hCg hequiv
        Cv hCv0 hCvtop hvol t
  have hvariationLp : MemLp (fun t ↦
      (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
        (variationForm t (u t))) 2 (timeMeasure T) :=
    bilinear_left_representative_memLp u variationForm
      hvariationMeas hvariationBound
  have hweakLp : MemLp (fun t ↦
      (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
        (weakForm t (u t))) 2 (timeMeasure T) :=
    bilinear_left_representative_memLp u weakForm hweakMeas hweakBound
  have hsourceLp : MemLp source 2 (timeMeasure T) := by
    have hadd : MemLp
        ((fun t ↦ (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
            (variationForm t (u t))) +
          fun t ↦ (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm
            (weakForm t (u t))) 2 (timeMeasure T) :=
      hvariationLp.add hweakLp
    apply hadd.ae_eq
    filter_upwards [] with t
    simp only [Pi.add_apply, source, sourceForm, add_apply]
    exact (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).symm.map_add _ _ |>.symm
  obtain ⟨w, hwinit, hwmass, hwsource⟩ :=
    exists_timeH1_of_scalar_representatives hsourceLp initial (by
      intro x
      obtain ⟨v, hvinit, hvrep, hvderiv⟩ := hscalar x
      refine ⟨v, ?_, ?_, ?_⟩
      · rw [hvinit]
        change initialForm x = inner ℝ x initial
        rw [real_inner_comm]
        exact (InnerProductSpace.toDual_symm_apply
          (x := x) (y := initialForm)).symm
      · filter_upwards [hvrep] with t ht
        change inner ℝ x (mass t) = v.toFun t
        rw [real_inner_comm]
        exact (InnerProductSpace.toDual_symm_apply
          (x := x) (y := massForm t (u t))).trans ht
      · filter_upwards [hvderiv] with t ht
        change v.deriv t = inner ℝ x (source t)
        rw [real_inner_comm]
        exact ht.trans (InnerProductSpace.toDual_symm_apply
          (x := x) (y := sourceForm t (u t))).symm)
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, w, ?_, ?_, ?_⟩
  · simpa only [initial, initialForm] using hwinit
  · simpa only [mass, massForm] using hwmass
  · filter_upwards [hwsource] with t ht
    simpa only [source, sourceForm, variationForm, weakForm,
      add_apply] using ht

theorem IsIntegratedWeakSolution.isWeakEvolutionSolution
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric}
    {T : ℝ} (hT : 0 < T) {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsIntegratedWeakSolution hG hT.le hreg X a Bx Bv
      hX htrace f₀ u) :
    IsWeakEvolutionSolution hG hT.le hreg X a Bx Bv
      hX htrace f₀ u := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, hid⟩ := hu
  obtain ⟨A, hAbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hacont
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hA : 0 ≤ A := (norm_nonneg (a 0)).trans (hAbound 0 hzero)
  have haBound : ∀ t ∈ Ico (0 : ℝ) T, |a t| ≤ A := by
    intro t ht
    rw [← Real.norm_eq_abs]
    exact hAbound t ⟨ht.1, ht.2.le⟩
  let massForm := dirichletMassComplOnIcc G.metric hCg hequiv
    Cv hCv0 hCvtop hvol
  let variationForm := dirichletMassVariationComplOnIco hG hreg Bv htrace
    hCg hequiv Cv hCv0 hCvtop hvol
  let weakForm := dirichletWeakFormComplOnIco G.metric X a Bx hX
    hCg hequiv Cv hCv0 hCvtop hvol
  have hmassMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ massForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletMassComplOnIcc_aestronglyMeasurable hG hreg hCg
      hequiv Cv hCv0 hCvtop hvol y z
  have hvariationMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ variationForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletMassVariationComplOnIco_aestronglyMeasurable hG hreg
      Bv htrace hCg hequiv Cv hCv0 hCvtop hvol y z
  have hweakMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ weakForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletWeakFormComplOnIco_aestronglyMeasurable hG hreg X
      hXcont a hacont Bx hX hCg hequiv Cv hCv0 hCvtop hvol y z
  have hmassBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletMassComplOnIcc_le
        G.metric hCg hequiv Cv hCv0 hCvtop hvol t
  have hvariationBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletMassVariationComplOnIco_le
        hG hreg Bv htrace hCg hequiv Cv hCv0 hCvtop hvol t
  have hweakBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletWeakFormComplOnIco_le
        G.metric X a A Bx hA haBound hX hCg hequiv
        Cv hCv0 hCvtop hvol t
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, ?_⟩
  intro v
  let p : ℝ → ℝ := fun t ↦ massForm t (u t) v
  let variation : ℝ → ℝ := fun t ↦ variationForm t (u t) v
  let weak : ℝ → ℝ := fun t ↦ weakForm t (u t) v
  let qderiv : ℝ → ℝ := fun t ↦ variation t + weak t
  have hp : MemLp p 2 (timeMeasure T) := by
    exact bilinear_apply_memLp u massForm hmassMeas hmassBound v
  have hvariation : MemLp variation 2 (timeMeasure T) := by
    exact bilinear_apply_memLp u variationForm hvariationMeas hvariationBound v
  have hweak : MemLp weak 2 (timeMeasure T) := by
    exact bilinear_apply_memLp u weakForm hweakMeas hweakBound v
  have hqderiv : MemLp qderiv 2 (timeMeasure T) := by
    change MemLp (variation + weak) 2 (timeMeasure T)
    exact hvariation.add hweak
  let initial := dirichletMassLp (G.metric 0) Cv hCvtop
    (hvol 0 hzero) f₀ (H1ComplDirichletToLp q v)
  apply exists_timeH1_of_integrated_weak_deriv hT hp hqderiv initial
  intro η dη hηcont hdηcont hηderiv hηT
  obtain ⟨Kη, hKη⟩ := isCompact_Icc.exists_bound_of_continuousOn hηcont
  have hηMeas : AEStronglyMeasurable η (timeMeasure T) := by
    unfold timeMeasure
    exact hηcont.aestronglyMeasurable measurableSet_Icc
  have hηBound : ∀ᵐ t ∂(timeMeasure T), ‖η t‖ ≤ Kη := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun t ht ↦ hKη t ht)
  have hvariationInt :=
    integrable_weighted_bilinear_of_apply_aestronglyMeasurable
      u variationForm hvariationMeas hvariationBound η hηMeas hηBound v
  have hweakInt :=
    integrable_weighted_bilinear_of_apply_aestronglyMeasurable
      u weakForm hweakMeas hweakBound η hηMeas hηBound v
  have hvariationInt' : Integrable (fun t ↦ η t * variation t)
      (volume.restrict (Icc (0 : ℝ) T)) := by
    simpa only [variation, timeMeasure] using hvariationInt
  have hweakInt' : Integrable (fun t ↦ η t * weak t)
      (volume.restrict (Icc (0 : ℝ) T)) := by
    simpa only [weak, timeMeasure] using hweakInt
  have hsum :
      (∫ t in Icc (0 : ℝ) T, η t * qderiv t) =
        (∫ t in Icc (0 : ℝ) T, η t * variation t) +
          ∫ t in Icc (0 : ℝ) T, η t * weak t := by
    rw [← MeasureTheory.integral_add hvariationInt' hweakInt']
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    simp only [qderiv, variation, weak]
    ring
  have hraw := hid η dη hηcont hdηcont hηderiv hηT v
  have hraw' :
      -(∫ t in Icc (0 : ℝ) T, dη t * p t) -
          (∫ t in Icc (0 : ℝ) T, η t * variation t) -
          η 0 * initial =
        ∫ t in Icc (0 : ℝ) T, η t * weak t := by
    simpa only [p, variation, weak, massForm, variationForm, weakForm,
      initial] using hraw
  have hset :
      -(∫ t in Icc (0 : ℝ) T, dη t * p t) - η 0 * initial =
        ∫ t in Icc (0 : ℝ) T, η t * qderiv t := by
    rw [hsum]
    linarith
  have hIccInterval (f : ℝ → ℝ) :
      (∫ t in Icc (0 : ℝ) T, f t) = ∫ t in (0 : ℝ)..T, f t := by
    rw [intervalIntegral.integral_of_le hT.le]
    exact MeasureTheory.integral_Icc_eq_integral_Ioc
  rw [hIccInterval, hIccInterval] at hset
  exact hset

theorem exists_dirichlet_weak_evolution_solution
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 < T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (Bx Bv : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t)
    (f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    ∃ u : timeL2 (H1ComplDirichlet q) T,
      IsWeakEvolutionSolution hG hT.le hreg X a Bx Bv
        hX htrace f₀ u := by
  obtain ⟨u, hu⟩ := exists_dirichlet_integrated_weak_solution
    hG hT hreg X hXcont a hacont Bx Bv hX htrace ha f₀
  exact ⟨u, hu.isWeakEvolutionSolution hT hXcont hacont⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
