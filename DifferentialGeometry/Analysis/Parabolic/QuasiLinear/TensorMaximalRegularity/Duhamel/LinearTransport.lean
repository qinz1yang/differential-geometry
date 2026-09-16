import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.FiniteProduct
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity

private theorem compLpL_comp_apply
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {T : ℝ}
    (A : Y →L[ℝ] Z) (B : X →L[ℝ] Y) (f : timeL2 X T) :
    (A.comp B).compLpL 2 (timeMeasure T) f =
      A.compLpL 2 (timeMeasure T) (B.compLpL 2 (timeMeasure T) f) := by
  apply Lp.ext
  filter_upwards [(A.comp B).coeFn_compLpL f,
    A.coeFn_compLpL (B.compLpL 2 (timeMeasure T) f), B.coeFn_compLpL f] with t h₁ h₂ h₃
  rw [h₁, h₂, h₃, ContinuousLinearMap.comp_apply]

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a b T : ℝ}

theorem duhamel_vector_comp_eq (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (D : PiLp 2 (fun _ : ι => TensorHs g r s b) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a))
    (Dh : PiLp 2 (fun _ : ι => TensorHs g r s (b + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)))
    (hD : (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).comp Dh =
      D.comp (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show b ≤ b + 2 by linarith))))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (b + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s b)) T) :
    let U := maximalRegularityDuhamelVectorField hT u₀ F
    let Lb := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := r) (s := s) b)
    let La := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := r) (s := s) a)
    let G := D.compLpL 2 (timeMeasure T) F +
      (D.comp Lb - La.comp Dh).compLpL 2 (timeMeasure T) U
    Dh.compLpL 2 (timeMeasure T) U =
        maximalRegularityDuhamelVectorField hT (Dh u₀) G ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        (maximalRegularityDuhamelVectorMap hT (Dh u₀) G).toFun t =
          D ((maximalRegularityDuhamelVectorMap hT u₀ F).toFun t) := by
  dsimp only
  let U := maximalRegularityDuhamelVectorField hT u₀ F
  let u := maximalRegularityDuhamelVectorMap hT u₀ F
  let Lb := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := r) (s := s) b)
  let La := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := r) (s := s) a)
  let Jb := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show b ≤ b + 2 by linarith))
  let Ja := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))
  let V := Dh.compLpL 2 (timeMeasure T) U
  let G := D.compLpL 2 (timeMeasure T) F +
    (D.comp Lb - La.comp Dh).compLpL 2 (timeMeasure T) U
  obtain ⟨v, hvi, hv, hvd⟩ := exists_timeH1_comp_clm D u
  have hvL2 : v.toFunL2 = D.compLpL 2 (timeMeasure T) u.toFunL2 := by
    apply Lp.ext
    filter_upwards [coeFn_ofContinuousOn v.continuousOn_toFun,
      D.coeFn_compLpL u.toFunL2, coeFn_ofContinuousOn u.continuousOn_toFun,
      ae_restrict_mem measurableSet_Icc] with t hvt hDt hut ht
    change v.toFunL2 t = v.toFun t at hvt
    change u.toFunL2 t = u.toFun t at hut
    rw [hvt, hDt, hut, hv t ht]
  have hderiv : v.deriv = D.compLpL 2 (timeMeasure T) u.deriv :=
    Lp.ext (hvd.trans (D.coeFn_compLpL u.deriv).symm)
  have htrace : timeH1.trace0 _ T v = Ja (Dh u₀) := by
    change v.initial = Ja (Dh u₀)
    rw [hvi]
    have hinit : u.initial = Jb u₀ := maximalRegularityDuhamelVectorMap_trace0 hT u₀ F
    rw [hinit]
    exact (congrArg (fun L => L u₀) hD).symm
  have hlink : Ja.compLpL 2 (timeMeasure T) V = v.toFunL2 := by
    rw [hvL2]
    change Ja.compLpL 2 (timeMeasure T) (Dh.compLpL 2 (timeMeasure T) U) = _
    rw [← compLpL_comp_apply, hD, compLpL_comp_apply]
    rw [show Jb.compLpL 2 (timeMeasure T) U = u.toFunL2 from
      maximalRegularityDuhamelVectorField_toFunL2 hT hc u₀ F]
  have heq : timeH1.timeDeriv _ T v = La.compLpL 2 (timeMeasure T) V + G := by
    change v.deriv = _
    rw [hderiv]
    have hu : u.deriv = Lb.compLpL 2 (timeMeasure T) U + F :=
      maximalRegularityDuhamelVectorMap_timeDeriv_eq hT hc u₀ F
    rw [hu, map_add]
    have hcomm : (D.comp Lb - La.comp Dh).compLpL 2 (timeMeasure T) U =
        D.compLpL 2 (timeMeasure T) (Lb.compLpL 2 (timeMeasure T) U) -
          La.compLpL 2 (timeMeasure T) V := by
      apply Lp.ext
      filter_upwards [(D.comp Lb - La.comp Dh).coeFn_compLpL U,
        D.coeFn_compLpL (Lb.compLpL 2 (timeMeasure T) U), Lb.coeFn_compLpL U,
        La.coeFn_compLpL V, Dh.coeFn_compLpL U,
        Lp.coeFn_sub (D.compLpL 2 (timeMeasure T) (Lb.compLpL 2 (timeMeasure T) U))
          (La.compLpL 2 (timeMeasure T) V)] with t h₁ h₂ h₃ h₄ h₅ h₆
      rw [h₁, h₆, Pi.sub_apply, h₂, h₃, h₄]
      change D (Lb (U t)) - La (Dh (U t)) = D (Lb (U t)) - La (V t)
      rw [show V t = Dh (U t) from h₅]
    change _ = La.compLpL 2 (timeMeasure T) V +
      (D.compLpL 2 (timeMeasure T) F + _)
    rw [hcomm]
    abel
  obtain ⟨hV, hvEq⟩ := strongPair_eq_duhamel_vector hT hc (Dh u₀) G v V
    htrace hlink heq
  exact ⟨hV, fun t ht => hvEq ▸ hv t ht⟩

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a b T : ℝ}

theorem duhamel_vector_comp_zero_eq (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (D : PiLp 2 (fun _ : ι => TensorHs g r s b) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s a))
    (Dh : PiLp 2 (fun _ : ι => TensorHs g r s (b + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)))
    (hD : (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).comp Dh =
      D.comp (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show b ≤ b + 2 by linarith))))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s b)) T) :
    let U := maximalRegularityDuhamelVectorField hT 0 F
    let Lb := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := r) (s := s) b)
    let La := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := r) (s := s) a)
    let G := D.compLpL 2 (timeMeasure T) F +
      (D.comp Lb - La.comp Dh).compLpL 2 (timeMeasure T) U
    Dh.compLpL 2 (timeMeasure T) U =
        maximalRegularityDuhamelVectorField hT 0 G ∧
      (maximalRegularityDuhamelVectorMap hT 0 G).initial = 0 ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        (maximalRegularityDuhamelVectorMap hT 0 G).toFun t =
          D ((maximalRegularityDuhamelVectorMap hT 0 F).toFun t) := by
  intro U Lb La G
  have h := duhamel_vector_comp_eq hT hc D Dh hD 0 F
  dsimp only at h
  rw [map_zero] at h
  refine ⟨h.1, ?_, h.2⟩
  have htrace := maximalRegularityDuhamelVectorMap_trace0 hT
    (0 : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) G
  simpa only [timeH1.trace0_apply, map_zero] using htrace

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
