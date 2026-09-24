import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.ContinuousRealization
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev
open DifferentialGeometry.Analysis.Spectral

variable {ι : Type*} [Fintype ι]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem initial_realization_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T)
    (htrace : timeH1.trace0 _ T u = 0) :
    scalarH1PiToContinuous g (u.toFun 0) = 0 := by
  have hzero : u.toFun 0 = 0 := by
    simpa only [timeH1.toFun_zero, timeH1.trace0_apply] using htrace
  rw [hzero, map_zero]

theorem iteratedDeriv_initial_realization_add
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T)
    (htrace : timeH1.trace0 _ T u = 0) (f₀ : ℝ → ι → ℝ) (m : ℕ) :
    iteratedDeriv m (fun x : ℝ => f₀ x +
      scalarH1PiToContinuous g (u.toFun 0) (x : AddCircle (1 : ℝ))) =
        iteratedDeriv m f₀ := by
  simp only [initial_realization_eq g u htrace, ContinuousMap.zero_apply, add_zero]


theorem tendstoUniformly_initial_realization_add
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T)
    (v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2))) T)
    (hlink : ∀ᵐ t ∂timeMeasure T,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (1 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)) (v t) = u.toFun t)
    (htrace : timeH1.trace0 _ T u = 0)
    (f₀ : ℝ → ι → ℝ) (hf₀ : Differentiable ℝ f₀) :
    TendstoUniformly (fun t x => f₀ x + scalarH1PiToContinuous g (u.toFun t)
      (x : AddCircle (1 : ℝ))) f₀ (𝓝[Icc 0 T] 0) ∧
    TendstoUniformly (fun t => deriv (fun x : ℝ => f₀ x +
      scalarH1PiToContinuous g (u.toFun t) (x : AddCircle (1 : ℝ))))
      (deriv f₀) (𝓝[Icc 0 T] 0) := by
  have hzero := initial_realization_eq g u htrace
  have hcont := (scalarH1PiToContinuous (ι := ι) g).continuous.comp_continuousOn
    u.continuousOn_toFun
  have hlim := ContinuousMap.tendsto_iff_tendstoUniformly.mp
    (hcont 0 ⟨le_rfl, hT.le⟩)
  simp only [Function.comp_def, hzero] at hlim
  have hlim' := hlim.comp (fun x : ℝ => (x : AddCircle (1 : ℝ)))
  change TendstoUniformly _ (0 : ℝ → ι → ℝ) _ at hlim'
  obtain ⟨d, _, hd, _, _, hder, _⟩ :=
    exists_continuousOn_parameterDerivative_representative g hT u v hlink
  have hd0 : d 0 = 0 := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    have h := (hder 0 ⟨le_rfl, hT.le⟩ x).deriv
    simpa only [hzero, ContinuousMap.zero_apply, deriv_const] using h.symm
  have hdlim := ContinuousMap.tendsto_iff_tendstoUniformly.mp
    (hd 0 ⟨le_rfl, hT.le⟩)
  rw [hd0] at hdlim
  have hdlim' := hdlim.comp (fun x : ℝ => (x : AddCircle (1 : ℝ)))
  change TendstoUniformly _ (0 : ℝ → ι → ℝ) _ at hdlim'
  have hconst (f : ℝ → ι → ℝ) : TendstoUniformly (fun _ : ℝ => f) f (𝓝[Icc 0 T] 0) := by
    intro s hs
    exact Eventually.of_forall (fun _ _ => refl_mem_uniformity hs)
  constructor
  · convert ((hconst f₀).add hlim') using 1 <;> ext <;> simp
  · have hsum := (hconst (deriv f₀)).add hdlim'
    have hsum' : TendstoUniformly (fun t x => deriv f₀ x + d t (x : AddCircle (1 : ℝ)))
        (deriv f₀) (𝓝[Icc 0 T] 0) := by
      convert hsum using 1 <;> ext <;> simp
    refine (tendstoUniformly_congr ?_).mp hsum'
    filter_upwards [self_mem_nhdsWithin] with t ht
    funext x
    exact ((hf₀ x).hasDerivAt.add (hder t ht x)).deriv.symm

theorem tendstoUniformly_initial_duhamel_realization
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1 by norm_num))
    let u := maximalRegularityDuhamelVectorMap hT (0 : PiLp 2 (fun _ : ι =>
      TensorHs g 0 0 ((1 : ℝ) + 2))) F
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g (P f₀ + u.toFun t)
      (x : AddCircle (1 : ℝ))
    TendstoUniformly f (f 0) (𝓝[Icc 0 T] 0) ∧
      TendstoUniformly (fun t => deriv (f t)) (deriv (f 0)) (𝓝[Icc 0 T] 0) := by
  intro P u f
  let v := maximalRegularityDuhamelVectorField hT (0 : PiLp 2 (fun _ : ι =>
    TensorHs g 0 0 ((1 : ℝ) + 2))) F
  let Q := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (1 : ℝ) ≤ (1 : ℝ) + 2 by norm_num))
  have hlink : ∀ᵐ t ∂timeMeasure T, Q (v t) = u.toFun t := by
    have hpin := maximalRegularityDuhamelVectorField_toFunL2 hT
      (tensorResolventL2_isCompactOperator
        (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0)
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2))) F
    have ha := Q.coeFn_compLpL (p := 2) (μ := timeMeasure T) v
    have hb := coeFn_ofContinuousOn u.continuousOn_toFun
    filter_upwards [ha, hb] with t hta htb
    change (Q.compLpL 2 (timeMeasure T) v) t = _ at hta
    change u.toFunL2 t = _ at htb
    rw [show Q.compLpL 2 (timeMeasure T) v = u.toFunL2 from hpin] at hta
    exact hta.symm.trans htb
  have htrace : timeH1.trace0 _ T u = 0 := by
    simp only [u, maximalRegularityDuhamelVectorMap_trace0, map_zero]
  let fbase := fun x : ℝ => scalarH1PiToContinuous g (P f₀) (x : AddCircle (1 : ℝ))
  have hfbase : Differentiable ℝ fbase := by
    exact (AddCircle.contDiff_two_scalarH1PiToContinuous g f₀).differentiable (by norm_num)
  have h := tendstoUniformly_initial_realization_add g hT u v hlink htrace fbase hfbase
  have hf (t : ℝ) : f t = fun x => fbase x +
      scalarH1PiToContinuous g (u.toFun t) (x : AddCircle (1 : ℝ)) := by
    funext x
    simp only [f, fbase, map_add, ContinuousMap.add_apply]
  have hfzero : f 0 = fbase := by
    rw [hf]
    simp only [initial_realization_eq g u htrace, ContinuousMap.zero_apply, add_zero]
  rw [hfzero]
  have hfeq := funext hf
  rw [hfeq]
  exact h

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
