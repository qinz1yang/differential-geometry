import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleIteratedDerivativeSource
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleSecondDerivativeSource
import DifferentialGeometry.Analysis.Integration.Lp.PiLp
import DifferentialGeometry.Analysis.Integration.Lp.BoundedConvergence
import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem tendsto_lp_iteratedParameterDerivativeSourceHs
    {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f : X → TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))
    (f0 : TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))
    (a b : X → Lp (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) p μ)
    (a0 b0 : Lp (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) p μ)
    (v : X → Lp (TensorHs g 0 0 ((1 + k : ℕ) : ℝ)) (⊤ : ℝ≥0∞) μ)
    (v0 : Lp (TensorHs g 0 0 ((1 + k : ℕ) : ℝ)) (⊤ : ℝ≥0∞) μ)
    (S : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) p μ)
    (S0 : Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) p μ)
    (hf : Tendsto f l (𝓝 f0)) (ha : Tendsto a l (𝓝 a0))
    (hb : Tendsto b l (𝓝 b0)) (hv : Tendsto v l (𝓝 v0))
    (hS : ∀ x, ∀ᵐ t ∂μ,
      S x t = iteratedParameterDerivativeSourceHs g k (f x) (a x t) (b x t) (v x t))
    (hS0 : ∀ᵐ t ∂μ,
      S0 t = iteratedParameterDerivativeSourceHs g k f0 (a0 t) (b0 t) (v0 t)) :
    Tendsto S l (𝓝 S0) := by
  let Ra := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by push_cast; linarith : ((1 + k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by exact_mod_cast (show 1 ≤ k + 3 by omega) : ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let A₁ := (iteratedParameterDerivativeHs g 1 1).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
        ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let D := (iteratedParameterDerivativeHs g 1 (k + 2)).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + (k + 2) : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let P := (iteratedParameterDerivativeHs g 1 (k + 1)).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + (k + 1) ≤ k + 3 by omega) :
        ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
  let M := scalarHsMul g 1 (by norm_num)
  let Q := parameterSecondDerivativeHs g (k + 3)
  let R := iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
  let Src := fun f' a' b' v' =>
    R.holderL μ p (⊤ : ℝ≥0∞) p (Ra.compLpL p μ a') v' +
      M.flip.compLpL₂ p μ (D (Q f')) (A.compLpL p μ a') +
      ((k + 2 : ℕ) : ℝ) • M.flip.compLpL₂ p μ (P (Q f')) (A₁.compLpL p μ a') +
      D.compLpL p μ b'
  have hSrc (f' : TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))
      (a' b' : Lp (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) p μ)
      (v' : Lp (TensorHs g 0 0 ((1 + k : ℕ) : ℝ)) (⊤ : ℝ≥0∞) μ) :
      Src f' a' b' v' =ᵐ[μ] fun t =>
        iteratedParameterDerivativeSourceHs g k f' (a' t) (b' t) (v' t) := by
    let r := R.holderL μ p (⊤ : ℝ≥0∞) p (Ra.compLpL p μ a') v'
    let s := M.flip.compLpL₂ p μ (D (Q f')) (A.compLpL p μ a')
    let z := M.flip.compLpL₂ p μ (P (Q f')) (A₁.compLpL p μ a')
    filter_upwards [Lp.coeFn_add (r + s + ((k + 2 : ℕ) : ℝ) • z) (D.compLpL p μ b'),
      Lp.coeFn_add (r + s) (((k + 2 : ℕ) : ℝ) • z), Lp.coeFn_add r s,
      Lp.coeFn_smul (((k + 2 : ℕ) : ℝ)) z,
      R.coeFn_holder (r := p) (Ra.compLpL p μ a') v', Ra.coeFn_compLpL a',
      (M.flip (D (Q f'))).coeFn_compLp (A.compLpL p μ a'), A.coeFn_compLpL a',
      (M.flip (P (Q f'))).coeFn_compLp (A₁.compLpL p μ a'), A₁.coeFn_compLpL a',
      D.coeFn_compLpL b'] with t h1 h2 h3 h4 hr hra hs hsa hz hza hd
    change (r + s + ((k + 2 : ℕ) : ℝ) • z + D.compLpL p μ b') t = _
    change r t = R ((Ra.compLpL p μ a') t) (v' t) at hr
    change s t = M ((A.compLpL p μ a') t) (D (Q f')) at hs
    change z t = M ((A₁.compLpL p μ a') t) (P (Q f')) at hz
    simp only [Pi.add_apply, Pi.smul_apply] at h1 h2 h3 h4
    rw [h1, h2, h3, h4, hr, hra, hs, hsa, hz, hza, hd]
    rfl
  have hSa (x : X) : S x = Src (f x) (a x) (b x) (v x) :=
    Lp.ext (Filter.EventuallyEq.trans (hS x) (hSrc (f x) (a x) (b x) (v x)).symm)
  have hS0a : S0 = Src f0 a0 b0 v0 := Lp.ext (Filter.EventuallyEq.trans hS0 (hSrc f0 a0 b0 v0).symm)
  have hRa := (Ra.compLpL p μ).continuous.tendsto (a0) |>.comp ha
  have hR := ((R.holderL μ p (⊤ : ℝ≥0∞) p).continuous₂.tendsto _).comp (hRa.prodMk_nhds hv)
  have hDQ := D.continuous.tendsto (Q f0) |>.comp (Q.continuous.tendsto f0 |>.comp hf)
  have hPQ := P.continuous.tendsto (Q f0) |>.comp (Q.continuous.tendsto f0 |>.comp hf)
  have hAa := (A.compLpL p μ).continuous.tendsto a0 |>.comp ha
  have hA₁a := (A₁.compLpL p μ).continuous.tendsto a0 |>.comp ha
  have hM := ((M.flip.compLpL₂ p μ).continuous₂.tendsto _).comp (hDQ.prodMk_nhds hAa)
  have hM₁ := ((M.flip.compLpL₂ p μ).continuous₂.tendsto _).comp (hPQ.prodMk_nhds hA₁a)
  have hDb := (D.compLpL p μ).continuous.tendsto b0 |>.comp hb
  have h := ((hR.add hM).add (hM₁.const_smul (((k + 2 : ℕ) : ℝ)))).add hDb
  change Tendsto (fun x => Src (f x) (a x) (b x) (v x)) l (𝓝 (Src f0 a0 b0 v0)) at h
  simpa only [← hSa, ← hS0a] using h

private theorem iterated_source_coordinate_ae
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
    (a : Lp (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) 2 μ)
    (b : Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) 2 μ)
    (v : Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 + k : ℕ) : ℝ))) (⊤ : ℝ≥0∞) μ)
    (S : Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) 2 μ)
    (hS : ∀ᵐ t ∂μ, ∀ i,
      S t i = iteratedParameterDerivativeSourceHs g k (f i) (a t) (b t i) (v t i))
    (i : ι) :
    let B := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) i).compLpL 2 μ
    let V := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 ((1 + k : ℕ) : ℝ)) i).compLpL (⊤ : ℝ≥0∞) μ
    let Z := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) i).compLpL 2 μ
    ∀ᵐ t ∂μ, Z S t = iteratedParameterDerivativeSourceHs g k (f i) (a t) (B b t) (V v t) := by
  intro B V Z
  filter_upwards [hS,
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) i).coeFn_compLpL b,
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 ((1 + k : ℕ) : ℝ)) i).coeFn_compLpL v,
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) i).coeFn_compLpL S]
      with t ht hbt hvt hst
  change B b t = b t i at hbt
  change V v t = v t i at hvt
  change Z S t = S t i at hst
  rw [hst, hbt, hvt]
  exact ht i

theorem tendsto_lp_iteratedParameterDerivativeSourceHs_piLp
    {Ω X ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
    (f0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
    (a : X → Lp (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) 2 μ)
    (a0 : Lp (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) 2 μ)
    (b : X → Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) 2 μ)
    (b0 : Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) 2 μ)
    (v : X → Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 + k : ℕ) : ℝ))) (⊤ : ℝ≥0∞) μ)
    (v0 : Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 + k : ℕ) : ℝ))) (⊤ : ℝ≥0∞) μ)
    (S : X → Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) 2 μ)
    (S0 : Lp (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) 2 μ)
    (hf : Tendsto f l (𝓝 f0)) (ha : Tendsto a l (𝓝 a0))
    (hb : Tendsto b l (𝓝 b0)) (hv : Tendsto v l (𝓝 v0))
    (hS : ∀ x, ∀ᵐ t ∂μ, ∀ i,
      S x t i = iteratedParameterDerivativeSourceHs g k (f x i) (a x t) (b x t i) (v x t i))
    (hS0 : ∀ᵐ t ∂μ, ∀ i,
      S0 t i = iteratedParameterDerivativeSourceHs g k (f0 i) (a0 t) (b0 t i) (v0 t i)) :
    Tendsto S l (𝓝 S0) := by
  let B i := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) i).compLpL 2 μ
  let V i := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 ((1 + k : ℕ) : ℝ)) i).compLpL (⊤ : ℝ≥0∞) μ
  let Z i := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) i).compLpL 2 μ
  apply (Lp.tendsto_piLp_iff (𝕜 := ℝ) μ).mpr
  intro i
  change Tendsto (fun x => Z i (S x)) l (𝓝 (Z i S0))
  apply tendsto_lp_iteratedParameterDerivativeSourceHs μ g k
    (fun x => f x i) (f0 i) a (fun x => B i (b x)) a0 (B i b0)
    (fun x => V i (v x)) (V i v0) (fun x => Z i (S x)) (Z i S0)
    ((PiLp.continuous_apply 2 _ i).tendsto f0 |>.comp hf) ha
    ((B i).continuous.tendsto b0 |>.comp hb)
    ((V i).continuous.tendsto v0 |>.comp hv)
  · intro x
    exact iterated_source_coordinate_ae μ g k (f x) (a x) (b x) (v x) (S x) (hS x) i
  · exact iterated_source_coordinate_ae μ g k f0 a0 b0 v0 S0 hS0 i

theorem tendsto_timeL2_iteratedParameterDerivativeSourceHs_of_tendstoUniformlyOn
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) (T : ℝ)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
    (f0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2)))
    (a : X → timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (a0 : timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (b : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
    (b0 : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
    (W : X → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
    (W0 : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
    (S : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (S0 : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (hf : Tendsto f l (𝓝 f0)) (ha : Tendsto a l (𝓝 a0)) (hb : Tendsto b l (𝓝 b0))
    (hWc : ∀ x, ContinuousOn (W x) (Icc 0 T)) (hW0c : ContinuousOn W0 (Icc 0 T))
    (hW : TendstoUniformlyOn W W0 l (Icc 0 T)) :
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let Q := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ))).comp
        ((parameterSecondDerivativeHs g (k + 1)).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ))))
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      S x t i = iteratedParameterDerivativeSourceHs g k (f x i) (a x t) (b x t i)
        (Q (B (f x i) + W x t i))) →
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      S0 t i = iteratedParameterDerivativeSourceHs g k (f0 i) (a0 t) (b0 t i)
        (Q (B (f0 i) + W0 t i))) →
    Tendsto S l (𝓝 S0) := by
  intro B Q hS hS0
  let Bp := ContinuousLinearMap.piLpMap 2 (fun _ : ι => B)
  let Qp := ContinuousLinearMap.piLpMap 2 (fun _ : ι => Q)
  let w := fun x t => Qp (Bp (f x) + W x t)
  let w0 := fun t => Qp (Bp f0 + W0 t)
  have hwc (x : X) : ContinuousOn (w x) (Icc 0 T) :=
    Qp.continuous.comp_continuousOn (continuousOn_const.add (hWc x))
  have hw0c : ContinuousOn w0 (Icc 0 T) :=
    Qp.continuous.comp_continuousOn (continuousOn_const.add hW0c)
  have hwm (x : X) : MemLp (w x) (⊤ : ℝ≥0∞) (timeMeasure T) :=
    (hwc x).memLp_top_of_isCompact isCompact_Icc measurableSet_Icc
  have hw0m : MemLp w0 (⊤ : ℝ≥0∞) (timeMeasure T) :=
    hw0c.memLp_top_of_isCompact isCompact_Icc measurableSet_Icc
  let v x := (hwm x).toLp (w x)
  let v0 := hw0m.toLp w0
  have hwt : TendstoUniformlyOn w w0 l (Icc 0 T) :=
    Qp.uniformContinuous.comp_tendstoUniformlyOn
      ((((Bp.continuous.tendsto f0).comp hf).tendstoUniformlyOn_const (Icc 0 T)).add hW)
  have hvt : Tendsto v l (𝓝 v0) :=
    Lp.tendsto_top_of_tendstoUniformlyOn
      (ae_restrict_mem (μ := volume) measurableSet_Icc) v v0 w w0
      (fun x => (hwm x).coeFn_toLp) hw0m.coeFn_toLp hwt
  apply tendsto_lp_iteratedParameterDerivativeSourceHs_piLp (timeMeasure T) g k
    f f0 a a0 b b0 v v0 S S0 hf ha hb hvt
  · intro x
    filter_upwards [hS x, (hwm x).coeFn_toLp] with t ht hvt
    intro i
    change v x t = w x t at hvt
    rw [hvt]
    exact ht i
  · filter_upwards [hS0, hw0m.coeFn_toLp] with t ht hvt
    intro i
    change v0 t = w0 t at hvt
    rw [hvt]
    exact ht i

theorem iteratedParameterDerivativeSourceHs_ae_eq_of_projection
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 3 : ℕ) : ℝ) + 2))) {T : ℝ}
    (a : timeL2 (TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)) T)
    (bHigh : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ))) T)
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 2 : ℕ) : ℝ)))
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k + 3 : ℕ) : ℝ)))
    (U : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((k + 2 : ℕ) : ℝ) + 2)))
    (S : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T) :
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let Qh := parameterSecondDerivativeHs g (k + 2)
    let Rw := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 + k ≤ k + 2 by omega) :
        ((1 + k : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    let Ra := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
        ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let A₁ := (iteratedParameterDerivativeHs g 1 1).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 + 1 ≤ k + 3 by omega) :
          ((1 + 1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)))
    let E₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let D := E₀.comp ((iteratedParameterDerivativeHs g 0 (k + 2)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((0 + (k + 2) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))))
    let W₁ := (iteratedParameterDerivativeHs g 1 (k + 1)).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((1 + (k + 1) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let m := scalarH0ContinuousMul g
    (∀ᵐ t ∂timeMeasure T, ∀ i, J (bHigh t i) = b t i) →
    (∀ᵐ t ∂timeMeasure T, ∀ i, W t i = K (U t i)) →
    (∀ᵐ t ∂timeMeasure T, ∀ i, Z (S t i) =
      Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
        (Ra (a t)) (Rw (Qh (P (f₀ i) + U t i)))) +
        m (C (A (a t))) (D (Qh (P (f₀ i)))) +
          ((k + 2 : ℕ) : ℝ) • m (C (A₁ (a t))) (Z (W₁ (Qh (P (f₀ i))))) + D (b t i)) →
    let B := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by linarith : ((k + 3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) + 2)
    let Qlow := (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((1 + k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ))).comp
        ((parameterSecondDerivativeHs g (k + 1)).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ))))
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      S t i = iteratedParameterDerivativeSourceHs g k (f₀ i) (a t) (bHigh t i)
        (Qlow (B (f₀ i) + W t i)) := by
  intro P K J Qh Rw Ra A A₁ E₀ D W₁ Z C m hb hW hS B Qlow
  have hcoordinate : ∀ i, ∀ᵐ t ∂timeMeasure T,
      Z (iteratedParameterDerivativeSourceHs g k (f₀ i) (a t) (bHigh t i)
        (Qlow (B (f₀ i) + W t i))) =
      Z (iteratedParameterDerivativeMulRemainderHs g 1 (by omega) k
        (Ra (a t)) (Rw (Qh (P (f₀ i) + U t i)))) +
        m (C (A (a t))) (D (Qh (P (f₀ i)))) +
          ((k + 2 : ℕ) : ℝ) • m (C (A₁ (a t))) (Z (W₁ (Qh (P (f₀ i))))) + D (b t i) := by
    intro i
    apply tensorHsInclusion_iteratedParameterDerivativeSourceHs_ae_eq
      g k (f₀ i) a (fun t => bHigh t i) (fun t => b t i)
        (fun t => W t i) (fun t => U t i)
    · filter_upwards [hb] with t ht
      exact ht i
    · filter_upwards [hW] with t ht
      exact ht i
  filter_upwards [hS, ae_all_iff.mpr hcoordinate] with t ht hct
  intro i
  apply tensorHsInclusion_injective (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
  exact (ht i).trans (hct i).symm

theorem iteratedParameterDerivativeSourceHs_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : TensorHs g 0 0 (((3 : ℕ) : ℝ) + 2))
    (a b : TensorHs g 0 0 ((3 : ℕ) : ℝ))
    (v : TensorHs g 0 0 ((1 : ℕ) : ℝ)) :
    let E := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((3 : ℕ) : ℝ))
    iteratedParameterDerivativeSourceHs g 0 f₀ a b v =
      parameterSecondDerivativeSourceHs g f₀ (E a) (E b) v := by
  intro E
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
  let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
  let Q := parameterSecondDerivativeHs g 1
  let D := J.comp ((parameterDerivativeHs g 2).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)))
  let q₀ := parameterSecondDerivativeHs g 3 f₀
  let M := scalarHsMul g 1 (by norm_num)
  have hQ (w : TensorHs g 0 0 ((3 : ℕ) : ℝ)) :
      iteratedParameterDerivativeHs g 1 2 w = Q (E w) := by
    have h := parameterSecondDerivativeHs_iteratedParameterDerivativeHs g 1 0 w
    simpa only [iteratedParameterDerivativeHs_zero, ContinuousLinearMap.id_apply,
      ← tensorHsInclusion_trans_apply, Q, E] using h.symm
  have hP (w : TensorHs g 0 0 ((3 : ℕ) : ℝ)) :
      iteratedParameterDerivativeHs g 1 1
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((2 : ℕ) : ℝ) ≤ ((3 : ℕ) : ℝ)) w) = D (E w) := by
    have h := parameterDerivativeHs_tensorHsInclusion g (by omega : 1 ≤ 2)
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((3 : ℕ) : ℝ)) w)
    simpa only [iteratedParameterDerivativeHs_succ_apply, iteratedParameterDerivativeHs_zero,
      ContinuousLinearMap.id_apply, D, J, E, ContinuousLinearMap.comp_apply,
      ← tensorHsInclusion_trans_apply] using h
  have hA (w : TensorHs g 0 0 ((3 : ℕ) : ℝ)) :
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((3 : ℕ) : ℝ)) w = K (E w) := by
    simp only [K, E, ← tensorHsInclusion_trans_apply]
  change iteratedParameterDerivativeMulRemainderHs g 1 (by omega) 0
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((3 : ℕ) : ℝ) ≤ ((3 : ℕ) : ℝ)) a) v +
    M (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((3 : ℕ) : ℝ)) a)
      (iteratedParameterDerivativeHs g 1 2
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((3 : ℕ) : ℝ) ≤ ((3 : ℕ) : ℝ)) q₀)) +
    (2 : ℝ) • M (iteratedParameterDerivativeHs g 1 1
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((2 : ℕ) : ℝ) ≤ ((3 : ℕ) : ℝ)) a))
      (iteratedParameterDerivativeHs g 1 1
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((2 : ℕ) : ℝ) ≤ ((3 : ℕ) : ℝ)) q₀)) +
    iteratedParameterDerivativeHs g 1 2
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((3 : ℕ) : ℝ) ≤ ((3 : ℕ) : ℝ)) b) =
    M (Q (E a)) v + (2 : ℝ) • M (D (E a)) (D (E q₀)) +
      M (K (E a)) (Q (E q₀)) + Q (E b)
  simp only [tensorHsInclusion_refl_apply,
    iteratedParameterDerivativeMulRemainderHs_zero_apply, hQ, hP, hA]
  abel

end AddCircle
