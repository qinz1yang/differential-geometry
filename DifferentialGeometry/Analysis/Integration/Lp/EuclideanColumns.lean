import DifferentialGeometry.Analysis.Integration.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory.Lp

private theorem tendsto_dual_of_tendsto_inner
    {A H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {l : Filter A} {u : A → H} {u₀ : H}
    (hu : ∀ z, Tendsto (fun a => inner ℝ (u a) z) l (𝓝 (inner ℝ u₀ z)))
    (F : H →L[ℝ] ℝ) :
    Tendsto (fun a => F (u a)) l (𝓝 (F u₀)) := by
  have hF (w : H) : F w = inner ℝ w ((_root_.InnerProductSpace.toDual ℝ H).symm F) := by
    rw [real_inner_comm, _root_.InnerProductSpace.toDual_symm_apply]
  simpa only [hF] using hu ((_root_.InnerProductSpace.toDual ℝ H).symm F)

theorem tendsto_dual_piLpEquiv_symm_of_tendsto_inner
    {P A ι : Type*} [MeasurableSpace P] {μ : Measure P} [Fintype ι]
    {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)]
    [∀ i, InnerProductSpace ℝ (X i)] [∀ i, CompleteSpace (X i)]
    {l : Filter A} (u : ∀ i, A → Lp (X i) 2 μ)
    (u₀ : ∀ i, Lp (X i) 2 μ)
    (hu : ∀ i (z : Lp (X i) 2 μ),
      Tendsto (fun a => inner ℝ (u i a) z) l (𝓝 (inner ℝ (u₀ i) z)))
    (F : Lp (PiLp 2 X) 2 μ →L[ℝ] ℝ) :
    Tendsto
      (fun a => F ((piLpEquiv (𝕜 := ℝ) μ).symm (WithLp.toLp 2 (fun i => u i a)))) l
      (𝓝 (F ((piLpEquiv (𝕜 := ℝ) μ).symm (WithLp.toLp 2 u₀)))) := by
  let V : A → PiLp 2 (fun i => Lp (X i) 2 μ) :=
    fun a => WithLp.toLp 2 (fun i => u i a)
  let V₀ : PiLp 2 (fun i => Lp (X i) 2 μ) := WithLp.toLp 2 u₀
  have hV (z : PiLp 2 (fun i => Lp (X i) 2 μ)) :
      Tendsto (fun a => inner ℝ (V a) z) l (𝓝 (inner ℝ V₀ z)) := by
    change Tendsto (fun a => ∑ i, inner ℝ (u i a) (z i)) l
      (𝓝 (∑ i, inner ℝ (u₀ i) (z i)))
    exact tendsto_finsetSum _ fun i _ => hu i (z i)
  exact tendsto_dual_of_tendsto_inner hV
    (F.comp (piLpEquiv (𝕜 := ℝ) (X := X) μ).symm.toContinuousLinearEquiv.toContinuousLinearMap)

variable {P ι κ : Type*} [MeasurableSpace P] {μ : Measure P}
  [Fintype ι] [Fintype κ]

def euclideanColumn (u : ι → Lp (EuclideanSpace ℝ κ) 2 μ) (j : κ) :
    Lp (EuclideanSpace ℝ ι) 2 μ :=
  (piLpEquiv (𝕜 := ℝ) (X := fun _ : ι => ℝ) μ).symm
    (WithLp.toLp 2 (fun i => (EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u i)))

theorem euclideanColumn_coeFn
    (u : ι → Lp (EuclideanSpace ℝ κ) 2 μ) (j : κ) :
    (euclideanColumn u j : P → EuclideanSpace ℝ ι) =ᵐ[μ]
      (fun x => WithLp.toLp 2 (fun i => u i x j)) := by
  have he : ∀ᵐ x ∂μ, ∀ i,
      ((EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u i)) x = u i x j :=
    ae_all_iff.mpr fun i => (EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL (u i)
  filter_upwards [piLpEquiv_symm_apply (𝕜 := ℝ) μ
    (WithLp.toLp 2 (fun i => (EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u i))), he]
    with x hx he
  exact hx.trans (PiLp.ext he)

theorem tendsto_dual_euclideanColumn_of_tendsto_inner
    {A : Type*} {l : Filter A}
    (u : ι → A → Lp (EuclideanSpace ℝ κ) 2 μ)
    (u₀ : ι → Lp (EuclideanSpace ℝ κ) 2 μ)
    (hu : ∀ i (z : Lp (EuclideanSpace ℝ κ) 2 μ),
      Tendsto (fun a => inner ℝ (u i a) z) l (𝓝 (inner ℝ (u₀ i) z)))
    (j : κ) (F : Lp (EuclideanSpace ℝ ι) 2 μ →L[ℝ] ℝ) :
    Tendsto (fun a => F (euclideanColumn (fun i => u i a) j)) l
      (𝓝 (F (euclideanColumn u₀ j))) := by
  have hc (i : ι) (z : Lp ℝ 2 μ) :
      Tendsto
        (fun a => inner ℝ ((EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u i a)) z) l
        (𝓝 (inner ℝ ((EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u₀ i)) z)) := by
    have h := tendsto_dual_of_tendsto_inner (hu i)
      ((innerSL ℝ z).comp ((EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ))
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm] using h
  exact tendsto_dual_piLpEquiv_symm_of_tendsto_inner
    (fun i a => (EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u i a))
    (fun i => (EuclideanSpace.proj (𝕜 := ℝ) j).compLpL 2 μ (u₀ i)) hc F

end MeasureTheory.Lp
