import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Path

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

structure IsContMDiffWithSittingInstants (n : ℕ∞ω) {x y : M} (p : Path x y) : Prop where
  contMDiff : ContMDiff 𝓘(Real, Real) I n p.extend
  eventuallyEq_zero : p.extend =ᶠ[𝓝 0] (fun _ : Real => x)
  eventuallyEq_one : p.extend =ᶠ[𝓝 1] (fun _ : Real => y)

namespace IsContMDiffWithSittingInstants

variable {m n : ℕ∞ω}

theorem of_le {x y : M} {p : Path x y}
    (hp : IsContMDiffWithSittingInstants (I := I) n p) (hmn : m ≤ n) :
    IsContMDiffWithSittingInstants (I := I) m p where
  contMDiff := hp.contMDiff.of_le hmn
  eventuallyEq_zero := hp.eventuallyEq_zero
  eventuallyEq_one := hp.eventuallyEq_one

variable {x y z : M} {p : Path x y} {q : Path y z}

theorem refl (x : M) : IsContMDiffWithSittingInstants (I := I) n (Path.refl x) where
  contMDiff := by
    change ContMDiff 𝓘(Real, Real) I n (fun _ : Real => x)
    exact contMDiff_const
  eventuallyEq_zero := Filter.Eventually.of_forall fun _ => rfl
  eventuallyEq_one := Filter.Eventually.of_forall fun _ => rfl

theorem symm (hp : IsContMDiffWithSittingInstants (I := I) n p) :
    IsContMDiffWithSittingInstants (I := I) n p.symm where
  contMDiff := by
    rw [Path.extend_symm]
    apply hp.contMDiff.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  eventuallyEq_zero := by
    rw [Path.extend_symm]
    have hsub : Continuous (fun t : Real => 1 - t) :=
      continuous_const.sub continuous_id
    change (p.extend ∘ fun t : Real => 1 - t) =ᶠ[𝓝 0]
      ((fun _ : Real => y) ∘ fun t => 1 - t)
    exact hp.eventuallyEq_one.comp_tendsto (by
      simpa only [sub_zero] using hsub.tendsto (0 : Real) :
      Tendsto (fun t : Real => 1 - t) (𝓝 0) (𝓝 1))
  eventuallyEq_one := by
    rw [Path.extend_symm]
    have hsub : Continuous (fun t : Real => 1 - t) :=
      continuous_const.sub continuous_id
    change (p.extend ∘ fun t : Real => 1 - t) =ᶠ[𝓝 1]
      ((fun _ : Real => x) ∘ fun t => 1 - t)
    exact hp.eventuallyEq_zero.comp_tendsto (by
      simpa only [sub_self] using hsub.tendsto (1 : Real) :
      Tendsto (fun t : Real => 1 - t) (𝓝 1) (𝓝 0))

theorem trans
    (hp : IsContMDiffWithSittingInstants (I := I) n p)
    (hq : IsContMDiffWithSittingInstants (I := I) n q) :
    IsContMDiffWithSittingInstants (I := I) n (p.trans q) := by
  let f : Real → M := fun t => p.extend (2 * t)
  let g : Real → M := fun t => q.extend (2 * t - 1)
  have hf : ContMDiff 𝓘(Real, Real) I n f := by
    apply hp.contMDiff.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hg : ContMDiff 𝓘(Real, Real) I n g := by
    apply hq.contMDiff.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hmul : Continuous (fun t : Real => 2 * t) :=
    continuous_const.mul continuous_id
  have hsub : Continuous (fun t : Real => 2 * t - 1) :=
    hmul.sub continuous_const
  have h2half :
      Tendsto (fun t : Real => 2 * t) (𝓝 (1 / 2)) (𝓝 1) := by
    convert hmul.tendsto (1 / 2 : Real) using 1; norm_num
  have h2half' :
      Tendsto (fun t : Real => 2 * t - 1) (𝓝 (1 / 2)) (𝓝 0) := by
    convert hsub.tendsto (1 / 2 : Real) using 1; norm_num
  have hpf : f =ᶠ[𝓝 (1 / 2)] (fun _ : Real => y) := by
    change (p.extend ∘ fun t : Real => 2 * t) =ᶠ[𝓝 (1 / 2)]
      ((fun _ : Real => y) ∘ fun t => 2 * t)
    exact hp.eventuallyEq_one.comp_tendsto h2half
  have hqg : g =ᶠ[𝓝 (1 / 2)] (fun _ : Real => y) := by
    change (q.extend ∘ fun t : Real => 2 * t - 1) =ᶠ[𝓝 (1 / 2)]
      ((fun _ : Real => y) ∘ fun t => 2 * t - 1)
    exact hq.eventuallyEq_zero.comp_tendsto h2half'
  have hext :
      (p.trans q).extend =
        Set.piecewise (Set.Iic (1 / 2)) f g := by
    funext t
    by_cases ht : t ≤ 1 / 2
    · rw [Path.extend_trans_of_le_half p q ht]
      simp only [Set.piecewise, Set.mem_Iic, ht, ↓reduceIte, f]
    · have hhalf : 1 / 2 ≤ t := (not_le.mp ht).le
      rw [Path.extend_trans_of_half_le p q hhalf]
      simp only [Set.piecewise, Set.mem_Iic, ht, ↓reduceIte, g]
  refine {
    contMDiff := ?_
    eventuallyEq_zero := ?_
    eventuallyEq_one := ?_ }
  · rw [hext]
    exact ContMDiff.piecewise_Iic hf hg (hpf.trans hqg.symm)
  · have ht0 :
        Tendsto (fun t : Real => 2 * t) (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero] using hmul.tendsto (0 : Real)
    have hp0 : f =ᶠ[𝓝 0] (fun _ : Real => x) := by
      change (p.extend ∘ fun t : Real => 2 * t) =ᶠ[𝓝 0]
        ((fun _ : Real => x) ∘ fun t => 2 * t)
      exact hp.eventuallyEq_zero.comp_tendsto ht0
    filter_upwards
      [hp0, eventually_le_nhds (show (0 : Real) < 1 / 2 by norm_num)]
      with t hpt ht
    rw [Path.extend_trans_of_le_half p q ht]
    exact hpt
  · have ht1 :
        Tendsto (fun t : Real => 2 * t - 1) (𝓝 1) (𝓝 1) := by
      convert hsub.tendsto (1 : Real) using 1; norm_num
    have hq1 : g =ᶠ[𝓝 1] (fun _ : Real => z) := by
      change (q.extend ∘ fun t : Real => 2 * t - 1) =ᶠ[𝓝 1]
        ((fun _ : Real => z) ∘ fun t => 2 * t - 1)
      exact hq.eventuallyEq_one.comp_tendsto ht1
    filter_upwards
      [hq1, eventually_ge_nhds (show (1 / 2 : Real) < 1 by norm_num)]
      with t hqt ht
    rw [Path.extend_trans_of_half_le p q ht]
    exact hqt

end IsContMDiffWithSittingInstants

end Path
