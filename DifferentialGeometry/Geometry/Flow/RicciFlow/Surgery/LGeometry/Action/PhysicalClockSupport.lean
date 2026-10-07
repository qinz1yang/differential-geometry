import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CostDefs
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

/-- Convert the same original-history clock support to physical time. The
original endpoint velocity is retained; its speed term cancels against the
trace term without a free-endpoint minimum or a zero-velocity premise. -/
theorem physical_clock_support_of_same_history_jets
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T Bfloor : ℝ) {v : ℝ} (hv : 0 < v)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) :
    let jf : H.StageInterval first last := ⟨first, le_rfl, hle⟩
    let jl : H.StageInterval first last := ⟨last, hle, le_rfl⟩
    let p := gamma jl 0
    let q := gamma jf v
    let L := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)
    let g := H.stageMetric first (T - v ^ 2)
    let V : TangentSpace ThreeModel q := lVelocity (I := ThreeModel) (gamma jf) v
    let R := metricScalarAt g q
    ∀ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen U → (q, v) ∈ U →
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U →
      F (q, v) = L →
      H.regularizedCost first last hle T Bfloor 0 v p q = (L : WithTop ℝ) →
      (∀ z ∈ U, H.regularizedCost first last hle T Bfloor 0 z.2 p z.1 ≤
        (F z : WithTop ℝ)) →
      gradientFun g (fun y => F (y, v)) q = V →
      HasDerivAt (fun w => F (q, w))
        (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v →
    ∀ epsilon : ℝ,
      laplacian (LeviCivita g) g (fun y => F (y, v)) q <
        3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + epsilon →
    let Omega : Set ((H.stage first).Carrier × ℝ) :=
      {z | z.2 < T ∧ z.2 ∈ Ioo (H.time first) (H.stageEndTime first) ∧
        (z.1, Real.sqrt (T - z.2)) ∈ U}
    let Aphys : (H.stage first).Carrier × ℝ → ℝ :=
      fun z => 2 * Real.sqrt (T - z.2) * F (z.1, Real.sqrt (T - z.2))
    IsOpen Omega ∧ (q, T - v ^ 2) ∈ Omega ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega ∧
      Aphys (q, T - v ^ 2) = 2 * v * L ∧
      (∀ z ∈ Omega, ∃ cost : ℝ,
        H.regularizedCost first last hle T Bfloor 0 (Real.sqrt (T - z.2)) p z.1 =
          (cost : WithTop ℝ) ∧ 2 * Real.sqrt (T - z.2) * cost ≤ Aphys z) ∧
      H.regularizedCost first last hle T Bfloor 0
        (Real.sqrt (T - (T - v ^ 2))) p q = (L : WithTop ℝ) ∧
      gradientFun g (fun y => Aphys (y, T - v ^ 2)) q = (2 * v) • V ∧
      HasDerivAt (fun s => Aphys (q, s))
        (-L / v - 2 * v ^ 2 * R + g.inner q V V / 2) (T - v ^ 2) ∧
      laplacian (LeviCivita g) g (fun y => Aphys (y, T - v ^ 2)) q =
        2 * v * laplacian (LeviCivita g) g (fun y => F (y, v)) q ∧
      -6 - 2 * v * epsilon <
        deriv (fun s => Aphys (q, s)) (T - v ^ 2) -
          laplacian (LeviCivita g) g (fun y => Aphys (y, T - v ^ 2)) q := by
  intro jf jl p q L g V R U F hU hqU hF hcontact hcost hupper
    hgradient hclock epsilon htrace Omega Aphys
  have hback : T - (T - v ^ 2) = v ^ 2 := by ring
  have hroot : Real.sqrt (T - (T - v ^ 2)) = v := by
    rw [hback, Real.sqrt_sq hv.le]
  have hOmega : IsOpen Omega :=
    (isOpen_lt continuous_snd continuous_const).inter
      ((isOpen_Ioo.preimage continuous_snd).inter
        (hU.preimage (continuous_fst.prodMk
          (Real.continuous_sqrt.comp (continuous_const.sub continuous_snd)))))
  have hqOmega : (q, T - v ^ 2) ∈ Omega := by
    refine ⟨?_, hpast, ?_⟩
    · nlinarith [sq_pos_of_pos hv]
    · simpa only [hroot] using hqU
  have hA : ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Aphys Omega := by
    intro z hz
    have hsqrt : ContMDiffAt (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2
        (fun z : (H.stage first).Carrier × ℝ => Real.sqrt (T - z.2)) z :=
      (Real.contDiffAt_sqrt (ne_of_gt (sub_pos.mpr hz.1))).contMDiffAt.comp z
        (contMDiffAt_const.sub contMDiffAt_snd)
    have hmap : ContMDiffAt (ThreeModel.prod 𝓘(ℝ, ℝ))
        (ThreeModel.prod 𝓘(ℝ, ℝ)) 2
        (fun z : (H.stage first).Carrier × ℝ => (z.1, Real.sqrt (T - z.2))) z :=
      contMDiffAt_fst.prodMk hsqrt
    have hcomp := (hF.contMDiffAt (hU.mem_nhds hz.2.2)).comp z hmap
    exact ((contMDiffAt_const.mul hsqrt).mul hcomp).contMDiffWithinAt
  have hvalue : Aphys (q, T - v ^ 2) = 2 * v * L := by
    change 2 * Real.sqrt (T - (T - v ^ 2)) *
      F (q, Real.sqrt (T - (T - v ^ 2))) = _
    rw [hroot, hcontact]
  have hnear : ∀ z ∈ Omega, ∃ cost : ℝ,
      H.regularizedCost first last hle T Bfloor 0 (Real.sqrt (T - z.2)) p z.1 =
        (cost : WithTop ℝ) ∧ 2 * Real.sqrt (T - z.2) * cost ≤ Aphys z := by
    intro z hz
    have hc := hupper (z.1, Real.sqrt (T - z.2)) hz.2.2
    have hfinite : H.regularizedCost first last hle T Bfloor 0
        (Real.sqrt (T - z.2)) p z.1 ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hc
    obtain ⟨cost, heq⟩ := WithTop.ne_top_iff_exists.mp hfinite
    refine ⟨cost, heq.symm, ?_⟩
    rw [← heq] at hc
    have hreal : cost ≤ F (z.1, Real.sqrt (T - z.2)) := WithTop.coe_le_coe.mp hc
    exact mul_le_mul_of_nonneg_left hreal
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hslice (y : (H.stage first).Carrier) (hy : (y, v) ∈ U) :
      ContMDiffAt ThreeModel 𝓘(ℝ, ℝ) 2 (fun y => F (y, v)) y :=
    (hF.contMDiffAt (hU.mem_nhds hy)).comp y
      (contMDiffAt_id.prodMk contMDiffAt_const)
  have hmd : ∀ᶠ y in 𝓝 q, MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ)
      (fun y => F (y, v)) y := by
    filter_upwards [(hU.preimage (continuous_id.prodMk continuous_const)).mem_nhds hqU]
      with y hy
    exact (hslice y hy).mdifferentiableAt (by norm_num)
  have hgradMD := (gradientFun_contMDiffAt_one g (hslice q hqU)).mdifferentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hscaledSlice : (fun y => Aphys (y, T - v ^ 2)) =
      (2 * v) • (fun y => F (y, v)) := by
    funext y
    change 2 * Real.sqrt (T - (T - v ^ 2)) *
      F (y, Real.sqrt (T - (T - v ^ 2))) = 2 * v * F (y, v)
    rw [hroot]
  have hgrad : gradientFun g (fun y => Aphys (y, T - v ^ 2)) q = (2 * v) • V := by
    rw [hscaledSlice, gradientFun_const_smul g (2 * v) hmd.self_of_nhds, hgradient]
  have hlap : laplacian (LeviCivita g) g (fun y => Aphys (y, T - v ^ 2)) q =
      2 * v * laplacian (LeviCivita g) g (fun y => F (y, v)) q := by
    rw [hscaledSlice]
    exact laplacian_smul_at (LeviCivita g) g (2 * v) hmd hgradMD
  have hw : HasDerivAt (fun s : ℝ => Real.sqrt (T - s))
      (-1 / (2 * v)) (T - v ^ 2) := by
    have hs : HasDerivAt (fun s : ℝ => T - s) (-1) (T - v ^ 2) :=
      (hasDerivAt_id (T - v ^ 2)).const_sub T
    simpa only [hroot] using hs.sqrt (by rw [hback]; exact ne_of_gt (sq_pos_of_pos hv))
  have hcomp := hclock.comp_of_eq (T - v ^ 2) hw hroot.symm
  have hproduct := (hw.const_mul 2).mul hcomp
  have hderiv : HasDerivAt (fun s => Aphys (q, s))
      (-L / v - 2 * v ^ 2 * R + g.inner q V V / 2) (T - v ^ 2) := by
    apply hproduct.congr_deriv
    simp only [Function.comp_apply, hroot, hcontact]
    field_simp [hv.ne']
    ring
  have hcancel : 2 * v *
      (3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + epsilon) =
      (-L / v - 2 * v ^ 2 * R + g.inner q V V / 2) + 6 + 2 * v * epsilon := by
    field_simp [hv.ne']
    ring
  have hheat : -6 - 2 * v * epsilon <
      deriv (fun s => Aphys (q, s)) (T - v ^ 2) -
        laplacian (LeviCivita g) g (fun y => Aphys (y, T - v ^ 2)) q := by
    have hscaled := mul_lt_mul_of_pos_left htrace (mul_pos (by norm_num : (0 : ℝ) < 2) hv)
    rw [hcancel] at hscaled
    rw [hderiv.deriv, hlap]
    linarith
  refine ⟨hOmega, hqOmega, hA, hvalue, hnear, ?_, hgrad, hderiv, hlap, hheat⟩
  simpa only [hroot] using hcost

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
