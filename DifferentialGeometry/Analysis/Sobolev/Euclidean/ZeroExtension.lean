import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation

noncomputable section

open MeasureTheory

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private noncomputable def zeroExtendWitness
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    {v : E → ℝ} (hv0 : MemH01 v W)
    (hv : MemW1pWitness 2 v W) :
    MemW1pWitness 2 (W.indicator v) Omega where
  memLp := by
    have hglobal : MemLp (W.indicator v) 2 (volume : Measure E) :=
      (memLp_indicator_iff_restrict hW.measurableSet).mpr hv.memLp
    exact hglobal.restrict Omega
  weakGrad := fun x => WithLp.toLp 2 fun i => W.indicator (fun y => hv.weakGrad y i) x
  weakGrad_component_memLp := by
    intro i
    have hglobal : MemLp (W.indicator (fun y => hv.weakGrad y i)) 2
        (volume : Measure E) :=
      (memLp_indicator_iff_restrict hW.measurableSet).mpr (hv.weakGrad_component_memLp i)
    exact hglobal.restrict Omega
  isWeakGrad := by
    intro i
    let : NeZero d := ⟨Nat.ne_zero_of_lt i.isLt⟩
    let hv0Real : MemW01p (ENNReal.ofReal (2 : ℝ)) v W := by simpa using hv0
    let hvReal : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) v W :=
      { memLp := by simpa using hv.memLp
        weakGrad := hv.weakGrad
        weakGrad_component_memLp := by
          intro j
          simpa using hv.weakGrad_component_memLp j
        isWeakGrad := hv.isWeakGrad }
    let hExt := zeroExtendMemW1pWitnessP hW (p := 2) (by norm_num) hv0Real hvReal
    exact (hExt.restrict hOmega (Set.subset_univ Omega)).isWeakGrad i

@[simp] private theorem zeroExtendWitness_weakGrad_apply
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    {v : E → ℝ} (hv0 : MemH01 v W)
    (hv : MemW1pWitness 2 v W) (x : E) (i : Fin d) :
    (zeroExtendWitness hOmega hW hv0 hv).weakGrad x i =
      W.indicator (fun y => hv.weakGrad y i) x := rfl

theorem MemH01.indicator_of_subset
    {Omega W : Set E} (hOmega : IsOpen Omega) (hW : IsOpen W)
    (hsub : W ⊆ Omega) {v : E → ℝ}
    (hv0 : MemH01 v W) :
    MemH01 (W.indicator v) Omega := by
  classical
  rcases hv0 with
    ⟨hv_mem, hw, phi, hphi_smooth, hphi_compact, hphi_sub,
      hphi_fun, hphi_grad⟩
  let hv0' : MemH01 v W :=
    ⟨hv_mem, hw, phi, hphi_smooth, hphi_compact, hphi_sub,
      hphi_fun, hphi_grad⟩
  let hExt : MemW1pWitness 2 (W.indicator v) Omega :=
    zeroExtendWitness (d := d) hOmega hW hv0' hw
  refine ⟨hExt.memW1p, hExt, phi, hphi_smooth, hphi_compact, ?_, ?_, ?_⟩
  · intro n
    exact (hphi_sub n).trans hsub
  · have hEq :
        (fun n => eLpNorm (fun x => phi n x - W.indicator v x) 2
          ((volume : Measure E).restrict Omega)) =
        fun n => eLpNorm (fun x => phi n x - v x) 2
          ((volume : Measure E).restrict W) := by
      funext n
      have hFn :
          (fun x => phi n x - W.indicator v x) =
            W.indicator (fun x => phi n x - v x) := by
        funext x
        by_cases hx : x ∈ W
        · simp [hx]
        · have hphi_zero : phi n x = 0 :=
            zero_outside_of_tsupport_subset (hphi_sub n) hx
          simp [hx, hphi_zero]
      rw [hFn, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := (volume : Measure E).restrict Omega) hW.measurableSet]
      rw [Measure.restrict_restrict_of_subset hsub]
    rw [hEq]
    exact hphi_fun
  · intro i
    have hEq :
        (fun n => eLpNorm
          (fun x => (fderiv ℝ (phi n) x) (EuclideanSpace.single i 1) -
            hExt.weakGrad x i) 2
          ((volume : Measure E).restrict Omega)) =
        fun n => eLpNorm
          (fun x => (fderiv ℝ (phi n) x) (EuclideanSpace.single i 1) -
            hw.weakGrad x i) 2
          ((volume : Measure E).restrict W) := by
      funext n
      have hFn :
          (fun x => (fderiv ℝ (phi n) x) (EuclideanSpace.single i 1) -
            hExt.weakGrad x i) =
            W.indicator (fun x =>
              (fderiv ℝ (phi n) x) (EuclideanSpace.single i 1) -
                hw.weakGrad x i) := by
        funext x
        by_cases hx : x ∈ W
        · simp [hExt, zeroExtendWitness_weakGrad_apply, hx]
        · have hdx :
              (fderiv ℝ (phi n) x) (EuclideanSpace.single i 1) = 0 :=
            zero_outside_of_tsupport_subset
              ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i (1 : ℝ))).trans
                (hphi_sub n)) hx
          simp [hExt, zeroExtendWitness_weakGrad_apply, hx, hdx]
      rw [hFn, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := (volume : Measure E).restrict Omega) hW.measurableSet]
      rw [Measure.restrict_restrict_of_subset hsub]
    rw [hEq]
    exact hphi_grad i

end DeGiorgi
