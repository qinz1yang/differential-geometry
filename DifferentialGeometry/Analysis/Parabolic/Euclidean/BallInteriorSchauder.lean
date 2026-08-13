import DifferentialGeometry.Analysis.Parabolic.Euclidean.CutoffClassicalSchauder
import DifferentialGeometry.Analysis.Parabolic.Euclidean.CutoffGauge
import DifferentialGeometry.Analysis.Schauder.ParabolicBallCutoff

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def parabolicBallInteriorSchauderConst
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (aTime t₀ t₁ bTime r R : Real)
    (Ksource Kcomm Bsource Bcomm X : NNReal)
    (Ka omega : n → n → NNReal) (T : Real) : NNReal :=
  spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
    (parabolicCutoffSourceHolderConst
        (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
        Ksource Kcomm 1 Bsource +
      X * parabolicMatrixFreezeHolderConst Ka omega)
    (parabolicCutoffSourceSupConst 1 Bsource Bcomm +
      X * parabolicMatrixFreezeSupConst omega) T

def parabolicBallInteriorAbsorbedSchauderConst
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (aTime t₀ t₁ bTime r R : Real)
    (Ksource Kcomm Bsource Bcomm : NNReal)
    (Ka omega : n → n → NNReal) (T : Real) : NNReal :=
  spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
      (parabolicCutoffSourceHolderConst
        (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
        Ksource Kcomm 1 Bsource)
      (parabolicCutoffSourceSupConst 1 Bsource Bcomm) T /
    (1 - spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T)

omit [Nonempty n] in
theorem parabolicBallInteriorAbsorbedSchauderConst_add
    {alpha : NNReal} (halpha1 : alpha < 1)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (aTime t₀ t₁ bTime r R : Real)
    (Ksource₁ Ksource₂ Kcomm₁ Kcomm₂ Bsource₁ Bsource₂ Bcomm₁ Bcomm₂ : NNReal)
    (Ka omega : n → n → NNReal) {T : Real} (hT : 0 ≤ T) :
    parabolicBallInteriorAbsorbedSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R (Ksource₁ + Ksource₂) (Kcomm₁ + Kcomm₂)
        (Bsource₁ + Bsource₂) (Bcomm₁ + Bcomm₂) Ka omega T =
      parabolicBallInteriorAbsorbedSchauderConst a p0 hA alpha
          aTime t₀ t₁ bTime r R Ksource₁ Kcomm₁ Bsource₁ Bcomm₁ Ka omega T +
        parabolicBallInteriorAbsorbedSchauderConst a p0 hA alpha
          aTime t₀ t₁ bTime r R Ksource₂ Kcomm₂ Bsource₂ Bcomm₂ Ka omega T := by
  unfold parabolicBallInteriorAbsorbedSchauderConst
  rw [show parabolicCutoffSourceHolderConst
      (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
      (Ksource₁ + Ksource₂) (Kcomm₁ + Kcomm₂) 1 (Bsource₁ + Bsource₂) =
    parabolicCutoffSourceHolderConst
        (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
        Ksource₁ Kcomm₁ 1 Bsource₁ +
      parabolicCutoffSourceHolderConst
        (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
        Ksource₂ Kcomm₂ 1 Bsource₂ by
    unfold parabolicCutoffSourceHolderConst
    ring]
  rw [show parabolicCutoffSourceSupConst 1
      (Bsource₁ + Bsource₂) (Bcomm₁ + Bcomm₂) =
    parabolicCutoffSourceSupConst 1 Bsource₁ Bcomm₁ +
      parabolicCutoffSourceSupConst 1 Bsource₂ Bcomm₂ by
    unfold parabolicCutoffSourceSupConst
    ring]
  rw [spdHeatPotentialSchauderConst_add halpha1 _ hA _ _ _ _ hT]
  rw [add_div]

omit [Nonempty n] in
theorem parabolicBallInteriorAbsorbedSchauderConst_nnreal_mul
    (d alpha : NNReal)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (aTime t₀ t₁ bTime r R : Real)
    (Ksource Kcomm Bsource Bcomm : NNReal)
    (Ka omega : n → n → NNReal) (T : Real) :
    parabolicBallInteriorAbsorbedSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R (d * Ksource) (d * Kcomm)
        (d * Bsource) (d * Bcomm) Ka omega T =
      d * parabolicBallInteriorAbsorbedSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm Ka omega T := by
  unfold parabolicBallInteriorAbsorbedSchauderConst
  rw [show parabolicCutoffSourceHolderConst
      (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
      (d * Ksource) (d * Kcomm) 1 (d * Bsource) =
    d * parabolicCutoffSourceHolderConst
      (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
      Ksource Kcomm 1 Bsource by
    unfold parabolicCutoffSourceHolderConst
    ring]
  rw [show parabolicCutoffSourceSupConst 1 (d * Bsource) (d * Bcomm) =
      d * parabolicCutoffSourceSupConst 1 Bsource Bcomm by
    unfold parabolicCutoffSourceSupConst
    ring]
  rw [spdHeatPotentialSchauderConst_nnreal_mul]
  ring

def parabolicBallCutoffOperatorCommutatorSupConst
    (aTime t₀ t₁ bTime r R : Real) (A : n → n → NNReal)
    (Mdu Mu : NNReal) : NNReal :=
  parabolicCutoffOperatorCommutatorSupConst A
    (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
    (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
    (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu

def parabolicBallCutoffOperatorCommutatorHolderConst
    (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (A Ka : n → n → NNReal) (Kdu Ku Mdu Mu : NNReal) : NNReal :=
  parabolicCutoffOperatorCommutatorHolderConst A Ka
    (parabolicBallCutoffTimeDerivativeHolderConst
      aTime t₀ t₁ bTime r R)
    (parabolicBallCutoffSpatialFDerivHolderConst
      aTime t₀ t₁ bTime r R)
    Kdu
    (parabolicBallCutoffSpatialFDeriv2HolderConst
      aTime t₀ t₁ bTime center hr hrR)
    Ku (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
    (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
    (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] [CompleteSpace F] in
theorem parabolicBallCutoffOperatorCommutatorSupConst_add
    (aTime t₀ t₁ bTime r R : Real) (A : n → n → NNReal)
    (Mdu₁ Mdu₂ Mu₁ Mu₂ : NNReal) :
    parabolicBallCutoffOperatorCommutatorSupConst aTime t₀ t₁ bTime r R A
        (Mdu₁ + Mdu₂) (Mu₁ + Mu₂) =
      parabolicBallCutoffOperatorCommutatorSupConst
          aTime t₀ t₁ bTime r R A Mdu₁ Mu₁ +
        parabolicBallCutoffOperatorCommutatorSupConst
          aTime t₀ t₁ bTime r R A Mdu₂ Mu₂ := by
  unfold parabolicBallCutoffOperatorCommutatorSupConst
  exact parabolicCutoffOperatorCommutatorSupConst_add (n := n) A
    (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
    (parabolicBallCutoffSpatialFDerivSupConst r R)
    (parabolicBallCutoffSpatialFDeriv2SupConst r R)
    Mdu₁ Mdu₂ Mu₁ Mu₂

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] [CompleteSpace F] in
theorem parabolicBallCutoffOperatorCommutatorSupConst_nnreal_mul
    (d : NNReal) (aTime t₀ t₁ bTime r R : Real)
    (A : n → n → NNReal) (Mdu Mu : NNReal) :
    parabolicBallCutoffOperatorCommutatorSupConst aTime t₀ t₁ bTime r R A
        (d * Mdu) (d * Mu) =
      d * parabolicBallCutoffOperatorCommutatorSupConst
        aTime t₀ t₁ bTime r R A Mdu Mu := by
  unfold parabolicBallCutoffOperatorCommutatorSupConst
  exact parabolicCutoffOperatorCommutatorSupConst_nnreal_mul (n := n) d A
    (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
    (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
    (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] [CompleteSpace F] in
theorem parabolicBallCutoffOperatorCommutatorHolderConst_add
    (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (A Ka : n → n → NNReal)
    (Kdu₁ Kdu₂ Ku₁ Ku₂ Mdu₁ Mdu₂ Mu₁ Mu₂ : NNReal) :
    parabolicBallCutoffOperatorCommutatorHolderConst aTime t₀ t₁ bTime
        center hr hrR A Ka (Kdu₁ + Kdu₂) (Ku₁ + Ku₂)
        (Mdu₁ + Mdu₂) (Mu₁ + Mu₂) =
      parabolicBallCutoffOperatorCommutatorHolderConst aTime t₀ t₁ bTime
          center hr hrR A Ka Kdu₁ Ku₁ Mdu₁ Mu₁ +
        parabolicBallCutoffOperatorCommutatorHolderConst aTime t₀ t₁ bTime
          center hr hrR A Ka Kdu₂ Ku₂ Mdu₂ Mu₂ := by
  unfold parabolicBallCutoffOperatorCommutatorHolderConst
  exact parabolicCutoffOperatorCommutatorHolderConst_add
    (n := n) A Ka
    (parabolicBallCutoffTimeDerivativeHolderConst aTime t₀ t₁ bTime r R)
    (parabolicBallCutoffSpatialFDerivHolderConst aTime t₀ t₁ bTime r R)
    (parabolicBallCutoffSpatialFDeriv2HolderConst
      aTime t₀ t₁ bTime center hr hrR)
    (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
    (parabolicBallCutoffSpatialFDerivSupConst r R)
    (parabolicBallCutoffSpatialFDeriv2SupConst r R)
    Kdu₁ Kdu₂ Ku₁ Ku₂ Mdu₁ Mdu₂ Mu₁ Mu₂

omit [DecidableEq n] [Nonempty n] [NormedAddCommGroup F]
  [NormedSpace Real F] [CompleteSpace F] in
theorem parabolicBallCutoffOperatorCommutatorHolderConst_nnreal_mul
    (d : NNReal) (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (A Ka : n → n → NNReal)
    (Kdu Ku Mdu Mu : NNReal) :
    parabolicBallCutoffOperatorCommutatorHolderConst aTime t₀ t₁ bTime
        center hr hrR A Ka (d * Kdu) (d * Ku) (d * Mdu) (d * Mu) =
      d * parabolicBallCutoffOperatorCommutatorHolderConst aTime t₀ t₁ bTime
        center hr hrR A Ka Kdu Ku Mdu Mu := by
  unfold parabolicBallCutoffOperatorCommutatorHolderConst
  exact parabolicCutoffOperatorCommutatorHolderConst_nnreal_mul
    (n := n) d A Ka
    (parabolicBallCutoffTimeDerivativeHolderConst aTime t₀ t₁ bTime r R)
    (parabolicBallCutoffSpatialFDerivHolderConst aTime t₀ t₁ bTime r R)
    Kdu (parabolicBallCutoffSpatialFDeriv2HolderConst
      aTime t₀ t₁ bTime center hr hrR) Ku
    (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
    (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
    (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu

def parabolicBallCutoffC2HolderGaugeConst
    (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Ku KdtimeU Kdu Kd2u Mu MdtimeU Mdu Md2u : NNReal) : NNReal :=
  parabolicCutoffC2HolderGaugeConst
    (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
    (parabolicBallCutoffTimeDerivativeHolderConst
      aTime t₀ t₁ bTime r R)
    (parabolicBallCutoffSpatialFDerivHolderConst
      aTime t₀ t₁ bTime r R)
    (parabolicBallCutoffSpatialFDeriv2HolderConst
      aTime t₀ t₁ bTime center hr hrR)
    Ku KdtimeU Kdu Kd2u 1
    (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
    (parabolicBallCutoffSpatialFDerivSupConst r R)
    (parabolicBallCutoffSpatialFDeriv2SupConst r R)
    Mu MdtimeU Mdu Md2u

def parabolicVariableCoefficientBallInteriorSchauderConst
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Ksource Ku KdtimeU Kdu Kd2u Bsource Mu MdtimeU Mdu Md2u : NNReal)
    (A Ka omega : n → n → NNReal) (T : Real) : NNReal :=
  parabolicBallInteriorSchauderConst a p0 hA alpha
    aTime t₀ t₁ bTime r R Ksource
    (parabolicBallCutoffOperatorCommutatorHolderConst
      aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
    Bsource
    (parabolicBallCutoffOperatorCommutatorSupConst
      aTime t₀ t₁ bTime r R A Mdu Mu)
    (parabolicBallCutoffC2HolderGaugeConst
      aTime t₀ t₁ bTime center hr hrR
      Ku KdtimeU Kdu Kd2u Mu MdtimeU Mdu Md2u)
    Ka omega T

def parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (alpha : NNReal) (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Ksource Kdu Ku Bsource Mdu Mu : NNReal)
    (A Ka omega : n → n → NNReal) (T : Real) : NNReal :=
  parabolicBallInteriorAbsorbedSchauderConst a p0 hA alpha
    aTime t₀ t₁ bTime r R Ksource
    (parabolicBallCutoffOperatorCommutatorHolderConst
      aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
    Bsource
    (parabolicBallCutoffOperatorCommutatorSupConst
      aTime t₀ t₁ bTime r R A Mdu Mu)
    Ka omega T

omit [Nonempty n] in
theorem parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst_add
    {alpha : NNReal} (halpha1 : alpha < 1)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Ksource₁ Ksource₂ Kdu₁ Kdu₂ Ku₁ Ku₂ Bsource₁ Bsource₂
      Mdu₁ Mdu₂ Mu₁ Mu₂ : NNReal)
    (A Ka omega : n → n → NNReal) {T : Real} (hT : 0 ≤ T) :
    parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (Ksource₁ + Ksource₂) (Kdu₁ + Kdu₂) (Ku₁ + Ku₂)
        (Bsource₁ + Bsource₂) (Mdu₁ + Mdu₂) (Mu₁ + Mu₂)
        A Ka omega T =
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Ksource₁ Kdu₁ Ku₁ Bsource₁ Mdu₁ Mu₁ A Ka omega T +
        parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
          a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
          Ksource₂ Kdu₂ Ku₂ Bsource₂ Mdu₂ Mu₂ A Ka omega T := by
  unfold parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
  rw [parabolicBallCutoffOperatorCommutatorHolderConst_add,
    parabolicBallCutoffOperatorCommutatorSupConst_add]
  exact parabolicBallInteriorAbsorbedSchauderConst_add halpha1
    a p0 hA aTime t₀ t₁ bTime r R Ksource₁ Ksource₂ _ _
    Bsource₁ Bsource₂ _ _ Ka omega hT

omit [Nonempty n] in
theorem parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst_nnreal_mul
    (d alpha : NNReal)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (aTime t₀ t₁ bTime : Real) (center : Euc n)
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (Ksource Kdu Ku Bsource Mdu Mu : NNReal)
    (A Ka omega : n → n → NNReal) (T : Real) :
    parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        (d * Ksource) (d * Kdu) (d * Ku) (d * Bsource) (d * Mdu) (d * Mu)
        A Ka omega T =
      d * parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        Ksource Kdu Ku Bsource Mdu Mu A Ka omega T := by
  unfold parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
  rw [parabolicBallCutoffOperatorCommutatorHolderConst_nnreal_mul,
    parabolicBallCutoffOperatorCommutatorSupConst_nnreal_mul]
  exact parabolicBallInteriorAbsorbedSchauderConst_nnreal_mul
    d alpha a p0 hA aTime t₀ t₁ bTime r R Ksource _ Bsource _ Ka omega T

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem eParabolicC2HolderGaugeOn_parabolicBallCutoff_le
    {J : Set Real} {alpha Ku KdtimeU Kdu Kd2u Mu MdtimeU Mdu Md2u : NNReal}
    (halpha1 : alpha ≤ 1)
    (aTime t₀ t₁ bTime : Real) (hat₀ : aTime < t₀)
    (ht₀t₁ : t₀ ≤ t₁) (ht₁b : t₁ < bTime)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ J, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p, p ∈ parabolicCylinder J Set.univ →
      ‖d2u p.time p.space‖ ≤ Md2u) :
    eParabolicC2HolderGaugeOn alpha (parabolicCylinder J Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤
      parabolicBallCutoffC2HolderGaugeConst
        aTime t₀ t₁ bTime center hr hrR
        Ku KdtimeU Kdu Kd2u Mu MdtimeU Mdu Md2u := by
  let Q := parabolicCylinder J (Set.univ : Set (Euc n))
  let chi : ParabolicPoint (Euc n) → Real := fun p ↦
    parabolicBallCutoff
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  let dtimeChi : ParabolicPoint (Euc n) → Real := fun p ↦
    parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  let dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real := fun p ↦
    parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  let d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real := fun p ↦
    parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  let dtimeUPoint : ParabolicPoint (Euc n) → F := fun p ↦
    dtimeU p.time p.space
  let duPoint : ParabolicPoint (Euc n) → Euc n →L[Real] F := fun p ↦
    du p.time p.space
  let d2uPoint : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F := fun p ↦ d2u p.time p.space
  have hchiSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ chi (parabolicPoint p.time y))
        (dchi (parabolicPoint p.time x)) x := by
    intro p _hp x
    exact parabolicBallCutoff_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time x
  have hdchiSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ dchi (parabolicPoint p.time y))
        (d2chi (parabolicPoint p.time x)) x := by
    intro p _hp x
    exact parabolicBallCutoffSpatialFDeriv_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time x
  have huSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (u p.time) (duPoint (parabolicPoint p.time x)) x := by
    intro p hp x
    exact hu p.time hp.1 x
  have hduSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ duPoint (parabolicPoint p.time y))
        (d2uPoint (parabolicPoint p.time x)) x := by
    intro p hp x
    exact hdu p.time hp.1 x
  have hchiTime : ∀ p ∈ Q,
      HasDerivAt (fun t ↦ chi (parabolicPoint t p.space))
        (dtimeChi p) p.time := by
    intro p _hp
    simpa only [chi, dtimeChi, parabolicPoint_time,
      parabolicPoint_space, parabolicPoint_time_space,
      BoundedContinuousFunction.evalCLM_apply] using
      (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time
          (parabolicBallCutoff_hasDerivAt
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time)
  have huTimePoint : ∀ p ∈ Q,
      HasDerivAt (fun t ↦ u t p.space) (dtimeUPoint p) p.time := by
    intro p hp
    simpa only [dtimeUPoint, BoundedContinuousFunction.evalCLM_apply] using
      (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time (huTime p.time hp.1)
  have hchiHolder := parabolicBallCutoff_holderWith_restrict
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  have hdtimeChiHolder := parabolicBallCutoffTimeDerivative_holderWith_restrict
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  have hdchiHolder := parabolicBallCutoffSpatialFDeriv_holderWith_restrict
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  have hd2chiHolder := parabolicBallCutoffSpatialFDeriv2_holderWith_restrict
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  apply eParabolicC2HolderGaugeOn_parabolicCutoffValue_le
    chi dtimeChi dchi d2chi (fun t x ↦ u t x)
      dtimeUPoint duPoint d2uPoint hchiSpatial hdchiSpatial
      huSpatial hduSpatial hchiTime huTimePoint
  · exact hchiHolder
  · exact hdtimeChiHolder
  · exact hdchiHolder
  · exact hd2chiHolder
  · exact huHolder
  · exact hdtimeUHolder
  · exact hduHolder
  · exact hd2uHolder
  · intro p _hp
    exact norm_parabolicBallCutoff_le_one
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  · intro p _hp
    exact norm_parabolicBallCutoffTimeDerivative_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  · intro p _hp
    exact norm_parabolicBallCutoffSpatialFDeriv_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  · intro p _hp
    exact norm_parabolicBallCutoffSpatialFDeriv2_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  · exact huNorm
  · exact hdtimeUNorm
  · exact hduNorm
  · exact hd2uNorm

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem eParabolicC2HolderGaugeOn_parabolicBallCutoff_le_of_local_solution
    {J : Set Real} {alpha Ku KdtimeU Kdu Kd2u Mu MdtimeU Mdu Md2u : NNReal}
    (halpha1 : alpha ≤ 1)
    (aTime t₀ t₁ bTime : Real) (hat₀ : aTime < t₀)
    (ht₀t₁ : t₀ ≤ t₁) (ht₁b : t₁ < bTime)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real → BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ J, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ J, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder J (Metric.ball center R)).restrict
        (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder J (Metric.ball center R)).restrict
        (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder J (Metric.ball center R)).restrict
        (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder J (Metric.ball center R)).restrict
        (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p, p ∈ parabolicCylinder J (Metric.ball center R) →
      ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p, p ∈ parabolicCylinder J (Metric.ball center R) →
      ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p, p ∈ parabolicCylinder J (Metric.ball center R) →
      ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p, p ∈ parabolicCylinder J (Metric.ball center R) →
      ‖d2u p.time p.space‖ ≤ Md2u) :
    eParabolicC2HolderGaugeOn alpha (parabolicCylinder J Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤
      parabolicBallCutoffC2HolderGaugeConst
        aTime t₀ t₁ bTime center hr hrR
        Ku KdtimeU Kdu Kd2u Mu MdtimeU Mdu Md2u := by
  let Q := parabolicCylinder J (Set.univ : Set (Euc n))
  let U := parabolicCylinder J (Metric.ball center R)
  let chi : ParabolicPoint (Euc n) → Real := fun p ↦
    parabolicBallCutoff
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  let dtimeChi : ParabolicPoint (Euc n) → Real := fun p ↦
    parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  let dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real := fun p ↦
    parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  let d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real := fun p ↦
    parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  let dtimeUPoint : ParabolicPoint (Euc n) → F := fun p ↦
    dtimeU p.time p.space
  let duPoint : ParabolicPoint (Euc n) → Euc n →L[Real] F := fun p ↦
    du p.time p.space
  let d2uPoint : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F := fun p ↦ d2u p.time p.space
  have hUQ : U ⊆ Q := fun p hp ↦ ⟨hp.1, Set.mem_univ p.space⟩
  have hQU : Q ∩ U = U := Set.inter_eq_right.mpr hUQ
  have hchiSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ chi (parabolicPoint p.time y))
        (dchi (parabolicPoint p.time x)) x := by
    intro p _hp x
    exact parabolicBallCutoff_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time x
  have hdchiSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ dchi (parabolicPoint p.time y))
        (d2chi (parabolicPoint p.time x)) x := by
    intro p _hp x
    exact parabolicBallCutoffSpatialFDeriv_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time x
  have huSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (u p.time) (duPoint (parabolicPoint p.time x)) x := by
    intro p hp x
    exact hu p.time hp.1 x
  have hduSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ duPoint (parabolicPoint p.time y))
        (d2uPoint (parabolicPoint p.time x)) x := by
    intro p hp x
    exact hdu p.time hp.1 x
  have hchiTime : ∀ p ∈ Q,
      HasDerivAt (fun t ↦ chi (parabolicPoint t p.space))
        (dtimeChi p) p.time := by
    intro p _hp
    simpa only [chi, dtimeChi, parabolicPoint_time,
      parabolicPoint_space, parabolicPoint_time_space,
      BoundedContinuousFunction.evalCLM_apply] using
      (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time
          (parabolicBallCutoff_hasDerivAt
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time)
  have huTimePoint : ∀ p ∈ Q,
      HasDerivAt (fun t ↦ u t p.space) (dtimeUPoint p) p.time := by
    intro p hp
    simpa only [dtimeUPoint, BoundedContinuousFunction.evalCLM_apply] using
      (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
        |>.comp_hasDerivAt p.time (huTime p.time hp.1)
  have hchiHolder := parabolicBallCutoff_holderWith_restrict
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  have hdtimeChiHolder := parabolicBallCutoffTimeDerivative_holderWith_restrict
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  have hdchiHolder := parabolicBallCutoffSpatialFDeriv_holderWith_restrict
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  have hd2chiHolder := parabolicBallCutoffSpatialFDeriv2_holderWith_restrict
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  apply eParabolicC2HolderGaugeOn_parabolicCutoffValue_le_of_eq_zero_outside
    (U := U) chi dtimeChi dchi d2chi (fun t x ↦ u t x)
      dtimeUPoint duPoint d2uPoint hchiSpatial hdchiSpatial
      huSpatial hduSpatial hchiTime huTimePoint
  · exact hchiHolder
  · exact hdtimeChiHolder
  · exact hdchiHolder
  · exact hd2chiHolder
  · rw [hQU]
    simpa only [U] using huHolder
  · rw [hQU]
    simpa only [U, dtimeUPoint] using hdtimeUHolder
  · rw [hQU]
    simpa only [U, duPoint] using hduHolder
  · rw [hQU]
    simpa only [U, d2uPoint] using hd2uHolder
  · intro p _hp _hpU
    exact norm_parabolicBallCutoff_le_one
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time p.space
  · intro p _hp _hpU
    exact norm_parabolicBallCutoffTimeDerivative_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time p.space
  · intro p _hp _hpU
    exact norm_parabolicBallCutoffSpatialFDeriv_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time p.space
  · intro p _hp _hpU
    exact norm_parabolicBallCutoffSpatialFDeriv2_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time p.space
  · intro p _hp hpU
    exact huNorm p (by simpa only [U] using hpU)
  · intro p _hp hpU
    exact hdtimeUNorm p (by simpa only [U] using hpU)
  · intro p _hp hpU
    exact hduNorm p (by simpa only [U] using hpU)
  · intro p _hp hpU
    exact hd2uNorm p (by simpa only [U] using hpU)
  · intro p hp hpU
    exact parabolicBallCutoff_eq_zero_of_space_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time
        (fun hspace ↦ hpU ⟨hp.1, hspace⟩)
  · intro p hp hpU
    exact parabolicBallCutoffTimeDerivative_eq_zero_of_space_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time
        (fun hspace ↦ hpU ⟨hp.1, hspace⟩)
  · intro p hp hpU
    exact parabolicBallCutoffSpatialFDeriv_eq_zero_of_space_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time
        (fun hspace ↦ hpU ⟨hp.1, hspace⟩)
  · intro p hp hpU
    exact parabolicBallCutoffSpatialFDeriv2_eq_zero_of_space_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR p.time
        (fun hspace ↦ hpU ⟨hp.1, hspace⟩)

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_parabolicBallCutoffOperatorCommutator_le
    {J : Set Real}
    (aTime t₀ t₁ bTime : Real) (hat₀ : aTime < t₀)
    (ht₀t₁ : t₀ ≤ t₁) (ht₁b : t₁ < bTime)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (Mdu Mu : NNReal)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder J Set.univ → ‖a i j p‖ ≤ A i j)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder J Set.univ → ‖du p‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder J Set.univ → ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n))
    (hp : p ∈ parabolicCylinder J Set.univ) :
    ‖parabolicCutoffOperatorCommutator a
      (fun q ↦ parabolicBallCutoffTimeDerivative
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      (fun q ↦ parabolicBallCutoffSpatialFDeriv
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      (fun q ↦ parabolicBallCutoffSpatialFDeriv2
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      u du p‖ ≤
        parabolicBallCutoffOperatorCommutatorSupConst
          aTime t₀ t₁ bTime r R A Mdu Mu := by
  apply norm_parabolicCutoffOperatorCommutator_le
    a
    (fun q ↦ parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    (fun q ↦ parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    (fun q ↦ parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    u du A (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
      (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
      (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu haNorm
  · intro q _hq
    exact norm_parabolicBallCutoffTimeDerivative_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · exact hduNorm
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv2_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · exact huNorm
  · exact hp

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem parabolicBallCutoffOperatorCommutator_holderWith_restrict
    {J : Set Real} {alpha Kdu Ku : NNReal}
    (halpha1 : alpha ≤ 1)
    (aTime t₀ t₁ bTime : Real) (hat₀ : aTime < t₀)
    (ht₀t₁ : t₀ ≤ t₁) (ht₁b : t₁ < bTime)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A Ka : n → n → NNReal) (Mdu Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder J Set.univ).restrict (a i j)))
    (hdu : HolderWith Kdu alpha
      ((parabolicCylinder J Set.univ).restrict du))
    (hu : HolderWith Ku alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder J Set.univ → ‖a i j p‖ ≤ A i j)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder J Set.univ → ‖du p‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder J Set.univ → ‖u p.time p.space‖ ≤ Mu) :
    HolderWith
      (parabolicBallCutoffOperatorCommutatorHolderConst
        aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
      alpha ((parabolicCylinder J Set.univ).restrict
        (parabolicCutoffOperatorCommutator a
          (fun q ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          u du)) := by
  apply parabolicCutoffOperatorCommutator_holderWith_restrict
    a
    (fun q ↦ parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    (fun q ↦ parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    (fun q ↦ parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space)
    u du A Ka (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
      (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
      (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu ha
  · exact parabolicBallCutoffTimeDerivative_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  · exact parabolicBallCutoffSpatialFDeriv_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  · exact hdu
  · exact parabolicBallCutoffSpatialFDeriv2_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  · exact hu
  · exact haNorm
  · intro q _hq
    exact norm_parabolicBallCutoffTimeDerivative_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · exact hduNorm
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv2_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  · exact huNorm

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_parabolicBallCutoffOperatorCommutator_le_of_local_solution
    {J : Set Real}
    (aTime t₀ t₁ bTime : Real) (hat₀ : aTime < t₀)
    (ht₀t₁ : t₀ ≤ t₁) (ht₁b : t₁ < bTime)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A : n → n → NNReal) (Mdu Mu : NNReal)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder J Set.univ → ‖a i j p‖ ≤ A i j)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder J (Metric.ball center R) → ‖du p‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder J (Metric.ball center R) →
        ‖u p.time p.space‖ ≤ Mu)
    (p : ParabolicPoint (Euc n))
    (hp : p ∈ parabolicCylinder J Set.univ) :
    ‖parabolicCutoffOperatorCommutator a
      (fun q ↦ parabolicBallCutoffTimeDerivative
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      (fun q ↦ parabolicBallCutoffSpatialFDeriv
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      (fun q ↦ parabolicBallCutoffSpatialFDeriv2
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      u du p‖ ≤
        parabolicBallCutoffOperatorCommutatorSupConst
          aTime t₀ t₁ bTime r R A Mdu Mu := by
  let Q := parabolicCylinder J (Set.univ : Set (Euc n))
  let U := parabolicCylinder J (Metric.ball center R)
  apply norm_parabolicCutoffOperatorCommutator_le_of_eq_zero_outside
    (Q := Q) (U := U) a
      (fun q ↦ parabolicBallCutoffTimeDerivative
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      (fun q ↦ parabolicBallCutoffSpatialFDeriv
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      (fun q ↦ parabolicBallCutoffSpatialFDeriv2
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      u du A (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
        (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
        (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu
  · exact haNorm
  · intro q _hq
    exact norm_parabolicBallCutoffTimeDerivative_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time q.space
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time q.space
  · intro q _hq hqU
    exact hduNorm q (by simpa only [U] using hqU)
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv2_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time q.space
  · intro q _hq hqU
    exact huNorm q (by simpa only [U] using hqU)
  · intro q hq hqU
    exact parabolicBallCutoffTimeDerivative_eq_zero_of_space_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time
        (fun hspace ↦ hqU ⟨hq.1, hspace⟩)
  · intro q hq hqU
    exact parabolicBallCutoffSpatialFDeriv_eq_zero_of_space_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time
        (fun hspace ↦ hqU ⟨hq.1, hspace⟩)
  · intro q hq hqU
    exact parabolicBallCutoffSpatialFDeriv2_eq_zero_of_space_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time
        (fun hspace ↦ hqU ⟨hq.1, hspace⟩)
  · exact hp

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem parabolicBallCutoffOperatorCommutator_holderWith_restrict_of_local_solution
    {J : Set Real} {alpha Kdu Ku : NNReal}
    (halpha1 : alpha ≤ 1)
    (aTime t₀ t₁ bTime : Real) (hat₀ : aTime < t₀)
    (ht₀t₁ : t₀ ≤ t₁) (ht₁b : t₁ < bTime)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (A Ka : n → n → NNReal) (Mdu Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder J Set.univ).restrict (a i j)))
    (hdu : HolderWith Kdu alpha
      ((parabolicCylinder J (Metric.ball center R)).restrict du))
    (hu : HolderWith Ku alpha
      ((parabolicCylinder J (Metric.ball center R)).restrict
        (fun p ↦ u p.time p.space)))
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder J Set.univ → ‖a i j p‖ ≤ A i j)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder J (Metric.ball center R) → ‖du p‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder J (Metric.ball center R) →
        ‖u p.time p.space‖ ≤ Mu) :
    HolderWith
      (parabolicBallCutoffOperatorCommutatorHolderConst
        aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
      alpha ((parabolicCylinder J Set.univ).restrict
        (parabolicCutoffOperatorCommutator a
          (fun q ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          u du)) := by
  let Q := parabolicCylinder J (Set.univ : Set (Euc n))
  let U := parabolicCylinder J (Metric.ball center R)
  have hUQ : U ⊆ Q := fun p hp ↦ ⟨hp.1, Set.mem_univ p.space⟩
  have hQU : Q ∩ U = U := Set.inter_eq_right.mpr hUQ
  apply parabolicCutoffOperatorCommutator_holderWith_restrict_of_eq_zero_outside
    (Q := Q) (U := U) a
      (fun q ↦ parabolicBallCutoffTimeDerivative
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      (fun q ↦ parabolicBallCutoffSpatialFDeriv
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      (fun q ↦ parabolicBallCutoffSpatialFDeriv2
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
          q.time q.space)
      u du A Ka (intervalCutoffDerivSupConst aTime t₀ t₁ bTime)
        (parabolicBallCutoffSpatialFDerivSupConst r R) Mdu
        (parabolicBallCutoffSpatialFDeriv2SupConst r R) Mu
  · exact ha
  · exact parabolicBallCutoffTimeDerivative_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  · exact parabolicBallCutoffSpatialFDeriv_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  · rw [hQU]
    simpa only [U] using hdu
  · exact parabolicBallCutoffSpatialFDeriv2_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR halpha1 J
  · rw [hQU]
    simpa only [U] using hu
  · exact haNorm
  · intro q _hq
    exact norm_parabolicBallCutoffTimeDerivative_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time q.space
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time q.space
  · intro q _hq hqU
    exact hduNorm q (by simpa only [U] using hqU)
  · intro q _hq
    exact norm_parabolicBallCutoffSpatialFDeriv2_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time q.space
  · intro q _hq hqU
    exact huNorm q (by simpa only [U] using hqU)
  · intro q hq hqU
    exact parabolicBallCutoffTimeDerivative_eq_zero_of_space_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time
        (fun hspace ↦ hqU ⟨hq.1, hspace⟩)
  · intro q hq hqU
    exact parabolicBallCutoffSpatialFDeriv_eq_zero_of_space_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time
        (fun hspace ↦ hqU ⟨hq.1, hspace⟩)
  · intro q hq hqU
    exact parabolicBallCutoffSpatialFDeriv2_eq_zero_of_space_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR q.time
        (fun hspace ↦ hqU ⟨hq.1, hspace⟩)

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_cutoff_source_estimates
    {alpha Ksource Kcomm Bsource Bcomm X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 ≤ aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (ht₁T : t₁ ≤ T)
    (hT : 0 ≤ T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hcommHolder : HolderWith Kcomm alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicCutoffOperatorCommutator a
          (fun p ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun p ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun p ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (hcommNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicCutoffOperatorCommutator a
          (fun q ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤ Bcomm)
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm X
        Ka omega T := by
  let chi := parabolicBallCutoff
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let dtimeChi := parabolicBallCutoffTimeDerivative
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let dchi := parabolicBallCutoffSpatialFDeriv
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let d2chi := parabolicBallCutoffSpatialFDeriv2
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let U := parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r)
  let W : Real → Euc n → F := fun t x ↦ chi t x • u t x
  have hchiTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt chi (dtimeChi s) s := by
    intro s _hs
    exact parabolicBallCutoff_hasDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s
  have hchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (chi s : Euc n → Real) (dchi s x) x := by
    intro s _hs x
    exact parabolicBallCutoff_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s x
  have hdchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (dchi s : Euc n → Euc n →L[Real] Real)
        (d2chi s x) x := by
    intro s _hs x
    exact parabolicBallCutoffSpatialFDeriv_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s x
  have hchiCont : Continuous chi := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (parabolicBallCutoff_hasDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s).continuousAt
  have hchi0 : chi 0 = 0 := by
    exact parabolicBallCutoff_eq_zero_of_time_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        (fun hmem ↦ (not_lt_of_ge haTime) hmem.1)
  have hchiHolder : HolderWith
      (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R) alpha
      (Q.restrict (fun p ↦ chi p.time p.space)) := by
    exact parabolicBallCutoff_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        halpha1.le (Icc (0 : Real) S)
  have hchiNorm : ∀ p, p ∈ Q → ‖chi p.time p.space‖ ≤ (1 : NNReal) := by
    intro p _hp
    exact norm_parabolicBallCutoff_le_one
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  have hraw : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) W ≤
        parabolicBallInteriorSchauderConst a p0 hA alpha
          aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm X
          Ka omega T := by
    simpa only [Q, chi, dtimeChi, dchi, d2chi, W,
      parabolicBallInteriorSchauderConst] using
      (parabolic_variable_coefficient_schauder_estimate_of_cutoff_source_estimates
        halpha0 halpha1 hT hTS a p0 hA chi dtimeChi dchi d2chi
        u dtimeU du d2u hchiTime huTime hchi hdchi hu hdu hchiCont huCont
        hchi0 hchiHolder hsourceHolder hcommHolder hchiNorm hsourceNorm
        hcommNorm Ka omega ha homega hcutoffGauge)
  have hUOpen : IsOpen U :=
    isOpen_parabolicCylinder isOpen_Ioo Metric.isOpen_ball
  have hUOut : U ⊆ parabolicCylinder (Ioc (0 : Real) T) Set.univ := by
    intro p hp
    exact ⟨⟨lt_of_le_of_lt haTime (hat₀.trans hp.1.1),
      hp.1.2.le.trans ht₁T⟩, Set.mem_univ p.space⟩
  have heq : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ W p.time p.space) U := by
    intro p hp
    change u p.time p.space = chi p.time p.space • u p.time p.space
    rw [show chi p.time p.space = 1 from
      parabolicBallCutoff_eq_one
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        ⟨hp.1.1.le, hp.1.2.le⟩ (Metric.ball_subset_closedBall hp.2), one_smul]
  calc
    eParabolicC2HolderGaugeOn alpha U (fun t x ↦ u t x) =
        eParabolicC2HolderGaugeOn alpha U W :=
      eParabolicC2HolderGaugeOn_congr_of_eqOn_open
        hUOpen Set.Subset.rfl heq alpha
    _ ≤ eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ) W :=
      eParabolicC2HolderGaugeOn_mono hUOut alpha W
    _ ≤ parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm X
        Ka omega T := hraw

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_cutoff_source_estimates_of_small_freeze_defect
    {alpha Ksource Kcomm Bsource Bcomm : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hcommHolder : HolderWith Kcomm alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicCutoffOperatorCommutator a
          (fun p ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun p ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun p ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              p.time p.space)
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (hcommNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicCutoffOperatorCommutator a
          (fun q ↦ parabolicBallCutoffTimeDerivative
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun q ↦ parabolicBallCutoffSpatialFDeriv2
            aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
              q.time q.space)
          (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤ Bcomm)
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (hcutoffFinite : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≠ ⊤)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicBallInteriorAbsorbedSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm
        Ka omega T := by
  let chi := parabolicBallCutoff
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let dtimeChi := parabolicBallCutoffTimeDerivative
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let dchi := parabolicBallCutoffSpatialFDeriv
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let d2chi := parabolicBallCutoffSpatialFDeriv2
    aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let QT := parabolicCylinder (Ioc (0 : Real) T) (Set.univ : Set (Euc n))
  let U := parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r)
  let W : Real → Euc n → F := fun t x ↦ chi t x • u t x
  have haTlt : aTime < T :=
    (hat₀.trans_le ht₀t₁).trans (ht₁b.trans hbT)
  have hT : 0 ≤ T := (haTime.trans haTlt).le
  have haT : aTime ≤ T := haTlt.le
  have hchiTime : ∀ s ∈ Icc (0 : Real) S,
      HasDerivAt chi (dtimeChi s) s := by
    intro s _hs
    exact parabolicBallCutoff_hasDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s
  have hchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (chi s : Euc n → Real) (dchi s x) x := by
    intro s _hs x
    exact parabolicBallCutoff_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s x
  have hdchi : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (dchi s : Euc n → Euc n →L[Real] Real)
        (d2chi s x) x := by
    intro s _hs x
    exact parabolicBallCutoffSpatialFDeriv_hasFDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s x
  have hchiCont : Continuous chi := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (parabolicBallCutoff_hasDerivAt
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR s).continuousAt
  have hchi0 : chi 0 = 0 := by
    exact parabolicBallCutoff_eq_zero_of_time_not_mem
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        (fun hmem ↦ (not_lt_of_ge haTime.le) hmem.1)
  have hchiHolder : HolderWith
      (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R) alpha
      (Q.restrict (fun p ↦ chi p.time p.space)) := by
    exact parabolicBallCutoff_holderWith_restrict
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        halpha1.le (Icc (0 : Real) S)
  have hchiNorm : ∀ p, p ∈ Q → ‖chi p.time p.space‖ ≤ (1 : NNReal) := by
    intro p _hp
    exact norm_parabolicBallCutoff_le_one
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        p.time p.space
  have hspatialSupport : ∀ j < 3, ∀ p,
      p.time ∈ Icc (0 : Real) S → p.time ∉ Ioo aTime bTime →
        parabolicSpatialJet j W p = 0 := by
    intro j _hj p _hp hpmem
    have hchiZero : chi p.time = 0 :=
      parabolicBallCutoff_eq_zero_of_time_not_mem
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR hpmem
    have hWZero : W p.time = 0 := by
      funext x
      change chi p.time x • u p.time x = 0
      rw [hchiZero]
      exact zero_smul Real (u p.time x)
    unfold parabolicSpatialJet
    rw [hWZero]
    change iteratedFDeriv Real j (fun _ : Euc n ↦ (0 : F)) p.space = 0
    rw [iteratedFDeriv_fun_zero]
    rfl
  have htimeSupport : ∀ p,
      p.time ∈ Icc (0 : Real) S → p.time ∉ Ioo aTime bTime →
        parabolicTimeDerivative W p = 0 := by
    intro p hp hpmem
    have hchiZero : chi p.time = 0 :=
      parabolicBallCutoff_eq_zero_of_time_not_mem
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR hpmem
    have hdtimeChiZero : dtimeChi p.time = 0 :=
      parabolicBallCutoffTimeDerivative_eq_zero_of_time_not_mem
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR hpmem
    have hchiTimePoint : HasDerivAt (fun t ↦ chi t p.space)
        (dtimeChi p.time p.space) p.time := by
      simpa only [BoundedContinuousFunction.evalCLM_apply] using
        (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
          |>.comp_hasDerivAt p.time (hchiTime p.time hp)
    have huTimePoint : HasDerivAt (fun t ↦ u t p.space)
        (dtimeU p.time p.space) p.time := by
      simpa only [BoundedContinuousFunction.evalCLM_apply] using
        (BoundedContinuousFunction.evalCLM Real p.space).hasFDerivAt
          |>.comp_hasDerivAt p.time (huTime p.time hp)
    have hproduct := parabolicTimeDerivative_cutoff
      (fun q ↦ chi q.time q.space) (fun q ↦ dtimeChi q.time q.space)
      (fun t x ↦ u t x) (fun q ↦ dtimeU q.time q.space) p
      (by simpa only [parabolicPoint_time, parabolicPoint_space,
        parabolicPoint_time_space] using hchiTimePoint)
      huTimePoint
    change parabolicTimeDerivative
      (parabolicCutoffValue (fun q ↦ chi q.time q.space)
        (fun t x ↦ u t x)) p = 0
    rw [hproduct]
    unfold parabolicCutoffTimeDerivative
    change chi p.time p.space • dtimeU p.time p.space +
      dtimeChi p.time p.space • u p.time p.space = 0
    rw [show chi p.time p.space = 0 by rw [hchiZero]; rfl,
      show dtimeChi p.time p.space = 0 by rw [hdtimeChiZero]; rfl]
    simp only [zero_smul, zero_add]
  have hlocalize : eParabolicC2HolderGaugeOn alpha Q W ≤
      eParabolicC2HolderGaugeOn alpha QT W := by
    exact eParabolicC2HolderGaugeOn_Icc_le_Ioc_of_time_support
      haTime haT hbT hTS.le alpha W hspatialSupport htimeSupport
  have hQTQ : QT ⊆ Q := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.trans hTS.le⟩, Set.mem_univ p.space⟩
  have hlocalFinite : eParabolicC2HolderGaugeOn alpha QT W ≠ ⊤ := by
    apply ne_of_lt
    exact (eParabolicC2HolderGaugeOn_mono hQTQ alpha W).trans_lt
      (lt_top_iff_ne_top.mpr (by simpa only [Q, W, chi] using hcutoffFinite))
  let X : NNReal :=
    (eParabolicC2HolderGaugeOn alpha QT W).toNNReal
  have hX : (X : ENNReal) = eParabolicC2HolderGaugeOn alpha QT W := by
    exact ENNReal.coe_toNNReal hlocalFinite
  have hcutoffGauge : eParabolicC2HolderGaugeOn alpha Q W ≤ X := by
    rw [hX]
    exact hlocalize
  have hraw : eParabolicC2HolderGaugeOn alpha QT W ≤
      spdHeatPotentialSchauderConst (fun i j ↦ a i j p0) hA alpha
        (parabolicCutoffSourceHolderConst
            (parabolicBallCutoffHolderConst aTime t₀ t₁ bTime r R)
            Ksource Kcomm 1 Bsource +
          X * parabolicMatrixFreezeHolderConst Ka omega)
        (parabolicCutoffSourceSupConst 1 Bsource Bcomm +
          X * parabolicMatrixFreezeSupConst omega) T := by
    simpa only [Q, QT, chi, dtimeChi, dchi, d2chi, W] using
      (parabolic_variable_coefficient_schauder_estimate_of_cutoff_source_estimates
        halpha0 halpha1 hT hTS a p0 hA chi dtimeChi dchi d2chi
        u dtimeU du d2u hchiTime huTime hchi hdchi hu hdu hchiCont huCont
        hchi0 hchiHolder hsourceHolder hcommHolder hchiNorm hsourceNorm
        hcommNorm Ka omega ha homega hcutoffGauge)
  have habsorb := parabolic_schauder_estimate_of_small_freeze_defect
    halpha1 hT (fun i j ↦ a i j p0) hA Ka omega W hraw hX.le hsmall
  have hUOpen : IsOpen U :=
    isOpen_parabolicCylinder isOpen_Ioo Metric.isOpen_ball
  have hUOut : U ⊆ QT := by
    intro p hp
    exact ⟨⟨haTime.trans (hat₀.trans hp.1.1),
      hp.1.2.le.trans (ht₁b.trans hbT).le⟩, Set.mem_univ p.space⟩
  have heq : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ W p.time p.space) U := by
    intro p hp
    change u p.time p.space = chi p.time p.space • u p.time p.space
    rw [show chi p.time p.space = 1 from
      parabolicBallCutoff_eq_one
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        ⟨hp.1.1.le, hp.1.2.le⟩ (Metric.ball_subset_closedBall hp.2), one_smul]
  calc
    eParabolicC2HolderGaugeOn alpha U (fun t x ↦ u t x) =
        eParabolicC2HolderGaugeOn alpha U W :=
      eParabolicC2HolderGaugeOn_congr_of_eqOn_open
        hUOpen Set.Subset.rfl heq alpha
    _ ≤ eParabolicC2HolderGaugeOn alpha QT W :=
      eParabolicC2HolderGaugeOn_mono hUOut alpha W
    _ ≤ parabolicBallInteriorAbsorbedSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource Kcomm Bsource Bcomm
        Ka omega T := by
      simpa only [parabolicBallInteriorAbsorbedSchauderConst] using habsorb

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_source_and_solution_estimates
    {alpha Ksource Kdu Ku Bsource Mdu Mu X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 ≤ aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (ht₁T : t₁ ≤ T)
    (hT : 0 ≤ T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖du p.time p.space‖ ≤ Mdu)
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖u p.time p.space‖ ≤ Mu)
    (hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤ X) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicBallInteriorSchauderConst a p0 hA alpha
        aTime t₀ t₁ bTime r R Ksource
        (parabolicBallCutoffOperatorCommutatorHolderConst
          aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
        Bsource
        (parabolicBallCutoffOperatorCommutatorSupConst
          aTime t₀ t₁ bTime r R A Mdu Mu)
        X Ka omega T := by
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let dtimeChi : ParabolicPoint (Euc n) → Real := fun q ↦
    parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  have hcommHolder : HolderWith
      (parabolicBallCutoffOperatorCommutatorHolderConst
        aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu)
      alpha (Q.restrict
        (parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))) := by
    exact parabolicBallCutoffOperatorCommutator_holderWith_restrict
      halpha1.le aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun p ↦ du p.time p.space)
      A Ka Mdu Mu ha hduHolder huHolder haNorm hduNorm huNorm
  have hcommNorm : ∀ p, p ∈ Q →
      ‖parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
        (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤
          parabolicBallCutoffOperatorCommutatorSupConst
            aTime t₀ t₁ bTime r R A Mdu Mu := by
    intro p hp
    exact norm_parabolicBallCutoffOperatorCommutator_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun q ↦ du q.time q.space)
      A Mdu Mu haNorm hduNorm huNorm p hp
  exact parabolic_variable_coefficient_ball_interior_schauder_estimate_of_cutoff_source_estimates
    halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b ht₁T hT hTS center hr hrR
    a p0 hA u dtimeU du d2u huTime hu hdu huCont hsourceHolder
    (by simpa only [Q, dtimeChi, dchi, d2chi] using hcommHolder)
    hsourceNorm (by simpa only [Q, dtimeChi, dchi, d2chi] using hcommNorm)
    Ka omega ha homega hcutoffGauge

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate
    {alpha Ksource Ku KdtimeU Kdu Kd2u Bsource Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 ≤ aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (ht₁T : t₁ ≤ T)
    (hT : 0 ≤ T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖d2u p.time p.space‖ ≤ Md2u) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicVariableCoefficientBallInteriorSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        Ksource Ku KdtimeU Kdu Kd2u Bsource Mu MdtimeU Mdu Md2u
        A Ka omega T := by
  let X := parabolicBallCutoffC2HolderGaugeConst
    aTime t₀ t₁ bTime center hr hrR
    Ku KdtimeU Kdu Kd2u Mu MdtimeU Mdu Md2u
  have hcutoffGauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Icc (0 : Real) S) Set.univ)
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤ X := by
    exact eParabolicC2HolderGaugeOn_parabolicBallCutoff_le
      halpha1.le aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      u dtimeU du d2u huTime hu hdu huHolder hdtimeUHolder
      hduHolder hd2uHolder huNorm hdtimeUNorm hduNorm hd2uNorm
  simpa only [parabolicVariableCoefficientBallInteriorSchauderConst, X] using
    (parabolic_variable_coefficient_ball_interior_schauder_estimate_of_source_and_solution_estimates
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b ht₁T hT hTS center hr hrR
      a p0 hA u dtimeU du d2u huTime hu hdu huCont hsourceHolder
      hsourceNorm A Ka omega ha homega haNorm hduHolder huHolder
      hduNorm huNorm hcutoffGauge)

theorem parabolic_variable_coefficient_ball_interior_schauder_estimate_of_small_freeze_defect
    {alpha Ksource Ku KdtimeU Kdu Kd2u Bsource Mu MdtimeU Mdu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {aTime t₀ t₁ bTime S T : Real}
    (haTime : 0 < aTime) (hat₀ : aTime < t₀) (ht₀t₁ : t₀ ≤ t₁)
    (ht₁b : t₁ < bTime) (hbT : bTime < T) (hTS : T < S)
    (center : Euc n) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (p0 : ParabolicPoint (Euc n))
    (hA : Matrix.PosDef (fun i j ↦ a i j p0))
    (u dtimeU : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Icc (0 : Real) S, HasDerivAt u (dtimeU s) s)
    (hu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Icc (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (huCont : Continuous u)
    (hsourceHolder : HolderWith Ksource alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (parabolicVariableMatrixOperator a (fun t x ↦ u t x))))
    (hsourceNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖parabolicVariableMatrixOperator a (fun t x ↦ u t x) p‖ ≤ Bsource)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict (a i j)))
    (homega : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p0 - a i j p‖ ≤ omega i j)
    (haNorm : ∀ i j p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖a i j p‖ ≤ A i j)
    (huHolder : HolderWith Ku alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ u p.time p.space)))
    (hdtimeUHolder : HolderWith KdtimeU alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ dtimeU p.time p.space)))
    (hduHolder : HolderWith Kdu alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ du p.time p.space)))
    (hd2uHolder : HolderWith Kd2u alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ d2u p.time p.space)))
    (huNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖dtimeU p.time p.space‖ ≤ MdtimeU)
    (hduNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖du p.time p.space‖ ≤ Mdu)
    (hd2uNorm : ∀ p,
      p ∈ parabolicCylinder (Icc (0 : Real) S) Set.univ →
        ‖d2u p.time p.space‖ ≤ Md2u)
    (hsmall : spdParabolicSchauderDefectConst
      (fun i j ↦ a i j p0) hA alpha Ka omega T < 1) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Ioo t₀ t₁) (Metric.ball center r))
        (fun t x ↦ u t x) ≤
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst
        a p0 hA alpha aTime t₀ t₁ bTime center hr hrR
        Ksource Kdu Ku Bsource Mdu Mu A Ka omega T := by
  let Q := parabolicCylinder (Icc (0 : Real) S) (Set.univ : Set (Euc n))
  let dtimeChi : ParabolicPoint (Euc n) → Real := fun q ↦
    parabolicBallCutoffTimeDerivative
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real := fun q ↦
    parabolicBallCutoffSpatialFDeriv2
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
        q.time q.space
  let Kcomm := parabolicBallCutoffOperatorCommutatorHolderConst
    aTime t₀ t₁ bTime center hr hrR A Ka Kdu Ku Mdu Mu
  let Bcomm := parabolicBallCutoffOperatorCommutatorSupConst
    aTime t₀ t₁ bTime r R A Mdu Mu
  have hcommHolder : HolderWith Kcomm alpha
      (Q.restrict
        (parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
          (fun t x ↦ u t x) (fun p ↦ du p.time p.space))) := by
    exact parabolicBallCutoffOperatorCommutator_holderWith_restrict
      halpha1.le aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun p ↦ du p.time p.space)
      A Ka Mdu Mu ha hduHolder huHolder haNorm hduNorm huNorm
  have hcommNorm : ∀ p, p ∈ Q →
      ‖parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi
        (fun t x ↦ u t x) (fun q ↦ du q.time q.space) p‖ ≤ Bcomm := by
    intro p hp
    exact norm_parabolicBallCutoffOperatorCommutator_le
      aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      a (fun t x ↦ u t x) (fun q ↦ du q.time q.space)
      A Mdu Mu haNorm hduNorm huNorm p hp
  have hcutoffBound : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≤
      parabolicBallCutoffC2HolderGaugeConst
        aTime t₀ t₁ bTime center hr hrR
        Ku KdtimeU Kdu Kd2u Mu MdtimeU Mdu Md2u := by
    exact eParabolicC2HolderGaugeOn_parabolicBallCutoff_le
      halpha1.le aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR
      u dtimeU du d2u huTime hu hdu huHolder hdtimeUHolder
      hduHolder hd2uHolder huNorm hdtimeUNorm hduNorm hd2uNorm
  have hcutoffFinite : eParabolicC2HolderGaugeOn alpha Q
      (fun t x ↦ parabolicBallCutoff
        aTime t₀ t₁ bTime hat₀ ht₀t₁ ht₁b center hr hrR t x •
          u t x) ≠ ⊤ := by
    exact ne_of_lt (hcutoffBound.trans_lt ENNReal.coe_lt_top)
  simpa only [Q, dtimeChi, dchi, d2chi, Kcomm, Bcomm,
      parabolicVariableCoefficientBallInteriorAbsorbedSchauderConst] using
    (parabolic_variable_coefficient_ball_interior_schauder_estimate_of_cutoff_source_estimates_of_small_freeze_defect
      halpha0 halpha1 haTime hat₀ ht₀t₁ ht₁b hbT hTS center hr hrR
      a p0 hA u dtimeU du d2u huTime hu hdu huCont hsourceHolder
      hcommHolder hsourceNorm hcommNorm Ka omega ha homega
      hcutoffFinite hsmall)

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
