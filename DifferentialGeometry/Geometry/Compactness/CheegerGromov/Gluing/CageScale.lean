import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.LiveCenterScale


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Partition

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]


theorem aliveSlots_tail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ k in Filter.atTop, ∀ gamma : Fin (pb.A r),
      (seqCenter hd D P (L.φ k) (gamma : Nat)).isSome =
        L.alive (gamma : Nat) :=
  Filter.eventually_all.mpr fun gamma => L.alive_eventually (gamma : Nat)


theorem hat_mem_live
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    {k : Nat} {gamma : Fin (pb.A r)} {x : (X.obj (L.φ k)).M}
    (hstable : (seqCenter hd D P (L.φ k) (gamma : Nat)).isSome =
      L.alive (gamma : Nat))
    (hx : x ∈ NetLimitData.hatBall (I := I) (X := X) hd D P L pb r k gamma) :
    L.alive (gamma : Nat) = true := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none => simp [NetLimitData.hatBall, hc] at hx
  | some c => simpa [hc] using hstable.symm


theorem hat_dist_centerD
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    {k : Nat} {gamma : Fin (pb.A r)} {x : (X.obj (L.φ k)).M}
    (hx : x ∈ NetLimitData.hatBall (I := I) (X := X) hd D P L pb r k gamma) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    dist x (seqCenterD (I := I) hd P L k (gamma : Nat)) <
      4 * L.lamInf (gamma : Nat) := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none => simp [NetLimitData.hatBall, hc] at hx
  | some c => simpa [NetLimitData.hatBall, seqCenterD, hc] using hx


theorem seqCenterD_dist_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (gamma : Nat) (hgamma : L.alive gamma = true) :
    ∀ᶠ k in Filter.atTop,
      hd.dist (L.φ k) (seqCenterD (I := I) hd P L k gamma)
          (X.obj (L.φ k)).basepoint ≤
        2 * hd.lambda D 0 * (gamma : Real) := by
  filter_upwards [seqCenterD_live (I := I) hd P L gamma hgamma] with k hk
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  rw [← ProperMetricOn.dist_eq hd hre P (L.φ k)]
  have hr : seqRadius hd D P (L.φ k) gamma =
      dist (seqCenterD (I := I) hd P L k gamma)
        (X.obj (L.φ k)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ gamma hk
  rw [← hr]
  exact (seqRadius_mem hd hD P (L.φ k) gamma).2


theorem seqCenterD_rInf_lt
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P) (gamma : Nat) :
    ∀ᶠ k in Filter.atTop,
      hd.dist (L.φ k) (seqCenterD (I := I) hd P L k gamma)
          (X.obj (L.φ k)).basepoint < L.rInf gamma + 1 := by
  have hrad : ∀ᶠ k in Filter.atTop,
      seqRadius hd D P (L.φ k) gamma < L.rInf gamma + 1 :=
    (L.tendsto gamma).eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hrad] with k hk
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  rw [← ProperMetricOn.dist_eq hd hre P (L.φ k),
    ← seqCenterD_dist_eq (I := I) hd P L k gamma]
  exact hk


theorem liveCenters_rInf
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot (I := I) L pb r,
      hd.dist (L.φ k) (seqCenterD (I := I) hd P L k (gamma.1 : Nat))
          (X.obj (L.φ k)).basepoint < L.rInf (gamma.1 : Nat) + 1 :=
  Filter.eventually_all.mpr fun gamma =>
    seqCenterD_rInf_lt (I := I) hd P hre L (gamma.1 : Nat)


theorem lamInf_lt_halfMin
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D aMin : Real} (hD : 0 < D)
    (hphys : 8 * Real.exp hd.C < aMin * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (gamma : Nat) :
    4 * L.lamInf gamma <
      (aMin * hd.mu (L.rInf gamma + 1)) / 2 := by
  have hratio : hd.lambda D (L.rInf gamma) ≤
      Real.exp hd.C * hd.lambda D (L.rInf gamma + 1) := by
    simpa only [mul_one] using hd.lambda_exp_le hD
      (s := L.rInf gamma + 1) (t := L.rInf gamma) (d := 1) (by linarith)
  have hhat : (8 * Real.exp hd.C) * hd.lambda D (L.rInf gamma + 1) <
      aMin * hd.mu (L.rInf gamma + 1) := by
    rw [InjRadiusDecayInput.lambda]
    calc
      (8 * Real.exp hd.C) * (hd.mu (L.rInf gamma + 1) / D) =
          ((8 * Real.exp hd.C) / D) * hd.mu (L.rInf gamma + 1) := by ring
      _ < aMin * hd.mu (L.rInf gamma + 1) :=
        mul_lt_mul_of_pos_right ((div_lt_iff₀ hD).2 hphys)
          (hd.mu_pos (L.rInf gamma + 1))
  calc
    4 * L.lamInf gamma = 4 * hd.lambda D (L.rInf gamma) := rfl
    _ ≤ 4 * (Real.exp hd.C * hd.lambda D (L.rInf gamma + 1)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = ((8 * Real.exp hd.C) * hd.lambda D (L.rInf gamma + 1)) / 2 := by ring
    _ < (aMin * hd.mu (L.rInf gamma + 1)) / 2 :=
      div_lt_div_of_pos_right hhat (by norm_num)


theorem exists_cage_rad
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D aMin : Real} (hD : 0 < D)
    (haMin : 0 < aMin)
    (hphys : 8 * Real.exp hd.C < aMin * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (gamma : Nat)
    (eps : Real) (heps : 0 < eps) :
    ∃ rad : Real, 0 < rad ∧ rad < eps ∧
      ENNReal.ofReal (4 * L.lamInf gamma + 6 * rad) <
        ENNReal.ofReal ((aMin * hd.mu (L.rInf gamma + 1)) / 2) := by
  let rho := aMin * hd.mu (L.rInf gamma + 1)
  let gap := rho / 2 - 4 * L.lamInf gamma
  have hgap : 0 < gap := by
    dsimp only [gap, rho]
    linarith [lamInf_lt_halfMin hd hD hphys P L gamma]
  let rad := min (gap / 12) (eps / 2)
  have hrad : 0 < rad := by
    dsimp only [rad]
    exact lt_min (div_pos hgap (by norm_num)) (div_pos heps (by norm_num))
  have hradGap : rad ≤ gap / 12 := min_le_left _ _
  have hradEps : rad ≤ eps / 2 := min_le_right _ _
  have hreal : 4 * L.lamInf gamma + 6 * rad < rho / 2 := by
    dsimp only [gap] at hradGap
    nlinarith
  refine ⟨rad, hrad, by linarith, ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff
    (div_pos (mul_pos haMin (hd.mu_pos _)) (by norm_num))).2 (by
      simpa only [rho] using hreal)


theorem exists_rad_cage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D aMin : Real} (hD : 0 < D)
    (haMin : 0 < aMin) (hphys : 8 * Real.exp hd.C < aMin * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (s : Set (X.obj (L.φ n)).M)
    (radSeq : Nat → Nat → (X.obj (L.φ n)).M → Real)
    (htail : ∀ epsilon > 0, ∃ N : Nat,
      ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ s, radSeq a b x < epsilon) :
    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ s,
      ∀ gamma : LiveSlot (I := I) L pb r,
        ENNReal.ofReal
            (4 * L.lamInf (gamma.1 : Nat) + 2 * radSeq a b x) <
          ENNReal.ofReal
            ((aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1)) / 2) := by
  classical
  let epsilon : LiveSlot (I := I) L pb r → Real := fun gamma =>
    ((aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1)) / 2 -
      4 * L.lamInf (gamma.1 : Nat)) / 2
  have hepsilon : ∀ gamma : LiveSlot (I := I) L pb r, 0 < epsilon gamma := by
    intro gamma
    dsimp only [epsilon]
    nlinarith [lamInf_lt_halfMin hd hD hphys P L (gamma.1 : Nat)]
  choose N hN using fun gamma : LiveSlot (I := I) L pb r =>
    htail (epsilon gamma) (hepsilon gamma)
  let Nmax : Nat := Finset.univ.sup N
  refine ⟨Nmax, ?_⟩
  intro a ha b hb x hx gamma
  have hgamma : N gamma ≤ Nmax :=
    Finset.le_sup (s := Finset.univ) (f := N) (Finset.mem_univ gamma)
  have hrad := hN gamma a (hgamma.trans ha) b (hgamma.trans hb) x hx
  have hreal : 4 * L.lamInf (gamma.1 : Nat) + 2 * radSeq a b x <
      (aMin * hd.mu (L.rInf (gamma.1 : Nat) + 1)) / 2 := by
    dsimp only [epsilon] at hrad
    linarith
  exact (ENNReal.ofReal_lt_ofReal_iff
    (div_pos (mul_pos haMin (hd.mu_pos _)) (by norm_num))).2 hreal

theorem liveCenters_dist_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot (I := I) L pb r,
      hd.dist (L.φ k) (seqCenterD (I := I) hd P L k (gamma.1 : Nat))
          (X.obj (L.φ k)).basepoint ≤
        2 * hd.lambda D 0 * (gamma.1 : Real) :=
  Filter.eventually_all.mpr fun gamma =>
    seqCenterD_dist_le (I := I) hd hD P hre L (gamma.1 : Nat) gamma.2

theorem liveCenters_cage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot (I := I) L pb r,
      hd.dist (L.φ k) (seqCenterD (I := I) hd P L k (gamma.1 : Nat))
          (X.obj (L.φ k)).basepoint ≤
        2 * hd.lambda D 0 * (pb.A r : Real) := by
  filter_upwards [liveCenters_dist_le hd hD P hre L pb r] with k hk
  intro gamma
  refine (hk gamma).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast Nat.le_of_lt gamma.1.isLt
  · exact (mul_pos (by norm_num) (hd.lambda_pos hD 0)).le

end HCGCompactness
end DifferentialGeometry
