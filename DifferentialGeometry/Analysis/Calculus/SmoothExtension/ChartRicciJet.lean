import DifferentialGeometry.Analysis.Calculus.MatrixInverseSmooth

/-!
# The coordinate Ricci-flow operator as a smooth function of the Gram 2-jet (Φ, Lemma 3)

The standalone operator `Φ` for the Ricci-flow time-jet match (`hglue` corollary (a)): the chart
Ricci-flow RHS `-2·chartRicci` expressed as a function of the chart-Gram spatial `2`-jet
`(g, ∂g, ∂²g)`, and shown `C∞` at any jet whose value matrix is positive-definite (invertible).

The jet is modelled on `jet2` (`TimeJetEvolution.lean`) with value space the `Pi` type
`Fin n → Fin n → ℝ` (default product norm — this avoids putting a norm on `Matrix`, which the
project otherwise avoids; the matrix structure is recovered with `Matrix.of` only for `det`/
`adjugate`/`inverse`). Smoothness of every ingredient reduces to:

* coordinate projections of the jet (`C∞`, continuous-linear), and
* the Cramer inverse `contDiffAt_inv_of_entries` from `MatrixInverseSmooth.lean`,

composed by the polynomial Christoffel/Riemann/Ricci formulas. This file currently builds the
smoothness ingredients bottom-up; the assembled `Φ`, its `chartRicci = Φ(jet2 chartGram)` identity,
and the Ricci-flow evolution `∂ₜ(chartGram) = Φ(jet2 chartGram)` are layered on top.
See `SmoothExtension/JetGlueParam.md`.
-/

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- The spatial `2`-jet space of a matrix-valued field: value, first and second Fréchet derivative,
with the matrix carried as the `Pi` type `Fin n → Fin n → ℝ` (default norm). Mirrors `jet2`'s shape
with `F' = Fin n → Fin n → ℝ`. -/
abbrev MatJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) : Type _ :=
  (Fin n → Fin n → ℝ) ×
    (E →L[ℝ] (Fin n → Fin n → ℝ)) × (E →L[ℝ] (E →L[ℝ] (Fin n → Fin n → ℝ)))

/-- The value entry `p ↦ (value matrix of p) a b` is `C∞` (a chain of continuous-linear coordinate
projections / evaluations of the jet). -/
theorem contDiff_jetVal (a b : Fin n) :
    ContDiff ℝ ∞ (fun p : MatJet E n => p.1 a b) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).contDiff.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) a).contDiff.comp
      contDiff_fst)

/-- The first-derivative entry `p ↦ (∂ along d of p) a b` is `C∞`. -/
theorem contDiff_jetD1 (d : E) (a b : Fin n) :
    ContDiff ℝ ∞ (fun p : MatJet E n => (p.2.1 d) a b) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).contDiff.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) a).contDiff.comp
      ((ContinuousLinearMap.apply ℝ (Fin n → Fin n → ℝ) d).contDiff.comp
        (contDiff_fst.comp contDiff_snd)))

/-- The second-derivative entry `p ↦ (∂² along (d,e) of p) a b` is `C∞`. -/
theorem contDiff_jetD2 (d e : E) (a b : Fin n) :
    ContDiff ℝ ∞ (fun p : MatJet E n => (p.2.2 d e) a b) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).contDiff.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) a).contDiff.comp
      (((contDiff_snd.comp contDiff_snd).clm_apply (contDiff_const (c := d))).clm_apply
        (contDiff_const (c := e))))

/-- The inverse-Gram entry `p ↦ (value matrix)⁻¹ k l` is `C∞` at any jet whose value matrix is
invertible (Cramer's rule, via `contDiffAt_inv_of_entries`). -/
theorem contDiffAt_jetInvGram {p₀ : MatJet E n} (hp₀ : (Matrix.of p₀.1).det ≠ 0) (k l : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => (Matrix.of p.1)⁻¹ k l) p₀ :=
  contDiffAt_inv_of_entries (fun p : MatJet E n => Matrix.of p.1)
    (fun a b => contDiff_jetVal a b) hp₀ k l

/-- The directional derivative of the inverse-Gram entry `∂_m (Gram⁻¹)_{kl} =
−∑_{a,c} (Gram⁻¹)_{ka}(Gram⁻¹)_{cl}·∂_m g_{ac}` (Cramer's rule for the derivative of the inverse) read
off the jet is `C∞` at any invertible-value jet. -/
theorem contDiffAt_jetInvGramDeriv (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (m k l : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n =>
      -∑ a : Fin n, ∑ c : Fin n,
        (Matrix.of p.1)⁻¹ k a * (Matrix.of p.1)⁻¹ c l * (p.2.1 (b m)) a c) p₀ := by
  refine ContDiffAt.neg (ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun c _ => ?_)))
  exact ((contDiffAt_jetInvGram hp₀ k a).mul (contDiffAt_jetInvGram hp₀ c l)).mul
    (contDiff_jetD1 (b m) a c).contDiffAt

/-- The Christoffel symbol `Γ^k_{ij}` read off the jet along directions `b ·`
(`½ ∑_l (Gram)⁻¹_{kl}·(∂ᵢg_{lj}+∂ⱼg_{li}−∂_lg_{ij})`; mirrors `chartChristoffel`). -/
def jetChristoffel (b : Fin n → E) (p : MatJet E n) (i j k : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin n, (Matrix.of p.1)⁻¹ k l *
    ((p.2.1 (b i)) l j + (p.2.1 (b j)) l i - (p.2.1 (b l)) i j)

/-- The directional derivative `∂_m Γ^k_{ij}` read off the jet (the explicit Cramer expansion of
`partialDeriv_chartChristoffel_eq`). -/
def jetChristoffelDeriv (b : Fin n → E) (p : MatJet E n) (m i j k : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin n,
    ((-∑ a : Fin n, ∑ c : Fin n,
          (Matrix.of p.1)⁻¹ k a * (Matrix.of p.1)⁻¹ c l * (p.2.1 (b m)) a c)
        * ((p.2.1 (b i)) l j + (p.2.1 (b j)) l i - (p.2.1 (b l)) i j)
      + (Matrix.of p.1)⁻¹ k l
        * ((p.2.2 (b m) (b i)) l j + (p.2.2 (b m) (b j)) l i - (p.2.2 (b m) (b l)) i j))

/-- The Riemann tensor `R^l{}_{ijk}` read off the jet (mirrors `chartRiemannTensor`). -/
def jetRiemann (b : Fin n → E) (p : MatJet E n) (i j k l : Fin n) : ℝ :=
  jetChristoffelDeriv b p j i k l - jetChristoffelDeriv b p k i j l
    + ∑ m : Fin n, (jetChristoffel b p j m l * jetChristoffel b p i k m
        - jetChristoffel b p k m l * jetChristoffel b p i j m)

/-- The Ricci tensor `Rc_{ik} = ∑_j R^j{}_{ijk}` read off the jet (mirrors `chartRicciTensor`). -/
def jetRicci (b : Fin n → E) (p : MatJet E n) (i k : Fin n) : ℝ :=
  ∑ j : Fin n, jetRiemann b p i j k j

/-- The coordinate Ricci-flow operator `Φ = -2·Ricci`, as a matrix-valued (`Pi`) function of the
jet. This is the standalone `Φ` of `hglue` corollary (a): `∂ₜ(chartGram) = Φ(jet2 chartGram)`. -/
def jetRicciFlow (b : Fin n → E) (p : MatJet E n) : Fin n → Fin n → ℝ :=
  fun i k => -2 * jetRicci b p i k

/-- `jetChristoffel` is `C∞` at any invertible-value jet. -/
theorem contDiffAt_jetChristoffel (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (i j k : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => jetChristoffel b p i j k) p₀ := by
  unfold jetChristoffel
  refine contDiffAt_const.mul (ContDiffAt.sum (fun l _ => ?_))
  refine (contDiffAt_jetInvGram hp₀ k l).mul ?_
  exact (((contDiff_jetD1 (b i) l j).contDiffAt).add (contDiff_jetD1 (b j) l i).contDiffAt).sub
    (contDiff_jetD1 (b l) i j).contDiffAt

/-- `jetChristoffelDeriv` is `C∞` at any invertible-value jet. -/
theorem contDiffAt_jetChristoffelDeriv (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (m i j k : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => jetChristoffelDeriv b p m i j k) p₀ := by
  unfold jetChristoffelDeriv
  refine contDiffAt_const.mul (ContDiffAt.sum (fun l _ => ?_))
  refine ContDiffAt.add (ContDiffAt.mul ?_ ?_) (ContDiffAt.mul ?_ ?_)
  · exact contDiffAt_jetInvGramDeriv b hp₀ m k l
  · exact (((contDiff_jetD1 (b i) l j).contDiffAt).add (contDiff_jetD1 (b j) l i).contDiffAt).sub
      (contDiff_jetD1 (b l) i j).contDiffAt
  · exact contDiffAt_jetInvGram hp₀ k l
  · exact (((contDiff_jetD2 (b m) (b i) l j).contDiffAt).add
      (contDiff_jetD2 (b m) (b j) l i).contDiffAt).sub (contDiff_jetD2 (b m) (b l) i j).contDiffAt

/-- `jetRiemann` is `C∞` at any invertible-value jet. -/
theorem contDiffAt_jetRiemann (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (i j k l : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => jetRiemann b p i j k l) p₀ := by
  unfold jetRiemann
  refine ((contDiffAt_jetChristoffelDeriv b hp₀ j i k l).sub
    (contDiffAt_jetChristoffelDeriv b hp₀ k i j l)).add (ContDiffAt.sum (fun m _ => ?_))
  exact ((contDiffAt_jetChristoffel b hp₀ j m l).mul (contDiffAt_jetChristoffel b hp₀ i k m)).sub
    ((contDiffAt_jetChristoffel b hp₀ k m l).mul (contDiffAt_jetChristoffel b hp₀ i j m))

/-- `jetRicci` is `C∞` at any invertible-value jet. -/
theorem contDiffAt_jetRicci (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (i k : Fin n) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => jetRicci b p i k) p₀ := by
  unfold jetRicci
  exact ContDiffAt.sum (fun j _ => contDiffAt_jetRiemann b hp₀ i j k j)

/-- **The Ricci-flow operator `Φ` is `C∞` at any invertible-value jet.** This discharges the `hΦ`
hypothesis of `jetMatch_of_evolution` (corollary (a)) at the seam jet of a positive-definite metric. -/
theorem contDiffAt_jetRicciFlow (b : Fin n → E) {p₀ : MatJet E n}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : MatJet E n => jetRicciFlow b p) p₀ := by
  refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun k => ?_))
  exact contDiffAt_const.mul (contDiffAt_jetRicci b hp₀ i k)

end Analysis
end DifferentialGeometry

end
