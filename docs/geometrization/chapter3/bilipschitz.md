# Ambient bilipschitz bounds give pointed ball approximations

This development proves the pure metric bridge MC17 from blueprint 207. It does not produce ambient distance bounds or target-ball coverage from a smooth chart or a tensor estimate.

## Source and exact contract

Read the complete proposition and its proof at docs/geometrization/blueprint/master207A.tex:1820–1839, together with the following smooth-domain caveat through line 1862. Blueprint source SHA256:

    277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b

No primary-source theorem is imported into this elementary argument. No new literature or erratum check is claimed. The reference archive remains unchanged.

The public constructor

    GC.MetricGeometry.PointedBallApprox.ofBilipschitz

takes arbitrary metric spaces \(X,Y\), points \(p\in X,q\in Y\), real numbers \(R,\varepsilon,a\), and:

- \(0\le a<1\), expressed as membership in the half-open interval \([0,1)\);
- \(0<\varepsilon<R\), which in particular implies \(R>0\);
- \(2aR<\varepsilon\);
- a function \(f:\overline B_X(p,R)\to Y\) defined on the actual ambient closed ball;
- the exact equality \(f(p)=q\);
- for every two points of that ball, the ambient-distance inequalities
  \[
  (1-a)d_X(x,x')\le d_Y(f(x),f(x'))
       \le(1+a)d_X(x,x');
  \]
- for every \(y\) with \(d_Y(y,q)\le R-\varepsilon\), an \(x\) in the source ball with \(d_Y(y,f(x))<\varepsilon\).

It returns the existing PointedBallApprox with the same \(p,q,R,\varepsilon\), and its underlying function is literally the supplied \(f\). Source and target distances are those of the original metric spaces. No intrinsic-domain distances are substituted. Coverage is a strict error bound on a closed target ball.

The proof's private estimate uses
\[
d_X(x,x')\le d_X(x,p)+d_X(x',p)\le 2R,
\]
and the two supplied inequalities to obtain
\[
\left|d_Y(f(x),f(x'))-d_X(x,x')\right|
  \le a\,d_X(x,x')\le 2aR<\varepsilon.
\]
The other record fields are exactly the given error inequalities, basepoint equality and coverage witness. The estimate itself needs only \(a\ge0\); the public bridge retains the blueprint's stronger \(a<1\) clause, which makes its lower multiplicative bound positive.

## Concrete consumer

The constructor

    GC.MetricGeometry.PointedBallApprox.ofIsometryEquiv

takes an actual isometry equivalence \(e:X\cong Y\), a point \(p\), and any \(0<\varepsilon<R\). It returns a PointedBallApprox from \(p\) to \(e(p)\), using \(x\mapsto e(x)\) on the radius-\(R\) closed ball.

Its proof applies the bilipschitz bridge with \(a=0\). For a target \(y\) in the required smaller ball, it supplies the exact preimage \(e^{-1}(y)\). This lies in the source ball by the isometry identity; the coverage error is zero, strictly less than \(\varepsilon\). Thus the zero-distortion edge case is included without allowing zero approximation error.

## Existing APIs and naming

Before naming the new constructors, searched the library approximation directory and the Mathlib metric/isometry/Gromov–Hausdorff sources for existing pointed approximation constructors and the proposed names. The existing PointedBallApproximation.lean already proves restriction, composition, radial bounds, inverse-lift error bounds and quasi-inverse construction. RealBallExamples.lean already has an identity approximation. Those constructions were not duplicated.

The new module imports the existing pointed-ball leaf and Mathlib's Isometry leaf. It belongs to Geometry/Metric/Approximation and uses the established GC.MetricGeometry.PointedBallApprox namespace. There are no new mathematical structure types, comments, docstrings, admissions or custom axioms in its Lean source. Root aggregate registration is left to the coordinating task.

## Verification actually performed

Executed in the isolated GC_CHAPTER3_435_RC3 checkout:

    lake build DifferentialGeometry.Geometry.Metric.Approximation.Bilipschitz

The target completed successfully: 1,281 Lake jobs, with the new leaf built in 887 ms. This is a narrow dependency build, not a full DifferentialGeometry root build.

Toolchain: Lean 4.35.0-rc3, compiler commit 470d5ce1400764999581fd26d5d72b00d990b0f4, arm64-apple-darwin24.6.0. Mathlib commit c55e6e786f49471c72fbddbec5415808896aec1e. The checkout's initial Git HEAD was 21a85473a9273e366b5ba16e9dfb5e8bfe029aea.

A separate Lean stdin check inspected the elaborated signatures and axiom closures of both public constructors. Each closure contains exactly:

    propext, Classical.choice, Quot.sound

It also successfully elaborated the isometry-equivalence consumer on the real line with basepoint zero, \(R=10,\varepsilon=1\), and proved that PointedBallApprox at \(R=1,\varepsilon=0\) cannot exist. Thus \(a=0\) is exercised, whereas \(\varepsilon=0\) remains excluded by the actual target type.

Source SHA256 for Bilipschitz.lean at this verification:

    23550420ba57550fd92b7a81fe5aa97b9a042f978d8b5f38b1f110194b2d6bc9

The existing PointedBallApproximation.lean read for this development had SHA256:

    c80d9e691fa0e0040f3802e67e064435780d049d97b7cdb2d056fe18d1d2a530

This is a genuine proof of MC17's metric implication. The smooth-domain producer, ambient/intrinsic comparison, buffered exhaustion, and target coverage obligations described immediately after MC17 remain separate work.
