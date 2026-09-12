# WindowedWitnessRestriction

Verified continuation of the Claude review. Final focused93 was empty (25.79s),
named lint build93 passed (32.49s), and external audit93 passed (19.00s): both
public declarations depend only on propext, Classical.choice and Quot.sound.
Source SHA256 a4fc18a3042585717c918e93851e3dc9b529ce850563ad5d34a150599a000c22.
Receipts: E:/lean-tools/chapter25-terminal-local-20260909/. Claim2647cd32;
registration/release are recorded in WORKING_STATUS.md.

MetricFamilySmoothOn.coeff already gives ContDiffOn Real infinity for each
metric coefficient on the REGULAR set. For a closed source [0,T], the old
witness window implies that all its interior normalized times map into (0,T).
Hence all old comparison time jets are smooth there. Their restriction at a
new left endpoint uses actual differentiability; the common terminal endpoint
uses equality of the old and new interval germs, not terminal differentiability.

The consumer is selected_countersequence_of_radius_failure: every counterexample
source is a closed [0,T] flow. This removes that producer's
OrientedWitnessRestriction input without asserting the overgeneral arbitrary-D
oriented_witness_mono card. A general RealTimeInterval's regular set need not
contain its carrier interior.

Implementation detail worth reusing: derive all comparison time jets' interior
smoothness by induction from the old jet_succ identity. Use const_smul on the
metric-coefficient smoothness proof before rewriting real scalar multiplication;
generic mul introduced a mismatched Real normed-space instance during elaboration.
