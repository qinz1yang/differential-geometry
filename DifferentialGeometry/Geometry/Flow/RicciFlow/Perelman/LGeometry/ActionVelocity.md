# ActionVelocity

`chartGram_time` packages the measurable, uniformly bounded fixed-chart Gram
coefficient obtained from compact chart-buffer continuity.  `chartVel_of_mom`
then inverts the actual Gram operator pointwise through `chartGramOp_unit` and
turns a continuous momentum representative into a continuous weak-velocity
representative.

`chartVel_rep_cont` consumes the verified integrable-force weak Euler identity
through `mom_rep_cont_l1`.  It keeps the force at its natural `IntegrableOn`
regularity and exposes no supplied inverse or velocity-regularity hypothesis.
Focused verification and the targeted module refresh passed without warnings.
