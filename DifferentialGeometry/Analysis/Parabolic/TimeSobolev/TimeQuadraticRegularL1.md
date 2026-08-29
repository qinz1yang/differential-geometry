# L1 momentum regularity

`mom_primitive_l1` uses the actual integral pairing of a raw integrable force
against zero-endpoint time-`H¹` test variations.  It reduces the resulting
distributional identity to `weakDeriv_primitive` with scalar test functions.

`mom_rep_cont_l1` packages the same primitive with its continuous closed-interval
representative.  Focused verification and the targeted module refresh passed.
