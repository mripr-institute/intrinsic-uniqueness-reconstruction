# M4: complete Gaussian/Wishart model

Independent reviewer: `/root/coverage_realizations`. **Whole-statement AUDIT PASS.**

The initial source audit found substantial existing local proofs, not four
missing probabilistic developments. Its true remainder was exactly:

1. Actual statistical sufficiency, beyond measurable density factorization.
2. Almost-sure full rank when the sample count is at least the dimension.

Both are now proved. A single native Markov kernel reconstructs the joint
scatter/sample law for every SPD covariance, using a proved disintegration
and density-tilt criterion. Independently sampled absolutely continuous vectors
avoid proper subspaces by native Haar-nullity and product induction, yielding
the exact sample and Wishart positive-definiteness iff. Neither result is a
supplied hypothesis or a definition of the desired conclusion.

The reviewer also checked every previously implemented clause: normalized
zero-mean covariance-X Gaussian measures; arbitrary-space measurable iid joint
and scatter laws; actual likelihood and unique MLE; singular nonattainment;
the full symmetric-Theta extended Wishart transform, including divergence for
zero as well as negative eigenvalues; and native Radon-Nikodym KL with the
correct orientation and independent-copy factor. No residual clause found.
