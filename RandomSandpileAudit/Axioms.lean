import RandomSandpile.Assembly.Main

/-! The axiom report of every numbered result of the paper; `scripts/check_axioms.py` checks it.

Each numbered result is reported through its theorems in `RandomSandpile/Assembly/Main.lean`: Theorem
1.1, Lemma 6.2 and Theorem 9.2 have two, two and four theorems. A result proved from literature inputs
takes them as explicit hypotheses of its theorem, so they do not appear in the report. -/

-- Theorem 1.1
#print axioms RandomSandpile.mainTheoremLawRadius_final               -- Theorem 1.1, weaker form
#print axioms RandomSandpile.mainTheorem_final                        -- Theorem 1.1

-- Section 3
#print axioms RandomSandpile.leastAction_final                        -- Proposition 3.1
#print axioms RandomSandpile.abelianDecomposition_final               -- Proposition 3.2
#print axioms RandomSandpile.burning_final                            -- Proposition 3.3
#print axioms RandomSandpile.recurrentOfToppled_final                 -- Proposition 3.4

-- Section 5
#print axioms RandomSandpile.stabilizingLegal_final                   -- Lemma 5.1
#print axioms RandomSandpile.abp_final                                -- Lemma 5.2
#print axioms RandomSandpile.concaveEnvelopeRep_final                 -- Proposition 5.1
#print axioms RandomSandpile.mongeAmpereRep_final                     -- Lemma 5.3
#print axioms RandomSandpile.muBounded_final                          -- Lemma 5.4
#print axioms RandomSandpile.harnackQuadratic_final                   -- Proposition 5.2
#print axioms RandomSandpile.subadditiveErgodic_final                 -- Proposition 5.3
#print axioms RandomSandpile.muConvergence_final                      -- Lemma 5.5

-- Section 6
#print axioms RandomSandpile.muMonotone_final                         -- Lemma 6.1
#print axioms RandomSandpile.strictConcavityBeta_final                -- Lemma 6.2
#print axioms RandomSandpile.strictConcavity_final                    -- Lemma 6.2
#print axioms RandomSandpile.muLipschitz_final                        -- Lemma 6.3
#print axioms RandomSandpile.effectiveOperatorBasic_final             -- Lemma 6.4

-- Section 7
#print axioms RandomSandpile.oneDimToppling_final                     -- Lemma 7.1
#print axioms RandomSandpile.compactness_final                        -- Lemma 7.2
#print axioms RandomSandpile.divisibleHomogenize_final                -- Lemma 7.3
#print axioms RandomSandpile.odometerLowerBound_final                 -- Lemma 7.4
#print axioms RandomSandpile.flat_final                               -- Lemma 7.5
#print axioms RandomSandpile.pegdenSmartRegularity_final              -- Lemma 7.6

-- Section 8
#print axioms RandomSandpile.divisibleLeastAction_final               -- Proposition 8.1
#print axioms RandomSandpile.divisibleHomogenizeDomain_final          -- Lemma 8.1
#print axioms RandomSandpile.divisibleTheorem_final                   -- Theorem 8.2

-- Section 9
#print axioms RandomSandpile.openBoundaryTheorem_final                -- Theorem 9.1
#print axioms RandomSandpile.singleSourceTheoremRecurrent_final       -- Theorem 9.2, height-bound form
#print axioms RandomSandpile.singleSourceTheoremRecurrentVT_final     -- Theorem 9.2, vanishing tail
#print axioms RandomSandpile.recurrentOperatorIdentification_final    -- Theorem 9.2, identification
#print axioms RandomSandpile.recurrentOperatorZeroBackgroundDifference_final  -- Theorem 9.2, zero background
